use super::rel::{
    exact_repeated_group_aggregate_definition, exact_repeated_group_identifier_lineage,
};
use super::scalar::{rel_expr_may_raise_runtime, scalar_ast_may_raise_runtime_for_input};
use super::*;
use crate::core::syntax::{FormalScalarQuantifier, query_expr_output_signature};
use std::fs;
use std::process::Command;

use logos_ir::calcite::CalciteFile;
use logos_ir::convert_raw_file;
use logos_ir::ir::ScalarOp;

use logos_ir::ir::{
    AggregateCall, AggregateModifiers, CheckConstraint, Column, CorrelationBinding,
    ForeignKeyConstraint, ForeignKeyMatch, IntegrityComparison, IntegrityPredicate,
    IntegritySortDirection, IntegrityValueExpr, JoinType, Query, QueryAnalysisError,
    QueryBinding as IrQueryBinding, RelExpr, ScalarAst, ScalarExpr, ScalarSourceClauseOwnership,
    ScalarSourceProvenance, Schema, SetOp, SortDirection, SortKey, SortNullDirection,
    SourceClauseKind, SourceGroupingProvenance, SqlStringType, SqlType, Table, TableConstraints,
    UniqueIndexConstraint, UniqueIndexTerm, WindowAst, WindowFrameAst, WindowFrameBoundAst,
    WindowFrameUnits, WindowOrderKey,
};

#[test]
fn lowers_query_local_binding_once_and_emits_bound_query_program() {
    let output = vec![typed_column("x", SqlType::Integer)];
    let definition = one_row_values(
        output.clone(),
        vec![ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: "1".to_owned(),
            }),
            ty: "INTEGER".to_owned(),
        }],
    );
    let reference = || RelExpr::QueryRef {
        binding: "cte_binding_0".to_owned(),
        output: output.clone(),
    };
    let body = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![reference(), reference()],
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Bindings {
            bindings: vec![IrQueryBinding {
                id: "cte_binding_0".to_owned(),
                source_name: "shared_rows".to_owned(),
                rel: definition,
            }],
            body: Box::new(body),
            output,
        },
        analysis_errors: Vec::new(),
    };
    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(lowered.bindings.len(), 1);
    assert_eq!(lowered.bindings[0].source_name, "shared_rows");
    assert_eq!(lowered.bindings[0].relation, "__logos_test_0_cte_0");

    let body = lowered.query_expr.as_ref().unwrap();
    let signature = lowered.output_signature.as_deref().unwrap();
    let target = lower_query(&Query {
        source_sql: None,
        rel: one_row_values(
            vec![typed_column("x", SqlType::Integer)],
            vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            }],
        ),
        analysis_errors: Vec::new(),
    });
    let module = emit_rocq_bound_query_program_module_with_signatures(
        &[(body, signature, lowered.bindings.as_slice())],
        &[(
            target.query_expr.as_ref().unwrap(),
            target.output_signature.as_deref().unwrap(),
            &[],
        )],
    )
    .expect("bound query module");
    assert!(
        module
            .rocq_module
            .contains("Definition source_query_binding_0_0_expr")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition source_bound_query_program")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition target_bound_query_program")
    );
    assert!(module.rocq_module.contains("declare_local_query_schemas"));
    assert_eq!(
        module
            .rocq_module
            .matches("Definition source_query_binding_0_0 :")
            .count(),
        1,
        "one CTE definition must be represented by one materialized binding"
    );

    let proof = emit_rocq_bound_query_proof_module_for_mode(VerificationMode::OutcomeUnconditional);
    assert!(
        proof
            .rocq_module
            .contains("bound_query_program_demand_safe_outcome_equiv"),
        "error-preserving acceptance must not trust eager CTE errors"
    );
    assert!(
        proof
            .rocq_module
            .contains("generated_query_program_materialization_safe"),
        "bound-query countermodels must certify local-binding materialization safety"
    );
}

#[test]
fn query_local_binding_preserves_typmodless_numeric_display_scale() {
    let definition_output = vec![decimal_column_unconstrained("total")];
    let definition = RelExpr::Aggregate {
        input: Box::new(one_row_values(
            vec![decimal_column("amount", 7, 2)],
            vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.00".to_owned(),
                }),
                ty: "DECIMAL(7,2)".to_owned(),
            }],
        )),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "SUM($0)".to_owned(),
            function: "SUM".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: definition_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Bindings {
            bindings: vec![IrQueryBinding {
                id: "cte_binding_0".to_owned(),
                source_name: "totals".to_owned(),
                rel: definition,
            }],
            body: Box::new(RelExpr::Aggregate {
                input: Box::new(RelExpr::QueryRef {
                    binding: "cte_binding_0".to_owned(),
                    output: definition_output,
                }),
                group_keys: Vec::new(),
                grouping_sets: vec![Vec::new()],
                agg_calls: vec![AggregateCall {
                    raw: "AVG($0)".to_owned(),
                    function: "AVG".to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                }],
                output: vec![decimal_column_unconstrained("average_total")],
            }),
            output: vec![decimal_column_unconstrained("average_total")],
        },
        analysis_errors: Vec::new(),
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let body = lowered.query_expr.as_ref().expect("bound query body");
    let signature = lowered
        .output_signature
        .as_deref()
        .expect("output signature");
    let module = emit_rocq_bound_query_program_module_with_signatures(
        &[(body, signature, lowered.bindings.as_slice())],
        &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
    )
    .expect("bound query module");
    assert!(
        module
            .rocq_module
            .contains("AAggregate (AggregateAverageNumericAtScale (2)%Z) AggregateAll"),
        "a typmodless SUM result must retain its independently proved display scale across the local binding"
    );
}

#[test]
fn bound_query_emission_rejects_cross_component_boolean_site_reuse() {
    let query_with_site = || FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::And {
            insertion_sites: vec![Vec::new(), vec!["shared-site".to_owned()]],
            operands: vec![FormalScalarExpr::True, FormalScalarExpr::True],
        },
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let body = query_with_site();
    let binding_query = query_with_site();
    let binding = FormalQueryBinding {
        id: "binding".to_owned(),
        source_name: "shared_rows".to_owned(),
        relation: "__logos_test_cte".to_owned(),
        output_signature: Vec::new(),
        query_expr: binding_query,
    };
    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(&body, &[], &[binding])],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_none(),
        "one statement-wide Boolean schedule requires globally unique site identities"
    );
}

#[test]
fn bound_query_emission_rejects_forward_local_relation_references() {
    let later_relation = "__logos_test_later_cte".to_owned();
    let first = FormalQueryBinding {
        id: "first".to_owned(),
        source_name: "first".to_owned(),
        relation: "__logos_test_first_cte".to_owned(),
        output_signature: Vec::new(),
        query_expr: FormalQueryExpr::Table {
            relation: later_relation.clone(),
            columns: Vec::new(),
        },
    };
    let later = FormalQueryBinding {
        id: "later".to_owned(),
        source_name: "later".to_owned(),
        relation: later_relation,
        output_signature: Vec::new(),
        query_expr: FormalQueryExpr::EmptyTuple,
    };
    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(&FormalQueryExpr::EmptyTuple, &[], &[first, later])],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_none(),
        "a CTE definition may reference only lexically earlier local bindings"
    );
}

#[test]
fn bound_query_emission_rejects_non_authoritative_local_scan_order() {
    let first = formal_attribute("first", FormalAttributeType::Z);
    let second = formal_attribute("second", FormalAttributeType::Bool);
    let authoritative = vec![first.clone(), second.clone()];
    let forged = vec![second, first];
    let relation = "__logos_test_ordered_cte".to_owned();
    let binding = FormalQueryBinding {
        id: "ordered".to_owned(),
        source_name: "ordered".to_owned(),
        relation: relation.clone(),
        output_signature: authoritative.clone(),
        query_expr: FormalQueryExpr::Empty {
            columns: authoritative,
        },
    };
    let body = FormalQueryExpr::Table {
        relation,
        columns: forged.clone(),
    };

    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(&body, forged.as_slice(), &[binding])],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_none(),
        "a local scan must retain the binding's exact name/type/arity/order signature"
    );
}

#[test]
fn bound_query_emission_rejects_non_root_analysis_errors() {
    let binding_error = FormalQueryBinding {
        id: "error".to_owned(),
        source_name: "error".to_owned(),
        relation: "__logos_test_error_cte".to_owned(),
        output_signature: Vec::new(),
        query_expr: FormalQueryExpr::Error {
            columns: Vec::new(),
            error: FormalQueryError::UndefinedColumn,
        },
    };
    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(&FormalQueryExpr::EmptyTuple, &[], &[binding_error])],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_none(),
        "a binding-local analysis error must not be executed as a CTE"
    );

    let ordinary_binding = FormalQueryBinding {
        id: "ordinary".to_owned(),
        source_name: "ordinary".to_owned(),
        relation: "__logos_test_ordinary_cte".to_owned(),
        output_signature: Vec::new(),
        query_expr: FormalQueryExpr::EmptyTuple,
    };
    let root_error = FormalQueryExpr::Error {
        columns: Vec::new(),
        error: FormalQueryError::UndefinedColumn,
    };
    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(&root_error, &[], &[ordinary_binding])],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_none(),
        "a statement-root analysis error must take priority over and remove all bindings"
    );
}

#[test]
fn lowering_promotes_attested_bound_analysis_error_to_the_statement_root() {
    let outer_output = vec![typed_column("x", SqlType::Integer)];
    let binding_output = vec![typed_column("y", SqlType::Integer)];
    let typed_one = || ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: "1".to_owned(),
        }),
        ty: "INTEGER".to_owned(),
    };
    let query = Query {
        source_sql: Some("with local as (select 1 as y) select 1 as x order by x + 1".to_owned()),
        rel: RelExpr::Bindings {
            bindings: vec![IrQueryBinding {
                id: "local".to_owned(),
                source_name: "local".to_owned(),
                rel: one_row_values(binding_output, vec![typed_one()]),
            }],
            body: Box::new(one_row_values(outer_output.clone(), vec![typed_one()])),
            output: outer_output,
        },
        analysis_errors: vec![
            QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                sql_state: "42703".to_owned(),
                query_block_id: "query-0".to_owned(),
                source_order_item_node_id: "query-0/order-0".to_owned(),
                source_order_item_sql: "x + 1".to_owned(),
                output_alias: "x".to_owned(),
            },
        ],
    };

    let lowered = lower_query_with_schema_config(
        &query,
        &Schema { tables: Vec::new() },
        &LoweringConfig::default(),
    );
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(
        lowered.bindings.is_empty(),
        "statement analysis happens before any query-local binding executes"
    );
    let Some(FormalQueryExpr::Error { columns, error }) = lowered.query_expr.as_ref() else {
        panic!("attested analysis error must be the sole statement root: {lowered:#?}");
    };
    assert_eq!(*error, FormalQueryError::UndefinedColumn);
    assert_eq!(Some(columns), lowered.output_signature.as_ref());
    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(
                lowered.query_expr.as_ref().unwrap(),
                lowered.output_signature.as_deref().unwrap(),
                lowered.bindings.as_slice(),
            )],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_some(),
        "canonical root analysis errors remain emit-ready"
    );
}

#[test]
fn binding_root_analysis_error_normalizes_to_the_outer_statement_signature() {
    let outer_columns = vec![formal_attribute("outer", FormalAttributeType::Z)];
    let mut body = Some(FormalQueryExpr::Empty {
        columns: outer_columns.clone(),
    });
    let mut bindings = vec![FormalQueryBinding {
        id: "local_error".to_owned(),
        source_name: "local_error".to_owned(),
        relation: "__logos_local_error".to_owned(),
        output_signature: vec![formal_attribute("inner", FormalAttributeType::Bool)],
        query_expr: FormalQueryExpr::Error {
            columns: vec![formal_attribute("inner", FormalAttributeType::Bool)],
            error: FormalQueryError::UndefinedFunction,
        },
    }];

    assert_eq!(
        normalize_bound_analysis_errors(&mut bindings, &mut body),
        BoundAnalysisErrorNormalization::Promoted
    );
    assert!(bindings.is_empty());
    assert_eq!(
        body,
        Some(FormalQueryExpr::Error {
            columns: outer_columns,
            error: FormalQueryError::UndefinedFunction,
        })
    );
}

fn scheduled_boolean_value(site: &str) -> FormalScalarExpr {
    FormalScalarExpr::BooleanValue {
        expression: Box::new(FormalScalarExpr::And {
            insertion_sites: vec![Vec::new(), vec![site.to_owned()]],
            operands: vec![FormalScalarExpr::True, FormalScalarExpr::True],
        }),
    }
}

#[test]
fn join_select_lists_participate_in_boolean_and_analysis_validation() {
    let repeated_site_join = FormalQueryExpr::Join {
        join_kind: FormalQueryJoinKind::Left,
        predicate: FormalScalarExpr::True,
        matched_select: vec![
            FormalScalarSelectItem {
                expr: scheduled_boolean_value("join.select.shared"),
                alias: "left_bool".to_owned(),
                alias_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
            FormalScalarSelectItem {
                expr: scheduled_boolean_value("join.select.shared"),
                alias: "right_bool".to_owned(),
                alias_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
        ],
        left_select: vec![
            FormalScalarSelectItem {
                expr: FormalScalarExpr::BooleanValue {
                    expression: Box::new(FormalScalarExpr::True),
                },
                alias: "left_bool".to_owned(),
                alias_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
            FormalScalarSelectItem {
                expr: FormalScalarExpr::BooleanValue {
                    expression: Box::new(FormalScalarExpr::True),
                },
                alias: "right_bool".to_owned(),
                alias_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
        ],
        right_select: Vec::new(),
        left: Box::new(FormalQueryExpr::EmptyTuple),
        right: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let repeated_signature = query_expr_output_signature(&repeated_site_join).unwrap();
    assert!(
        emit_rocq_query_program_module_with_signatures(
            &[(&repeated_site_join, repeated_signature.as_slice())],
            &[(&FormalQueryExpr::EmptyTuple, &[])],
        )
        .is_none(),
        "JOIN projection sites share the statement-wide Boolean schedule namespace"
    );

    let nested_error_join = FormalQueryExpr::Join {
        join_kind: FormalQueryJoinKind::Left,
        predicate: FormalScalarExpr::True,
        matched_select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Subquery {
                result_ty: FormalAttributeType::Z,
                query: Box::new(FormalQueryExpr::Error {
                    columns: vec![formal_attribute("value", FormalAttributeType::Z)],
                    error: FormalQueryError::UndefinedColumn,
                }),
            },
            alias: "value".to_owned(),
            alias_ty: FormalAttributeType::Z,
            numeric_dscale: None,
        }],
        left_select: vec![z_select_item("value")],
        right_select: Vec::new(),
        left: Box::new(FormalQueryExpr::EmptyTuple),
        right: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let nested_signature = query_expr_output_signature(&nested_error_join).unwrap();
    assert!(
        emit_rocq_query_program_module_with_signatures(
            &[(&nested_error_join, nested_signature.as_slice())],
            &[(&FormalQueryExpr::EmptyTuple, &[])],
        )
        .is_none(),
        "an analysis error inside a JOIN projection scalar subquery is not a statement root"
    );
}

#[test]
fn join_select_scalar_subqueries_participate_in_local_dependency_validation() {
    let later_relation = "__logos_test_join_select_later".to_owned();
    let later_output = vec![formal_attribute("x", FormalAttributeType::Z)];
    let first_output = vec![formal_attribute("projected", FormalAttributeType::Z)];
    let first = FormalQueryBinding {
        id: "first".to_owned(),
        source_name: "first".to_owned(),
        relation: "__logos_test_join_select_first".to_owned(),
        output_signature: first_output.clone(),
        query_expr: FormalQueryExpr::Join {
            join_kind: FormalQueryJoinKind::Left,
            predicate: FormalScalarExpr::True,
            matched_select: vec![FormalScalarSelectItem {
                expr: FormalScalarExpr::Subquery {
                    result_ty: FormalAttributeType::Z,
                    query: Box::new(FormalQueryExpr::Table {
                        relation: later_relation.clone(),
                        columns: later_output.clone(),
                    }),
                },
                alias: "projected".to_owned(),
                alias_ty: FormalAttributeType::Z,
                numeric_dscale: None,
            }],
            left_select: vec![z_select_item("projected")],
            right_select: Vec::new(),
            left: Box::new(FormalQueryExpr::EmptyTuple),
            right: Box::new(FormalQueryExpr::EmptyTuple),
        },
    };
    let later = FormalQueryBinding {
        id: "later".to_owned(),
        source_name: "later".to_owned(),
        relation: later_relation,
        output_signature: later_output.clone(),
        query_expr: FormalQueryExpr::Empty {
            columns: later_output,
        },
    };

    assert!(
        emit_rocq_bound_query_program_module_with_signatures(
            &[(&FormalQueryExpr::EmptyTuple, &[], &[first, later])],
            &[(&FormalQueryExpr::EmptyTuple, &[], &[])],
        )
        .is_none(),
        "a forward CTE reference cannot hide inside a JOIN projection scalar subquery"
    );
}

#[test]
fn generated_numeric_annotations_use_the_shared_closed_parser() {
    for ty in [
        "INTEGER",
        "DOUBLE PRECISION",
        "NUMERIC",
        "NUMERIC(10, 2)",
        "DECIMAL(8,0)",
    ] {
        assert!(generated_numeric_type_annotation(ty), "rejected valid {ty}");
    }
    for malformed in [
        "NUMERIC(10)",
        "NUMERIC(+10,2)",
        "NUMERIC(10,-2)",
        "NUMERIC(10,2) trailing",
        "NUMERIC(10,,2)",
        "DECIMAL",
    ] {
        assert!(
            !generated_numeric_type_annotation(malformed),
            "accepted malformed generated annotation {malformed}"
        );
    }
}

fn emit_rocq_query_module_for_test(query: &Query) -> FormalQueryModule {
    let lowered = lower_query(query);
    let query_expr = lowered
        .query_expr
        .as_ref()
        .expect("test query should lower to an exact query expression");
    emit_rocq_query_module(query_expr, query_expr)
}

fn emitted_definition_shape<'a>(module: &'a FormalQueryModule, symbol: &str) -> &'a str {
    &module
        .definition_graph
        .definitions
        .iter()
        .find(|definition| definition.symbol == symbol)
        .unwrap_or_else(|| panic!("missing emitted definition shape for {symbol}"))
        .tree
}

fn assert_no_physical_plan_constructs(module: &FormalQueryModule) {
    for marker in [
        "QExpr_Pg",
        "frozen_",
        "PgFetch",
        "PgGroupFetch",
        "PgInnerJoin",
    ] {
        assert!(
            !module.rocq_module.contains(marker),
            "declarative lowering emitted physical-plan marker {marker}"
        );
    }
}

/// A scalar-subquery owner may now have one capture-avoiding input rename and
/// one public-name restoring projection around its Selection.  Tests that
/// inspect the predicate should treat that transparent output boundary as
/// part of the lowering invariant rather than requiring Selection at the
/// root.
fn selection_under_optional_output_restore(
    query: &FormalQueryExpr,
) -> Option<(&FormalScalarExpr, &FormalQueryExpr)> {
    let query = match query {
        FormalQueryExpr::Projection { input, .. }
            if matches!(input.as_ref(), FormalQueryExpr::Selection { .. }) =>
        {
            input.as_ref()
        }
        query => query,
    };
    let FormalQueryExpr::Selection { predicate, input } = query else {
        return None;
    };
    Some((predicate, input.as_ref()))
}

#[test]
fn proof_emitters_select_success_outcome_and_conditional_goals() {
    let safe = emit_rocq_query_expr_proof_module_for_mode(VerificationMode::SafeUnconditional);
    assert!(
        safe.rocq_module
            .contains("@query_program_possible_equiv TNull relname")
    );
    assert!(
        safe.rocq_module
            .contains("@eval_query_expr_possible_outcome TNull relname")
    );
    assert!(
        !safe
            .rocq_module
            .contains("@query_program_equiv TNull relname")
    );
    assert!(
        !safe
            .rocq_module
            .contains("generated_precondition_obligation")
    );
    assert!(safe.rocq_module.contains("generated_countermodel_goal"));
    assert!(
        safe.rocq_module
            .contains("Logos.FormalSQL.VerificationConditions.verification_claim_kind :=")
    );
    assert!(
        safe.rocq_module
            .contains("Definition generated_query_program_outcome_equiv")
    );
    let countermodel = safe
        .rocq_module
        .find("Definition generated_countermodel_goal")
        .expect("unconditional countermodel statement");
    let fixed_db = safe.rocq_module[countermodel..]
        .find("Witness.generated_witness_db")
        .expect("one host-frozen database witness");
    let source_program = safe.rocq_module[countermodel..]
        .find("source_query_program")
        .expect("source program in the countermodel contract");
    assert!(
        fixed_db < source_program,
        "the fixed database witness must precede the compared programs"
    );

    let outcome =
        emit_rocq_query_expr_proof_module_for_mode(VerificationMode::OutcomeUnconditional);
    assert!(
        outcome
            .rocq_module
            .contains("@query_program_possible_outcome_equiv TNull relname")
    );
    assert!(
        !outcome
            .rocq_module
            .contains("@query_program_outcome_equiv TNull relname")
    );
    assert!(
        !outcome
            .rocq_module
            .contains("generated_precondition_obligation")
    );

    let conditional = emit_rocq_query_expr_proof_module_for_mode(VerificationMode::Conditional);
    assert!(
        conditional
            .rocq_module
            .contains("@query_program_possible_outcome_equiv TNull relname")
    );
    assert!(
        conditional
            .rocq_module
            .contains("generated_precondition_obligation")
    );
    assert!(
        conditional
            .rocq_module
            .contains("Logos.FormalSQL.VerificationConditions.verification_condition")
    );
    assert!(
        conditional
            .rocq_module
            .contains("Logos.FormalSQL.VerificationConditions.precondition_source")
    );
    assert!(
        conditional
            .rocq_module
            .contains("verification_condition_holds db condition ->")
    );
    assert!(
        !conditional
            .rocq_module
            .contains("Definition generated_countermodel_goal")
    );
    assert!(
        !conditional
            .rocq_module
            .contains("generated_verification_claim")
    );
}

fn scalar_validation_query(expr: FormalAggregateTerm) -> FormalQueryExpr {
    FormalQueryExpr::Projection {
        select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Bool,
                term: expr,
            },
            alias: "value".to_owned(),
            alias_ty: FormalAttributeType::Bool,
            numeric_dscale: None,
        }],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    }
}

fn formal_attribute(name: &str, ty: FormalAttributeType) -> FormalAttribute {
    FormalAttribute {
        name: name.to_owned(),
        ty,
    }
}

#[test]
fn scalar_operator_arity_table_rejects_nearby_malformed_calls() {
    let exact = [
        (ScalarOperator::PredicateValue(FormalPredicate::IsNull), 1),
        (ScalarOperator::PredicateValue(FormalPredicate::Eq), 2),
        (ScalarOperator::Boolean(ScalarBooleanOperator::And), 2),
        (ScalarOperator::Boolean(ScalarBooleanOperator::Not), 1),
        (ScalarOperator::StringCase(ScalarStringCase::Upper), 1),
        (ScalarOperator::ExtractDate(ScalarDatePart::Year), 1),
        (ScalarOperator::Cast(ScalarCast::Identity), 1),
        (
            ScalarOperator::Cast(ScalarCast::ToNumericTypmod(ScalarNumericSource::Int32)),
            3,
        ),
        (ScalarOperator::Cast(ScalarCast::StringExplicit), 3),
        (ScalarOperator::Add(ScalarNumericKind::Numeric), 2),
        (ScalarOperator::Divide(ScalarNumericKind::Int32), 2),
        (ScalarOperator::Divide(ScalarNumericKind::Numeric), 4),
        (ScalarOperator::Negate(ScalarNumericKind::Int64), 1),
        (ScalarOperator::NumericDivideResultScale, 4),
        (ScalarOperator::NumericDivideTypmod, 6),
        (ScalarOperator::PowerHalfInt64ToInt32, 1),
        (ScalarOperator::StringConcat, 2),
        (ScalarOperator::SubstringNonnegative, 3),
        (ScalarOperator::TimestampAdd(ScalarTimestampUnit::Second), 2),
    ];
    for (operator, arity) in exact {
        assert!(operator.accepts_arity(arity), "{operator:?}");
        assert!(!operator.accepts_arity(arity + 1), "{operator:?}");
    }
    assert!(ScalarOperator::Case.accepts_arity(3));
    assert!(!ScalarOperator::Case.accepts_arity(0));
    assert!(!ScalarOperator::Case.accepts_arity(1));
    assert!(!ScalarOperator::Case.accepts_arity(2));
}

#[test]
fn aggregate_function_terms_match_rocq_strict_admission_boundary() {
    let function_constant = |raw: &str, ty| FormalFunctionTerm::Constant {
        raw: raw.to_owned(),
        ty: Some(ty),
    };
    let hidden_calls = vec![
        (
            "CASE",
            FormalFunctionTerm::ScalarCall {
                operator: ScalarOperator::Case,
                args: vec![
                    function_constant("true", FormalAttributeType::Bool),
                    function_constant("1", FormalAttributeType::Int32),
                    function_constant("0", FormalAttributeType::Int32),
                ],
            },
        ),
        (
            "predicate value",
            FormalFunctionTerm::ScalarCall {
                operator: ScalarOperator::PredicateValue(FormalPredicate::IsNull),
                args: vec![function_constant("1", FormalAttributeType::Int32)],
            },
        ),
        (
            "Boolean NOT",
            FormalFunctionTerm::ScalarCall {
                operator: ScalarOperator::Boolean(ScalarBooleanOperator::Not),
                args: vec![function_constant("true", FormalAttributeType::Bool)],
            },
        ),
        (
            "scheduled Boolean AND",
            FormalFunctionTerm::ScalarCall {
                operator: ScalarOperator::Boolean(ScalarBooleanOperator::And),
                args: vec![
                    function_constant("true", FormalAttributeType::Bool),
                    function_constant("false", FormalAttributeType::Bool),
                ],
            },
        ),
    ];

    for (label, arg) in hidden_calls {
        let query = FormalQueryExpr::Group {
            select: vec![FormalScalarSelectItem {
                expr: FormalScalarExpr::Leaf {
                    result_ty: FormalAttributeType::Int64,
                    term: FormalAggregateTerm::Aggregate {
                        function: FormalAggregateFunction::Count,
                        quantifier: FormalAggregateQuantifier::All,
                        arg,
                    },
                },
                alias: "counted".to_owned(),
                alias_ty: FormalAttributeType::Int64,
                numeric_dscale: None,
            }],
            group_by: Vec::new(),
            having: FormalScalarExpr::True,
            input: Box::new(FormalQueryExpr::EmptyTuple),
        };
        let error = validate_query_expr_scalar_operators(&query)
            .expect_err("strict aggregate argument must be rejected");
        assert!(
            error.contains("strict aggregate function terms reject CASE, Boolean, and predicate-value operators"),
            "{label}: {error}"
        );
        assert!(
            try_emit_rocq_query_module(&query, &query).is_none(),
            "{label} must fail before Rocq emission"
        );
    }

    let value_leaf = |raw: &str| FormalScalarExpr::Leaf {
        result_ty: FormalAttributeType::Int32,
        term: FormalAggregateTerm::Expr {
            term: function_constant(raw, FormalAttributeType::Int32),
        },
    };
    let is_null = || FormalScalarExpr::Predicate {
        predicate: FormalPredicate::IsNull,
        args: vec![value_leaf("1")],
    };
    let canonical = FormalQueryExpr::Projection {
        select: vec![
            FormalScalarSelectItem {
                expr: FormalScalarExpr::Case {
                    result_ty: FormalAttributeType::Int32,
                    condition: Box::new(is_null()),
                    then_expr: Box::new(value_leaf("1")),
                    else_expr: Box::new(value_leaf("0")),
                },
                alias: "case_value".to_owned(),
                alias_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
            FormalScalarSelectItem {
                expr: FormalScalarExpr::BooleanValue {
                    expression: Box::new(FormalScalarExpr::And {
                        insertion_sites: vec![Vec::new(), vec!["typed_boolean_rhs".to_owned()]],
                        operands: vec![is_null(), FormalScalarExpr::True],
                    }),
                },
                alias: "boolean_value".to_owned(),
                alias_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
        ],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    validate_query_expr_scalar_operators(&canonical)
        .expect("typed CASE, predicate, Boolean schedule, and BooleanValue remain canonical");
    let module = try_emit_rocq_query_module(&canonical, &canonical)
        .expect("canonical scalar expressions should emit");
    assert!(
        module
            .rocq_module
            .contains("|- forall truth, _ => intros []; reflexivity")
    );
    assert!(
        module
            .rocq_module
            .contains("Lemma scalar_select_list_0_admissible_row_select_generated_schema")
    );
    assert!(
        module
            .rocq_module
            .contains("apply (scalar_select_list_0_admissible_row_select_generated_schema).")
    );
}

#[test]
fn window_items_share_the_rocq_scalar_leaf_shape_boundary() {
    let aggregate_constant = |raw: &str, ty| FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::Constant {
            raw: raw.to_owned(),
            ty: Some(ty),
        },
    };
    let invalid_functions = vec![
        (
            "ordinary aggregate-term call",
            FormalWindowFunction::Aggregate {
                term: FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::Add(ScalarNumericKind::Int32),
                    args: vec![
                        aggregate_constant("1", FormalAttributeType::Int32),
                        aggregate_constant("2", FormalAttributeType::Int32),
                    ],
                },
            },
        ),
        (
            "structured aggregate-term CASE",
            FormalWindowFunction::FullPartitionAggregate {
                term: FormalAggregateTerm::Case {
                    branches: vec![FormalCaseBranch {
                        when: aggregate_constant("true", FormalAttributeType::Bool),
                        then_expr: aggregate_constant("1", FormalAttributeType::Int32),
                    }],
                    else_expr: Box::new(aggregate_constant("0", FormalAttributeType::Int32)),
                },
            },
        ),
    ];

    let window_query = |function| FormalQueryExpr::Window {
        partition_keys: Vec::new(),
        order_keys: Vec::new(),
        items: vec![FormalWindowItem {
            output: formal_attribute("window_value", FormalAttributeType::Int32),
            function,
            numeric_dscale: None,
        }],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    for (label, function) in invalid_functions {
        let query = window_query(function);
        let error = validate_query_expr_scalar_operators(&query)
            .expect_err("window items must use the scalar leaf shape");
        assert!(
            error.contains("window items use the same leaf boundary"),
            "{label}: {error}"
        );
        assert!(
            try_emit_rocq_query_module(&query, &query).is_none(),
            "{label} must fail before Rocq emission"
        );
    }

    let admitted = FormalQueryExpr::Window {
        partition_keys: Vec::new(),
        order_keys: Vec::new(),
        items: vec![FormalWindowItem {
            output: formal_attribute("window_count", FormalAttributeType::Int64),
            function: FormalWindowFunction::Aggregate {
                term: FormalAggregateTerm::Aggregate {
                    function: FormalAggregateFunction::Count,
                    quantifier: FormalAggregateQuantifier::All,
                    arg: FormalFunctionTerm::Constant {
                        raw: "1".to_owned(),
                        ty: Some(FormalAttributeType::Int32),
                    },
                },
            },
            numeric_dscale: None,
        }],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    validate_query_expr_scalar_operators(&admitted)
        .expect("a true aggregate window leaf remains admitted");
    let module = try_emit_rocq_query_module(&admitted, &admitted)
        .expect("a true aggregate window leaf should emit Rocq");
    assert!(
        module
            .rocq_module
            .contains("unfold WindowAggregateItem, TNullLeafHasType; split; reflexivity.")
    );

    let full_partition = window_query(FormalWindowFunction::FullPartitionAggregate {
        term: FormalAggregateTerm::Aggregate {
            function: FormalAggregateFunction::MinInt32,
            quantifier: FormalAggregateQuantifier::All,
            arg: FormalFunctionTerm::Constant {
                raw: "1".to_owned(),
                ty: Some(FormalAttributeType::Int32),
            },
        },
    });
    let module = try_emit_rocq_query_module(&full_partition, &full_partition)
        .expect("a full-partition aggregate window leaf should emit Rocq");
    assert!(module.rocq_module.contains(
        "unfold WindowFullPartitionAggregateItem, TNullLeafHasType; split; reflexivity."
    ));
}

#[test]
fn malformed_scalar_calls_are_rejected_before_rocq_emission() {
    let malformed_arity = scalar_validation_query(FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::ScalarCall {
            operator: ScalarOperator::Boolean(ScalarBooleanOperator::Not),
            args: Vec::new(),
        },
    });
    let error = validate_query_expr_scalar_operators(&malformed_arity)
        .expect_err("zero-argument NOT must be rejected");
    assert!(error.contains("scalar leaves admit only atomic"));
    assert!(try_emit_rocq_query_module(&malformed_arity, &malformed_arity).is_none());

    let strict_boolean = scalar_validation_query(FormalAggregateTerm::ScalarCall {
        operator: ScalarOperator::Boolean(ScalarBooleanOperator::And),
        args: vec![
            FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "true".to_owned(),
                    ty: Some(FormalAttributeType::Bool),
                },
            },
            FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "false".to_owned(),
                    ty: Some(FormalAttributeType::Bool),
                },
            },
        ],
    });
    let error = validate_query_expr_scalar_operators(&strict_boolean)
        .expect_err("strict aggregate-term AND must not bypass canonical Boolean scheduling");
    assert!(error.contains("scalar leaves admit only atomic"));
    assert!(try_emit_rocq_query_module(&strict_boolean, &strict_boolean).is_none());

    let generic_aggregate_case = scalar_validation_query(FormalAggregateTerm::ScalarCall {
        operator: ScalarOperator::Case,
        args: vec![FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: "true".to_owned(),
                ty: Some(FormalAttributeType::Bool),
            },
        }],
    });
    let error = validate_query_expr_scalar_operators(&generic_aggregate_case)
        .expect_err("aggregate CASE must retain its structured representation");
    assert!(error.contains("scalar leaves admit only atomic"));
    assert!(try_emit_rocq_query_module(&generic_aggregate_case, &generic_aggregate_case).is_none());

    let malformed_predicate = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::Predicate {
            predicate: FormalPredicate::Eq,
            args: vec![FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Int32,
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        raw: "1".to_owned(),
                        ty: Some(FormalAttributeType::Int32),
                    },
                },
            }],
        },
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let error = validate_query_expr_scalar_operators(&malformed_predicate)
        .expect_err("one-argument equality must be rejected");
    assert!(error.contains("predicate Eq does not accept 1 arguments"));
    assert!(try_emit_rocq_query_module(&malformed_predicate, &malformed_predicate).is_none());

    let mistyped_scalar_predicate = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::Predicate {
            predicate: FormalPredicate::IsTrue,
            args: vec![FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Int32,
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        raw: "1".to_owned(),
                        ty: Some(FormalAttributeType::Int32),
                    },
                },
            }],
        },
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let error = validate_query_expr_scalar_operators(&mistyped_scalar_predicate)
        .expect_err("IS TRUE over INTEGER must be rejected by the typed scalar boundary");
    assert!(error.contains("predicate IsTrue rejects argument types"));
    assert!(
        try_emit_rocq_query_module(&mistyped_scalar_predicate, &mistyped_scalar_predicate)
            .is_none()
    );

    let int_leaf = || FormalScalarExpr::Leaf {
        result_ty: FormalAttributeType::Int32,
        term: FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: "1".to_owned(),
                ty: Some(FormalAttributeType::Int32),
            },
        },
    };
    let mistyped_scalar_call = FormalQueryExpr::Projection {
        select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Call {
                result_ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                operator: ScalarOperator::StringConcat,
                args: vec![int_leaf(), int_leaf()],
            },
            alias: "value".to_owned(),
            alias_ty: FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
            numeric_dscale: None,
        }],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let error = validate_query_expr_scalar_operators(&mistyped_scalar_call)
        .expect_err("string concatenation over INTEGER operands must be rejected");
    assert!(error.contains("StringConcat rejects argument types"));
    assert!(try_emit_rocq_query_module(&mistyped_scalar_call, &mistyped_scalar_call).is_none());

    let unconstrained_numeric_leaf = || FormalScalarExpr::Leaf {
        result_ty: FormalAttributeType::Numeric,
        term: FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: "1.0".to_owned(),
                ty: Some(FormalAttributeType::Numeric),
            },
        },
    };
    let invented_decimal_typmod = FormalQueryExpr::Projection {
        select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Call {
                result_ty: FormalAttributeType::Decimal {
                    precision: 5,
                    scale: 2,
                },
                operator: ScalarOperator::Add(ScalarNumericKind::Numeric),
                args: vec![unconstrained_numeric_leaf(), unconstrained_numeric_leaf()],
            },
            alias: "value".to_owned(),
            alias_ty: FormalAttributeType::Decimal {
                precision: 5,
                scale: 2,
            },
            numeric_dscale: Some(NumericDscaleProvenance::Exact(2)),
        }],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let error = validate_query_expr_scalar_operators(&invented_decimal_typmod)
        .expect_err("unconstrained NUMERIC arithmetic must not invent DECIMAL(p,s)");
    assert!(error.contains("numeric typmod shape"));
    assert!(
        try_emit_rocq_query_module(&invented_decimal_typmod, &invented_decimal_typmod).is_none()
    );

    let nested_analysis_error = FormalQueryExpr::Fetch {
        count: 0,
        input: Box::new(FormalQueryExpr::Error {
            columns: vec![formal_attribute("value", FormalAttributeType::Int32)],
            error: FormalQueryError::UndefinedFunction,
        }),
    };
    let error = validate_query_expr_scalar_operators(&nested_analysis_error)
        .expect_err("FETCH 0 must not suppress an analysis-time query error");
    assert!(error.contains("analysis error may occur only at the query root"));
    assert!(try_emit_rocq_query_module(&nested_analysis_error, &nested_analysis_error).is_none());

    let mistyped_aggregate_leaf = FormalQueryExpr::Projection {
        select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Int64,
                term: FormalAggregateTerm::Aggregate {
                    function: FormalAggregateFunction::SumInt32,
                    quantifier: FormalAggregateQuantifier::All,
                    arg: FormalFunctionTerm::Constant {
                        raw: "true".to_owned(),
                        ty: Some(FormalAttributeType::Bool),
                    },
                },
            },
            alias: "value".to_owned(),
            alias_ty: FormalAttributeType::Int64,
            numeric_dscale: None,
        }],
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let error = validate_query_expr_scalar_operators(&mistyped_aggregate_leaf)
        .expect_err("SUM(INTEGER) over BOOLEAN must be rejected");
    assert!(error.contains("cannot determine the FormalSQL value type of scalar leaf"));
    assert!(
        try_emit_rocq_query_module(&mistyped_aggregate_leaf, &mistyped_aggregate_leaf).is_none()
    );

    let empty_case = scalar_validation_query(FormalAggregateTerm::Case {
        branches: Vec::new(),
        else_expr: Box::new(FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: "true".to_owned(),
                ty: Some(FormalAttributeType::Bool),
            },
        }),
    });
    let error = validate_query_expr_scalar_operators(&empty_case)
        .expect_err("CASE without a WHEN/THEN branch must be rejected");
    assert!(error.contains("scalar leaves admit only atomic"));
    assert!(try_emit_rocq_query_module(&empty_case, &empty_case).is_none());

    let malformed_quantified_predicate = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::QuantifiedComparison {
            quantifier: FormalScalarQuantifier::Exists,
            predicate: FormalPredicate::IsNull,
            args: vec![FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Bool,
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        raw: "true".to_owned(),
                        ty: Some(FormalAttributeType::Bool),
                    },
                },
            }],
            query: Box::new(scalar_validation_query(FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "false".to_owned(),
                    ty: Some(FormalAttributeType::Bool),
                },
            })),
        },
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let error = validate_query_expr_scalar_operators(&malformed_quantified_predicate)
        .expect_err("quantified comparison must use a binary predicate");
    assert!(error.contains("predicate IsNull does not accept 2 arguments"));
    assert!(
        try_emit_rocq_query_module(
            &malformed_quantified_predicate,
            &malformed_quantified_predicate
        )
        .is_none()
    );

    let bool_item = FormalScalarSelectItem {
        expr: FormalScalarExpr::Leaf {
            result_ty: FormalAttributeType::Bool,
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "true".to_owned(),
                    ty: Some(FormalAttributeType::Bool),
                },
            },
        },
        alias: "value".to_owned(),
        alias_ty: FormalAttributeType::Bool,
        numeric_dscale: None,
    };
    let wrong_width_subqueries = [
        ("zero-column", FormalQueryExpr::EmptyTuple),
        (
            "two-column",
            FormalQueryExpr::Projection {
                select: vec![bool_item.clone(), bool_item],
                input: Box::new(FormalQueryExpr::EmptyTuple),
            },
        ),
    ];
    for (label, subquery) in wrong_width_subqueries {
        let malformed_quantified_width = FormalQueryExpr::Selection {
            predicate: FormalScalarExpr::QuantifiedComparison {
                quantifier: FormalScalarQuantifier::Exists,
                predicate: FormalPredicate::Eq,
                args: vec![FormalScalarExpr::Leaf {
                    result_ty: FormalAttributeType::Bool,
                    term: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Constant {
                            raw: "true".to_owned(),
                            ty: Some(FormalAttributeType::Bool),
                        },
                    },
                }],
                query: Box::new(subquery),
            },
            input: Box::new(FormalQueryExpr::EmptyTuple),
        };
        let error = validate_query_expr_scalar_operators(&malformed_quantified_width)
            .expect_err("quantified comparison must consume one subquery column");
        assert!(
            error.contains("requires exactly one subquery output column"),
            "{label}: {error}"
        );
        assert!(
            try_emit_rocq_query_module(&malformed_quantified_width, &malformed_quantified_width)
                .is_none(),
            "{label}"
        );
    }
}

#[test]
fn quantified_comparison_uses_semi_anti_authoritative_output_signature() {
    let empty_input = || FormalQueryExpr::EmptyTuple;
    let join = |join_kind, matched_select, left_select| FormalQueryExpr::Join {
        join_kind,
        predicate: FormalScalarExpr::True,
        matched_select,
        left_select,
        right_select: vec![z_select_item("right")],
        left: Box::new(empty_input()),
        right: Box::new(empty_input()),
    };
    let quantified_query = |query| FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::QuantifiedComparison {
            quantifier: FormalScalarQuantifier::Exists,
            predicate: FormalPredicate::Eq,
            args: vec![FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Z,
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        raw: "1".to_owned(),
                        ty: Some(FormalAttributeType::Z),
                    },
                },
            }],
            query: Box::new(query),
        },
        input: Box::new(empty_input()),
    };

    // Construct this directly: normal join lowering keeps these lists aligned
    // and would therefore hide a drift between validation and denotation.
    let semi_subquery = join(
        FormalQueryJoinKind::Semi,
        vec![z_select_item("matched_0"), z_select_item("matched_1")],
        vec![z_select_item("left_only")],
    );
    assert_eq!(
        query_expr_output_signature(&semi_subquery),
        Some(vec![FormalAttribute {
            name: "left_only".to_owned(),
            ty: FormalAttributeType::Z,
        }])
    );
    let valid = quantified_query(semi_subquery);
    validate_query_expr_scalar_operators(&valid)
        .expect("SEMI output is its one-column left projection, not matched_select");
    assert!(try_emit_rocq_query_module(&valid, &valid).is_some());

    let anti_subquery = join(
        FormalQueryJoinKind::Anti,
        vec![z_select_item("matched_only")],
        vec![z_select_item("left_0"), z_select_item("left_1")],
    );
    assert_eq!(
        query_expr_output_signature(&anti_subquery)
            .expect("ANTI syntax carries its left output signature")
            .len(),
        2
    );
    let invalid = quantified_query(anti_subquery);
    let error = validate_query_expr_scalar_operators(&invalid)
        .expect_err("ANTI's two-column left projection must be rejected");
    assert!(error.contains("requires exactly one subquery output column"));
    assert!(try_emit_rocq_query_module(&invalid, &invalid).is_none());
}

#[test]
fn query_output_signature_requires_exact_ordered_attributes() {
    let unified_signature = vec![
        formal_attribute("first", FormalAttributeType::Z),
        formal_attribute("second", FormalAttributeType::Z),
    ];
    let unified_set = |right_columns| FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(FormalQueryExpr::Empty {
            columns: unified_signature.clone(),
        }),
        right: Box::new(FormalQueryExpr::Empty {
            columns: right_columns,
        }),
    };

    let matching_unified_set = unified_set(unified_signature.clone());
    assert_eq!(
        query_expr_output_signature(&matching_unified_set),
        Some(unified_signature.clone())
    );

    let unified_label_drift = unified_set(vec![
        formal_attribute("other_first", FormalAttributeType::Z),
        formal_attribute("second", FormalAttributeType::Z),
    ]);
    assert_eq!(query_expr_output_signature(&unified_label_drift), None);
    assert!(try_emit_rocq_query_module(&unified_label_drift, &unified_label_drift).is_none());

    let unified_arity_drift = unified_set(vec![formal_attribute("first", FormalAttributeType::Z)]);
    assert_eq!(query_expr_output_signature(&unified_arity_drift), None);

    let unified_type_drift = unified_set(vec![
        formal_attribute("first", FormalAttributeType::Z),
        formal_attribute("second", FormalAttributeType::Bool),
    ]);
    assert_eq!(query_expr_output_signature(&unified_type_drift), None);

    let projected = |names: &[&str]| FormalQueryExpr::Projection {
        select: names.iter().map(|name| z_select_item(name)).collect(),
        input: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let attribute_names = |signature: Vec<FormalAttribute>| {
        signature
            .into_iter()
            .map(|attribute| attribute.name)
            .collect::<Vec<_>>()
    };

    let set = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(projected(&["left_0", "left_1"])),
        right: Box::new(projected(&["left_0", "left_1"])),
    };
    assert_eq!(
        attribute_names(query_expr_output_signature(&set).expect("matching set arity")),
        ["left_0", "left_1"]
    );

    let mismatched_set_labels = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(projected(&["left_0", "left_1"])),
        right: Box::new(projected(&["right_0", "right_1"])),
    };
    assert_eq!(query_expr_output_signature(&mismatched_set_labels), None);
    assert!(try_emit_rocq_query_module(&mismatched_set_labels, &mismatched_set_labels).is_none());

    let mismatched_set_arity = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(projected(&["left_0", "left_1"])),
        right: Box::new(projected(&["right_only"])),
    };
    assert_eq!(query_expr_output_signature(&mismatched_set_arity), None);
    let mismatched_set_type = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(projected(&["left"])),
        right: Box::new(FormalQueryExpr::Projection {
            select: vec![FormalScalarSelectItem {
                expr: FormalScalarExpr::Leaf {
                    result_ty: FormalAttributeType::Bool,
                    term: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Constant {
                            raw: "true".to_owned(),
                            ty: Some(FormalAttributeType::Bool),
                        },
                    },
                },
                alias: "left".to_owned(),
                alias_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            }],
            input: Box::new(FormalQueryExpr::EmptyTuple),
        }),
    };
    assert_eq!(query_expr_output_signature(&mismatched_set_type), None);

    let grouping_sets = FormalQueryExpr::GroupingSets {
        grouping_sets: vec![
            FormalGroupingSet {
                select: vec![z_select_item("first_0"), z_select_item("first_1")],
                group_by: Vec::new(),
            },
            FormalGroupingSet {
                select: vec![z_select_item("first_0"), z_select_item("first_1")],
                group_by: Vec::new(),
            },
        ],
        input: Box::new(projected(&["input"])),
    };
    assert_eq!(
        attribute_names(
            query_expr_output_signature(&grouping_sets).expect("matching grouping-set arity")
        ),
        ["first_0", "first_1"]
    );

    let mismatched_grouping_set_labels = FormalQueryExpr::GroupingSets {
        grouping_sets: vec![
            FormalGroupingSet {
                select: vec![z_select_item("first_0"), z_select_item("first_1")],
                group_by: Vec::new(),
            },
            FormalGroupingSet {
                select: vec![z_select_item("other_0"), z_select_item("other_1")],
                group_by: Vec::new(),
            },
        ],
        input: Box::new(projected(&["input"])),
    };
    assert_eq!(
        query_expr_output_signature(&mismatched_grouping_set_labels),
        None
    );
    assert!(
        try_emit_rocq_query_module(
            &mismatched_grouping_set_labels,
            &mismatched_grouping_set_labels
        )
        .is_none()
    );

    let mismatched_grouping_set_arity = FormalQueryExpr::GroupingSets {
        grouping_sets: vec![
            FormalGroupingSet {
                select: vec![z_select_item("first_0"), z_select_item("first_1")],
                group_by: Vec::new(),
            },
            FormalGroupingSet {
                select: vec![z_select_item("other_only")],
                group_by: Vec::new(),
            },
        ],
        input: Box::new(projected(&["input"])),
    };
    assert_eq!(
        query_expr_output_signature(&mismatched_grouping_set_arity),
        None
    );

    let mismatched_grouping_set_type = FormalQueryExpr::GroupingSets {
        grouping_sets: vec![
            FormalGroupingSet {
                select: vec![z_select_item("first")],
                group_by: Vec::new(),
            },
            FormalGroupingSet {
                select: vec![FormalScalarSelectItem {
                    expr: FormalScalarExpr::Leaf {
                        result_ty: FormalAttributeType::Bool,
                        term: FormalAggregateTerm::Expr {
                            term: FormalFunctionTerm::Constant {
                                raw: "true".to_owned(),
                                ty: Some(FormalAttributeType::Bool),
                            },
                        },
                    },
                    alias: "first".to_owned(),
                    alias_ty: FormalAttributeType::Bool,
                    numeric_dscale: None,
                }],
                group_by: Vec::new(),
            },
        ],
        input: Box::new(projected(&["input"])),
    };
    assert_eq!(
        query_expr_output_signature(&mismatched_grouping_set_type),
        None
    );

    let cross_join = FormalQueryExpr::CrossJoin {
        left: Box::new(projected(&["left"])),
        right: Box::new(projected(&["right_0", "right_1"])),
    };
    assert_eq!(
        attribute_names(query_expr_output_signature(&cross_join).expect("known cross join shape")),
        ["left", "right_0", "right_1"]
    );
    assert_eq!(
        query_expr_output_signature(&FormalQueryExpr::Table {
            relation: "ordered_table".to_owned(),
            columns: vec![
                formal_attribute("z_second", FormalAttributeType::Z),
                formal_attribute("bool_first", FormalAttributeType::Bool),
            ],
        })
        .expect("table syntax carries its validated scan-order witness")
        .into_iter()
        .map(|attribute| attribute.name)
        .collect::<Vec<_>>(),
        ["z_second", "bool_first"]
    );
}

#[test]
fn malformed_predicate_arity_is_rejected_during_lowering() {
    let input = vec![typed_column("value", SqlType::Integer)];
    let query = query_for_rel(
        RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![ScalarAst::InputRef { index: 0 }],
            }),
            correlations: Vec::new(),
            output: input.clone(),
        },
        input,
    );

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "predicate_arity_mismatch")
    );
}

fn nested_scalar_query(relation: &str) -> FormalQueryExpr {
    FormalQueryExpr::Table {
        relation: relation.to_owned(),
        columns: vec![formal_attribute("value", FormalAttributeType::Numeric)],
    }
}

fn nested_exists_selection(outer_relation: &str, inner_relation: &str) -> FormalQueryExpr {
    FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::Exists {
            query: Box::new(nested_scalar_query(inner_relation)),
        },
        input: Box::new(FormalQueryExpr::Table {
            relation: outer_relation.to_owned(),
            columns: vec![formal_attribute("probe", FormalAttributeType::Numeric)],
        }),
    }
}

#[test]
fn generated_metadata_solver_uses_only_structural_and_local_cbn_closure() {
    let query = nested_exists_selection("OUTER", "INNER");
    let module = emit_rocq_query_module(&query, &query);
    let tactic = module
        .rocq_module
        .find("Ltac solve_generated_query_metadata :=\n  first [")
        .expect("generated metadata solver should start with a structural branch");
    let structural_close = module
        .rocq_module
        .find("solve [contradiction | reflexivity | congruence | tauto |")
        .expect("generated metadata solver should close trivial structural goals");
    let cbn_fallback = module
        .rocq_module
        .find("| cbn;")
        .expect("generated metadata solver should retain the local cbn fallback");
    assert!(tactic < structural_close);
    assert!(structural_close < cbn_fallback);
    assert!(!module.rocq_module.contains("vm_compute"));
    assert!(!module.rocq_module.contains("native_compute"));
}

#[test]
fn nested_not_exists_admissibility_stays_compositional() {
    let query = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::And {
            insertion_sites: vec![vec![], vec!["test.scalar-selection.and".to_owned()]],
            operands: vec![
                FormalScalarExpr::Not {
                    expression: Box::new(FormalScalarExpr::Exists {
                        query: Box::new(nested_scalar_query("INNER_LEFT")),
                    }),
                },
                FormalScalarExpr::Exists {
                    query: Box::new(nested_scalar_query("INNER_RIGHT")),
                },
            ],
        },
        input: Box::new(FormalQueryExpr::Table {
            relation: "OUTER".to_owned(),
            columns: vec![formal_attribute("probe", FormalAttributeType::Numeric)],
        }),
    };
    let module = emit_rocq_query_module(&query, &query);
    assert!(
        module
            .rocq_module
            .contains("@SExpr_ConjList TNull relname ([[]; [\"b0\"]]) And_F")
    );
    assert!(!module.rocq_module.contains("test.scalar-selection.and"));
    let certificate_start = module
        .rocq_module
        .find("Lemma scalar_expr_predicate_0_admissible_where_generated_schema")
        .expect("nested scalar admissibility certificate");
    let certificate_tail = &module.rocq_module[certificate_start..];
    let certificate_end = certificate_tail
        .find("\nQed.")
        .expect("end of nested scalar admissibility certificate");
    let certificate = &certificate_tail[..certificate_end];
    assert!(certificate.contains("split."), "{certificate}");
    assert_eq!(
        certificate
            .matches("eapply query_expr_admissible_of_with_outputs.")
            .count(),
        2,
        "{certificate}"
    );
    assert!(
        module
            .rocq_module
            .contains("@SExpr_Not TNull relname (@SExpr_Exists TNull relname")
    );
}

#[test]
fn rocq_emission_compacts_boolean_sites_injectively_across_query_sides() {
    fn query(site: &str) -> FormalQueryExpr {
        FormalQueryExpr::Selection {
            predicate: FormalScalarExpr::And {
                insertion_sites: vec![Vec::new(), vec![site.to_owned()]],
                operands: vec![FormalScalarExpr::True, FormalScalarExpr::True],
            },
            input: Box::new(FormalQueryExpr::Table {
                relation: "t".to_owned(),
                columns: Vec::new(),
            }),
        }
    }

    let source_site = "source.deep.path.predicate.booleanOrder[1][0]";
    let target_site = "target.other.path.predicate.booleanOrder[1][0]";
    let module = emit_rocq_query_module(&query(source_site), &query(target_site));

    assert!(module.rocq_module.contains("[[]; [\"b0\"]]"));
    assert!(module.rocq_module.contains("[[]; [\"b1\"]]"));
    assert!(!module.rocq_module.contains(source_site));
    assert!(!module.rocq_module.contains(target_site));
}

fn lowered_query_expr(lowered: &LoweredQuery) -> Option<&FormalQueryExpr> {
    lowered.query_expr.as_ref()
}

fn finalize_output_pair(source: &mut LoweredQuery, target: &mut LoweredQuery) {
    normalize_output_pair_for_equivalence(source, target);
}

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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(lowered_query_expr(&lowered).is_some());
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity == DiagnosticSeverity::Warning)
    );
    assert_no_physical_plan_constructs(&module);
}
#[test]
fn lowers_peer_complete_partition_count_window_with_one_shared_child() {
    let table_output = vec![column("empno"), column("deptno")];
    let output = vec![
        typed_column("count_a", SqlType::BigInt),
        typed_column("count_b", SqlType::BigInt),
    ];
    let window = partition_peer_complete_count_window(0);
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["emp".to_owned()],
                output: table_output,
            }),
            exprs: vec![window.clone(), window],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(lowered.diagnostics.is_empty());
    let Some(FormalQueryExpr::Projection { select, input }) = lowered.query_expr.as_ref() else {
        panic!("window result should be a final projection");
    };
    assert_eq!(select.len(), 2);
    let FormalQueryExpr::Window {
        partition_keys,
        order_keys,
        items,
        input: window_input,
    } = input.as_ref()
    else {
        panic!("partition count should use the native shared-child window");
    };
    assert_eq!(partition_keys.len(), 1);
    assert_eq!(order_keys.len(), 1);
    assert_eq!(items.len(), 2);
    assert!(items.iter().all(|item| matches!(
        item.function,
        FormalWindowFunction::FullPartitionAggregate {
            term: FormalAggregateTerm::CountStar
        }
    )));
    assert!(matches!(
        window_input.as_ref(),
        FormalQueryExpr::Table { .. }
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("WindowExpr"));
    assert!(
        module
            .rocq_module
            .contains("WindowFullPartitionAggregateItem")
    );
    assert!(!module.rocq_module.contains("QExpr_Join QueryJoinInner"));
}
#[test]
fn lowers_global_full_count_expression_window_with_null_ignoring_count() {
    let table_output = vec![column("empno"), column("deptno")];
    let output = vec![
        typed_column("count_empno", SqlType::BigInt),
        column("deptno"),
    ];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["emp".to_owned()],
                output: table_output,
            }),
            exprs: vec![
                global_full_count_window(0),
                scalar(ScalarAst::InputRef { index: 1 }),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(lowered.diagnostics.is_empty());
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("window result should be a final projection");
    };
    let FormalQueryExpr::Window {
        partition_keys,
        order_keys,
        items,
        input: window_input,
    } = input.as_ref()
    else {
        panic!("global full count should use the native shared-child window");
    };
    assert!(partition_keys.is_empty());
    assert!(order_keys.is_empty());
    assert!(matches!(
        items.as_slice(),
        [FormalWindowItem {
            function: FormalWindowFunction::FullPartitionAggregate {
                term: FormalAggregateTerm::Aggregate { function, .. }
            },
            ..
        }] if *function == FormalAggregateFunction::Count
    ));
    assert!(matches!(
        window_input.as_ref(),
        FormalQueryExpr::Table { .. }
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("WindowExpr"));
    assert!(!module.rocq_module.contains("QExpr_CrossJoin"));
    assert!(
        module
            .rocq_module
            .contains("WindowFullPartitionAggregateItem")
    );
}
#[test]
fn rejects_every_other_window_shape_conservatively() {
    let mut rows_frame = partition_peer_complete_count_window(0);
    let ScalarAst::Window { parsed, .. } = &mut rows_frame.parsed else {
        unreachable!()
    };
    parsed.frame = Some(WindowFrameAst {
        units: WindowFrameUnits::Rows,
        start: WindowFrameBoundAst::UnboundedPreceding,
        end: Some(WindowFrameBoundAst::CurrentRow),
    });

    let mut different_order_key = partition_peer_complete_count_window(0);
    let ScalarAst::Window { parsed, .. } = &mut different_order_key.parsed else {
        unreachable!()
    };
    parsed.order_by[0].expr = ScalarAst::InputRef { index: 1 };

    let mut distinct = global_full_count_window(0);
    let ScalarAst::Window { parsed, .. } = &mut distinct.parsed else {
        unreachable!()
    };
    parsed.distinct = true;

    let mut global_count_star = global_full_count_window(0);
    let ScalarAst::Window { parsed, .. } = &mut global_count_star.parsed else {
        unreachable!()
    };
    parsed.args.clear();

    for (label, window) in [
        ("ROWS frame", rows_frame),
        ("different order key", different_order_key),
        ("DISTINCT", distinct),
        ("global COUNT star", global_count_star),
    ] {
        let output = vec![typed_column("count_value", SqlType::BigInt)];
        let query = query_for_rel(
            RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["emp".to_owned()],
                    output: vec![column("empno"), column("deptno")],
                }),
                exprs: vec![window],
                correlations: Vec::new(),
                output: output.clone(),
            },
            output,
        );
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "window_shape_not_supported"),
            "{label}: {:?}",
            lowered.diagnostics
        );
    }
}
#[test]
fn lowers_row_number_and_cumulative_sum_with_one_shared_peer_order() {
    let input = vec![
        typed_column("item", SqlType::Integer),
        typed_column("day", SqlType::Date),
        typed_column("amount", SqlType::BigInt),
    ];
    let output = vec![
        typed_column("item", SqlType::Integer),
        Column {
            name: "rn".to_owned(),
            ty: SqlType::BigInt,
            nullable: false,
        },
        decimal_column_unconstrained("running_amount"),
    ];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["sales".to_owned()],
                output: input,
            }),
            exprs: vec![
                scalar(ScalarAst::InputRef { index: 0 }),
                cumulative_rows_window("ROW_NUMBER", Vec::new()),
                cumulative_rows_window("SUM", vec![ScalarAst::InputRef { index: 2 }]),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("window result should have one final projection");
    };
    let FormalQueryExpr::Window {
        partition_keys,
        order_keys,
        items,
        ..
    } = input.as_ref()
    else {
        panic!("ROW_NUMBER and SUM must share one declarative window node");
    };
    assert_eq!(partition_keys.len(), 1);
    assert_eq!(order_keys.len(), 1);
    assert!(matches!(
        items.as_slice(),
        [
            FormalWindowItem {
                function: FormalWindowFunction::RowNumber,
                ..
            },
            FormalWindowItem {
                function: FormalWindowFunction::Aggregate {
                    term: FormalAggregateTerm::Aggregate { function, .. }
                },
                ..
            }
        ] if *function == FormalAggregateFunction::SumInt64Numeric
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("WindowExpr"));
    assert!(module.rocq_module.contains("WindowRowNumberItem"));
    assert!(module.rocq_module.contains("WindowAggregateItem"));
    assert!(
        module.rocq_module.contains("cbn [ListFacts.all_diff].\n"),
        "multi-item Window outputs should use a structural all_diff certificate"
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateSumInt64Numeric AggregateAll")
    );
}

#[test]
fn lowers_boolean_cumulative_window_order_through_the_sql_order_carrier() {
    let input = vec![
        typed_column("partition_id", SqlType::Integer),
        typed_column("flag", SqlType::Boolean),
    ];
    let output = vec![Column {
        name: "rn".to_owned(),
        ty: SqlType::BigInt,
        nullable: false,
    }];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["flags".to_owned()],
                output: input,
            }),
            exprs: vec![cumulative_rows_window("ROW_NUMBER", Vec::new())],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("window result should have one final projection");
    };
    let FormalQueryExpr::Window { order_keys, .. } = input.as_ref() else {
        panic!("ROW_NUMBER should use the declarative cumulative window node");
    };
    assert!(matches!(order_keys.as_slice(), [key]
        if key.attribute_ty == FormalAttributeType::Bool));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SortAscNullsFirst (AttrBool"));
}

#[test]
fn cumulative_max_over_numeric_rejects_stale_calcite_fixed_decimal_type() {
    let input = vec![
        typed_column("item", SqlType::Integer),
        typed_column("day", SqlType::Date),
        decimal_column_unconstrained("web_sales"),
        decimal_column_unconstrained("store_sales"),
    ];
    let output = vec![
        decimal_column("web_cumulative", 19, 2),
        decimal_column("store_cumulative", 19, 2),
    ];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["combined_sales".to_owned()],
                output: input,
            }),
            exprs: vec![
                cumulative_rows_window("MAX", vec![ScalarAst::InputRef { index: 2 }]),
                cumulative_rows_window("MAX", vec![ScalarAst::InputRef { index: 3 }]),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    assert!(lowered.diagnostics.iter().all(|diagnostic| {
        diagnostic.severity == DiagnosticSeverity::Warning
            && diagnostic.code == "calcite_window_aggregate_type_overridden"
    }));
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("window result should have one final projection");
    };
    let FormalQueryExpr::Window { items, .. } = input.as_ref() else {
        panic!("the two cumulative MAX calls must share one window node");
    };
    assert!(
        items
            .iter()
            .all(|item| item.output.ty == FormalAttributeType::Numeric)
    );
}
#[test]
fn lowers_structured_rank_from_logical_window_without_frozen_plan_authority() {
    let query = query_with_default_rank_window(
        default_range_rank_window(
            vec![ScalarAst::InputRef { index: 0 }],
            ScalarAst::InputRef { index: 1 },
            SortDirection::Descending,
            SortNullDirection::Last,
        ),
        false,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("RANK result should have one final projection");
    };
    let FormalQueryExpr::Rank {
        partition_keys,
        order_keys,
        rank_attribute,
        ..
    } = input.as_ref()
    else {
        panic!("structured RANK should use the declarative logical rank node");
    };
    assert_eq!(partition_keys.len(), 1);
    assert!(matches!(order_keys.as_slice(), [key]
        if key.direction == FormalSortDirection::Desc
            && key.null_direction == FormalNullDirection::Last));
    assert!(rank_attribute.name.starts_with("__logos_rank_value"));
    assert_eq!(rank_attribute.ty, FormalAttributeType::Int64);

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("RankExpr ("));
    assert_no_physical_plan_constructs(&module);
}

#[test]
fn lowers_boolean_rank_order_through_the_sql_order_carrier() {
    let input = vec![
        typed_column("partition_id", SqlType::Integer),
        typed_column("flag", SqlType::Boolean),
    ];
    let output = vec![
        typed_column("partition_id", SqlType::Integer),
        typed_column("flag", SqlType::Boolean),
        Column {
            name: "ranking".to_owned(),
            ty: SqlType::BigInt,
            nullable: false,
        },
    ];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["flags".to_owned()],
                output: input,
            }),
            exprs: vec![
                scalar(ScalarAst::InputRef { index: 0 }),
                scalar(ScalarAst::InputRef { index: 1 }),
                default_range_rank_window(
                    vec![ScalarAst::InputRef { index: 0 }],
                    ScalarAst::InputRef { index: 1 },
                    SortDirection::Ascending,
                    SortNullDirection::First,
                ),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("RANK result should have one final projection");
    };
    let FormalQueryExpr::Rank { order_keys, .. } = input.as_ref() else {
        panic!("RANK should use the declarative rank node");
    };
    assert!(matches!(order_keys.as_slice(), [key]
        if key.attribute_ty == FormalAttributeType::Bool));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SortAscNullsFirst (AttrBool"));
}

#[test]
fn declarative_rank_fails_closed_on_incomplete_or_observable_staging() {
    let base = default_range_rank_window(
        vec![ScalarAst::InputRef { index: 0 }],
        ScalarAst::InputRef { index: 1 },
        SortDirection::Descending,
        SortNullDirection::Last,
    );

    let mut wrong_frame = base.clone();
    let ScalarAst::Window { parsed, .. } = &mut wrong_frame.parsed else {
        unreachable!()
    };
    parsed.frame.as_mut().unwrap().units = WindowFrameUnits::Rows;

    let risky_order = default_range_rank_window(
        vec![ScalarAst::InputRef { index: 0 }],
        ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::InputRef { index: 1 },
                ScalarAst::InputRef { index: 0 },
            ],
        },
        SortDirection::Descending,
        SortNullDirection::Last,
    );

    for (label, window, expected_code) in [(
        "non-default frame",
        wrong_frame,
        "rank_window_shape_not_supported",
    )] {
        let lowered = lower_query(&query_with_default_rank_window(window, false));
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == expected_code),
            "{label}: {:#?}",
            lowered.diagnostics
        );
    }

    let direct_division = lower_query(&query_with_default_rank_window(risky_order, false));
    assert_eq!(
        direct_division.status,
        LoweringStatus::Lowered,
        "one direct division key is evaluated once in the staged key projection: {:#?}",
        direct_division.diagnostics
    );

    let nested_risky_order = default_range_rank_window(
        vec![ScalarAst::InputRef { index: 0 }],
        ScalarAst::Call {
            operator: "+".to_owned(),
            op: ScalarOp::Plus,
            args: vec![
                ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::InputRef { index: 1 },
                        ScalarAst::InputRef { index: 0 },
                    ],
                },
                ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::InputRef { index: 1 },
                    ],
                },
            ],
        },
        SortDirection::Descending,
        SortNullDirection::Last,
    );
    let nested = lower_query(&query_with_default_rank_window(nested_risky_order, false));
    assert_eq!(nested.status, LoweringStatus::Blocked);
    assert!(
        nested.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "rank_window_expression_runtime_not_supported"
        })
    );

    let nullable = lower_query(&query_with_default_rank_window(base, true));
    assert_eq!(nullable.status, LoweringStatus::Blocked);
    assert!(
        nullable
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "rank_output_type_not_supported" })
    );
}
#[test]
fn lowers_builtin_boolean_value_expressions_with_typed_operators() {
    let table_output = vec![column("a"), column("b")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: table_output,
            }),
            exprs: vec![scalar(ScalarAst::Call {
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
                    ScalarAst::Call {
                        operator: "IS NULL".to_owned(),
                        op: ScalarOp::IsNull,
                        args: vec![ScalarAst::Literal {
                            raw: "NULL".to_owned(),
                        }],
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("ok", SqlType::Boolean)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("boolean value expression should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("boolean value expression should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("@SExpr_ConjList TNull relname"));
    assert!(
        module
            .rocq_module
            .contains("@SExpr_Pred TNull relname (PredicateLt")
    );
    assert!(
        module
            .rocq_module
            .contains("@SExpr_Pred TNull relname (PredicateIsNull")
    );
    assert!(module.rocq_module.contains("NullZ"));
}

#[test]
fn variadic_boolean_lowering_assigns_distinct_stable_sites() {
    let ast = ScalarAst::Call {
        operator: "AND".to_owned(),
        op: ScalarOp::And,
        args: vec![
            ScalarAst::Literal {
                raw: "true".to_owned(),
            },
            ScalarAst::Literal {
                raw: "false".to_owned(),
            },
            ScalarAst::Literal {
                raw: "true".to_owned(),
            },
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    let lowered = context
        .lower_scalar_boolean_expr(
            "predicate",
            &ast,
            &Scope {
                attributes: Vec::new(),
            },
        )
        .expect("variadic AND should lower");

    let FormalScalarExpr::And {
        insertion_sites,
        operands,
    } = lowered
    else {
        panic!("three-way AND should lower to one flattened scheduled node");
    };
    assert_eq!(operands.len(), 3);
    assert_eq!(
        insertion_sites,
        vec![
            Vec::<String>::new(),
            vec!["predicate.booleanOrder[1][0]".to_owned()],
            vec![
                "predicate.booleanOrder[2][0]".to_owned(),
                "predicate.booleanOrder[2][1]".to_owned(),
            ],
        ]
    );
}

#[test]
fn rocq_emission_rejects_empty_or_reused_boolean_sites() {
    fn query_with_sites(outer: &str, inner: &str) -> FormalQueryExpr {
        FormalQueryExpr::Selection {
            predicate: FormalScalarExpr::And {
                insertion_sites: vec![vec![], vec![outer.to_owned()]],
                operands: vec![
                    FormalScalarExpr::And {
                        insertion_sites: vec![vec![], vec![inner.to_owned()]],
                        operands: vec![FormalScalarExpr::True, FormalScalarExpr::True],
                    },
                    FormalScalarExpr::True,
                ],
            },
            input: Box::new(FormalQueryExpr::Table {
                relation: "T".to_owned(),
                columns: vec![formal_attribute("x", FormalAttributeType::Z)],
            }),
        }
    }

    for (label, query) in [
        ("empty", query_with_sites("", "inner")),
        ("duplicate", query_with_sites("shared", "shared")),
    ] {
        let signature = query_expr_output_signature(&query).expect("table signature");
        assert!(
            emit_rocq_query_program_module_with_signatures(
                &[(&query, &signature)],
                &[(&query, &signature)],
            )
            .is_none(),
            "{label} Boolean sites must fail before Rocq emission"
        );
    }
}

#[test]
fn boolean_connectives_lower_runtime_risky_operands_for_relational_scheduling() {
    let scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "numerator".to_owned(),
                visible_name: "numerator".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "denominator".to_owned(),
                visible_name: "denominator".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
        ],
    };
    let risky = ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    let total = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
        ],
    };

    for op in [ScalarOp::And, ScalarOp::Or] {
        for risky_first in [false, true] {
            let args = if risky_first {
                vec![risky.clone(), total.clone()]
            } else {
                vec![total.clone(), risky.clone()]
            };
            let predicate = ScalarAst::Call {
                operator: format!("{op:?}"),
                op: op.clone(),
                args,
            };
            let mut context = LoweringContext::new(LoweringConfig::default(), None);

            assert!(
                context
                    .lower_scalar_boolean_expr("predicate", &predicate, &scope)
                    .is_some(),
                "{op:?} risky_first={risky_first}: {:#?}",
                context.diagnostics
            );
            assert!(
                context.diagnostics.is_empty(),
                "{op:?} risky_first={risky_first}: {:#?}",
                context.diagnostics
            );
        }

        let safe_predicate = ScalarAst::Call {
            operator: format!("{op:?}"),
            op: op.clone(),
            args: vec![total.clone(), total.clone()],
        };
        let mut safe_context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(
            safe_context
                .lower_scalar_boolean_expr("predicate", &safe_predicate, &scope)
                .is_some(),
            "{op:?}: {:#?}",
            safe_context.diagnostics
        );
    }
}

#[test]
fn boolean_absorption_with_runtime_error_fails_closed() {
    let scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "numerator".to_owned(),
                visible_name: "numerator".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "denominator".to_owned(),
                visible_name: "denominator".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
        ],
    };
    let repeated = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
        ],
    };
    let risky = ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    let predicate = ScalarAst::Call {
        operator: "OR".to_owned(),
        op: ScalarOp::Or,
        args: vec![
            repeated.clone(),
            ScalarAst::Call {
                operator: "AND".to_owned(),
                op: ScalarOp::And,
                args: vec![repeated, risky],
            },
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);

    assert!(
        context
            .lower_scalar_boolean_expr("predicate", &predicate, &scope)
            .is_none()
    );
    assert!(
        context
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "boolean_algebra_runtime_error_not_supported" })
    );
}

#[test]
fn planner_foldable_boolean_constant_with_runtime_error_fails_closed() {
    let closed_error = ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "0".to_owned(),
                    },
                ],
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    for (op, decisive) in [(ScalarOp::And, "false"), (ScalarOp::Or, "true")] {
        let predicate = ScalarAst::Call {
            operator: format!("{op:?}"),
            op,
            args: vec![
                ScalarAst::Literal {
                    raw: decisive.to_owned(),
                },
                closed_error.clone(),
            ],
        };
        let mut context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(
            context
                .lower_scalar_boolean_expr(
                    "predicate",
                    &predicate,
                    &Scope {
                        attributes: Vec::new(),
                    },
                )
                .is_none()
        );
        assert!(context.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "boolean_planner_constant_error_not_supported"
        }));
    }

    let dynamic_case_with_closed_error = ScalarAst::Call {
        operator: "AND".to_owned(),
        op: ScalarOp::And,
        args: vec![
            ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "true".to_owned(),
                    },
                    closed_error,
                ],
            },
            ScalarAst::Literal {
                raw: "true".to_owned(),
            },
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    assert!(
        context
            .lower_scalar_boolean_expr(
                "predicate",
                &dynamic_case_with_closed_error,
                &Scope {
                    attributes: vec![ScopeAttribute {
                        name: "flag".to_owned(),
                        visible_name: "flag".to_owned(),
                        formal_ty: FormalAttributeType::Bool,
                        numeric_dscale: None,
                    }],
                },
            )
            .is_none()
    );
    assert!(
        context.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "boolean_planner_constant_error_not_supported"
        })
    );
}

#[test]
fn planner_closed_immutable_errors_fail_closed_across_query_tree() {
    let closed_error = || ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "0".to_owned(),
                    },
                ],
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    let assert_planner_blocked = |query: Query| {
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked);
        assert!(
            lowered.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "boolean_planner_constant_error_not_supported"
            }),
            "{:#?}",
            lowered.diagnostics
        );
    };

    let bool_input = vec![typed_column("flag", SqlType::Boolean)];
    let case_output = vec![typed_column("result", SqlType::Integer)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Project {
            input: Box::new(one_row_values(
                bool_input.clone(),
                vec![ScalarAst::Literal {
                    raw: "true".to_owned(),
                }],
            )),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    closed_error(),
                ],
            })],
            correlations: Vec::new(),
            output: case_output.clone(),
        },
        case_output,
    ));

    let subquery_output = vec![typed_column("subquery_flag", SqlType::Boolean)];
    let subquery = one_row_values(subquery_output, vec![closed_error()]);
    let boolean_output = vec![typed_column("result", SqlType::Boolean)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Project {
            input: Box::new(one_row_values(
                bool_input,
                vec![ScalarAst::Literal {
                    raw: "true".to_owned(),
                }],
            )),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "OR".to_owned(),
                op: ScalarOp::Or,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::RelSubquery {
                        rel: Box::new(subquery),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: boolean_output.clone(),
        },
        boolean_output,
    ));

    let aggregate_output = vec![typed_column("count", SqlType::BigInt)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Aggregate {
            input: Box::new(one_row_values(
                vec![typed_column("value", SqlType::Integer)],
                vec![ScalarAst::Literal {
                    raw: "1".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT(*) FILTER (WHERE 1 / 0 > 0)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: Vec::new(),
                filter: Some(scalar(closed_error())),
            }],
            output: aggregate_output.clone(),
        },
        aggregate_output,
    ));

    let projection_output = vec![typed_column("value", SqlType::Boolean)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::Values {
                rows: Vec::new(),
                output: Vec::new(),
            }),
            exprs: vec![scalar(closed_error())],
            correlations: Vec::new(),
            output: projection_output.clone(),
        },
        projection_output,
    ));

    let aggregate_output = vec![typed_column("count", SqlType::BigInt)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Aggregate {
            input: Box::new(RelExpr::Values {
                rows: Vec::new(),
                output: Vec::new(),
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT(1 / 0)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::Literal {
                            raw: "1".to_owned(),
                        },
                        ScalarAst::Literal {
                            raw: "0".to_owned(),
                        },
                    ],
                })],
                filter: None,
            }],
            output: aggregate_output.clone(),
        },
        aggregate_output,
    ));

    let truncated_sign = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'+1'".to_owned(),
                    }],
                }),
                ty: "CHAR(1)".to_owned(),
            }],
        }),
        ty: "INTEGER".to_owned(),
    };
    let integer_output = vec![typed_column("value", SqlType::Integer)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Project {
            input: Box::new(one_row_values(Vec::new(), Vec::new())),
            exprs: vec![scalar(truncated_sign)],
            correlations: Vec::new(),
            output: integer_output.clone(),
        },
        integer_output,
    ));

    let dynamic_text_to_int = || ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::InputRef { index: 0 }],
        }),
        ty: "INTEGER".to_owned(),
    };
    let closed_division = || ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    let text_input = one_row_values(
        vec![typed_column("text_value", SqlType::text())],
        vec![ScalarAst::Literal {
            raw: "'bad'".to_owned(),
        }],
    );
    let competing_output = vec![
        typed_column("dynamic_error", SqlType::Integer),
        typed_column("planner_error", SqlType::Integer),
    ];
    assert_planner_blocked(query_for_rel(
        RelExpr::Project {
            input: Box::new(text_input.clone()),
            exprs: vec![scalar(dynamic_text_to_int()), scalar(closed_division())],
            correlations: Vec::new(),
            output: competing_output.clone(),
        },
        competing_output,
    ));

    let nested_output = vec![typed_column("value", SqlType::Integer)];
    assert_planner_blocked(query_for_rel(
        RelExpr::Project {
            input: Box::new(text_input),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![dynamic_text_to_int(), closed_division()],
            })],
            correlations: Vec::new(),
            output: nested_output.clone(),
        },
        nested_output,
    ));
}

#[test]
fn boolean_connectives_lower_scalar_and_relational_subquery_roles() {
    let scope = Scope {
        attributes: vec![ScopeAttribute {
            name: "outer_flag".to_owned(),
            visible_name: "outer_flag".to_owned(),
            formal_ty: FormalAttributeType::Bool,
            numeric_dscale: None,
        }],
    };
    let subquery = || RelExpr::TableScan {
        table: vec!["inner_flags".to_owned()],
        output: vec![typed_column("flag", SqlType::Boolean)],
    };
    let true_literal = ScalarAst::Literal {
        raw: "true".to_owned(),
    };

    let direct_scalar = ScalarAst::RelSubquery {
        rel: Box::new(subquery()),
    };
    let direct_predicate = ScalarAst::Call {
        operator: "AND".to_owned(),
        op: ScalarOp::And,
        args: vec![true_literal.clone(), direct_scalar],
    };
    let mut direct_context = LoweringContext::new(LoweringConfig::default(), None);
    assert!(
        direct_context
            .lower_scalar_boolean_expr("predicate", &direct_predicate, &scope)
            .is_some(),
        "{:#?}",
        direct_context.diagnostics
    );
    assert!(direct_context.diagnostics.is_empty());

    let exists = ScalarAst::Call {
        operator: "EXISTS".to_owned(),
        op: ScalarOp::Exists,
        args: vec![ScalarAst::RelSubquery {
            rel: Box::new(subquery()),
        }],
    };
    let membership = ScalarAst::Call {
        operator: "IN".to_owned(),
        op: ScalarOp::In,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::RelSubquery {
                rel: Box::new(subquery()),
            },
        ],
    };
    for (label, relational_predicate) in [("EXISTS", exists), ("IN", membership)] {
        let predicate = ScalarAst::Call {
            operator: "AND".to_owned(),
            op: ScalarOp::And,
            args: vec![true_literal.clone(), relational_predicate],
        };
        let mut context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(
            context
                .lower_scalar_boolean_expr("predicate", &predicate, &scope)
                .is_some(),
            "{label}: {:#?}",
            context.diagnostics
        );
        assert!(
            context.diagnostics.is_empty(),
            "{label}: {:#?}",
            context.diagnostics
        );
    }
}

#[test]
fn predicate_value_reuses_mixed_integral_numeric_coercion() {
    let input = vec![
        typed_column("integral_value", SqlType::Integer),
        decimal_column_unconstrained("numeric_value"),
    ];
    let output = vec![
        typed_column("forward_equal", SqlType::Boolean),
        typed_column("reverse_equal", SqlType::Boolean),
    ];
    let equality = |left, right| {
        scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: left },
                ScalarAst::InputRef { index: right },
            ],
        })
    };
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            exprs: vec![equality(0, 1), equality(1, 0)],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let FormalQueryExpr::Projection { select, .. } =
        lowered_query_expr(&lowered).expect("mixed numeric comparison projection")
    else {
        panic!("expected relational projection");
    };
    for (item, cast_index) in select.iter().zip([0, 1]) {
        let FormalScalarExpr::BooleanValue { expression } = &item.expr else {
            panic!("expected equality predicate value, got {:?}", item.expr);
        };
        let FormalScalarExpr::Predicate {
            predicate: FormalPredicate::Eq,
            args,
        } = expression.as_ref()
        else {
            panic!("expected equality predicate value, got {:?}", item.expr);
        };
        assert!(matches!(
            &args[cast_index],
            FormalScalarExpr::Call {
                operator: ScalarOperator::Cast(ScalarCast::ToNumeric(
                    ScalarNumericSource::Int32
                )),
                args,
                ..
            } if args.len() == 1
        ));
    }

    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumeric ScalarSourceInt32)")
    );
}

#[test]
fn rejects_locale_dependent_string_case_mapping() {
    for op in [ScalarOp::Lower, ScalarOp::Upper] {
        let case_mapping = ScalarAst::Call {
            operator: format!("{op:?}"),
            op: op.clone(),
            args: vec![ScalarAst::InputRef { index: 0 }],
        };
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: vec![typed_column("name", SqlType::varchar(None))],
                }),
                exprs: vec![scalar(case_mapping.clone())],
                correlations: Vec::new(),
                output: vec![typed_column("mapped_name", SqlType::varchar(None))],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);

        assert_eq!(lowered.status, LoweringStatus::Blocked);
        assert!(
            lowered.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "string_case_locale_semantics_not_supported"
            })
        );

        let scope = Scope {
            attributes: vec![ScopeAttribute {
                name: "name".to_owned(),
                visible_name: "name".to_owned(),
                formal_ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                numeric_dscale: None,
            }],
        };
        let mut context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(
            context
                .lower_function_term("caseMapping", &case_mapping, &scope)
                .is_none()
        );
        assert!(
            context.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "string_case_locale_semantics_not_supported"
            })
        );
    }
}
#[test]
fn lowers_ascii_string_case_mapping_with_explicit_postgres_utf8_c_environment() {
    for op in [ScalarOp::Lower, ScalarOp::Upper] {
        let output = vec![typed_column("mapped_name", SqlType::text())];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: vec![typed_column("name", SqlType::text())],
                }),
                exprs: vec![scalar(ScalarAst::Call {
                    operator: format!("{op:?}"),
                    op: op.clone(),
                    args: vec![ScalarAst::InputRef { index: 0 }],
                })],
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        };
        let lowered = lower_query_with_config(
            &query,
            &LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            },
        );

        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("lowered case mapping"),
            lowered.query_expr.as_ref().expect("lowered case mapping"),
        );
        let expected = match op {
            ScalarOp::Upper => "ScalarStringCase ScalarUpper",
            ScalarOp::Lower => "ScalarStringCase ScalarLower",
            _ => unreachable!("test covers only UPPER/LOWER"),
        };
        assert!(module.rocq_module.contains(expected));
    }
}
#[test]
fn locale_dependent_case_mapping_is_not_masked_by_outer_boolean_runtime_risk() {
    let predicate = ScalarAst::Call {
        operator: "AND".to_owned(),
        op: ScalarOp::And,
        args: vec![
            ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::Call {
                        operator: "*".to_owned(),
                        op: ScalarOp::Multiply,
                        args: vec![
                            ScalarAst::InputRef { index: 0 },
                            ScalarAst::InputRef { index: 1 },
                        ],
                    },
                    ScalarAst::InputRef { index: 2 },
                ],
            },
            ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::Call {
                        operator: "UPPER".to_owned(),
                        op: ScalarOp::Upper,
                        args: vec![ScalarAst::InputRef { index: 3 }],
                    },
                    ScalarAst::Literal {
                        raw: "'FOO'".to_owned(),
                    },
                ],
            },
        ],
    };
    let scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "sal".to_owned(),
                visible_name: "sal".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "comm".to_owned(),
                visible_name: "comm".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "expected".to_owned(),
                visible_name: "expected".to_owned(),
                formal_ty: FormalAttributeType::Int32,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "ename".to_owned(),
                visible_name: "ename".to_owned(),
                formal_ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                numeric_dscale: None,
            },
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);

    assert!(
        context
            .lower_scalar_boolean_expr("predicate", &predicate, &scope)
            .is_none()
    );
    assert!(
        context
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "string_case_locale_semantics_not_supported" })
    );
}
#[test]
fn rejects_scalar_functions_without_a_rocq_interpretation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("x", SqlType::Double)],
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "EXP".to_owned(),
                op: ScalarOp::Exp,
                args: vec![ScalarAst::InputRef { index: 0 }],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("result", SqlType::Double)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "function_interpretation_not_supported" }),
        "an ordinary DOUBLE EXP must remain on the generic unsupported-function path: {:#?}",
        lowered.diagnostics
    );
}
#[test]
fn lowers_extract_year_from_date_to_numeric_builtin() {
    let input = vec![typed_column("d", SqlType::Date)];
    let extract = ScalarAst::Call {
        operator: "EXTRACT".to_owned(),
        op: ScalarOp::Extract,
        args: vec![
            ScalarAst::Flag {
                name: "YEAR".to_owned(),
            },
            ScalarAst::InputRef { index: 0 },
        ],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["events".to_owned()],
                output: input.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    extract,
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "2014".to_owned(),
                        }),
                        ty: "NUMERIC".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: input.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("ScalarExtractDate ScalarYear"));
    assert!(module.rocq_module.contains("CstNumeric"));
}
#[test]
fn lowers_extract_month_from_date_to_numeric_builtin() {
    let input = vec![typed_column("d", SqlType::Date)];
    let extract = ScalarAst::Call {
        operator: "EXTRACT".to_owned(),
        op: ScalarOp::Extract,
        args: vec![
            ScalarAst::Flag {
                name: "MONTH".to_owned(),
            },
            ScalarAst::InputRef { index: 0 },
        ],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["events".to_owned()],
                output: input.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    extract,
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "4".to_owned(),
                        }),
                        ty: "NUMERIC".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: input.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("ScalarExtractDate ScalarMonth"));
    assert!(module.rocq_module.contains("CstNumeric"));
}
#[test]
fn overrides_stale_integral_project_type_for_postgres_extract() {
    let input = vec![typed_column("d", SqlType::Date)];
    let stale_output = vec![typed_column("year", SqlType::BigInt)];
    let query = Query {
        source_sql: Some("SELECT EXTRACT(YEAR FROM d) FROM events".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["events".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "EXTRACT".to_owned(),
                op: ScalarOp::Extract,
                args: vec![
                    ScalarAst::Flag {
                        name: "YEAR".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: stale_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert_eq!(
        lowered.output_signature.as_ref().expect("output signature")[0].ty,
        FormalAttributeType::Numeric
    );
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_extract_type_overridden" })
    );
}
#[test]
fn folds_exact_postgres_boolean_source_literals_before_formal_lowering() {
    for (source, expected) in [("'t'", "CstBool true"), ("'f'", "CstBool false")] {
        let output = vec![typed_column("enabled", SqlType::Boolean)];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(one_row_values(Vec::new(), Vec::new())),
                exprs: vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Call {
                        operator: "CAST".to_owned(),
                        op: ScalarOp::Cast,
                        args: vec![ScalarAst::Literal {
                            raw: source.to_owned(),
                        }],
                    }),
                    ty: "BOOLEAN".to_owned(),
                })],
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "source={source}: {:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("query expression"),
            lowered.query_expr.as_ref().expect("query expression"),
        );
        assert!(module.rocq_module.contains(expected));
        assert!(!module.rocq_module.contains("cast_not_supported"));
    }
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
            constraints: Default::default(),
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let schema = lowered.schema.as_ref().expect("schema should lower");
    assert!(schema.rocq_module.contains("Attr_float \"f\""));
    assert!(schema.rocq_module.contains("Attr_double \"d\""));
    let report = serde_json::to_value(schema).expect("serialize formal schema");
    let object = report.as_object().expect("formal schema object");
    assert!(!object.contains_key("rocqCreateSchema"));
    assert!(object.contains_key("tables"));
    assert!(object.contains_key("rocqModule"));
}
#[test]
fn rejects_duplicate_canonical_schema_relation_names() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "foo".to_owned(),
                columns: vec![typed_column("a", SqlType::Integer)],
                constraints: Default::default(),
            },
            Table {
                name: "foo".to_owned(),
                columns: vec![typed_column("b", SqlType::Integer)],
                constraints: Default::default(),
            },
        ],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.schema.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "duplicate_schema_relation")
    );
}
#[test]
fn retains_distinct_quoted_and_unquoted_schema_relation_identities() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "foo".to_owned(),
                columns: vec![typed_column("a", SqlType::Integer)],
                constraints: Default::default(),
            },
            Table {
                name: "Foo".to_owned(),
                columns: vec![typed_column("b", SqlType::Integer)],
                constraints: Default::default(),
            },
        ],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let tables = &lowered.schema.as_ref().expect("schema").tables;
    assert_eq!(tables[0].relation, "foo");
    assert_eq!(tables[1].relation, "Foo");
}
#[test]
fn lowers_double_arithmetic_with_double_operator() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("ScalarAdd ScalarDouble"));
    assert!(!module.rocq_module.contains("ScalarAdd ScalarFloat"));
}
#[test]
fn lowers_integer_and_bigint_arithmetic_with_checked_operators() {
    let input = vec![
        typed_column("left_int", SqlType::Integer),
        typed_column("right_int", SqlType::Integer),
        typed_column("big_value", SqlType::BigInt),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            exprs: vec![
                scalar(ScalarAst::Call {
                    operator: "+".to_owned(),
                    op: ScalarOp::Plus,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::InputRef { index: 1 },
                    ],
                }),
                scalar(ScalarAst::Call {
                    operator: "*".to_owned(),
                    op: ScalarOp::Multiply,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::InputRef { index: 2 },
                    ],
                }),
                scalar(ScalarAst::Call {
                    operator: "+".to_owned(),
                    op: ScalarOp::Plus,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::Literal {
                            raw: "1".to_owned(),
                        },
                    ],
                }),
            ],
            correlations: Vec::new(),
            output: vec![
                typed_column("int_sum", SqlType::Integer),
                typed_column("mixed_product", SqlType::BigInt),
                typed_column("int_plus_literal", SqlType::Integer),
            ],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("ScalarAdd ScalarInt32"));
    assert!(module.rocq_module.contains("ScalarMultiply ScalarInt64"));
    assert!(module.rocq_module.contains("CstInt32 (1)"));
}

#[test]
fn rejects_integer_expression_output_type_mismatch() {
    let input = vec![
        typed_column("left_int", SqlType::Integer),
        typed_column("right_int", SqlType::Integer),
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
            output: vec![typed_column("sum_value", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "integer_output_type_not_supported")
    );
}

#[test]
fn rejects_out_of_range_integer_literal_annotation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: Vec::new(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "2147483648".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("too_big", SqlType::Integer)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "integer_literal_out_of_range")
    );
}

#[test]
fn rejects_smallint_cast_instead_of_widening_it_to_integer() {
    let smallint_cast = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "32768".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            }],
        }),
        ty: "SMALLINT".to_owned(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: Vec::new(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![smallint_cast],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Integer)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        matches!(
            diagnostic.code.as_str(),
            "cast_target_type_not_supported" | "cast_source_type_not_supported"
        )
    }));
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
        analysis_errors: vec![],
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
        analysis_errors: vec![],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
            analysis_errors: vec![],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4620130267728707584)")
    );
}

#[test]
fn lowers_non_integer_double_literal_in_predicate_context() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4620130267728707584)")
    );
}

#[test]
fn lowers_float_and_double_order_predicates_with_matching_operators() {
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
        analysis_errors: vec![],
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
        analysis_errors: vec![],
    };

    let lowered_float = lower_query(&float_query);
    let lowered_double = lower_query(&double_query);

    assert_eq!(lowered_float.status, LoweringStatus::Lowered);
    assert_eq!(lowered_double.status, LoweringStatus::Lowered);
    let FormalQueryExpr::Selection {
        predicate:
            FormalScalarExpr::Predicate {
                predicate: float_predicate,
                ..
            },
        ..
    } = lowered_query_expr(&lowered_float).unwrap()
    else {
        panic!("expected float selection predicate");
    };
    let FormalQueryExpr::Selection {
        predicate:
            FormalScalarExpr::Predicate {
                predicate: double_predicate,
                ..
            },
        ..
    } = lowered_query_expr(&lowered_double).unwrap()
    else {
        panic!("expected double selection predicate");
    };
    assert_eq!(*float_predicate, FormalPredicate::FloatGt);
    assert_eq!(*double_predicate, FormalPredicate::DoubleLt);
}

#[test]
fn rejects_string_order_predicate_without_collation_semantics() {
    let output = vec![
        typed_column("left_value", SqlType::varchar(None)),
        typed_column("right_value", SqlType::varchar(None)),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["names".to_owned()],
                output: output.clone(),
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
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "string_collation_predicate_not_supported" })
    );
}

#[test]
fn lowers_complementary_text_order_disjunction_as_disequality() {
    for (label, first_op, second_op) in [
        ("lt-gt", ScalarOp::Lt, ScalarOp::Gt),
        ("gt-lt", ScalarOp::Gt, ScalarOp::Lt),
    ] {
        let predicate_ast = complementary_string_order_ast(0, 0, "'3'", "'3'", first_op, second_op);
        let output = vec![typed_column("name", SqlType::text())];
        let query = query_for_rel(
            RelExpr::Filter {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["names".to_owned()],
                    output: output.clone(),
                }),
                predicate: scalar(predicate_ast.clone()),
                correlations: Vec::new(),
                output: output.clone(),
            },
            output,
        );

        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Lowered, "{label}");
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("query expression"),
            lowered.query_expr.as_ref().expect("query expression"),
        );
        assert!(module.rocq_module.contains("PredicateNeq"), "{label}");
        assert!(!module.rocq_module.contains("PredicateLt"), "{label}");
        assert!(!module.rocq_module.contains("PredicateGt"), "{label}");

        let scope = Scope {
            attributes: vec![ScopeAttribute {
                name: "name".to_owned(),
                visible_name: "name".to_owned(),
                formal_ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                numeric_dscale: None,
            }],
        };
        let mut predicate_context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(matches!(
            predicate_context.lower_scalar_boolean_expr("predicate", &predicate_ast, &scope),
            Some(FormalScalarExpr::Predicate {
                predicate: FormalPredicate::Neq,
                ..
            })
        ));
        let mut expression_context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(matches!(
            expression_context.lower_scalar_boolean_expr("predicate", &predicate_ast, &scope),
            Some(FormalScalarExpr::Predicate {
                predicate: FormalPredicate::Neq,
                ..
            })
        ));
    }
}

fn date_plus_interval_comparison_ast(op: ScalarOp) -> ScalarAst {
    ScalarAst::Call {
        operator: format!("{op:?}"),
        op,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "0".to_owned(),
                        }),
                        ty: "DATE".to_owned(),
                    },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "3".to_owned(),
                        }),
                        ty: "INTERVAL DAY".to_owned(),
                    },
                ],
            },
        ],
    }
}

#[test]
fn date_interval_comparisons_use_exact_postgres_cross_type_order_predicates() {
    let scope = Scope {
        attributes: vec![ScopeAttribute {
            name: "d".to_owned(),
            visible_name: "d".to_owned(),
            formal_ty: FormalAttributeType::Date,
            numeric_dscale: None,
        }],
    };
    for (op, expected) in [
        (ScalarOp::Lt, FormalPredicate::DateLtTimestamp),
        (ScalarOp::Lte, FormalPredicate::DateLteTimestamp),
        (ScalarOp::Gt, FormalPredicate::DateGtTimestamp),
        (ScalarOp::Gte, FormalPredicate::DateGteTimestamp),
    ] {
        let mut context = LoweringContext::new(LoweringConfig::default(), None);
        let lowered = context.lower_scalar_boolean_expr(
            "predicate",
            &date_plus_interval_comparison_ast(op),
            &scope,
        );
        assert!(
            matches!(lowered,
                Some(FormalScalarExpr::Predicate { predicate, args })
                    if predicate == expected && args.len() == 2),
            "{}: {:#?}",
            expected.model_name(),
            context.diagnostics
        );
        assert!(context.diagnostics.is_empty(), "{}", expected.model_name());
    }

    let mut equality = LoweringContext::new(LoweringConfig::default(), None);
    assert!(
        equality
            .lower_scalar_boolean_expr(
                "predicate",
                &date_plus_interval_comparison_ast(ScalarOp::Eq),
                &scope,
            )
            .is_none()
    );
    assert!(equality.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "date_timestamp_comparison_predicate_not_supported"
    }));
}

#[test]
fn date_timestamp_value_comparison_uses_the_cross_type_predicate_operator() {
    let input = vec![
        typed_column("date_value", SqlType::Date),
        timestamp_column("timestamp_value", None),
    ];
    let output = vec![typed_column("is_before", SqlType::Boolean)];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["events".to_owned()],
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
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let FormalQueryExpr::Projection { select, .. } =
        lowered_query_expr(&lowered).expect("value comparison projection")
    else {
        panic!("expected relational projection");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::BooleanValue {
                expression,
            },
            ..
        }] if matches!(expression.as_ref(),
            FormalScalarExpr::Predicate {
                predicate: FormalPredicate::DateLtTimestamp,
                args,
            } if args.len() == 2)
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("PredicateDateLtTimestamp"));
}

#[test]
fn complementary_text_order_rewrite_remains_fail_closed() {
    let cases = [
        (
            "mismatched-literals",
            complementary_string_order_ast(0, 0, "'a'", "'b'", ScalarOp::Lt, ScalarOp::Gt),
            SqlStringType::Text,
        ),
        (
            "mismatched-references",
            complementary_string_order_ast(0, 1, "'a'", "'a'", ScalarOp::Lt, ScalarOp::Gt),
            SqlStringType::Text,
        ),
        (
            "non-strict-order",
            complementary_string_order_ast(0, 0, "'a'", "'a'", ScalarOp::Lte, ScalarOp::Gt),
            SqlStringType::Text,
        ),
        (
            "varchar",
            complementary_string_order_ast(0, 0, "'a'", "'a'", ScalarOp::Lt, ScalarOp::Gt),
            SqlStringType::Varchar { length: None },
        ),
        (
            "bpchar",
            complementary_string_order_ast(0, 0, "'a'", "'a'", ScalarOp::Lt, ScalarOp::Gt),
            SqlStringType::Bpchar,
        ),
    ];

    for (label, predicate, typmod) in cases {
        let scope = Scope {
            attributes: vec![
                ScopeAttribute {
                    name: "left".to_owned(),
                    visible_name: "left".to_owned(),
                    formal_ty: FormalAttributeType::String { typmod },
                    numeric_dscale: None,
                },
                ScopeAttribute {
                    name: "right".to_owned(),
                    visible_name: "right".to_owned(),
                    formal_ty: FormalAttributeType::String { typmod },
                    numeric_dscale: None,
                },
            ],
        };
        let mut context = LoweringContext::new(LoweringConfig::default(), None);
        assert!(
            context
                .lower_scalar_boolean_expr("predicate", &predicate, &scope)
                .is_none(),
            "{label}"
        );
        assert!(
            context.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "string_collation_predicate_not_supported"
            }),
            "{label}: {:#?}",
            context.diagnostics
        );
    }

    let two_references = ScalarAst::Call {
        operator: "OR".to_owned(),
        op: ScalarOp::Or,
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
                operator: ">".to_owned(),
                op: ScalarOp::Gt,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            },
        ],
    };
    let text_scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "left".to_owned(),
                visible_name: "left".to_owned(),
                formal_ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "right".to_owned(),
                visible_name: "right".to_owned(),
                formal_ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                numeric_dscale: None,
            },
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    assert!(
        context
            .lower_scalar_boolean_expr("predicate", &two_references, &text_scope)
            .is_none()
    );
    assert!(
        context
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "string_collation_predicate_not_supported" })
    );
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
        analysis_errors: vec![],
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
fn rejects_integer_temporal_comparison_predicate() {
    let output = vec![
        typed_column("id", SqlType::Integer),
        typed_column("created_on", SqlType::Date),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["events".to_owned()],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "comparison_operand_type_not_supported")
    );
}

#[test]
fn lowers_mixed_integer_bigint_comparison_predicate() {
    let output = vec![
        typed_column("small_id", SqlType::Integer),
        typed_column("large_id", SqlType::BigInt),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["ids".to_owned()],
                output: output.clone(),
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
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::Predicate { predicate, .. },
        ..
    } = lowered_query_expr(&lowered).unwrap()
    else {
        panic!("expected selection predicate");
    };
    assert_eq!(*predicate, FormalPredicate::Lt);
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
        analysis_errors: vec![],
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
fn lowers_double_sum_with_representative_order_semantics() {
    let input = vec![typed_column("value", SqlType::Double)];
    for distinct in [false, true] {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["measurements".to_owned()],
                    output: input.clone(),
                }),
                group_keys: Vec::new(),
                grouping_sets: vec![Vec::new()],
                agg_calls: vec![AggregateCall {
                    raw: "SUM($0)".to_owned(),
                    function: "SUM".to_owned(),
                    distinct,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                }],
                output: vec![typed_column("sum_value", SqlType::Double)],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);

        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "diagnostics: {:#?}",
            lowered.diagnostics
        );
        let Some(FormalQueryExpr::Group { select, .. }) = lowered.query_expr.as_ref() else {
            panic!("floating SUM should lower as an explicit logical Group");
        };
        let expected_quantifier = if distinct {
            FormalAggregateQuantifier::Distinct
        } else {
            FormalAggregateQuantifier::All
        };
        assert!(matches!(
            select.as_slice(),
            [FormalScalarSelectItem {
                expr: FormalScalarExpr::Leaf {
                    term: FormalAggregateTerm::Aggregate {
                        function: FormalAggregateFunction::SumDouble,
                        quantifier,
                        ..
                    },
                    ..
                },
                alias_ty: FormalAttributeType::Double,
                ..
            }] if *quantifier == expected_quantifier
        ));
    }
}

#[test]
fn lowers_real_average_as_double_precision() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![typed_column("value", SqlType::Float)],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("average_value", SqlType::Double)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Group { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("REAL AVG should lower as an explicit logical Group");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                term: FormalAggregateTerm::Aggregate {
                    function: FormalAggregateFunction::AverageFloat,
                    ..
                },
                ..
            },
            alias_ty: FormalAttributeType::Double,
            ..
        }]
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("lowered REAL AVG"),
        lowered.query_expr.as_ref().expect("lowered REAL AVG"),
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateAverageFloat AggregateAll")
    );
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
            grouping_sets: vec![Vec::new()],
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
        analysis_errors: vec![],
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
            grouping_sets: vec![Vec::new()],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "integer_sum_output_type_not_supported" })
    );
}

#[test]
fn lowers_literal_integer_sum_as_bigint_counted_aggregate() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                vec![column("id")],
                vec![ScalarAst::Literal {
                    raw: "1".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
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
            output: vec![typed_column("sum_value", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateSumInt32 AggregateAll")
    );
    assert!(
        module
            .rocq_module
            .contains("Constant (Value_int32 (int32_checked (7)%Z))")
    );
}

#[test]
fn lowers_filtered_aggregates_through_lazy_case_projection() {
    let input = vec![
        typed_column("value", SqlType::Integer),
        typed_column("keep", SqlType::Boolean),
    ];
    let filter = scalar(ScalarAst::InputRef { index: 1 });
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![
                AggregateCall {
                    raw: "COUNT(*) FILTER (WHERE keep)".to_owned(),
                    function: "COUNT".to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: Vec::new(),
                    filter: Some(filter.clone()),
                },
                AggregateCall {
                    raw: "SUM(value) FILTER (WHERE keep)".to_owned(),
                    function: "SUM".to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: Some(filter),
                },
            ],
            output: vec![
                typed_column("kept_rows", SqlType::BigInt),
                typed_column("kept_sum", SqlType::BigInt),
            ],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Group { input, select, .. }) = lowered.query_expr.as_ref() else {
        panic!("global aggregate should use exact query-expression grouping");
    };
    let FormalQueryExpr::Projection {
        select: projected, ..
    } = input.as_ref()
    else {
        panic!("FILTER must materialize lazy CASE arguments in one projection");
    };
    assert_eq!(projected.len(), 4);
    assert!(matches!(projected[2].expr, FormalScalarExpr::Case { .. }));
    assert!(matches!(projected[3].expr, FormalScalarExpr::Case { .. }));
    assert!(matches!(
        select[0].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Aggregate {
                function: FormalAggregateFunction::Count,
                ..
            },
            ..
        }
    ));
    assert!(matches!(
        select[1].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Aggregate {
                function: FormalAggregateFunction::SumInt32,
                ..
            },
            ..
        }
    ));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("@SExpr_Case TNull relname"));
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateSumInt32 AggregateAll")
    );
}

#[test]
fn lowers_integer_avg_with_postgres_wrapping_transition() {
    let input = vec![typed_column("value", SqlType::Integer)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input,
                vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1".to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column_unconstrained("avg_value")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateAverageInt32Numeric AggregateAll")
    );
}

#[test]
fn lowers_integral_postgres_variance_and_stddev_families() {
    for (function, constructor) in [
        ("VAR_POP", "AggregateVariancePopulationInt32"),
        ("VAR_SAMP", "AggregateVarianceSampleInt32"),
        ("VARIANCE", "AggregateVarianceSampleInt32"),
        ("STDDEV_POP", "AggregateStddevPopulationInt32"),
        ("STDDEV_SAMP", "AggregateStddevSampleInt32"),
        ("STDDEV", "AggregateStddevSampleInt32"),
    ] {
        let input = vec![typed_column("value", SqlType::Integer)];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["measurements".to_owned()],
                    output: input,
                }),
                group_keys: Vec::new(),
                grouping_sets: vec![Vec::new()],
                agg_calls: vec![AggregateCall {
                    raw: format!("{function}($0)"),
                    function: function.to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                }],
                // Calcite reports INTEGER for this family. PostgreSQL's
                // authoritative result type is unconstrained NUMERIC.
                output: vec![typed_column("stat", SqlType::Integer)],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{function:?}: {:?}",
            lowered.diagnostics
        );
        assert_eq!(
            lowered.output_signature.as_ref().unwrap()[0].ty,
            FormalAttributeType::Numeric
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().unwrap(),
            lowered.query_expr.as_ref().unwrap(),
        );
        assert!(
            module
                .rocq_module
                .contains(&format!("AAggregate {constructor} AggregateAll"))
        );
    }
}

fn attested_numeric_stddev_samp_call() -> AggregateCall {
    AggregateCall {
        raw: "STDDEV_SAMP($0)".to_owned(),
        function: "STDDEV_SAMP".to_owned(),
        distinct: false,
        modifiers: AggregateModifiers {
            source: Some(ScalarSourceProvenance {
                sql: Some("STDDEV_SAMP(`ss_net_profit`)".to_owned()),
                node_id: Some("test:stddev-samp-root".to_owned()),
                text: Some("STDDEV_SAMP(ss_net_profit)".to_owned()),
                kind: Some("OTHER_FUNCTION".to_owned()),
                operator: Some("stddev_samp".to_owned()),
                clause_ownership: None,
                operands: vec![Some(ScalarSourceProvenance {
                    sql: Some("ss_net_profit".to_owned()),
                    node_id: Some("test:stddev-samp-argument".to_owned()),
                    text: Some("ss_net_profit".to_owned()),
                    kind: Some("IDENTIFIER".to_owned()),
                    operator: None,
                    clause_ownership: None,
                    operands: Vec::new(),
                })],
            }),
            source_distinct: Some(false),
            ..AggregateModifiers::default()
        },
        args: vec![scalar(ScalarAst::InputRef { index: 0 })],
        filter: None,
    }
}

fn numeric_stddev_samp_query(call: AggregateCall, precision: u32, scale: u32) -> Query {
    Query {
        source_sql: Some("select stddev_samp(ss_net_profit) from store_sales".to_owned()),
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["store_sales".to_owned()],
                output: vec![decimal_column("ss_net_profit", precision, scale)],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![call],
            // Exercise the Rust guard independently of Logos-IR's earlier
            // authoritative correction by retaining Calcite's stale typmod.
            output: vec![decimal_column("store_sales_profit", precision, scale)],
        },
        analysis_errors: vec![],
    }
}

#[test]
fn lowers_only_attested_numeric_stddev_samp_to_postgres_numeric() {
    let query = numeric_stddev_samp_query(attested_numeric_stddev_samp_call(), 12, 3);
    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_ref().unwrap()[0].ty,
        FormalAttributeType::Numeric
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate (AggregateStddevSampleNumericFixed (12)%Z (3)%Z) AggregateAll")
    );

    let mut rendered_drift = attested_numeric_stddev_samp_call();
    let source = rendered_drift.modifiers.source.as_mut().unwrap();
    source.sql = Some("STDDEV_SAMP(`rendered_other`)".to_owned());
    source.operands[0].as_mut().unwrap().sql = Some("rendered_other".to_owned());
    let lowered = lower_query(&numeric_stddev_samp_query(rendered_drift, 12, 3));
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "rendered SQL is diagnostic-only when the exact node/text pair is unchanged: {:?}",
        lowered.diagnostics
    );
}

#[test]
fn rejects_unattested_or_source_cast_numeric_stddev_samp() {
    let mut missing = attested_numeric_stddev_samp_call();
    missing.modifiers.source = None;

    let mut source_cast = attested_numeric_stddev_samp_call();
    let operand = source_cast
        .modifiers
        .source
        .as_mut()
        .and_then(|source| source.operands[0].as_mut())
        .unwrap();
    operand.kind = Some("CAST".to_owned());
    operand.operator = Some("CAST".to_owned());
    operand.node_id = Some("test:stddev-samp-explicit-cast".to_owned());
    operand.text = Some("CAST(ss_net_profit AS DECIMAL(7,2))".to_owned());
    let source = source_cast.modifiers.source.as_mut().unwrap();
    source.text = Some("STDDEV_SAMP(CAST(ss_net_profit AS DECIMAL(7,2)))".to_owned());

    let mut source_distinct = attested_numeric_stddev_samp_call();
    source_distinct.modifiers.source_distinct = Some(true);

    for (label, call) in [
        ("missing", missing),
        ("source-cast", source_cast),
        ("source-distinct", source_distinct),
    ] {
        let lowered = lower_query(&numeric_stddev_samp_query(call, 12, 3));
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "aggregate_result_type_not_supported"),
            "{label}: {:?}",
            lowered.diagnostics
        );
    }
}

#[test]
fn rejects_bigint_statistic_until_exact_numeric_transition_is_modeled() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![typed_column("value", SqlType::BigInt)],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "VAR_POP($0)".to_owned(),
                function: "VAR_POP".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("stat", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "bigint_statistic_not_supported")
    );
}

#[test]
fn lowers_total_explicit_integer_to_bigint_cast() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("value", SqlType::Integer)],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "BIGINT".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastInt32ToInt64")
    );
}

#[test]
fn lowers_checked_explicit_bigint_to_integer_cast() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("value", SqlType::BigInt)],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Integer)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastInt64ToInt32")
    );
}

#[test]
fn lowers_postgres_string_to_fixed_width_integer_casts() {
    for (target_sql, target_type, expected_operator) in [
        (
            "INTEGER",
            SqlType::Integer,
            "ScalarCast ScalarCastStringToInt32",
        ),
        (
            "BIGINT",
            SqlType::BigInt,
            "ScalarCast ScalarCastStringToInt64",
        ),
    ] {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: vec![typed_column("value", SqlType::text())],
                }),
                exprs: vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Call {
                        operator: "CAST".to_owned(),
                        op: ScalarOp::Cast,
                        args: vec![ScalarAst::InputRef { index: 0 }],
                    }),
                    ty: target_sql.to_owned(),
                })],
                correlations: Vec::new(),
                output: vec![typed_column("value", target_type)],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{target_sql}: {:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().unwrap(),
            lowered.query_expr.as_ref().unwrap(),
        );
        assert!(
            module.rocq_module.contains(expected_operator),
            "{target_sql}: {}",
            module.rocq_module
        );
    }
}

#[test]
fn count_over_double_still_returns_integer_count() {
    let input = vec![typed_column("value", SqlType::Double)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input,
                vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1.0".to_owned(),
                    }),
                    ty: "DOUBLE".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
}

#[test]
fn lowers_global_aggregate_over_potentially_empty_input_to_exact_group() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("a")],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT()".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: Vec::new(),
                filter: None,
            }],
            output: vec![typed_column("c", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    let Some(FormalQueryExpr::Group {
        group_by, input, ..
    }) = lowered.query_expr
    else {
        panic!("global aggregation must use the exact query Group constructor");
    };
    assert!(group_by.is_empty());
    assert!(matches!(*input, FormalQueryExpr::Table { .. }));
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert_no_physical_plan_constructs(&module);
}

#[test]
fn rejects_string_min_without_a_matching_formal_aggregate() {
    let input = vec![typed_column("value", SqlType::varchar(None))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "MIN($0)".to_owned(),
                function: "MIN".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("min_value", SqlType::varchar(None))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "aggregate_result_type_not_supported")
    );
}

#[test]
fn lowers_max_text_only_with_explicit_postgres_utf8_c_environment() {
    let output = vec![typed_column("max_value", SqlType::text())];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![typed_column("value", SqlType::text())],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "MAX($0)".to_owned(),
                function: "MAX".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let unspecified = lower_query(&query);
    assert_eq!(unspecified.status, LoweringStatus::Blocked);
    assert!(
        unspecified
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "string_collation_aggregate_not_supported" })
    );

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_environment: SqlEnvironment::postgres_utf8_c(),
            ..LoweringConfig::default()
        },
    );
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("lowered MAX(text)"),
        lowered.query_expr.as_ref().expect("lowered MAX(text)"),
    );
    assert!(module.rocq_module.contains("AggregateMaxString"));
}

#[test]
fn lowers_grouped_text_minmax_as_key_identity_with_authoritative_type() {
    let input = vec![typed_column("name", SqlType::text())];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["departments".to_owned()],
                output: input,
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![
                AggregateCall {
                    raw: "MAX($0)".to_owned(),
                    function: "MAX".to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                },
                AggregateCall {
                    raw: "MIN($0)".to_owned(),
                    function: "MIN".to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                },
            ],
            // Calcite loses PostgreSQL's recovered TEXT provenance on these
            // aggregate result columns and reports unconstrained VARCHAR.
            output: vec![
                typed_column("name", SqlType::text()),
                typed_column("largest_name", SqlType::varchar(None)),
                typed_column("smallest_name", SqlType::varchar(None)),
            ],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "calcite_aggregate_type_overridden")
            .count(),
        2
    );
    let Some(FormalQueryExpr::Group { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("expected grouped query");
    };
    let expected_type = FormalAttributeType::String {
        typmod: SqlStringType::Text,
    };
    for (item, alias) in select[1..].iter().zip(["largest_name", "smallest_name"]) {
        assert_eq!(item.alias, alias);
        assert_eq!(item.alias_ty, expected_type);
        assert!(matches!(
            &item.expr,
            FormalScalarExpr::Leaf {
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute { name, ty }
                },
                ..
            } if name == "name" && *ty == expected_type
        ));
    }
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(!module.rocq_module.contains("AAggregate AggregateMax"));
    assert!(!module.rocq_module.contains("AAggregate AggregateMin"));
}

#[test]
fn rejects_grouped_non_text_string_minmax_until_postgres_coercion_is_modeled() {
    let output = vec![
        typed_column("name", SqlType::varchar(Some(32))),
        typed_column("largest_name", SqlType::varchar(None)),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["departments".to_owned()],
                output: vec![typed_column("name", SqlType::varchar(Some(32)))],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![AggregateCall {
                raw: "MAX($0)".to_owned(),
                function: "MAX".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "aggregate_result_type_not_supported")
    );
}

#[test]
fn rejects_text_minmax_when_argument_is_not_in_active_grouping_set() {
    let input = vec![
        typed_column("department_id", SqlType::Integer),
        typed_column("employee_name", SqlType::text()),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["employees".to_owned()],
                output: input,
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![AggregateCall {
                raw: "MAX($1)".to_owned(),
                function: "MAX".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 1 })],
                filter: None,
            }],
            output: vec![
                typed_column("department_id", SqlType::Integer),
                typed_column("employee_name", SqlType::text()),
            ],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "string_collation_aggregate_not_supported")
    );
}

#[test]
fn rejects_text_minmax_when_group_key_is_absent_from_active_grouping_set() {
    let input = vec![typed_column("name", SqlType::text())];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["departments".to_owned()],
                output: input,
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![]],
            agg_calls: vec![AggregateCall {
                raw: "MAX($0)".to_owned(),
                function: "MAX".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![
                typed_column("name", SqlType::text()),
                typed_column("largest_name", SqlType::text()),
            ],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "string_collation_aggregate_not_supported")
    );
}

#[test]
fn rejects_non_plain_grouped_text_minmax_forms() {
    let base_call = AggregateCall {
        raw: "MAX($0)".to_owned(),
        function: "MAX".to_owned(),
        distinct: false,
        modifiers: AggregateModifiers::default(),
        args: vec![scalar(ScalarAst::InputRef { index: 0 })],
        filter: None,
    };
    let mut distinct = base_call.clone();
    distinct.distinct = true;
    let mut filtered = base_call.clone();
    filtered.filter = Some(scalar(ScalarAst::Literal {
        raw: "true".to_owned(),
    }));
    let mut expression = base_call.clone();
    expression.args = vec![scalar(ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::InputRef { index: 0 }),
        ty: "TEXT".to_owned(),
    })];
    let mut multiple_arguments = base_call.clone();
    multiple_arguments
        .args
        .push(scalar(ScalarAst::InputRef { index: 0 }));
    let mut modified = base_call;
    modified.modifiers.ignore_nulls = true;

    for (label, call, expected_code) in [
        (
            "distinct",
            distinct,
            "string_collation_aggregate_not_supported",
        ),
        (
            "filtered",
            filtered,
            "string_collation_aggregate_not_supported",
        ),
        (
            "expression",
            expression,
            "string_collation_aggregate_not_supported",
        ),
        (
            "multiple-arguments",
            multiple_arguments,
            "aggregate_argument_arity_not_supported",
        ),
        (
            "modifier",
            modified,
            "string_collation_aggregate_not_supported",
        ),
    ] {
        let output = vec![
            typed_column("name", SqlType::text()),
            typed_column("largest_name", SqlType::text()),
        ];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["departments".to_owned()],
                    output: vec![typed_column("name", SqlType::text())],
                }),
                group_keys: vec![0],
                grouping_sets: vec![vec![0]],
                agg_calls: vec![call],
                output: output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Blocked,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == expected_code),
            "{label}: {:#?}",
            lowered.diagnostics
        );
    }
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("CASE expression should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("CASE expression should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let project = match lowered
        .query_expr
        .as_ref()
        .expect("query expression should lower")
    {
        FormalQueryExpr::Projection { select, .. } => &select[0].expr,
        other => panic!("expected projection query, got {other:?}"),
    };
    let FormalScalarExpr::Case { condition, .. } = project else {
        panic!("expected canonical CASE scalar, got {project:?}");
    };
    assert!(matches!(
        condition.as_ref(),
        FormalScalarExpr::And { operands, insertion_sites }
            if operands.len() == 3
                && insertion_sites.iter().map(Vec::len).collect::<Vec<_>>() == vec![0, 1, 2]
    ));
    assert!(module.rocq_module.contains("@SExpr_Case TNull relname"));
    assert!(module.rocq_module.contains("@SExpr_ConjList TNull relname"));
    assert!(
        module
            .rocq_module
            .contains("@SExpr_Pred TNull relname (PredicateIsNull")
    );
}

#[test]
fn preserves_postgres_case_string_typmods() {
    fn explicit_char_literal(raw: &str) -> ScalarAst {
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: "TEXT".to_owned(),
                }],
            }),
            ty: "CHAR(2)".to_owned(),
        }
    }

    fn case_query(else_expr: ScalarAst, output_ty: SqlType) -> Query {
        let input = vec![typed_column("flag", SqlType::Boolean)];
        let output = vec![typed_column("x", output_ty)];
        Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: input,
                }),
                exprs: vec![scalar(ScalarAst::Call {
                    operator: "CASE".to_owned(),
                    op: ScalarOp::Case,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        explicit_char_literal("'a'"),
                        else_expr,
                    ],
                })],
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        }
    }

    let typmodless = lower_query(&case_query(
        ScalarAst::Literal {
            raw: "NULL".to_owned(),
        },
        SqlType::bpchar(),
    ));
    let constrained = lower_query(&case_query(
        explicit_char_literal("NULL"),
        SqlType::character(2),
    ));
    let stale_constrained = lower_query(&case_query(
        ScalarAst::Literal {
            raw: "NULL".to_owned(),
        },
        SqlType::character(2),
    ));
    assert_eq!(
        typmodless.status,
        LoweringStatus::Lowered,
        "{:#?}",
        typmodless.diagnostics
    );
    assert_eq!(
        constrained.status,
        LoweringStatus::Lowered,
        "{:#?}",
        constrained.diagnostics
    );
    assert_eq!(
        stale_constrained.status,
        LoweringStatus::Lowered,
        "{:#?}",
        stale_constrained.diagnostics
    );
    let Some(FormalQueryExpr::Projection {
        select: stale_select,
        ..
    }) = stale_constrained.query_expr.as_ref()
    else {
        panic!("expected source-derived typmodless CASE projection");
    };
    assert_eq!(
        stale_select[0].alias_ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Bpchar,
        }
    );
    assert!(
        stale_constrained
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_case_string_typmod_overridden" })
    );

    let Some(FormalQueryExpr::Projection {
        select: typmodless_select,
        ..
    }) = typmodless.query_expr.as_ref()
    else {
        panic!("expected typmodless CASE projection");
    };
    assert_eq!(
        typmodless_select[0].alias_ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Bpchar,
        }
    );
    let FormalScalarExpr::Case {
        then_expr,
        else_expr,
        ..
    } = &typmodless_select[0].expr
    else {
        panic!("expected typmodless CASE term");
    };
    assert!(matches!(
        then_expr.as_ref(),
        FormalScalarExpr::Call {
            operator: ScalarOperator::Cast(ScalarCast::StringImplicit),
            ..
        }
    ));
    assert!(matches!(
        else_expr.as_ref(),
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    ty: Some(FormalAttributeType::String {
                        typmod: SqlStringType::Bpchar
                    }),
                    ..
                }
            },
            ..
        }
    ));

    let Some(FormalQueryExpr::Projection {
        select: constrained_select,
        ..
    }) = constrained.query_expr.as_ref()
    else {
        panic!("expected constrained CASE projection");
    };
    assert_eq!(
        constrained_select[0].alias_ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Char { length: 2 },
        }
    );
    let FormalScalarExpr::Case { then_expr, .. } = &constrained_select[0].expr else {
        panic!("expected constrained CASE term");
    };
    assert!(!matches!(
        then_expr.as_ref(),
        FormalScalarExpr::Call {
            operator: ScalarOperator::Cast(ScalarCast::StringImplicit),
            ..
        }
    ));
}

#[test]
fn lowers_postgres_string_concat_as_text() {
    let input = vec![typed_column("code", SqlType::character(4))];
    let query = Query {
        source_sql: Some("SELECT 'prefix:' || code FROM t".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "||".to_owned(),
                op: ScalarOp::StringConcat,
                args: vec![
                    ScalarAst::Literal {
                        raw: "'prefix:'".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            // Deliberately stale Calcite width metadata must not override the
            // PostgreSQL operator's text result type.
            output: vec![typed_column("EXPR$0", SqlType::character(11))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_deref(),
        Some(
            [FormalAttribute {
                name: "EXPR$0".to_owned(),
                ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
            }]
            .as_slice()
        )
    );
    let FormalQueryExpr::Projection { select, .. } =
        lowered_query_expr(&lowered).expect("concat query")
    else {
        panic!("expected projection");
    };
    assert!(matches!(
        &select[0].expr,
        FormalScalarExpr::Call {
            operator: ScalarOperator::StringConcat,
            args,
            ..
        } if args.len() == 2
    ));
}

#[test]
fn rejects_variadic_string_concat_before_scalar_emission() {
    let output = vec![typed_column("value", SqlType::text())];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::Values {
                rows: vec![Vec::new()],
                output: Vec::new(),
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "||".to_owned(),
                op: ScalarOp::StringConcat,
                args: vec![
                    ScalarAst::Literal {
                        raw: "'a'".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "'b'".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "'c'".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "string_concat_arity_not_supported")
    );
}

#[test]
fn rejects_unbounded_text_concat_without_losing_postgres_size_error() {
    let input = vec![typed_column("body", SqlType::text())];
    let query = Query {
        source_sql: Some("SELECT body || body FROM t".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "||".to_owned(),
                op: ScalarOp::StringConcat,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("EXPR$0", SqlType::text())],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "string_concat_size_not_provably_total" })
    );
}

#[test]
fn lowers_exact_literal_like_prefix_in_predicate_and_case_contexts() {
    let input = vec![typed_column("kind", SqlType::varchar(Some(25)))];
    let like = || ScalarAst::Call {
        operator: "LIKE".to_owned(),
        op: ScalarOp::Like,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Literal {
                raw: "'PROMO%'".to_owned(),
            },
        ],
    };
    let filtered = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["part".to_owned()],
                output: input.clone(),
            }),
            predicate: scalar(like()),
            correlations: Vec::new(),
            output: input.clone(),
        },
        analysis_errors: vec![],
    };
    let projected = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["part".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    like(),
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "0".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![column("is_promo")],
        },
        analysis_errors: vec![],
    };

    let filtered = lower_query(&filtered);
    let projected = lower_query(&projected);
    assert_eq!(filtered.status, LoweringStatus::Lowered, "{filtered:#?}");
    assert_eq!(projected.status, LoweringStatus::Lowered, "{projected:#?}");
    let filter_module = emit_rocq_query_module(
        filtered.query_expr.as_ref().expect("filter query"),
        filtered.query_expr.as_ref().expect("filter query"),
    );
    let project_module = emit_rocq_query_module(
        projected.query_expr.as_ref().expect("project query"),
        projected.query_expr.as_ref().expect("project query"),
    );
    assert!(filter_module.rocq_module.contains("PredicateLikePrefix"));
    assert!(filter_module.rocq_module.contains("\"PROMO\""));
    assert!(project_module.rocq_module.contains("PredicateLikePrefix"));
}

#[test]
fn lowers_exact_literal_like_percent_patterns() {
    for raw in ["'%pending%accounts%'", "'%Customer%Complaints%'"] {
        let output = vec![typed_column("comment", SqlType::varchar(Some(101)))];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Filter {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["orders".to_owned()],
                    output: output.clone(),
                }),
                predicate: scalar(ScalarAst::Call {
                    operator: "LIKE".to_owned(),
                    op: ScalarOp::Like,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::Literal {
                            raw: raw.to_owned(),
                        },
                    ],
                }),
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{raw}: {lowered:#?}"
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("LIKE query"),
            lowered.query_expr.as_ref().expect("LIKE query"),
        );
        assert!(module.rocq_module.contains("PredicateLikePercent"));
        assert!(module.rocq_module.contains(raw.trim_matches('\'')));
    }
}

#[test]
fn rejects_like_patterns_with_underscore_or_escape_syntax() {
    for raw in ["'PR_MO%'", "'PR\\\\OMO%'"] {
        let output = vec![typed_column("kind", SqlType::varchar(Some(25)))];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Filter {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["part".to_owned()],
                    output: output.clone(),
                }),
                predicate: scalar(ScalarAst::Call {
                    operator: "LIKE".to_owned(),
                    op: ScalarOp::Like,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::Literal {
                            raw: raw.to_owned(),
                        },
                    ],
                }),
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Blocked,
            "{raw}: {lowered:#?}"
        );
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code == "like_pattern_not_supported" })
        );
    }
}

#[test]
fn rejects_like_on_typmodless_bpchar_without_physical_padding() {
    let output = vec![typed_column("value", SqlType::bpchar())];
    let query = Query {
        source_sql: Some("SELECT value LIKE 'a' FROM t".to_owned()),
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "LIKE".to_owned(),
                op: ScalarOp::Like,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "'a'".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "like_typmodless_bpchar_not_supported" })
    );
}

#[test]
fn lowers_bounded_literal_nonnegative_substring_as_text() {
    let integer_literal = |raw: &str| ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: raw.to_owned(),
        }),
        ty: "INTEGER".to_owned(),
    };
    let input = vec![typed_column("zip", SqlType::character(10))];
    let query = Query {
        source_sql: Some("SELECT substring(zip, 1, 5) FROM address".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["address".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "SUBSTRING".to_owned(),
                op: ScalarOp::Substring,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    integer_literal("1"),
                    integer_literal("5"),
                ],
            })],
            correlations: Vec::new(),
            // Calcite reports unconstrained VARCHAR here even though the
            // PostgreSQL character-string substring overload returns text.
            output: vec![typed_column("EXPR$0", SqlType::varchar(None))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert_eq!(
        lowered.output_signature.as_ref().expect("output signature")[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Text,
        }
    );
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_substring_type_overridden" })
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("substring query"),
        lowered.query_expr.as_ref().expect("substring query"),
    );
    assert!(module.rocq_module.contains("ScalarSubstringNonnegative"));
    assert!(
        module
            .rocq_module
            .contains("DotString \"zip\" (StringChar 10)")
    );
    assert!(module.rocq_module.contains("CstInt32 (1)"));
    assert!(module.rocq_module.contains("CstInt32 (5)"));
}

#[test]
fn rejects_substring_outside_bounded_literal_nonnegative_subset() {
    let integer_literal = |raw: &str| ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: raw.to_owned(),
        }),
        ty: "INTEGER".to_owned(),
    };
    for (input_ty, start, count, expected_code) in [
        (
            SqlType::text(),
            integer_literal("1"),
            integer_literal("5"),
            "substring_operand_type_not_supported",
        ),
        (
            SqlType::character(10),
            integer_literal("0"),
            integer_literal("5"),
            "substring_start_not_supported",
        ),
        (
            SqlType::character(10),
            integer_literal("1"),
            integer_literal("-1"),
            "substring_count_not_supported",
        ),
        (
            SqlType::character(10),
            ScalarAst::InputRef { index: 1 },
            integer_literal("5"),
            "substring_start_not_supported",
        ),
    ] {
        let input = vec![
            typed_column("value", input_ty),
            typed_column("dynamic_start", SqlType::Integer),
        ];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: input,
                }),
                exprs: vec![scalar(ScalarAst::Call {
                    operator: "SUBSTRING".to_owned(),
                    op: ScalarOp::Substring,
                    args: vec![ScalarAst::InputRef { index: 0 }, start, count],
                })],
                correlations: Vec::new(),
                output: vec![typed_column("EXPR$0", SqlType::text())],
            },
            analysis_errors: vec![],
        };
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == expected_code),
            "{lowered:#?}"
        );
    }
}

#[test]
fn rejects_nonstring_operand_for_modeled_concat() {
    let query = Query {
        source_sql: Some("SELECT 'prefix:' || id FROM t".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("id", SqlType::Integer)],
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "||".to_owned(),
                op: ScalarOp::StringConcat,
                args: vec![
                    ScalarAst::Literal {
                        raw: "'prefix:'".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("EXPR$0", SqlType::varchar(None))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "string_concat_operand_type_not_supported")
    );
}

#[test]
fn lowers_schema_to_formal_sql_create_table_shape() {
    let schema = Schema {
        tables: vec![Table {
            name: "EMP".to_owned(),
            columns: vec![
                typed_column("EMPNO", SqlType::Integer),
                typed_column("ENAME", SqlType::varchar(None)),
                typed_column("SLACKER", SqlType::Boolean),
                typed_column("HIREDATE", SqlType::Date),
                decimal_column("BONUS", 10, 2),
                typed_column("SHIFT_START", SqlType::Time),
                timestamp_column("EVENT_TS", Some(6)),
            ],
            constraints: Default::default(),
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
            .rocq_module
            .contains("create_table")
    );
    assert!(
            lowered
                .schema
                .as_ref()
                .unwrap()
                .rocq_module
                .contains("Attr_int32 \"EMPNO\" :: Attr_string \"ENAME\" StringVarchar :: Attr_bool \"SLACKER\" :: Attr_date \"HIREDATE\" :: Attr_decimal \"BONUS\" 10 2 :: Attr_time \"SHIFT_START\" :: Attr_timestamp \"EVENT_TS\" 6 :: nil")
    );
    assert!(lowered.schema.as_ref().unwrap().rocq_module.starts_with(
        "From SQLFS Require Import SqlSyntax GenericInstance ValueCore ValueInteger ValueString Formula SchemaConstraints.\n"
    ));
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
fn lowers_typed_table_constraints_and_emits_every_table_in_schema_order() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "orders".to_owned(),
                columns: vec![
                    typed_column("tenant", SqlType::Integer),
                    decimal_column("amount", 12, 2),
                    typed_column("external_id", SqlType::text()),
                ],
                constraints: TableConstraints {
                    not_null: vec![
                        "tenant".to_owned(),
                        "amount".to_owned(),
                        "external_id".to_owned(),
                    ],
                    primary_key: Some(vec!["external_id".to_owned(), "tenant".to_owned()]),
                    ..TableConstraints::default()
                },
            },
            Table {
                name: "audit".to_owned(),
                columns: vec![typed_column("payload", SqlType::Integer)],
                constraints: TableConstraints::default(),
            },
        ],
    };

    let lowered = lower_schema_with_config(
        &schema,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::postgres_utf8_c(),
        },
    );
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let formal = lowered.schema.as_ref().expect("formal schema");
    assert_eq!(
        formal.tables[0].constraints.not_null,
        vec![
            FormalAttribute {
                name: "tenant".to_owned(),
                ty: FormalAttributeType::Int32,
            },
            FormalAttribute {
                name: "amount".to_owned(),
                ty: FormalAttributeType::Decimal {
                    precision: 12,
                    scale: 2,
                },
            },
            FormalAttribute {
                name: "external_id".to_owned(),
                ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
            },
        ]
    );
    assert_eq!(
        formal.tables[0].constraints.primary_key.as_ref().unwrap(),
        &vec![
            FormalAttribute {
                name: "external_id".to_owned(),
                ty: FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
            },
            FormalAttribute {
                name: "tenant".to_owned(),
                ty: FormalAttributeType::Int32,
            },
        ],
        "declared primary-key order must be preserved independently of column order"
    );
    assert!(formal.tables[1].constraints.is_empty());

    let constraints_module = formal
        .rocq_module
        .split_once("Definition generated_schema_constraints")
        .expect("generated constraints definition")
        .1;
    assert_eq!(constraints_module.matches("TableConstraint").count(), 2);
    assert!(
        constraints_module.find("(Rel \"orders\")") < constraints_module.find("(Rel \"audit\")"),
        "constraints must remain in schema declaration order"
    );
    assert!(
        constraints_module
            .contains("Attr_string \"external_id\" StringText :: Attr_int32 \"tenant\" :: nil")
    );
    let audit_constraint = &constraints_module[constraints_module
        .find("(Rel \"audit\")")
        .expect("unconstrained audit table")..];
    assert!(
        audit_constraint.find("(nil)").expect("empty NOT NULL list")
            < audit_constraint.find("(None)").expect("absent primary key"),
        "unconstrained table must emit an empty NOT NULL list and no primary key"
    );
    assert!(formal.rocq_module.contains(
        "database_conforms_schema\n    generated_schema generated_schema_constraints db"
    ));
}

#[test]
fn constraint_formula_emission_uses_the_generic_empty_query_formula_syntax() {
    let column = |name: &str| IntegrityValueExpr::Column {
        name: name.to_owned(),
    };
    let predicate = IntegrityPredicate::And {
        left: Box::new(IntegrityPredicate::IsTrue {
            expression: column("active"),
        }),
        right: Box::new(IntegrityPredicate::Not {
            predicate: Box::new(IntegrityPredicate::Or {
                left: Box::new(IntegrityPredicate::IsNull {
                    expression: column("id"),
                }),
                right: Box::new(IntegrityPredicate::Comparison {
                    comparison: IntegrityComparison::Equal,
                    left: column("id"),
                    right: IntegrityValueExpr::Literal {
                        raw: "1".to_owned(),
                        ty: SqlType::Integer,
                    },
                }),
            }),
        }),
    };
    let schema = Schema {
        tables: vec![Table {
            name: "items".to_owned(),
            columns: vec![
                typed_column("id", SqlType::Integer),
                typed_column("active", SqlType::Boolean),
            ],
            constraints: TableConstraints {
                checks: vec![CheckConstraint {
                    name: Some("items_check".to_owned()),
                    expression: predicate,
                    source_sql: "active IS TRUE AND NOT (id IS NULL OR id = 1)".to_owned(),
                }],
                ..TableConstraints::default()
            },
        }],
    };

    let lowered = lower_schema(&schema);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let module = &lowered.schema.expect("formal schema").rocq_module;
    for constructor in [
        "@Sql_Conj TNull constraint_query And_F",
        "@Sql_Conj TNull constraint_query Or_F",
        "@Sql_Not TNull constraint_query",
        "@Sql_Pred TNull constraint_query",
    ] {
        assert!(
            module.contains(constructor),
            "missing {constructor}:\n{module}"
        );
    }
    assert!(!module.contains("TrueFormula"));
    assert!(!module.contains("Some (Pred "));
    assert!(!module.contains("CheckConstraint (Pred "));
}

#[test]
fn string_integrity_equality_requires_the_exact_postgres_c_environment() {
    let schema = Schema {
        tables: vec![Table {
            name: "keys".to_owned(),
            columns: vec![typed_column("value", SqlType::text())],
            constraints: TableConstraints {
                not_null: vec!["value".to_owned()],
                primary_key: Some(vec!["value".to_owned()]),
                ..TableConstraints::default()
            },
        }],
    };
    let blocked = lower_schema(&schema);
    assert_eq!(blocked.status, LoweringStatus::Blocked, "{blocked:#?}");
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "integrity_text_environment_not_attested" })
    );

    let lowered = lower_schema_with_config(
        &schema,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::postgres_utf8_c(),
        },
    );
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
}

#[test]
fn schema_lowering_rejects_heterogeneous_string_foreign_keys() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "parent".to_owned(),
                columns: vec![typed_column(
                    "id",
                    SqlType::String(SqlStringType::Char { length: 4 }),
                )],
                constraints: TableConstraints {
                    not_null: vec!["id".to_owned()],
                    primary_key: Some(vec!["id".to_owned()]),
                    ..TableConstraints::default()
                },
            },
            Table {
                name: "child".to_owned(),
                columns: vec![typed_column("id", SqlType::text())],
                constraints: TableConstraints {
                    foreign_keys: vec![ForeignKeyConstraint {
                        name: None,
                        columns: vec!["id".to_owned()],
                        referenced_table: "parent".to_owned(),
                        referenced_columns: vec!["id".to_owned()],
                        match_type: ForeignKeyMatch::Simple,
                        referential_actions: None,
                    }],
                    ..TableConstraints::default()
                },
            },
        ],
    };

    let lowered = lower_schema_with_config(
        &schema,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::postgres_utf8_c(),
        },
    );
    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "foreign_key_equality_not_supported" })
    );
}

#[test]
fn schema_lowering_rejects_varchar_pattern_ops_for_character() {
    let schema = Schema {
        tables: vec![Table {
            name: "items".to_owned(),
            columns: vec![typed_column(
                "code",
                SqlType::String(SqlStringType::Char { length: 4 }),
            )],
            constraints: TableConstraints {
                unique_indexes: vec![UniqueIndexConstraint {
                    name: None,
                    terms: vec![UniqueIndexTerm {
                        expression: IntegrityValueExpr::Column {
                            name: "code".to_owned(),
                        },
                        source_sql: "code varchar_pattern_ops".to_owned(),
                        direction: IntegritySortDirection::Asc,
                        nulls: None,
                        operator_class: Some("varchar_pattern_ops".to_owned()),
                    }],
                    predicate: None,
                    predicate_sql: None,
                }],
                ..TableConstraints::default()
            },
        }],
    };

    let lowered = lower_schema_with_config(
        &schema,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::postgres_utf8_c(),
        },
    );
    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "unique_index_operator_class_not_supported" })
    );
}

#[test]
fn schema_constraint_lowering_revalidates_malformed_typed_ir() {
    let cases = [
        (
            "unknown-not-null",
            TableConstraints {
                not_null: vec!["missing".to_owned()],
                primary_key: None,
                ..TableConstraints::default()
            },
            "unknown_not_null_constraint_attribute",
        ),
        (
            "duplicate-not-null",
            TableConstraints {
                not_null: vec!["a".to_owned(), "a".to_owned()],
                primary_key: None,
                ..TableConstraints::default()
            },
            "duplicate_not_null_constraint_attribute",
        ),
        (
            "not-null-order",
            TableConstraints {
                not_null: vec!["b".to_owned(), "a".to_owned()],
                primary_key: None,
                ..TableConstraints::default()
            },
            "not_null_constraint_declaration_order",
        ),
        (
            "empty-primary-key",
            TableConstraints {
                not_null: vec!["a".to_owned()],
                primary_key: Some(Vec::new()),
                ..TableConstraints::default()
            },
            "empty_primary_key_constraint",
        ),
        (
            "unknown-primary-key",
            TableConstraints {
                not_null: vec!["a".to_owned()],
                primary_key: Some(vec!["missing".to_owned()]),
                ..TableConstraints::default()
            },
            "unknown_primary_key_constraint_attribute",
        ),
        (
            "duplicate-primary-key",
            TableConstraints {
                not_null: vec!["a".to_owned()],
                primary_key: Some(vec!["a".to_owned(), "a".to_owned()]),
                ..TableConstraints::default()
            },
            "duplicate_primary_key_constraint_attribute",
        ),
        (
            "primary-key-not-not-null",
            TableConstraints {
                not_null: vec!["a".to_owned()],
                primary_key: Some(vec!["b".to_owned()]),
                ..TableConstraints::default()
            },
            "primary_key_constraint_not_not_null",
        ),
    ];

    for (label, constraints, expected_code) in cases {
        let lowered = lower_schema(&Schema {
            tables: vec![Table {
                name: "t".to_owned(),
                columns: vec![
                    typed_column("a", SqlType::Integer),
                    typed_column("b", SqlType::Integer),
                ],
                constraints,
            }],
        });
        assert_eq!(
            lowered.status,
            LoweringStatus::Blocked,
            "{label}: {lowered:#?}"
        );
        assert!(lowered.schema.is_none(), "{label}: {lowered:#?}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == expected_code),
            "{label}: {lowered:#?}"
        );
    }
}

#[test]
fn schema_constraints_never_infer_from_calcite_column_nullability() {
    let mut column = typed_column("a", SqlType::Integer);
    column.nullable = false;
    let lowered = lower_schema(&Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: vec![column],
            constraints: TableConstraints::default(),
        }],
    });

    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
    assert!(
        lowered.schema.as_ref().unwrap().tables[0]
            .constraints
            .is_empty()
    );
}

#[test]
fn formal_table_constraint_serialization_omits_empty_constraints_and_preserves_key_order() {
    let unconstrained = FormalTable {
        relation: "t".to_owned(),
        attributes: Vec::new(),
        constraints: FormalTableConstraints {
            not_null: Vec::new(),
            primary_key: None,
            ..FormalTableConstraints::default()
        },
    };
    assert_eq!(
        serde_json::to_value(&unconstrained).expect("serialize unconstrained FormalTable"),
        serde_json::json!({
            "relation": "t",
            "attributes": []
        }),
        "empty constraints must remain omitted from reports"
    );

    let id = FormalAttribute {
        name: "id".to_owned(),
        ty: FormalAttributeType::Int32,
    };
    let tenant = FormalAttribute {
        name: "tenant".to_owned(),
        ty: FormalAttributeType::Int64,
    };
    let constrained = FormalTable {
        relation: "typed".to_owned(),
        attributes: vec![id.clone(), tenant.clone()],
        constraints: FormalTableConstraints {
            not_null: vec![id.clone(), tenant.clone()],
            primary_key: Some(vec![tenant, id]),
            ..FormalTableConstraints::default()
        },
    };
    let encoded = serde_json::to_value(&constrained).expect("serialize constrained FormalTable");
    assert_eq!(
        encoded
            .pointer("/constraints/primaryKey/0/name")
            .and_then(serde_json::Value::as_str),
        Some("tenant")
    );
}

#[test]
#[ignore = "requires the repository Rocq switch and compiled FormalSQL/Logos objects"]
fn emitted_constrained_schema_module_compiles() {
    let lowered = lower_schema(&Schema {
        tables: vec![Table {
            name: "typed_keys".to_owned(),
            columns: vec![
                typed_column("tenant", SqlType::Integer),
                typed_column("id", SqlType::Integer),
                typed_column("payload", SqlType::text()),
            ],
            constraints: TableConstraints {
                not_null: vec!["tenant".to_owned(), "id".to_owned()],
                primary_key: Some(vec!["id".to_owned(), "tenant".to_owned()]),
                ..TableConstraints::default()
            },
        }],
    });
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");

    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("workspace root");
    let switch = repo.join(".opam-rocq/_opam");
    let rocq = switch.join("bin/rocq");
    assert!(
        rocq.is_file(),
        "repository Rocq switch is required for this ignored regression"
    );
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-schema-constraints-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&temp);
    fs::create_dir_all(&temp).unwrap();
    let module_path = temp.join("Schema.v");
    fs::write(&module_path, &lowered.schema.as_ref().unwrap().rocq_module).unwrap();
    let rocqlib = switch.join("lib/coq");
    let output = Command::new(rocq)
        .arg("compile")
        .arg("-Q")
        .arg(repo.join("vendor/FormalSQL/src"))
        .arg("SQLFS")
        .arg("-Q")
        .arg(repo.join("theories"))
        .arg("Logos")
        .arg(&module_path)
        .env("ROCQLIB", &rocqlib)
        .env("COQLIB", &rocqlib)
        .env("OCAMLFIND_CONF", switch.join("lib/findlib.conf"))
        .current_dir(&temp)
        .output()
        .unwrap();
    let _ = fs::remove_dir_all(&temp);
    assert!(
        output.status.success(),
        "generated constrained Schema.v failed Rocq compilation: stdout={:?}, stderr={:?}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "requires the repository Rocq switch and compiled FormalSQL/Logos objects"]
fn emitted_unparameterized_query_module_compiles() {
    let lowered_schema = lower_schema(&Schema { tables: Vec::new() });
    assert_eq!(
        lowered_schema.status,
        LoweringStatus::Lowered,
        "{lowered_schema:#?}"
    );
    let query = FormalQueryExpr::EmptyTuple;
    let query_module = emit_rocq_query_module(&query, &query);

    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("workspace root");
    let switch = repo.join(".opam-rocq/_opam");
    let rocq = switch.join("bin/rocq");
    assert!(
        rocq.is_file(),
        "repository Rocq switch is required for this ignored regression"
    );
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-unparameterized-query-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&temp);
    fs::create_dir_all(&temp).unwrap();
    fs::write(
        temp.join("Schema.v"),
        &lowered_schema.schema.as_ref().unwrap().rocq_module,
    )
    .unwrap();
    fs::write(temp.join("Queries.v"), &query_module.rocq_module).unwrap();

    let rocqlib = switch.join("lib/coq");
    for module in ["Schema.v", "Queries.v"] {
        let output = Command::new(&rocq)
            .arg("compile")
            .arg("-Q")
            .arg(repo.join("vendor/FormalSQL/src"))
            .arg("SQLFS")
            .arg("-Q")
            .arg(repo.join("theories"))
            .arg("Logos")
            .arg("-Q")
            .arg(&temp)
            .arg("LogosGenerated")
            .arg(temp.join(module))
            .env("ROCQLIB", &rocqlib)
            .env("COQLIB", &rocqlib)
            .env("OCAMLFIND_CONF", switch.join("lib/findlib.conf"))
            .current_dir(&temp)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "generated {module} failed Rocq compilation: stdout={:?}, stderr={:?}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(&temp).unwrap();
}

#[test]
fn lowers_all_postgres_string_typmods_into_one_string_domain() {
    let schema = Schema {
        tables: vec![Table {
            name: "strings".to_owned(),
            columns: vec![
                typed_column("body", SqlType::text()),
                typed_column("free", SqlType::varchar(None)),
                typed_column("limited", SqlType::varchar(Some(12))),
                typed_column("fixed", SqlType::character(8)),
            ],
            constraints: Default::default(),
        }],
    };

    let lowered = lower_schema(&schema);
    let rocq = &lowered
        .schema
        .as_ref()
        .expect("schema should lower")
        .rocq_module;

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(rocq.contains("Attr_string \"body\" StringText"));
    assert!(rocq.contains("Attr_string \"free\" StringVarchar"));
    assert!(rocq.contains("Attr_string \"limited\" (StringVarcharN 12)"));
    assert!(rocq.contains("Attr_string \"fixed\" (StringChar 8)"));
}

#[test]
fn lowers_time_schema_attribute() {
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: vec![typed_column("clock_time", SqlType::Time)],
            constraints: Default::default(),
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .schema
            .as_ref()
            .unwrap()
            .rocq_module
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AttrTime \"clock_time\""));
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
        analysis_errors: vec![],
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
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "'25:00:00'".to_owned(),
            })]],
            output: output.clone(),
        },
        analysis_errors: vec![],
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
fn resolves_mixed_numeric_case_to_typmodless_numeric() {
    let input = vec![
        typed_column("flag", SqlType::Boolean),
        decimal_column("amount", 15, 2),
    ];
    let output = vec![decimal_column_unconstrained("result")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Call {
                        operator: "+".to_owned(),
                        op: ScalarOp::Plus,
                        args: vec![
                            ScalarAst::InputRef { index: 1 },
                            ScalarAst::TypeAnnotation {
                                expr: Box::new(ScalarAst::Literal {
                                    raw: "1".to_owned(),
                                }),
                                ty: "INTEGER".to_owned(),
                            },
                        ],
                    },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "0.00".to_owned(),
                        }),
                        ty: "DECIMAL(15, 2)".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("expected projection");
    };
    assert_eq!(select[0].alias_ty, FormalAttributeType::Numeric);
    assert!(matches!(
        &select[0].expr,
        FormalScalarExpr::Case {
            result_ty: FormalAttributeType::Numeric,
            else_expr,
            ..
        } if matches!(else_expr.as_ref(),
            FormalScalarExpr::Leaf {
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        ty: Some(FormalAttributeType::Numeric),
                        ..
                    }
                },
                ..
            })
    ));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarAdd ScalarNumeric"));
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumeric ScalarSourceInt32)")
    );
}

#[test]
fn numeric_case_does_not_trust_null_or_literal_derived_typmods() {
    let make_query = |else_expr: ScalarAst| {
        let input = vec![
            typed_column("flag", SqlType::Boolean),
            decimal_column("amount", 5, 2),
        ];
        let output = vec![decimal_column_unconstrained("result")];
        Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: input,
                }),
                exprs: vec![scalar(ScalarAst::Call {
                    operator: "CASE".to_owned(),
                    op: ScalarOp::Case,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::InputRef { index: 1 },
                        else_expr,
                    ],
                })],
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        }
    };
    let derived_null = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: "NULL".to_owned(),
        }),
        ty: "DECIMAL(5, 2)".to_owned(),
    };
    let derived_integer = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: "0.00".to_owned(),
        }),
        ty: "DECIMAL(5, 2)".to_owned(),
    };

    for query in [make_query(derived_null), make_query(derived_integer)] {
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{:#?}",
            lowered.diagnostics
        );
        let Some(FormalQueryExpr::Projection { select, .. }) = lowered.query_expr.as_ref() else {
            panic!("expected projection");
        };
        assert_eq!(select[0].alias_ty, FormalAttributeType::Numeric);
    }
}

#[test]
fn rejects_decimal_schema_with_zero_precision() {
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: vec![typed_column(
                "amount",
                SqlType::Decimal {
                    precision: Some(0),
                    scale: Some(0),
                },
            )],
            constraints: Default::default(),
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("decimal query should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("decimal query should lower"),
    );
    assert!(module.rocq_module.contains("ScalarAdd ScalarNumeric"));
    assert!(module.rocq_module.contains("CstDecimal (10) (2) (125)"));
    assert!(module.rocq_module.contains("AttrNumeric \"amount_plus\""));
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_numeric_type_overridden" })
    );
}

#[test]
fn overrides_calcite_decimal_arithmetic_output_typmod_mismatch() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_numeric_type_overridden")
    );
    assert_eq!(
        lowered.output_signature,
        Some(vec![FormalAttribute {
            name: "amount_plus".to_owned(),
            ty: FormalAttributeType::Numeric,
        }])
    );
}

#[test]
fn schema_bound_numeric_operator_results_discard_calcite_typmods() {
    let input = vec![decimal_column("amount", 10, 2)];
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: input.clone(),
            constraints: Default::default(),
        }],
    };
    let operators = [
        (ScalarOp::Plus, "+", 2usize),
        (ScalarOp::Minus, "-", 2usize),
        (ScalarOp::Multiply, "*", 2usize),
        (ScalarOp::Minus, "-", 1usize),
    ];

    for (op, operator, arity) in operators {
        let args = if arity == 1 {
            vec![ScalarAst::InputRef { index: 0 }]
        } else {
            vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 0 },
            ]
        };
        let expression = ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: operator.to_owned(),
                op: op.clone(),
                args,
            }),
            ty: "DECIMAL(20, 4)".to_owned(),
        };
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: input.clone(),
                }),
                exprs: vec![scalar(expression)],
                correlations: Vec::new(),
                output: vec![decimal_column("result", 20, 4)],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "operator {op:?}: {:?}",
            lowered.diagnostics
        );
        assert_eq!(
            lowered.output_signature,
            Some(vec![FormalAttribute {
                name: "result".to_owned(),
                ty: FormalAttributeType::Numeric,
            }]),
            "operator {op:?}"
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("operator should lower"),
            lowered.query_expr.as_ref().expect("operator should lower"),
        );
        assert!(
            module.rocq_module.contains("AttrNumeric \"result\""),
            "operator {op:?}"
        );
        assert!(
            !module.rocq_module.contains("AttrDecimal \"result\""),
            "operator {op:?}"
        );
    }
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("decimal query should lower"),
        lowered
            .query_expr
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "numeric_literal_not_supported")
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstDecimal (10) (0) (1)"));
}

#[test]
fn rejects_negative_scale_and_malformed_tail_decimal_annotations() {
    for annotation in ["DECIMAL(10, -2)", "DECIMAL(10, 2) trailing"] {
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
                    ty: annotation.to_owned(),
                })],
                correlations: Vec::new(),
                output: vec![decimal_column("amount", 10, 2)],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);

        assert_eq!(lowered.status, LoweringStatus::Blocked, "{annotation}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "decimal_typmod_not_supported"),
            "{annotation}"
        );
    }
}

#[test]
fn overrides_calcite_decimal_output_for_unconstrained_numeric_literal() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_numeric_type_overridden")
    );
}

#[test]
fn rejects_numeric_nan_and_infinity_literals() {
    for raw in ["NaN", "Infinity", "-Infinity"] {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: vec![column("id")],
                }),
                exprs: vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: "NUMERIC".to_owned(),
                })],
                correlations: Vec::new(),
                output: vec![decimal_column_unconstrained("amount")],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked, "literal: {raw}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code == "numeric_literal_not_supported" })
        );
    }
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
        analysis_errors: vec![],
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
        analysis_errors: vec![],
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
fn enforces_postgres_unconstrained_numeric_literal_limits() {
    let largest_integer = "9".repeat(131_072);
    let oversized_integer = format!("1{}", "0".repeat(131_072));
    let largest_fraction = format!("0.{}1", "0".repeat(16_382));
    let oversized_fraction = format!("0.{}1", "0".repeat(16_383));

    assert!(super::emit::numeric_literal_fits_postgres_runtime(
        &largest_integer
    ));
    assert!(!super::emit::numeric_literal_fits_postgres_runtime(
        &oversized_integer
    ));
    assert!(super::emit::numeric_literal_fits_postgres_runtime(
        &largest_fraction
    ));
    assert!(!super::emit::numeric_literal_fits_postgres_runtime(
        &oversized_fraction
    ));
}

#[test]
fn enforces_postgres_temporal_literal_ranges() {
    assert!(super::emit::date_literal_conforms_to_day("-2440588"));
    assert!(!super::emit::date_literal_conforms_to_day("-2440589"));
    assert!(super::emit::date_literal_conforms_to_day("2145042905"));
    assert!(!super::emit::date_literal_conforms_to_day("2145042906"));

    assert!(super::emit::timestamp_literal_conforms_to_precision(
        "-210866803200000000",
        6
    ));
    assert!(!super::emit::timestamp_literal_conforms_to_precision(
        "-210866803200000001",
        6
    ));
    assert!(!super::emit::timestamp_literal_conforms_to_precision(
        "294276-12-31 23:59:59",
        6
    ));
    assert!(!super::emit::timestamp_literal_conforms_to_precision(
        "1970-01-01 00:00:00",
        7
    ));

    assert_eq!(
        super::emit::parse_source_date_cast_literal("'2002-6-01'"),
        Some(11_839)
    );
    assert!(super::emit::parse_source_date_cast_literal("'8766'").is_none());
    assert!(super::emit::parse_source_date_cast_literal("'01-02-03'").is_none());
    assert!(super::emit::parse_source_time_cast_literal("'100'").is_none());
    assert!(super::emit::parse_source_timestamp_cast_literal("'100'", 6).is_none());
    assert!(super::emit::parse_source_timestamp_cast_literal("'01-02-03 04:05:06'", 6).is_none());
}

#[test]
fn retained_timestamp_source_cast_routes_through_datestyle_guard() {
    let output = vec![timestamp_column("ts", Some(6))];
    let query = |raw: &str| Query {
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
                    args: vec![ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: raw.to_owned(),
                        }),
                        ty: "TEXT".to_owned(),
                    }],
                }),
                ty: "TIMESTAMP(6)".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let exact = lower_query(&query("'1970-01-01 00:00:00'"));
    assert_eq!(
        exact.status,
        LoweringStatus::Lowered,
        "{:?}",
        exact.diagnostics
    );

    for raw in ["'01-02-03 00:00:00'", "'null'"] {
        let blocked = lower_query(&query(raw));
        assert_eq!(blocked.status, LoweringStatus::Blocked, "{raw}");
        assert!(
            blocked.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "temporal_source_cast_literal_not_supported"
            })
        );
    }

    let sql_null = lower_query(&query("NULL"));
    assert_eq!(sql_null.status, LoweringStatus::Lowered);
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("decimal query should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("decimal query should lower"),
    );
    assert!(module.rocq_module.contains("ScalarAdd ScalarNumeric"));
    assert!(module.rocq_module.contains("ScalarMultiply ScalarNumeric"));
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumericTypmod ScalarSourceNumeric)")
    );
    assert!(module.rocq_module.contains("CstZ (12)"));
    assert!(module.rocq_module.contains("CstZ (2)"));
}

#[test]
fn lowers_preserved_source_numeric_literal_cast() {
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
                    args: vec![ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1.235".to_owned(),
                        }),
                        ty: "NUMERIC".to_owned(),
                    }],
                }),
                ty: "DECIMAL(4, 2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 4, 2)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumericTypmod ScalarSourceNumeric)")
    );
}

#[test]
fn lowers_numeric_typmod_cast_with_possible_runtime_overflow() {
    let input = vec![decimal_column("amount", 2, 4)];
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
                ty: "DECIMAL(2, 5)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_cast", 2, 5)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity != DiagnosticSeverity::Error)
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumericTypmod ScalarSourceNumeric)")
    );
    let proof = emit_rocq_query_expr_proof_module();
    assert!(
        proof
            .rocq_module
            .contains("NullValues.interp_scalar_operator_runtime_error")
    );
    assert!(proof.rocq_module.contains("generated_query_program_equiv"));
}

#[test]
fn rejects_literal_numeric_typmod_cast_that_is_already_out_of_range() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(one_row_values(Vec::new(), Vec::new())),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1000".to_owned(),
                        }),
                        ty: "NUMERIC".to_owned(),
                    }],
                }),
                ty: "DECIMAL(2, 0)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 2, 0)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "numeric_cast_literal_overflow")
    );
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
            output: vec![decimal_column("amount_numeric", 12, 2)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumericTypmod ScalarSourceInt32)")
    );
    assert!(module.rocq_module.contains("CstZ (12)"));
    assert!(module.rocq_module.contains("CstZ (2)"));
}

#[test]
fn infers_integer_cast_source_from_nonconstant_case_division() {
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
        analysis_errors: vec![],
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
        analysis_errors: vec![],
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
fn infers_integral_power_arguments_as_postgres_double_overload() {
    let input = vec![
        typed_column("base", SqlType::BigInt),
        typed_column("exponent", SqlType::BigInt),
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
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Call {
                        operator: "POWER".to_owned(),
                        op: ScalarOp::Power,
                        args: vec![
                            ScalarAst::InputRef { index: 0 },
                            ScalarAst::InputRef { index: 1 },
                        ],
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![column("powered_amount")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "cast_not_supported" && diagnostic.message.contains("Double to Int32")
    }));
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_source_expression_not_supported")
    );
}

#[test]
fn lowers_postgres_numeric_power_half_of_int64_directly_to_checked_int32() {
    let input = vec![typed_column("amount", SqlType::BigInt)];
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
                                    raw: "0.5".to_owned(),
                                }),
                                ty: "NUMERIC".to_owned(),
                            },
                        ],
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![column("powered_amount")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("ScalarPowerHalfInt64ToInt32"));
}

#[test]
fn rejects_general_postgres_numeric_power() {
    let input = vec![typed_column("amount", SqlType::BigInt)];
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
                                    raw: "0.6".to_owned(),
                                }),
                                ty: "DECIMAL(2,1)".to_owned(),
                            },
                        ],
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![column("powered_amount")],
        },
        analysis_errors: vec![],
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
fn lowers_checked_explicit_numeric_to_integer_cast() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![decimal_column_unconstrained("value")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Integer)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastNumericToInt32")
    );
}

#[test]
fn classifies_postgres_numeric_to_integer_rounding_boundaries() {
    for raw in ["2147483647.4", "-2147483648.4", "0.5", "-0.5", ".0000005"] {
        assert_eq!(
            super::scalar::numeric_literal_rounds_to_int32(raw),
            Some(true),
            "{raw} should round into int4"
        );
    }
    for raw in ["2147483647.5", "-2147483648.5"] {
        assert_eq!(
            super::scalar::numeric_literal_rounds_to_int32(raw),
            Some(false),
            "{raw} should round outside int4"
        );
    }
    let very_large = "9".repeat(200);
    assert_eq!(
        super::scalar::numeric_literal_rounds_to_int32(&very_large),
        Some(false)
    );
    assert_eq!(super::scalar::numeric_literal_rounds_to_int32("NaN"), None);
}

fn wrapped_constant_numeric_to_int32_overflow() -> ScalarAst {
    ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "9223372036854775807".to_owned(),
                        }),
                        ty: "BIGINT".to_owned(),
                    }],
                }),
                ty: "NUMERIC".to_owned(),
            }],
        }),
        ty: "INTEGER".to_owned(),
    }
}

#[test]
fn boolean_subquery_projection_rejects_wrapped_constant_planner_error() {
    let input_output = vec![column("seed")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::Values {
                rows: vec![vec![scalar(ScalarAst::Literal {
                    raw: "1".to_owned(),
                })]],
                output: input_output,
            }),
            exprs: vec![
                scalar(wrapped_constant_numeric_to_int32_overflow()),
                scalar(ScalarAst::Call {
                    operator: "EXISTS".to_owned(),
                    op: ScalarOp::Exists,
                    args: vec![ScalarAst::RelSubquery {
                        rel: Box::new(one_row_values(Vec::new(), Vec::new())),
                    }],
                }),
            ],
            correlations: Vec::new(),
            output: vec![
                typed_column("value", SqlType::Integer),
                typed_column("exists_value", SqlType::Boolean),
            ],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "boolean_planner_constant_error_not_supported"
        })
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
        analysis_errors: vec![],
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
fn poisons_invalid_string_literal_integer_cast_before_scalar_lowering() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| diagnostic.code
            == "invalid_int4_unknown_literal_analysis_error_not_attested")
    );
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_source_type_not_supported")
    );
}

#[test]
fn overrides_calcite_fixed_output_for_bare_decimal_division() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_numeric_type_overridden")
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("AttrNumeric \"ratio\""));
    assert!(!module.rocq_module.contains("AttrDecimal \"ratio\""));
}

#[test]
fn inferred_decimal_division_annotation_remains_unconstrained_numeric() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_numeric_type_overridden")
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("AttrNumeric \"ratio\""));
}

#[test]
fn lowers_dynamic_decimal_division_to_runtime_checked_operator() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity != DiagnosticSeverity::Error)
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("AttrNumeric \"ratio\""));
    let proof = emit_rocq_query_expr_proof_module();
    assert!(
        proof
            .rocq_module
            .contains("NullValues.interp_scalar_operator_runtime_error")
    );
    assert!(proof.rocq_module.contains("generated_query_program_equiv"));
}

#[test]
fn lowers_decimal_division_when_divisor_rounds_to_zero_as_runtime_error() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity != DiagnosticSeverity::Error)
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
}

#[test]
fn lowers_implicit_integral_to_numeric_arithmetic() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "decimal_mixed_arithmetic_not_supported")
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumeric ScalarSourceInt32")
    );
    assert!(module.rocq_module.contains("ScalarAdd ScalarNumeric"));
}

#[test]
fn lowers_bigint_numeric_division_in_aggregate_and_function_paths() {
    let project_output = vec![decimal_column_unconstrained("ratio")];
    let project = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![
                    typed_column("quantity", SqlType::BigInt),
                    decimal_column("factor", 10, 2),
                ],
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: project_output.clone(),
        },
        analysis_errors: vec![],
    };
    let lowered = lower_query(&project);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let module = emit_rocq_query_module_for_test(&project);
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumeric ScalarSourceInt64")
    );
    assert!(module.rocq_module.contains("CstZ (0)"));

    let scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "quantity".to_owned(),
                visible_name: "quantity".to_owned(),
                formal_ty: FormalAttributeType::Int64,
                numeric_dscale: Some(NumericDscaleProvenance::Exact(0)),
            },
            ScopeAttribute {
                name: "factor".to_owned(),
                visible_name: "factor".to_owned(),
                formal_ty: FormalAttributeType::Decimal {
                    precision: 10,
                    scale: 2,
                },
                numeric_dscale: Some(NumericDscaleProvenance::Exact(2)),
            },
        ],
    };
    let ast = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::InputRef { index: 1 },
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    let term = context
        .lower_function_term("functionDivision", &ast, &scope)
        .expect("function term");
    let FormalFunctionTerm::ScalarCall { operator, args } = term else {
        panic!("expected function division");
    };
    assert_eq!(operator, ScalarOperator::Divide(ScalarNumericKind::Numeric));
    assert!(matches!(
        &args[0],
        FormalFunctionTerm::ScalarCall {
            operator: ScalarOperator::Cast(ScalarCast::ToNumeric(ScalarNumericSource::Int64)),
            ..
        }
    ));
    assert!(matches!(
        &args[1],
        FormalFunctionTerm::Constant { raw, ty: Some(FormalAttributeType::Z) } if raw == "0"
    ));
}

#[test]
fn lowers_nested_numeric_division_with_runtime_result_dscale() {
    let numeric_sum = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![
            ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            },
            ScalarAst::InputRef { index: 2 },
        ],
    };
    let average = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            numeric_sum,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "3".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            },
        ],
    };
    let ratio = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![ScalarAst::InputRef { index: 0 }, average],
    };
    let output = vec![decimal_column_unconstrained("ratio")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![
                    decimal_column("a", 7, 2),
                    decimal_column("b", 7, 2),
                    decimal_column("c", 7, 2),
                ],
            }),
            exprs: vec![scalar(ratio)],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "numeric_display_scale_not_available"),
        "{lowered:#?}"
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert_eq!(
        module
            .rocq_module
            .matches("ScalarDivide ScalarNumeric")
            .count(),
        2
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarNumericDivideResultScale")
    );
    assert!(module.rocq_module.contains("CstZ (2)"));
    assert!(module.rocq_module.contains("CstZ (0)"));
}

#[test]
fn integral_division_result_has_zero_dscale_when_coerced_to_numeric() {
    let total = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![
            ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            },
            ScalarAst::InputRef { index: 2 },
        ],
    };
    let integral_ratio = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![ScalarAst::InputRef { index: 0 }, total],
    };
    let numeric_ratio = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            integral_ratio,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "3.0".to_owned(),
                }),
                ty: "NUMERIC".to_owned(),
            },
        ],
    };
    let percentage = ScalarAst::Call {
        operator: "*".to_owned(),
        op: ScalarOp::Multiply,
        args: vec![
            numeric_ratio,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "100".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            },
        ],
    };
    let output = vec![decimal_column_unconstrained("percentage")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![
                    typed_column("a", SqlType::BigInt),
                    typed_column("b", SqlType::BigInt),
                    typed_column("c", SqlType::BigInt),
                ],
            }),
            exprs: vec![scalar(percentage)],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt64"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("ScalarMultiply ScalarNumeric"));
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumeric ScalarSourceInt64")
    );
    assert!(module.rocq_module.contains("CstZ (0)"));
    assert!(module.rocq_module.contains("CstZ (1)"));
    assert!(
        !module
            .rocq_module
            .contains("ScalarNumericDivideResultScale")
    );
}

#[test]
fn numeric_dscale_reconstructs_integral_numeric_literals_and_combines_zero_only_in_case() {
    fn numeric_literal(raw: &str) -> ScalarAst {
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: raw.to_owned(),
            }),
            ty: "NUMERIC".to_owned(),
        }
    }

    fn int32_to_numeric(raw: &str) -> ScalarAst {
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                }],
            }),
            ty: "NUMERIC".to_owned(),
        }
    }

    fn searched_case(then_expr: ScalarAst, else_expr: ScalarAst) -> ScalarAst {
        ScalarAst::Call {
            operator: "CASE".to_owned(),
            op: ScalarOp::Case,
            args: vec![
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "false".to_owned(),
                    }),
                    ty: "BOOLEAN".to_owned(),
                },
                then_expr,
                else_expr,
            ],
        }
    }

    let scope = Scope {
        attributes: Vec::new(),
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);

    let zero = int32_to_numeric("0");
    assert_eq!(
        context.infer_numeric_dscale(&zero, &scope),
        Some(NumericDscaleProvenance::Exact(0)),
        "a standalone source int4 zero must not inherit Calcite's DECIMAL scale"
    );

    let large_plus_zero = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![numeric_literal("100000000000000000000"), zero.clone()],
    };
    assert_eq!(
        context.infer_numeric_dscale(&large_plus_zero, &scope),
        Some(NumericDscaleProvenance::Exact(0)),
        "the PostgreSQL (large numeric + 0::numeric) witness must retain scale zero"
    );

    let calcite15 = searched_case(numeric_literal("2.1"), int32_to_numeric("1"));
    assert_eq!(
        context.infer_numeric_dscale(&calcite15, &scope),
        None,
        "a CASE whose possible nonzero branches have scales one and zero cannot use Calcite Exact(1)"
    );

    let zero_case = searched_case(numeric_literal("2.1"), zero);
    assert_eq!(
        context.infer_numeric_dscale(&zero_case, &scope),
        Some(NumericDscaleProvenance::Representative(1)),
        "only the exact CASE combination may abstract a smaller-scale zero branch"
    );

    let decimal_scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "flag".to_owned(),
                visible_name: "flag".to_owned(),
                formal_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "amount".to_owned(),
                visible_name: "amount".to_owned(),
                formal_ty: FormalAttributeType::Decimal {
                    precision: 7,
                    scale: 2,
                },
                numeric_dscale: Some(NumericDscaleProvenance::Exact(2)),
            },
        ],
    };
    let nullable_decimal_case = ScalarAst::Call {
        operator: "CASE".to_owned(),
        op: ScalarOp::Case,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::InputRef { index: 1 },
            ScalarAst::Literal {
                raw: "NULL".to_owned(),
            },
        ],
    };
    assert_eq!(
        context.infer_numeric_dscale(&nullable_decimal_case, &decimal_scope),
        Some(NumericDscaleProvenance::Exact(2)),
        "an untyped NULL arm has no value scale and cannot erase the scale of every observable non-NULL branch"
    );
    let select = context
        .lower_project_select(
            "rel",
            &[scalar(nullable_decimal_case)],
            &[decimal_column("conditional_amount", 7, 2)],
            &decimal_scope,
        )
        .expect("fixed DECIMAL CASE projection");
    assert_eq!(
        select[0].numeric_dscale,
        Some(NumericDscaleProvenance::Exact(2)),
        "the fixed DECIMAL result typmod supplies the CASE display scale"
    );
}

#[test]
fn numeric_dscale_provenance_survives_case_projection_sum_and_outer_division() {
    fn sum(index: usize) -> AggregateCall {
        AggregateCall {
            raw: format!("SUM(${index})"),
            function: "SUM".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index })],
            filter: None,
        }
    }

    fn pipeline(else_expr: ScalarAst) -> Query {
        let product = || ScalarAst::Call {
            operator: "*".to_owned(),
            op: ScalarOp::Multiply,
            args: vec![
                ScalarAst::InputRef { index: 1 },
                ScalarAst::InputRef { index: 1 },
            ],
        };
        let projected = RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![
                    typed_column("flag", SqlType::Boolean),
                    decimal_column("amount", 10, 2),
                ],
            }),
            exprs: vec![
                scalar(ScalarAst::Call {
                    operator: "CASE".to_owned(),
                    op: ScalarOp::Case,
                    args: vec![ScalarAst::InputRef { index: 0 }, product(), else_expr],
                }),
                scalar(product()),
            ],
            correlations: Vec::new(),
            output: vec![
                decimal_column_unconstrained("conditional_amount"),
                decimal_column_unconstrained("total_amount"),
            ],
        };
        let aggregate = RelExpr::Aggregate {
            input: Box::new(projected),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![sum(0), sum(1)],
            output: vec![
                decimal_column_unconstrained("conditional_sum"),
                decimal_column_unconstrained("total_sum"),
            ],
        };
        let scaled_numerator = ScalarAst::Call {
            operator: "*".to_owned(),
            op: ScalarOp::Multiply,
            args: vec![
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "100.00".to_owned(),
                    }),
                    ty: "DECIMAL(5,2)".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        };
        let output = vec![decimal_column_unconstrained("ratio")];
        Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(aggregate),
                exprs: vec![scalar(ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![scaled_numerator, ScalarAst::InputRef { index: 1 }],
                })],
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        }
    }

    // The converter now retains PostgreSQL's real source path: ELSE 0 starts
    // as int4 and is coerced to typmodless NUMERIC with dscale zero. The CASE
    // combination—not the literal—derives Representative(4), because every
    // possible nonzero product has dscale four and zero has the smaller scale.
    let reconstructed_zero = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "0".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            }],
        }),
        ty: "NUMERIC".to_owned(),
    };
    let dscale_scope = Scope {
        attributes: vec![
            ScopeAttribute {
                name: "flag".to_owned(),
                visible_name: "flag".to_owned(),
                formal_ty: FormalAttributeType::Bool,
                numeric_dscale: None,
            },
            ScopeAttribute {
                name: "amount".to_owned(),
                visible_name: "amount".to_owned(),
                formal_ty: FormalAttributeType::Decimal {
                    precision: 10,
                    scale: 2,
                },
                numeric_dscale: Some(NumericDscaleProvenance::Exact(2)),
            },
        ],
    };
    let case = ScalarAst::Call {
        operator: "CASE".to_owned(),
        op: ScalarOp::Case,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Call {
                operator: "*".to_owned(),
                op: ScalarOp::Multiply,
                args: vec![
                    ScalarAst::InputRef { index: 1 },
                    ScalarAst::InputRef { index: 1 },
                ],
            },
            reconstructed_zero.clone(),
        ],
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    assert_eq!(
        context.infer_numeric_dscale(&case, &dscale_scope),
        Some(NumericDscaleProvenance::Representative(4))
    );

    let lowered = lower_query(&pipeline(reconstructed_zero));
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("CstZ (6)"));
    assert!(module.rocq_module.contains("CstZ (4)"));

    let explicit_scale_three = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.000".to_owned(),
                }),
                ty: "NUMERIC".to_owned(),
            }],
        }),
        ty: "DECIMAL(10,3)".to_owned(),
    };
    let blocked = lower_query(&pipeline(explicit_scale_three));
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "numeric_display_scale_not_available"),
        "{:#?}",
        blocked.diagnostics
    );
}

#[test]
fn lowers_decimal_avg_to_unconstrained_numeric() {
    for precision in [7, 15] {
        let input_output = vec![decimal_column("amount", precision, 2)];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(one_row_values(
                    input_output,
                    vec![ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1.00".to_owned(),
                        }),
                        ty: format!("DECIMAL({precision},2)"),
                    }],
                )),
                group_keys: Vec::new(),
                grouping_sets: vec![Vec::new()],
                agg_calls: vec![AggregateCall {
                    raw: "AVG($0)".to_owned(),
                    function: "AVG".to_owned(),
                    distinct: false,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                }],
                output: vec![decimal_column_unconstrained("avg_amount")],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "DECIMAL({precision},2): {:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module_for_test(&query);
        assert!(module.rocq_module.contains(&format!(
            "AAggregate (AggregateAverageNumericFixed ({precision})%Z (2)%Z) AggregateAll"
        )));
        assert!(
            !module
                .rocq_module
                .contains("AggregateAverageNumericAtScale")
        );
        assert!(
            !module
                .rocq_module
                .contains("AAggregate AggregateSumNumeric")
        );
        assert!(!module.rocq_module.contains("AAggregate AggregateCount"));
        assert!(module.rocq_module.contains("AttrNumeric \"avg_amount\""));
    }
}

#[test]
fn lowers_numeric_expression_avg_with_exact_scale_two_provenance() {
    let product_output = vec![decimal_column_unconstrained("extended_price")];
    let projected = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["sales".to_owned()],
            output: vec![
                typed_column("quantity", SqlType::Integer),
                decimal_column("list_price", 7, 2),
            ],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "*".to_owned(),
            op: ScalarOp::Multiply,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 1 },
            ],
        })],
        correlations: Vec::new(),
        output: product_output,
    };
    let output = vec![decimal_column_unconstrained("average_extended_price")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(projected),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("AAggregate (AggregateAverageNumericAtScale (2)%Z) AggregateAll")
    );
}

#[test]
fn lowers_numeric_case_avg_with_representative_scale_two_provenance() {
    let projected = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["sales".to_owned()],
            output: vec![
                typed_column("quantity", SqlType::Integer),
                decimal_column("list_price", 7, 2),
            ],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "CASE".to_owned(),
            op: ScalarOp::Case,
            args: vec![
                ScalarAst::Call {
                    operator: ">".to_owned(),
                    op: ScalarOp::Gt,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "0".to_owned(),
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                    ],
                },
                ScalarAst::InputRef { index: 1 },
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "0.00".to_owned(),
                    }),
                    ty: "DECIMAL(3,2)".to_owned(),
                },
            ],
        })],
        correlations: Vec::new(),
        output: vec![decimal_column_unconstrained("conditional_price")],
    };
    let output = vec![decimal_column_unconstrained("average_conditional_price")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(projected),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("AAggregate (AggregateAverageNumericAtScale (2)%Z) AggregateAll")
    );
}

#[test]
fn rejects_avg_over_unconstrained_numeric_column_without_dscale() {
    let input_output = vec![decimal_column_unconstrained("amount")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column_unconstrained("avg_amount")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "numeric_avg_typmod_not_supported" })
    );
}

#[test]
fn lowers_decimal_avg_at_any_fixed_scale() {
    let input_output = vec![decimal_column("amount", 10, 3)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input_output,
                vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1.000".to_owned(),
                    }),
                    ty: "DECIMAL(10,3)".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column_unconstrained("avg_amount")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("AAggregate (AggregateAverageNumericFixed (10)%Z (3)%Z) AggregateAll")
    );
}

#[test]
fn overrides_calcite_fixed_decimal_avg_output_with_postgres_numeric() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(one_row_values(
            input_output,
            vec![ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.00".to_owned(),
                }),
                ty: "DECIMAL(10,2)".to_owned(),
            }],
        )),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "AVG($0)".to_owned(),
            function: "AVG".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![decimal_column("avg_amount", 10, 3)],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(aggregate),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![decimal_column("avg_amount", 10, 3)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_aggregate_type_overridden"),
        "{:?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("AttrNumeric \"avg_amount\""));
}

#[test]
fn lowers_decimal_sum_to_unconstrained_numeric() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input_output,
                vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1.00".to_owned(),
                    }),
                    ty: "DECIMAL(10,2)".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "SUM($0)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column_unconstrained("sum_amount")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateSumNumeric AggregateAll")
    );
}

#[test]
fn overrides_decimal_min_output_with_postgres_numeric() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input_output,
                vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1.00".to_owned(),
                    }),
                    ty: "DECIMAL(10,2)".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_aggregate_type_overridden")
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("AttrNumeric \"min_amount\""));
}

#[test]
fn preserves_unconstrained_numeric_through_calcite_fixed_projection() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_project_input_type_overridden")
    );
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Projection { ref select, .. })
            if matches!(select.as_slice(), [FormalScalarSelectItem {
                alias_ty: FormalAttributeType::Numeric,
                ..
            }])
    ));
}

#[test]
fn sort_uses_actual_lowered_numeric_scope_not_stale_calcite_decimal() {
    let reported_output = vec![decimal_column("amount", 10, 2)];
    let projected = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![decimal_column_unconstrained("amount")],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: reported_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Sort {
            input: Box::new(projected),
            collation: vec![logos_ir::ir::SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: None,
            offset: None,
            output: reported_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::OrderBy { keys, .. }) = lowered.query_expr else {
        panic!("expected exact OrderBy expression");
    };
    assert_eq!(keys.len(), 1);
    assert_eq!(keys[0].attribute_ty, FormalAttributeType::Numeric);
}

#[test]
fn lowers_unconstrained_numeric_table_scan_output() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![decimal_column_unconstrained("amount")],
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![decimal_column_unconstrained("amount")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("AttrNumeric \"amount\""));
}

#[test]
fn rejects_invalid_decimal_input_scope_typmod() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column(
                    "amount",
                    SqlType::Decimal {
                        precision: Some(0),
                        scale: Some(0),
                    },
                )],
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        analysis_errors: vec![],
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
                expr: Box::new(ScalarAst::InputRef { index: 0 }),
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
        analysis_errors: vec![],
    };

    let source = lower_query(&make_query(timestamp_literal));
    let target = lower_query(&make_query(timestamp_plus_interval));
    assert_eq!(source.status, LoweringStatus::Lowered);
    assert_eq!(
        target.status,
        LoweringStatus::Lowered,
        "{:?}",
        target.diagnostics
    );

    let module = emit_rocq_query_module(
        source.query_expr.as_ref().unwrap(),
        target.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AttrTimestamp \"ts\" 6"));
    assert!(module.rocq_module.contains("CstTimestamp (1000001)"));
    assert!(
        module
            .rocq_module
            .contains("ScalarTimestampAdd ScalarTimestampSecond")
    );
}

#[test]
fn lowers_date_interval_arithmetic_through_timestamp_semantics() {
    let input = vec![typed_column("base_date", SqlType::Date)];
    let output = vec![timestamp_column("result", Some(6))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::Values {
                rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "'2024-01-31'".to_owned(),
                    }),
                    ty: "DATE".to_owned(),
                })]],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    // Calcite can omit a redundant Rex type annotation here;
                    // the authoritative input scope still identifies DATE.
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1".to_owned(),
                        }),
                        ty: "INTERVAL MONTH".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastDateToTimestamp")
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarTimestampAdd ScalarTimestampMonth")
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AttrTimestamp \"ts\" 0"));
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastDateToTimestamp")
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AttrDate \"d\""));
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastTimestampToDate")
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
        analysis_errors: vec![],
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::parse("UTC"),
            sql_environment: Default::default(),
        },
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstTimestamptz (0)"));
}

#[test]
fn enforces_postgres_timestamp_time_zone_displacement_limit() {
    assert!(
        super::emit::timestamptz_literal_to_utc_micros(
            "'2000-01-01 00:00:00+15:59'",
            6,
            &SqlTimeZone::utc(),
        )
        .is_some()
    );
    assert!(
        super::emit::timestamptz_literal_to_utc_micros(
            "'2000-01-01 00:00:00-15:59'",
            6,
            &SqlTimeZone::utc(),
        )
        .is_some()
    );
    assert!(
        super::emit::timestamptz_literal_to_utc_micros(
            "'2000-01-01 00:00:00+16:00'",
            6,
            &SqlTimeZone::utc(),
        )
        .is_none()
    );
    assert!(
        super::emit::source_timestamptz_cast_to_utc_micros(
            "'2000-01-01 00:00:00-16:00'",
            6,
            &SqlTimeZone::utc(),
        )
        .is_none()
    );

    let negative_fourteen = SqlTimeZone::parse("-14:00");
    assert!(
        super::emit::timestamptz_literal_to_utc_micros(
            "'294247-01-10 00:00:00'",
            6,
            &negative_fourteen,
        )
        .is_none()
    );
    assert!(
        super::emit::source_timestamptz_cast_to_utc_micros(
            "'294247-01-10 00:00:00'",
            6,
            &negative_fourteen,
        )
        .is_none()
    );
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
        analysis_errors: vec![],
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::parse("Asia/Shanghai"),
            sql_environment: Default::default(),
        },
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstTimestamptz (0)"));
}

#[test]
fn rejects_unoffset_timestamp_tz_literal_in_unattested_named_time_zone() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::parse("Asia/Shanghai"),
            sql_environment: Default::default(),
        },
    );

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "timestamp_tz_literal_not_supported")
    );
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let lowered_query = format!("{:?}", lowered_query_expr(&lowered).unwrap());
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
        analysis_errors: vec![],
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
fn rejects_timestamp_attribute_precision_outside_postgres_range() {
    let output = vec![typed_column(
        "ts",
        SqlType::Timestamp { precision: Some(7) },
    )];
    let query = Query {
        source_sql: None,
        rel: RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output,
        },
        analysis_errors: vec![],
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
    let source = FormalQueryExpr::Table {
        relation: "EMP".to_owned(),
        columns: vec![formal_attribute("EMPNO", FormalAttributeType::Z)],
    };
    let target = FormalQueryExpr::Projection {
        select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Z,
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: "EMPNO".to_owned(),
                        ty: FormalAttributeType::Z,
                    },
                },
            },
            alias: "EMPNO".to_owned(),
            alias_ty: FormalAttributeType::Z,
            numeric_dscale: Some(NumericDscaleProvenance::Exact(0)),
        }],
        input: Box::new(source.clone()),
    };

    let module = emit_rocq_query_module(&source, &target);
    assert_eq!(
        module.definition_graph,
        emit_rocq_query_module(&source, &target).definition_graph
    );
    assert_eq!(module.definition_graph.schema_version, 2);

    let report = serde_json::to_value(&module).expect("serialize formal query module");
    let object = report.as_object().expect("formal query module object");
    assert_eq!(object.len(), 2);
    assert!(object.contains_key("rocqModule"));
    assert!(object.contains_key("definitionGraph"));
    let graph_json = serde_json::to_string(&module.definition_graph).unwrap();
    assert!(!graph_json.contains("EMPNO"));
    assert!(!graph_json.contains("\"EMP\""));
    assert_eq!(
        emitted_definition_shape(&module, "target_query_expr"),
        "QExpr_Project(@scalar_select_list_0,QExpr_Table{columns=1})"
    );

    assert!(module.rocq_module.starts_with(
        "From SQLFS Require Import FTuples FiniteSet FiniteBag FiniteCollection FlatData SqlSyntax GenericInstance Values ValueCore ValueNumeric ValueNumericTypmod ValueString SchemaConstraints SqlOutcome SqlOrder Formula SqlQuerySyntax SqlQuerySemantics SqlQueryWellFormed."
    ));
    assert!(
        module.rocq_module.contains(
            "From Logos Require Import FormalSQL.TNullSyntax FormalSQL.QueryTNullSyntax."
        )
    );
    assert!(
        module
            .rocq_module
            .contains("From LogosGenerated Require Import Schema.")
    );
    assert!(
        !module
            .rocq_module
            .contains("Definition source_query : Query :=")
    );
    assert!(
        !module
            .rocq_module
            .contains("Definition target_query : Query :=")
    );
    assert!(module.rocq_module.contains("QExpr_Table"));
    assert!(
        module
            .rocq_module
            .contains("QExpr_Project (scalar_select_list_0)")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition source_query_expr : QueryExpr :=")
    );
    assert!(
        module
            .rocq_module
            .contains("@QExpr_Table TNull relname ([AttrZ \"EMPNO\"]) (Rel \"EMP\")")
    );
    for certificate in [
        "source_query_expr_admissible_with_outputs_generated_schema",
        "target_query_expr_admissible_with_outputs_generated_schema",
        "source_query_expr_admissible",
        "source_query_program_admissible_generated_schema",
        "source_query_program_admissible",
        "target_query_program_admissible",
    ] {
        assert!(
            module.rocq_module.contains(certificate),
            "missing deterministic admissibility certificate {certificate}"
        );
    }
    assert!(
        module
            .rocq_module
            .contains("eapply TNullQueryExprAdmissibleWithOutputs_intro.")
    );
    assert!(module.rocq_module.contains(
        "query_expr_admissible_database_schema_transport\n    Schema.generated_schema Schema.generated_schema_constraints db"
    ));
    assert!(
        !module
            .rocq_module
            .contains("unfold source_query_program, source_query_expr; vm_compute")
    );
}

#[test]
fn reuses_exact_scalar_select_list_prefix_definitions_and_certificates() {
    let parent_select = vec![z_select_item("a"), z_select_item("b"), z_select_item("c")];
    let child_select = parent_select[..2].to_vec();
    let query = FormalQueryExpr::Projection {
        select: child_select,
        input: Box::new(FormalQueryExpr::Projection {
            select: parent_select,
            input: Box::new(FormalQueryExpr::Table {
                relation: "t".to_owned(),
                columns: vec![
                    formal_attribute("a", FormalAttributeType::Z),
                    formal_attribute("b", FormalAttributeType::Z),
                    formal_attribute("c", FormalAttributeType::Z),
                ],
            }),
        }),
    };

    let module = emit_rocq_query_module(&query.clone(), &query);
    let parent_definition = module
        .rocq_module
        .find("Definition scalar_select_list_1")
        .expect("parent select-list definition");
    let child_definition = module
        .rocq_module
        .find("Definition scalar_select_list_0")
        .expect("child select-list definition");
    assert!(parent_definition < child_definition);
    assert!(
        module
            .rocq_module
            .contains("firstn (2%nat) (scalar_select_list_1)")
    );
    assert!(
        module
            .rocq_module
            .contains("cbn [prop_forall fst snd firstn app]")
    );

    let parent_certificate = module
        .rocq_module
        .find("Lemma scalar_select_list_1_admissible_row_select_generated_schema")
        .expect("parent select-list certificate");
    let child_certificate = module
        .rocq_module
        .find("Lemma scalar_select_list_0_admissible_row_select_generated_schema")
        .expect("child select-list certificate");
    assert!(parent_certificate < child_certificate);
    let child_certificate_tail = &module.rocq_module[child_certificate..];
    let child_certificate_body = &child_certificate_tail[..child_certificate_tail
        .find("\nQed.")
        .expect("child select-list certificate end")];
    assert!(child_certificate_body.contains("eapply (@prop_forall_firstn"));
    assert!(
        child_certificate_body
            .contains("exact (scalar_select_list_1_admissible_row_select_generated_schema).")
    );
}

#[test]
fn chunks_wide_scalar_select_list_definitions_and_certificates() {
    let names = (0..96).map(|index| format!("c{index}")).collect::<Vec<_>>();
    let query = FormalQueryExpr::Projection {
        select: names.iter().map(|name| z_select_item(name)).collect(),
        input: Box::new(FormalQueryExpr::Table {
            relation: "wide".to_owned(),
            columns: names
                .iter()
                .map(|name| formal_attribute(name, FormalAttributeType::Z))
                .collect(),
        }),
    };

    let module = emit_rocq_query_module(&query.clone(), &query);
    for chunk_index in 0..3 {
        assert!(module.rocq_module.contains(&format!(
            "Definition scalar_select_list_0_chunk_{chunk_index}"
        )));
        assert!(module.rocq_module.contains(&format!(
            "Lemma scalar_select_list_0_chunk_{chunk_index}_admissible_row_select_generated_schema"
        )));
    }
    assert!(!module.rocq_module.contains("scalar_select_list_0_chunk_3"));
    assert!(module.rocq_module.contains(
        "scalar_select_list_0_chunk_0 ++ (scalar_select_list_0_chunk_1 ++ (scalar_select_list_0_chunk_2))"
    ));
    assert!(
        module
            .rocq_module
            .contains("eapply (@prop_forall_app _ _ (scalar_select_list_0_chunk_0) _).")
    );
}

#[test]
fn timestamp_default_precision_identity_select_matches_explicit_six() {
    let query = FormalQueryExpr::Projection {
        select: vec![FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Timestamp { precision: Some(6) },
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: "ts".to_owned(),
                        ty: FormalAttributeType::Timestamp { precision: None },
                    },
                },
            },
            alias: "ts".to_owned(),
            alias_ty: FormalAttributeType::Timestamp { precision: Some(6) },
            numeric_dscale: None,
        }],
        input: Box::new(FormalQueryExpr::Table {
            relation: "events".to_owned(),
            columns: vec![formal_attribute(
                "ts",
                FormalAttributeType::Timestamp { precision: None },
            )],
        }),
    };

    let module = emit_rocq_query_module(&query.clone(), &query);

    assert!(module.rocq_module.contains("DotTimestamp \"ts\" 6"));
}

#[test]
fn suppresses_nested_shared_queries_covered_by_larger_shared_query() {
    let select = vec![z_select_item("EMPNO")];
    let nested = FormalQueryExpr::Projection {
        select: select.clone(),
        input: Box::new(FormalQueryExpr::Table {
            relation: "EMP".to_owned(),
            columns: vec![formal_attribute("EMPNO", FormalAttributeType::Z)],
        }),
    };
    let shared = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::True,
        input: Box::new(FormalQueryExpr::CrossJoin {
            left: Box::new(FormalQueryExpr::Table {
                relation: "DEPT".to_owned(),
                columns: Vec::new(),
            }),
            right: Box::new(nested),
        }),
    };
    let source = FormalQueryExpr::Projection {
        select: select.clone(),
        input: Box::new(shared.clone()),
    };
    let target = FormalQueryExpr::Projection {
        select,
        input: Box::new(FormalQueryExpr::Selection {
            predicate: FormalScalarExpr::True,
            input: Box::new(shared),
        }),
    };

    let module = emit_rocq_query_module(&source, &target);

    assert!(
        module
            .rocq_module
            .contains("Definition shared_query_expr_0")
    );
    assert!(
        !module
            .rocq_module
            .contains("Definition shared_query_expr_1")
    );
    assert_eq!(
        emitted_definition_shape(&module, "source_query_expr"),
        "QExpr_Project(@scalar_select_list_0,@shared_query_expr_0)"
    );
    let shared_shape = emitted_definition_shape(&module, "shared_query_expr_0");
    assert!(shared_shape.starts_with("QExpr_Filter(@scalar_expr_predicate_0,QExpr_CrossJoin("));
    assert!(shared_shape.contains("QExpr_Project(@scalar_select_list_0,QExpr_Table{columns=1})"));
    assert!(!shared_shape.contains("@shared_query_expr_0"));
    assert_eq!(
        module.definition_graph.opaque_helper_symbols,
        ["scalar_select_list_0"]
    );
    assert_eq!(
        module.definition_graph.source_statements[0].statement_index,
        1
    );
    assert_eq!(
        module.definition_graph.source_statements[0].root_symbol,
        "source_query_expr"
    );
}

#[test]
fn keeps_nested_shared_query_when_it_is_used_independently() {
    let select = vec![z_select_item("EMPNO")];
    let nested = FormalQueryExpr::Projection {
        select: select.clone(),
        input: Box::new(FormalQueryExpr::Table {
            relation: "EMP".to_owned(),
            columns: vec![formal_attribute("EMPNO", FormalAttributeType::Z)],
        }),
    };
    let parent = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::True,
        input: Box::new(nested.clone()),
    };
    let source = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(parent.clone()),
        right: Box::new(nested),
    };
    let target = parent;

    let module = emit_rocq_query_module(&source, &target);

    assert!(
        module
            .rocq_module
            .contains("Definition shared_query_expr_0")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition shared_query_expr_1")
    );
    assert!(
        module
            .rocq_module
            .contains("QExpr_Set Union (shared_query_expr_0) (shared_query_expr_1)")
    );
    assert_eq!(
        emitted_definition_shape(&module, "source_query_expr"),
        "QExpr_Set(Union,@shared_query_expr_0,@shared_query_expr_1)"
    );
    for symbol in ["shared_query_expr_0", "shared_query_expr_1"] {
        assert!(module.rocq_module.contains(&format!("Definition {symbol}")));
        assert!(!emitted_definition_shape(&module, symbol).contains(&format!("@{symbol}")));
    }
}

fn shared_query_expr_cse_leaf(relation: &str) -> FormalQueryExpr {
    FormalQueryExpr::Projection {
        select: vec![z_select_item("x")],
        input: Box::new(FormalQueryExpr::Table {
            relation: relation.to_owned(),
            columns: vec![formal_attribute("x", FormalAttributeType::Z)],
        }),
    }
}

#[test]
fn factors_exact_nested_shared_query_exprs_in_dependency_order() {
    let leaf = shared_query_expr_cse_leaf("EMP");
    let parent = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::True,
        input: Box::new(leaf.clone()),
    };
    let source = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(parent.clone()),
        right: Box::new(leaf),
    };
    let target = parent;

    let module = emit_rocq_query_module(&source, &target);
    let repeated = emit_rocq_query_module(&source, &target);
    assert_eq!(module.rocq_module, repeated.rocq_module);
    assert_eq!(module.definition_graph, repeated.definition_graph);

    // Stable first-occurrence symbols name the parent `0` and leaf `1`, while
    // dependency-safe textual/graph order emits the exact leaf first.
    let shared_symbols = module
        .definition_graph
        .definitions
        .iter()
        .filter(|definition| definition.symbol.starts_with("shared_query_expr_"))
        .map(|definition| definition.symbol.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        shared_symbols,
        ["shared_query_expr_1", "shared_query_expr_0"]
    );
    assert_eq!(
        emitted_definition_shape(&module, "shared_query_expr_0"),
        "QExpr_Filter(@scalar_expr_predicate_0,@shared_query_expr_1)"
    );
    assert_eq!(
        emitted_definition_shape(&module, "shared_query_expr_1"),
        "QExpr_Project(@scalar_select_list_0,QExpr_Table{columns=1})"
    );
    assert_eq!(
        emitted_definition_shape(&module, "source_query_expr"),
        "QExpr_Set(Union,@shared_query_expr_0,@shared_query_expr_1)"
    );
    assert_eq!(
        emitted_definition_shape(&module, "target_query_expr"),
        "@shared_query_expr_0"
    );
    assert_eq!(
        module.definition_graph.source_statements[0].root_symbol,
        "source_query_expr"
    );
    assert_eq!(
        module.definition_graph.target_statements[0].root_symbol,
        "target_query_expr"
    );

    let leaf_position = module
        .rocq_module
        .find("Definition shared_query_expr_1")
        .expect("leaf definition");
    let scalar_position = module
        .rocq_module
        .find("Definition scalar_expr_predicate_0")
        .expect("scalar definition");
    let parent_position = module
        .rocq_module
        .find("Definition shared_query_expr_0")
        .expect("parent definition");
    assert!(scalar_position < leaf_position);
    assert!(leaf_position < parent_position);
    let source_position = module
        .rocq_module
        .find("Definition source_query_expr")
        .expect("source root definition");
    let parent_definition = &module.rocq_module[parent_position..source_position];
    assert!(
        parent_definition.contains("QExpr_Filter (scalar_expr_predicate_0) (shared_query_expr_1)"),
        "{parent_definition}"
    );
    assert!(!parent_definition.contains("QExpr_Project"));

    let leaf_certificate = module
        .rocq_module
        .find("Lemma shared_query_expr_1_admissible_with_outputs_generated_schema")
        .expect("leaf admissibility certificate");
    let scalar_certificate = module
        .rocq_module
        .find("Lemma scalar_expr_predicate_0_admissible_where_generated_schema")
        .expect("scalar admissibility certificate");
    let parent_certificate = module
        .rocq_module
        .find("Lemma shared_query_expr_0_admissible_with_outputs_generated_schema")
        .expect("parent admissibility certificate");
    let source_certificate = module
        .rocq_module
        .find("Lemma source_query_expr_admissible_with_outputs_generated_schema")
        .expect("source admissibility certificate");
    assert!(scalar_certificate < leaf_certificate);
    assert!(leaf_certificate < parent_certificate);
    assert!(parent_certificate < source_certificate);
    let parent_certificate_body = &module.rocq_module[parent_certificate..source_certificate];
    assert!(parent_certificate_body.contains(
        "exact (proj1 (proj1 (shared_query_expr_1_admissible_with_outputs_generated_schema)))."
    ));
    assert!(
        parent_certificate_body
            .contains("apply (scalar_expr_predicate_0_admissible_where_generated_schema)."),
        "a shared query should reuse the already emitted opaque scalar certificate: {parent_certificate_body}"
    );
}

#[test]
fn shared_query_expr_cse_rejects_structural_near_misses() {
    let exact_leaf = shared_query_expr_cse_leaf("EMP");
    let parent = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::True,
        input: Box::new(exact_leaf),
    };
    let source = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(parent.clone()),
        right: Box::new(shared_query_expr_cse_leaf("DEPT")),
    };
    let module = emit_rocq_query_module(&source, &parent);

    let shared_symbols = module
        .definition_graph
        .definitions
        .iter()
        .filter(|definition| definition.symbol.starts_with("shared_query_expr_"))
        .map(|definition| definition.symbol.as_str())
        .collect::<Vec<_>>();
    assert_eq!(shared_symbols, ["shared_query_expr_0"]);
    assert!(emitted_definition_shape(&module, "shared_query_expr_0").contains("QExpr_Project"));
    assert!(
        !module
            .rocq_module
            .contains("Definition shared_query_expr_1")
    );
    assert!(module.rocq_module.contains("Rel \"EMP\""));
    assert!(module.rocq_module.contains("Rel \"DEPT\""));
}

#[test]
fn keeps_pure_outer_joins_in_native_unified_formal_queries() {
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
    let mut query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    for (join_type, expected_kind, emitted_kind) in [
        (JoinType::Left, FormalQueryJoinKind::Left, "QueryJoinLeft"),
        (
            JoinType::Right,
            FormalQueryJoinKind::Right,
            "QueryJoinRight",
        ),
        (JoinType::Full, FormalQueryJoinKind::Full, "QueryJoinFull"),
    ] {
        let RelExpr::Join {
            join_type: actual_join_type,
            ..
        } = &mut query.rel
        else {
            unreachable!();
        };
        *actual_join_type = join_type;
        let lowered = lower_query(&query);
        let module = emit_rocq_query_module(
            lowered
                .query_expr
                .as_ref()
                .expect("outer join should lower"),
            lowered
                .query_expr
                .as_ref()
                .expect("outer join should lower"),
        );

        assert_eq!(lowered.status, LoweringStatus::Lowered);
        let Some(FormalQueryExpr::Join { join_kind, .. }) = lowered.query_expr.as_ref() else {
            panic!("pure outer join should use one native join node");
        };
        assert_eq!(*join_kind, expected_kind);
        assert!(
            module
                .rocq_module
                .contains(&format!("QExpr_Join {emitted_kind}"))
        );
        assert!(!module.rocq_module.contains("QExpr_Set Union"));
        assert!(module.rocq_module.contains("NullInt32"));
        assert_no_physical_plan_constructs(&module);
    }
}

#[test]
fn keeps_pure_semi_and_anti_join_in_unified_formal_queries() {
    let semi = existence_join_query(JoinType::Semi);
    let anti = existence_join_query(JoinType::Anti);

    let semi_lowered = lower_query(&semi);
    let anti_lowered = lower_query(&anti);
    let semi_module = emit_rocq_query_module(
        semi_lowered
            .query_expr
            .as_ref()
            .expect("semi join should lower"),
        semi_lowered
            .query_expr
            .as_ref()
            .expect("semi join should lower"),
    );
    let anti_module = emit_rocq_query_module(
        anti_lowered
            .query_expr
            .as_ref()
            .expect("anti join should lower"),
        anti_lowered
            .query_expr
            .as_ref()
            .expect("anti join should lower"),
    );

    assert_eq!(semi_lowered.status, LoweringStatus::Lowered);
    assert_eq!(anti_lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Join { join_kind, .. }) = semi_lowered.query_expr.as_ref() else {
        panic!("pure semi join should use one native join node");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Semi);
    let Some(FormalQueryExpr::Join { join_kind, .. }) = anti_lowered.query_expr.as_ref() else {
        panic!("pure anti join should use one native join node");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Anti);
    assert!(semi_module.rocq_module.contains("QExpr_Join QueryJoinSemi"));
    assert!(anti_module.rocq_module.contains("QExpr_Join QueryJoinAnti"));
}

#[test]
fn native_existence_join_uses_lowered_numeric_scope_and_provenance() {
    let left_output = vec![decimal_column_unconstrained("left_value")];
    let right_output = vec![decimal_column_unconstrained("right_value")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["left_rows".to_owned()],
                    output: left_output.clone(),
                }),
                exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
                correlations: Vec::new(),
                output: left_output,
            }),
            right: Box::new(RelExpr::TableScan {
                table: vec!["right_rows".to_owned()],
                output: right_output,
            }),
            join_type: JoinType::Semi,
            condition: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            }),
            correlations: Vec::new(),
            // Calcite can copy a stale fixed typmod onto a logical join even
            // though the lowered child remains PostgreSQL NUMERIC.
            output: vec![decimal_column("left_value", 10, 2)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Join {
        join_kind,
        predicate,
        matched_select,
        left_select,
        ..
    }) = lowered.query_expr.as_ref()
    else {
        panic!("SEMI join should use the native join node");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Semi);
    assert_eq!(matched_select.len(), 1);
    assert_eq!(left_select.len(), 1);
    for item in [
        matched_select.first().unwrap(),
        left_select.first().unwrap(),
    ] {
        assert_eq!(item.alias_ty, FormalAttributeType::Numeric);
        let FormalScalarExpr::Leaf {
            term:
                FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute { ty, .. },
                },
            ..
        } = &item.expr
        else {
            panic!("existence output should be an identity scope projection");
        };
        assert_eq!(*ty, FormalAttributeType::Numeric);
    }
    let FormalScalarExpr::Predicate { args, .. } = predicate else {
        panic!("expected typed scalar equality predicate");
    };
    assert!(args.iter().all(|arg| matches!(
        arg,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    ty: FormalAttributeType::Numeric,
                    ..
                }
            },
            ..
        }
    )));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Join QueryJoinSemi"));
    assert!(module.rocq_module.contains("AttrNumeric"));
    assert!(!module.rocq_module.contains("AttrDecimal"));
}

#[test]
fn emits_proof_rocq_module_with_schema_and_query_pair() {
    let module = emit_rocq_query_expr_proof_module();

    assert!(
        module
            .rocq_module
            .contains("SqlErrorSemantics SqlListFacts SqlQuerySyntax")
    );
    assert!(
        module
            .rocq_module
            .contains("From LogosGenerated Require Import Schema Queries Witness.\n")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_equivalence_input :=")
    );
    assert!(
        module
            .rocq_module
            .contains("Schema.generated_schema_constraints")
    );
    assert!(
        module
            .rocq_module
            .contains("Schema.generated_schema_conforms db ->")
    );
    assert!(
        !module
            .rocq_module
            .contains("Definition generated_schema_conforms")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_query_expr_equiv")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_equivalence_goal : Prop :=")
    );
    assert!(
        module
            .rocq_module
            .contains("Lemma generated_equivalence_goal_intro :\n  (forall db,")
    );
    assert!(
        module
            .rocq_module
            .contains("apply source_query_program_admissible.\n  exact Hschema.")
    );
    assert!(
        module
            .rocq_module
            .contains("apply target_query_program_admissible.\n    exact Hschema.")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_query_program_admissible")
    );
    assert!(
        module
            .rocq_module
            .contains("generated_query_program_admissible\n        db (source_query_program) /\\")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_countermodel_goal : Prop :=\n  Witness.generated_witness_available = true /\\")
    );
    assert!(!module.rocq_module.contains("exists db : db_state,"));
    assert!(module.rocq_module.contains(
        "Definition generated_verification_goal\n    (claim : verification_claim_kind) : Prop :="
    ));
    assert!(module.rocq_module.contains(
        "Theorem generated_queries_verified :\n       generated_verification_goal generated_verification_claim."
    ));
    assert!(!module.rocq_module.contains("Abort."));
    assert!(
        !module
            .rocq_module
            .contains("Definition generated_schema :=")
    );
    assert!(!module.rocq_module.contains("Definition source_query :="));
    assert!(!module.rocq_module.contains("Definition target_query :="));
}

#[test]
fn every_problem_template_uses_the_trusted_generated_schema_constraints() {
    let label = "query-expression";
    let module = emit_rocq_query_expr_proof_module();
    assert!(
        module
            .rocq_module
            .contains("Schema.generated_schema_constraints"),
        "{label}"
    );
    assert!(
        module
            .rocq_module
            .contains("Schema.generated_schema_conforms db ->"),
        "{label}"
    );
    assert!(
            module.rocq_module.contains(
                "source_program_output_signatures =\n      map query_expr_outputs\n        (source_query_program) /\\"
            ),
            "{label}"
        );
    assert!(
            module.rocq_module.contains(
                "target_program_output_signatures =\n      map query_expr_outputs\n        (target_query_program) /\\"
            ),
            "{label}"
        );
    assert!(
        !module
            .rocq_module
            .contains("Definition generated_schema_conforms"),
        "{label}"
    );
    assert!(
        module
            .rocq_module
            .starts_with(&emit_trusted_proof_import_block()),
        "{label}: complete registry-owned trusted imports must be emitted"
    );
    assert!(
        !module
            .rocq_module
            .lines()
            .any(|line| line.trim_start().starts_with("Check ")),
        "{label}: production Problem.v must not emit diagnostic Check commands"
    );
}

#[test]
fn production_schema_and_query_modules_omit_diagnostic_check_commands() {
    let schema_module =
        super::emit::emit_rocq_schema_module("init_db", &[], SqlEnvironment::default());
    let query = FormalQueryExpr::Empty {
        columns: Vec::new(),
    };
    let query_module = emit_rocq_query_module(&query, &query);

    for (label, source) in [
        ("Schema.v", schema_module.as_str()),
        ("Queries.v", query_module.rocq_module.as_str()),
    ] {
        assert!(
            !source
                .lines()
                .any(|line| line.trim_start().starts_with("Check ")),
            "{label} must not emit diagnostic Check commands"
        );
    }
}

#[test]
fn emits_typed_query_observation_proof_obligations() {
    let module = emit_rocq_query_expr_proof_module();

    assert!(
        module
            .rocq_module
            .contains("SqlErrorSemantics SqlListFacts SqlQuerySyntax")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_query_expr_equiv")
    );
    assert!(
        module
            .rocq_module
            .contains("@query_expr_possible_equiv TNull relname")
    );
    assert!(module.rocq_module.contains("generated_query_program_equiv"));
    assert!(
        module
            .rocq_module
            .contains("Definition generated_query_program_admissible")
    );
    assert!(
        module
            .rocq_module
            .contains("Schema.generated_schema_constraints")
    );
    assert!(
        module
            .rocq_module
            .contains("Schema.generated_schema_conforms db ->")
    );
    assert!(
        !module
            .rocq_module
            .contains("Definition generated_schema_conforms")
    );
    assert!(
        module
            .rocq_module
            .contains("generated_query_program_admissible\n        db (target_query_program) /\\")
    );
    assert!(
        module
            .rocq_module
            .contains("@query_program_possible_equiv TNull relname")
    );
    assert!(!module.rocq_module.contains("Abort."));
}

#[test]
fn lowers_identity_sort_to_permutation_closed_observation() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered_query_expr(&lowered),
        Some(FormalQueryExpr::Table { .. })
    ));
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Table { .. })
    ));
    assert_no_physical_plan_constructs(&module);
}

#[test]
fn lowering_report_serializes_query_expr() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![column("a")],
        },
        analysis_errors: vec![],
    };
    let lowered = lower_query(&query);
    let value = serde_json::to_value(&lowered).expect("serialize lowering report");
    let object = value.as_object().expect("lowered query object");
    assert!(!object.contains_key("query"));
    assert!(object.contains_key("queryExpr"));
    assert!(object.contains_key("outputSignature"));
}

#[test]
fn lowers_sort_offset_fetch_to_ordered_observation() {
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
        offset: Some(Box::new(scalar(ScalarAst::Literal {
            raw: "2".to_owned(),
        }))),
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let query_expr = lowered
        .query_expr
        .expect("sort should lower as a query expression");
    let FormalQueryExpr::Fetch { count, input } = query_expr else {
        panic!("expected top-level Fetch");
    };
    assert_eq!(count, 10);
    let FormalQueryExpr::Offset { count, input } = *input else {
        panic!("expected Offset under Fetch");
    };
    assert_eq!(count, 2);
    let FormalQueryExpr::OrderBy { keys, input } = *input else {
        panic!("expected OrderBy under Offset");
    };
    assert_eq!(keys.len(), 1);
    assert_eq!(keys[0].attribute_name, "b");
    assert_eq!(keys[0].attribute_ty, FormalAttributeType::Int32);
    assert_eq!(keys[0].direction, FormalSortDirection::Desc);
    assert_eq!(keys[0].null_direction, FormalNullDirection::First);
    assert!(matches!(*input, FormalQueryExpr::Table { .. }));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
    assert!(module.rocq_module.contains("QExpr_Offset"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert_no_physical_plan_constructs(&module);
}

#[test]
fn lowers_boolean_order_by_through_the_sql_order_carrier() {
    for (direction, null_direction, expected) in [
        (
            SortDirection::Ascending,
            SortNullDirection::Last,
            "SortAscNullsLast (AttrBool \"flag\")",
        ),
        (
            SortDirection::Descending,
            SortNullDirection::First,
            "SortDescNullsFirst (AttrBool \"flag\")",
        ),
    ] {
        let output = vec![typed_column("flag", SqlType::Boolean)];
        let query = query_for_rel(
            RelExpr::Sort {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["flags".to_owned()],
                    output: output.clone(),
                }),
                collation: vec![logos_ir::ir::SortKey {
                    field_index: 0,
                    direction,
                    null_direction: Some(null_direction),
                }],
                fetch: None,
                offset: None,
                output: output.clone(),
            },
            output,
        );

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{:#?}",
            lowered.diagnostics
        );
        let Some(FormalQueryExpr::OrderBy { keys, .. }) = lowered.query_expr.as_ref() else {
            panic!("Boolean ORDER BY must remain an exact ordered observation");
        };
        assert!(matches!(keys.as_slice(), [key]
            if key.attribute_ty == FormalAttributeType::Bool));
        let module = emit_rocq_query_module_for_test(&query);
        assert!(
            module.rocq_module.contains(expected),
            "{}",
            module.rocq_module
        );
    }
}

#[test]
fn lowers_project_over_nested_sort_fetch_to_recursive_query_expr() {
    let output = vec![column("a")];
    let ordered_top_k = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })),
        offset: None,
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(ordered_top_k),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("projection should remain above the order-sensitive child");
    };
    let FormalQueryExpr::Fetch { input, .. } = input.as_ref() else {
        panic!("nested FETCH should be retained");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::OrderBy { .. }));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Project"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
    assert!(module.rocq_module.contains("QExpr_Table"));
    assert!(module.rocq_module.contains("shared_query_expr_0"));
    assert!(!module.rocq_module.contains("shared_query_expr_1"));
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_preserves_case_mapping_text_through_parent_project_and_union_all() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-case-mapping-text-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(&schema_path, "create table emp(ename text);\n").expect("write wrapper schema");

    let cases = [
        (
            "direct-project",
            "select upper(ename) as mapped from emp;\n",
            "calcite_string_case_mapping_type_overridden",
        ),
        (
            "union-all",
            "select upper(ename) as mapped from emp union all select lower(ename) as mapped from emp;\n",
            "calcite_set_string_case_mapping_type_overridden",
        ),
    ];
    for (label, sql, expected_warning) in cases {
        fs::write(&query_path, sql).expect("write wrapper query");
        let output = Command::new(repo.join("scripts/calcite-ir"))
            .arg("--schema")
            .arg(&schema_path)
            .arg("--sql")
            .arg(&query_path)
            .arg("--default-collation")
            .arg("C")
            .arg("--character-classification")
            .arg("C")
            .arg("--locale-provider")
            .arg("libc")
            .arg("--server-encoding")
            .arg("UTF8")
            .output()
            .expect("run Calcite wrapper");
        assert!(
            output.status.success(),
            "{label}: calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let raw: CalciteFile =
            serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
        assert_eq!(raw.environment, SqlEnvironment::postgres_utf8_c());
        let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
        let lowered = lower_query_with_config(
            &ir.queries[0],
            &LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            },
        );
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert_eq!(
            lowered
                .output_signature
                .as_ref()
                .and_then(|signature| signature.first())
                .map(|attribute| attribute.ty),
            Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
            "{label}"
        );
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == expected_warning),
            "{label}: {:#?}",
            lowered.diagnostics
        );
    }

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_numeric_values_zero_dscale_stays_dynamic_downstream() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-numeric-values-dscale-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(&schema_path, "create table t(n numeric(19,0));\n").expect("write wrapper schema");
    fs::write(
        &query_path,
        "select x, (n + x) / 3 as y\n\
         from t cross join (values (0), (2.1)) as v(x);\n\
         select coalesce(n, 0) as x from t;\n",
    )
    .expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .arg("--default-collation")
        .arg("C")
        .arg("--character-classification")
        .arg("C")
        .arg("--locale-provider")
        .arg("libc")
        .arg("--server-encoding")
        .arg("UTF8")
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
    assert_eq!(ir.queries.len(), 2);
    let config = LoweringConfig {
        sql_environment: SqlEnvironment::postgres_utf8_c(),
        ..LoweringConfig::default()
    };

    let downstream = lower_query_with_config(&ir.queries[0], &config);
    assert_eq!(
        downstream.status,
        LoweringStatus::Blocked,
        "{downstream:#?}"
    );
    assert!(
        downstream
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "numeric_display_scale_not_available"),
        "a mixed VALUES column must not receive one invented static dscale: {downstream:#?}"
    );

    let coalesce = lower_query_with_config(&ir.queries[1], &config);
    assert_eq!(coalesce.status, LoweringStatus::Lowered, "{coalesce:#?}");
    assert_eq!(
        coalesce.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::Numeric
    );
    let module = emit_rocq_query_module(
        coalesce.query_expr.as_ref().expect("COALESCE query"),
        coalesce.query_expr.as_ref().expect("COALESCE query"),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumeric ScalarSourceInt32")
    );

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and Maven bootstrap"]
fn calcite_wrappers_preserve_postgres_unknown_string_set_typing() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-unknown-string-set-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    let schema_sql = "create table t(id integer);\n";
    fs::write(&schema_path, schema_sql).expect("write wrapper schema");
    let cases = [
        (
            "unknown-varchar",
            "select 'x' as v from t union all select cast('y' as varchar(3)) as v from t;\n",
            SqlStringType::Varchar { length: None },
        ),
        (
            "varchar-unknown",
            "select cast('y' as varchar(3)) as v from t union all select 'x' as v from t;\n",
            SqlStringType::Varchar { length: None },
        ),
        (
            "unknown-char",
            "select 'x' as v from t union all select cast('y' as char(3)) as v from t;\n",
            SqlStringType::Bpchar,
        ),
    ];
    let config = LoweringConfig {
        sql_environment: SqlEnvironment::postgres_utf8_c(),
        ..LoweringConfig::default()
    };

    for (label, sql, expected_typmod) in cases {
        fs::write(&query_path, sql).expect("write wrapper query");
        for production in [false, true] {
            let mut command = Command::new(if production {
                repo.join("scripts/calcite-ir-sqlglot")
            } else {
                repo.join("scripts/calcite-ir")
            });
            if production {
                command
                    .arg("--read")
                    .arg("postgres")
                    .arg("--write")
                    .arg("postgres");
            }
            let output = command
                .arg("--schema")
                .arg(&schema_path)
                .arg("--sql")
                .arg(&query_path)
                .arg("--default-collation")
                .arg("C")
                .arg("--character-classification")
                .arg("C")
                .arg("--locale-provider")
                .arg("libc")
                .arg("--server-encoding")
                .arg("UTF8")
                .output()
                .expect("run Calcite wrapper");
            let frontend = if production { "production" } else { "direct" };
            assert!(
                output.status.success(),
                "{label}/{frontend}: wrapper failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            let raw: CalciteFile =
                serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
            let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
            let lowered = lower_query_with_schema_config(&ir.queries[0], &ir.schema, &config);
            assert_eq!(
                lowered.status,
                LoweringStatus::Lowered,
                "{label}/{frontend}: {:#?}",
                lowered.diagnostics
            );
            assert_eq!(
                lowered.output_signature.as_deref().unwrap()[0].ty,
                FormalAttributeType::String {
                    typmod: expected_typmod,
                },
                "{label}/{frontend}"
            );
            let module = emit_rocq_query_module(
                lowered.query_expr.as_ref().expect("set query"),
                lowered.query_expr.as_ref().expect("set query"),
            );
            assert!(module.rocq_module.contains("ScalarCoerceStringImplicit"));
        }
    }

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_no_from_string_cast_reaches_solver() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-no-from-string-cast-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(&schema_path, "create table t(id integer);\n").expect("write wrapper schema");
    fs::write(&query_path, "select cast('a' as char(2)) as x;\n").expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
    let lowered = lower_query(&ir.queries[0]);
    assert_eq!(lowered.status, LoweringStatus::Lowered);

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_project_over_nested_order_offset_fetch_reaches_solver() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-nested-query-expr-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(&schema_path, "create table t(a integer, b integer);\n")
        .expect("write wrapper schema");
    fs::write(
        &query_path,
        "select ranked.a from (\n  select a, b from t\n  order by b desc nulls first\n  offset 1 rows fetch next 2 rows only\n) as ranked;\n",
    )
    .expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let raw_root = raw.queries[0].rel.as_ref().expect("outer wrapper project");
    assert_eq!(raw_root.rel_type, "LogicalProject");
    let [outer_rex] = raw_root.project_rex.as_slice() else {
        panic!("outer SELECT must expose one direct projected reference");
    };
    assert_eq!(outer_rex.source_text.as_deref(), Some("ranked.a"));
    assert_eq!(outer_rex.source_node_id.as_deref(), Some("1:8-1:15"));
    assert_eq!(outer_rex.source_identifier_names, ["ranked", "a"]);
    assert_eq!(outer_rex.source_identifier_quoted, [false, false]);
    assert!(outer_rex.source_expansion.is_none());

    let mut borrowed_inner_role = raw.clone();
    let borrowed_root = borrowed_inner_role.queries[0]
        .rel
        .as_mut()
        .expect("mutable outer wrapper project");
    let inner_rex = borrowed_root.inputs[0].inputs[0].project_rex[0].clone();
    borrowed_root.project_rex[0].source_sql = inner_rex.source_sql;
    borrowed_root.project_rex[0].source_node_id = inner_rex.source_node_id;
    borrowed_root.project_rex[0].source_text = inner_rex.source_text;
    borrowed_root.project_rex[0].source_kind = inner_rex.source_kind;
    borrowed_root.project_rex[0].source_identifier_names = inner_rex.source_identifier_names;
    borrowed_root.project_rex[0].source_identifier_quoted = inner_rex.source_identifier_quoted;
    let borrowed_error = convert_raw_file(borrowed_inner_role)
        .expect_err("an inner SELECT item cannot replace the outer direct role");
    assert!(matches!(
        borrowed_error,
        logos_ir::Error::InvalidRelSourceProvenance(message)
            if message.contains("does not belong to direct SELECT item 0")
    ));

    let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
    let query = &ir.queries[0];
    let RelExpr::Project { input, .. } = &query.rel else {
        panic!("expected converted outer Project");
    };
    let RelExpr::Sort {
        input,
        collation,
        fetch,
        offset,
        ..
    } = input.as_ref()
    else {
        panic!("expected converted nested Sort");
    };
    assert!(matches!(
        collation.as_slice(),
        [logos_ir::ir::SortKey {
            field_index: 1,
            direction: SortDirection::Descending,
            null_direction: Some(SortNullDirection::First),
        }]
    ));
    assert_eq!(offset.as_ref().map(|expr| expr.raw.as_str()), Some("1"));
    assert_eq!(fetch.as_ref().map(|expr| expr.raw.as_str()), Some("2"));
    assert!(matches!(
        input.as_ref(),
        RelExpr::Project { input, .. }
            if matches!(input.as_ref(), RelExpr::TableScan { .. })
    ));

    let lowered = lower_query(query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("expected outer project to survive across the wrapper/IR boundary");
    };
    let FormalQueryExpr::Fetch { input, count } = input.as_ref() else {
        panic!("expected nested FETCH");
    };
    assert_eq!(*count, 2);
    let FormalQueryExpr::Offset { input, count } = input.as_ref() else {
        panic!("expected nested OFFSET");
    };
    assert_eq!(*count, 1);
    assert!(matches!(input.as_ref(), FormalQueryExpr::OrderBy { .. }));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Project"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(module.rocq_module.contains("QExpr_Offset"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_fetch_over_division_uses_declarative_list_semantics() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-fetch-demand-boundary-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(&schema_path, "create table t(x integer);\n").expect("write wrapper schema");
    fs::write(
        &query_path,
        "select 10 / x from t fetch first 1 row only;\n",
    )
    .expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
    let query = &ir.queries[0];
    let RelExpr::Sort { input, fetch, .. } = &query.rel else {
        panic!("expected Calcite LogicalSort around the projected division");
    };
    assert!(fetch.is_some());
    assert!(matches!(input.as_ref(), RelExpr::Project { .. }));
    assert!(rel_expr_may_raise_runtime(input));

    let lowered = lower_query(query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Fetch { count, input }) = lowered.query_expr.as_ref() else {
        panic!("FETCH must remain a declarative list operator");
    };
    assert_eq!(*count, 1);
    let FormalQueryExpr::Projection { select, .. } = input.as_ref() else {
        panic!("FETCH must still consume the complete logical division projection");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::Call {
                operator: ScalarOperator::Divide(ScalarNumericKind::Int32),
                ..
            },
            ..
        }]
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(module.rocq_module.contains("QExpr_Project"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_fetch_zero_preserves_oversized_offset_rejection() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-fetch-zero-offset-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(&schema_path, "create table t(a integer);\n").expect("write wrapper schema");
    fs::write(
        &query_path,
        "select a from t offset 9223372036854775808 rows fetch next 0 rows only;\n",
    )
    .expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let raw_offset = raw.queries[0]
        .rel
        .as_ref()
        .and_then(|rel| rel.offset_rex.as_ref())
        .expect("wrapper offset RexLiteral");
    assert_eq!(
        raw_offset.literal_value2.as_deref(),
        Some("9223372036854775808"),
        "DECIMAL unscaled payload must not wrap through signed BIGINT"
    );
    assert_eq!(
        raw_offset.source_text.as_deref(),
        Some("9223372036854775808")
    );

    let mut wrapped_payload = raw.clone();
    wrapped_payload.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .offset_rex
        .as_mut()
        .unwrap()
        .literal_value2 = Some("-9223372036854775808".to_owned());
    assert!(
        convert_raw_file(wrapped_payload).is_err(),
        "a wrapped Calcite payload must remain fail-closed"
    );

    let mut rendered_scale_drift = raw.clone();
    rendered_scale_drift.queries[0]
        .rel
        .as_mut()
        .unwrap()
        .offset_rex
        .as_mut()
        .unwrap()
        .source_sql = Some("9223372036854775808.0".to_owned());
    let exact_ir = convert_raw_file(rendered_scale_drift)
        .expect("rendered sourceSql must not override exact sourceText");
    let RelExpr::Sort { offset, .. } = &exact_ir.queries[0].rel else {
        panic!("expected exact rendered-drift LogicalSort");
    };
    assert!(matches!(
        offset.as_ref().map(|offset| &offset.parsed),
        Some(ScalarAst::TypeAnnotation { expr, .. })
            if matches!(expr.as_ref(), ScalarAst::Literal { raw }
                if raw == "9223372036854775808")
    ));

    let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
    let query = &ir.queries[0];
    let RelExpr::Sort { fetch, offset, .. } = &query.rel else {
        panic!("expected Calcite LogicalSort");
    };
    assert_eq!(fetch.as_ref().map(|expr| expr.raw.as_str()), Some("0"));
    assert!(
        offset
            .as_ref()
            .is_some_and(|expr| expr.raw.contains("9223372036854775808"))
    );

    let lowered = lower_query(query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered_query_expr(&lowered).is_none());
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "row_count_out_of_bigint_range")
    );

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_row_in_reaches_exact_componentwise_formula() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!("logos-solver-row-in-e2e-{}", std::process::id()));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(
        &schema_path,
        "create table outer_values(a integer, b integer);\ncreate table inner_values(a integer, b integer);\n",
    )
    .expect("write wrapper schema");
    fs::write(
        &query_path,
        "select a, b from outer_values where (a, b) in (select a, b from inner_values);\n",
    )
    .expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let ir = convert_raw_file(raw).expect("convert wrapper output to Logos IR");
    let query = &ir.queries[0];

    let lowered = lower_query(query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("expected Calcite's final projection");
    };
    let FormalQueryExpr::Selection { predicate, .. } = input.as_ref() else {
        panic!("expected exact row-IN selection");
    };
    let FormalScalarExpr::In { args, .. } = predicate else {
        panic!("expected exact componentwise IN predicate");
    };
    assert_eq!(args.len(), 2);

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_In"));
    assert!(!module.rocq_module.contains("__logos_in_"));
    assert!(!module.rocq_module.contains("QExpr_Set Union"));

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
fn lowers_exists_with_nested_sort_fetch_to_recursive_scalar_expr() {
    let outer_output = vec![column("a")];
    let subquery_output = vec![column("b")];
    let subquery = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["u".to_owned()],
            output: subquery_output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Descending,
            null_direction: Some(SortNullDirection::First),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "2".to_owned(),
        })),
        offset: None,
        output: subquery_output,
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: Vec::new(),
            output: outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("outer filter should lower compositionally");
    };
    let FormalScalarExpr::Exists { query } = predicate else {
        panic!("EXISTS must embed a query-expression subquery");
    };
    assert!(matches!(query.as_ref(), FormalQueryExpr::Fetch { .. }));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(module.rocq_module.contains("QExpr_Filter"));
    assert_eq!(
        emitted_definition_shape(&module, "source_query_expr"),
        "@shared_query_expr_0"
    );
    let shared_shape = emitted_definition_shape(&module, "shared_query_expr_0");
    assert!(shared_shape.starts_with("QExpr_Project("), "{shared_shape}");
    assert!(
        shared_shape.contains("QExpr_Filter(@scalar_expr_predicate_0,"),
        "{shared_shape}"
    );
    assert!(
        module
            .definition_graph
            .definitions
            .iter()
            .any(|definition| definition.symbol == "scalar_expr_predicate_0"
                && definition.tree.contains("SExpr_Exists")
                && definition
                    .tree
                    .contains("QExpr_Fetch{count=2}(QExpr_OrderBy{keys=1}(")
                && definition.tree.contains("QExpr_Table{columns=1}"))
    );
}

#[test]
fn lowers_select_in_to_one_nullable_boolean_scalar_projection() {
    let input = vec![typed_column("a", SqlType::Integer)];
    let subquery_output = vec![typed_column("b", SqlType::Integer)];
    let subquery = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["u".to_owned()],
            output: subquery_output.clone(),
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: subquery_output,
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "IN".to_owned(),
                op: ScalarOp::In,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::RelSubquery {
                        rel: Box::new(subquery),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("member", SqlType::Boolean)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Projection { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("three-valued IN projection should use one typed scalar projection");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::BooleanValue { expression },
            ..
        }] if matches!(expression.as_ref(), FormalScalarExpr::In { .. })
    ));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_BoolValue"));
    assert!(module.rocq_module.contains("SExpr_In"));
    let nested_select = module
        .rocq_module
        .find("Definition scalar_select_list_0")
        .expect("typed IN subquery select-list definition");
    let containing_select = module
        .rocq_module
        .find("Definition scalar_select_list_1")
        .expect("containing typed IN select-list definition");
    assert!(
        nested_select < containing_select,
        "nested scalar select lists must be emitted before their containers"
    );
    let nested_certificate = module
        .rocq_module
        .find("Lemma scalar_select_list_0_admissible_row_select_generated_schema")
        .expect("typed IN subquery select-list certificate");
    let containing_certificate = module
        .rocq_module
        .find("Lemma scalar_select_list_1_admissible_row_select_generated_schema")
        .expect("containing typed IN select-list certificate");
    assert!(
        nested_certificate < containing_certificate,
        "nested scalar select-list certificates must precede their users"
    );
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
}

#[test]
fn lowers_select_not_in_once_inside_nullable_boolean_scalar_projection() {
    let outer_input = vec![typed_column("a", SqlType::Integer)];
    let subquery_output = vec![typed_column("b", SqlType::Integer)];
    let subquery = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["u".to_owned()],
            output: subquery_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: "a".to_owned(),
                    index: Some(0),
                    ty: SqlType::Integer,
                },
            ],
        }),
        correlations: Vec::new(),
        output: subquery_output,
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: outer_input.clone(),
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "NOT".to_owned(),
                op: ScalarOp::Not,
                args: vec![ScalarAst::Call {
                    operator: "IN".to_owned(),
                    op: ScalarOp::In,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::RelSubquery {
                            rel: Box::new(subquery),
                        },
                    ],
                }],
            })],
            correlations: vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: outer_input,
            }],
            output: vec![typed_column("not_member", SqlType::Boolean)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("three-valued NOT IN projection should use one scalar projection");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::BooleanValue { expression },
            ..
        }] if matches!(
            expression.as_ref(),
            FormalScalarExpr::Not { expression }
                if matches!(expression.as_ref(), FormalScalarExpr::In { .. })
        )
    ));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("@SExpr_Not TNull relname (@SExpr_In TNull relname")
    );
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
}

#[test]
fn lowers_select_exists_once_to_boolean_scalar_projection() {
    let input = vec![typed_column("a", SqlType::Integer)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(RelExpr::TableScan {
                        table: vec!["u".to_owned()],
                        output: vec![typed_column("b", SqlType::Integer)],
                    }),
                }],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("present", SqlType::Boolean)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Projection { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("EXISTS projection should use one typed scalar projection");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::BooleanValue { expression },
            ..
        }] if matches!(expression.as_ref(), FormalScalarExpr::Exists { .. })
    ));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
}

#[test]
fn lowers_boolean_subquery_projection_over_inner_join_without_wrapper() {
    let joined_output = vec![
        typed_column("a", SqlType::Integer),
        typed_column("b", SqlType::Integer),
    ];
    let input = RelExpr::Join {
        left: Box::new(RelExpr::TableScan {
            table: vec!["l".to_owned()],
            output: vec![joined_output[0].clone()],
        }),
        right: Box::new(RelExpr::TableScan {
            table: vec!["r".to_owned()],
            output: vec![joined_output[1].clone()],
        }),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 1 },
            ],
        }),
        correlations: Vec::new(),
        output: joined_output,
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(input),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(RelExpr::TableScan {
                        table: vec!["u".to_owned()],
                        output: vec![typed_column("c", SqlType::Integer)],
                    }),
                }],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("present", SqlType::Boolean)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    assert!(matches!(
        lowered.query_expr.as_ref(),
        Some(FormalQueryExpr::Projection { .. })
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_CrossJoin"));
    assert!(module.rocq_module.contains("QExpr_Filter"));
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
    assert!(!module.rocq_module.contains("QExpr_Unordered"));
}

#[test]
fn lowers_join_over_nested_order_to_permutation_closed_result() {
    let left_output = vec![column("a")];
    let right_output = vec![column("b")];
    let ordered_left = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["l".to_owned()],
            output: left_output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: None,
        offset: None,
        output: left_output.clone(),
    };
    let output = vec![column("a"), column("b")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(ordered_left),
            right: Box::new(RelExpr::TableScan {
                table: vec!["r".to_owned()],
                output: right_output,
            }),
            join_type: JoinType::Inner,
            condition: scalar(ScalarAst::Call {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Selection { input: joined, .. }) = lowered.query_expr.as_ref() else {
        panic!("theta join should filter the cartesian product");
    };
    let FormalQueryExpr::CrossJoin { left, right } = joined.as_ref() else {
        panic!("theta join should retain an explicit query-expression cartesian product");
    };
    let FormalQueryExpr::Projection {
        input: ordered_input,
        ..
    } = left.as_ref()
    else {
        panic!("join input alignment should preserve the ordered child");
    };
    assert!(matches!(
        ordered_input.as_ref(),
        FormalQueryExpr::OrderBy { .. }
    ));
    assert!(matches!(right.as_ref(), FormalQueryExpr::Projection { .. }));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(!module.rocq_module.contains("QExpr_Unordered"));
    assert!(module.rocq_module.contains("QExpr_CrossJoin"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
}

#[test]
fn lowers_semi_join_over_ordered_input_with_one_shared_child() {
    let left_output = vec![column("a")];
    let ordered_left = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["l".to_owned()],
            output: left_output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "3".to_owned(),
        })),
        offset: None,
        output: left_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(ordered_left),
            right: Box::new(RelExpr::TableScan {
                table: vec!["r".to_owned()],
                output: vec![column("b")],
            }),
            join_type: JoinType::Semi,
            condition: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            }),
            correlations: Vec::new(),
            output: left_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Join {
        join_kind,
        left,
        right,
        ..
    }) = lowered.query_expr.as_ref()
    else {
        panic!("semi join must use the native shared-child reset operator");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Semi);
    let FormalQueryExpr::Projection { input, .. } = left.as_ref() else {
        panic!("join input should retain its alignment projection");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Fetch { .. }));
    assert!(matches!(right.as_ref(), FormalQueryExpr::Projection { .. }));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Join QueryJoinSemi"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));

    let mut anti_query = query.clone();
    let RelExpr::Join { join_type, .. } = &mut anti_query.rel else {
        unreachable!();
    };
    *join_type = JoinType::Anti;
    let anti_lowered = lower_query(&anti_query);
    assert_eq!(anti_lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Join { join_kind, .. }) = anti_lowered.query_expr.as_ref() else {
        panic!("anti join must use the native shared-child reset operator");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Anti);
}

fn integral_cast_input(index: usize, target: &str) -> ScalarAst {
    ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::InputRef { index }],
        }),
        ty: target.to_owned(),
    }
}

fn equality_condition(left: ScalarAst, right: ScalarAst) -> ScalarAst {
    ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![left, right],
    }
}

#[test]
fn join_runtime_risk_authority_tracks_exact_positional_types_for_every_kind() {
    for join_type in [
        JoinType::Inner,
        JoinType::Left,
        JoinType::Right,
        JoinType::Full,
        JoinType::Semi,
        JoinType::Anti,
    ] {
        let left_column = Column {
            name: "left_source".to_owned(),
            ty: SqlType::Integer,
            nullable: false,
        };
        let right_column = Column {
            name: "right_source".to_owned(),
            ty: SqlType::BigInt,
            nullable: false,
        };
        let left = RelExpr::TableScan {
            table: vec!["left_table".to_owned()],
            output: vec![left_column],
        };
        let right = RelExpr::TableScan {
            table: vec!["right_table".to_owned()],
            output: vec![right_column],
        };
        let output = match join_type {
            JoinType::Semi | JoinType::Anti => vec![Column {
                name: "renamed_left".to_owned(),
                ty: SqlType::Integer,
                nullable: false,
            }],
            JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => vec![
                Column {
                    name: "renamed_left".to_owned(),
                    ty: SqlType::Integer,
                    nullable: matches!(join_type, JoinType::Right | JoinType::Full),
                },
                Column {
                    name: "renamed_right".to_owned(),
                    ty: SqlType::BigInt,
                    nullable: matches!(join_type, JoinType::Left | JoinType::Full),
                },
            ],
        };
        let nested = RelExpr::Join {
            left: Box::new(left),
            right: Box::new(right),
            join_type,
            condition: scalar(ScalarAst::Literal {
                raw: "true".to_owned(),
            }),
            correlations: Vec::new(),
            output,
        };
        let comparison_input = RelExpr::TableScan {
            table: vec!["comparison_table".to_owned()],
            output: vec![typed_column("comparison_value", SqlType::BigInt)],
        };
        let condition = equality_condition(
            integral_cast_input(0, "BIGINT"),
            ScalarAst::InputRef {
                index: nested.output().len(),
            },
        );

        assert!(
            !super::scalar::join_condition_may_raise_runtime(
                &nested,
                &comparison_input,
                &condition,
            ),
            "{join_type:?} should preserve exact positional type authority"
        );
    }
}

#[test]
fn lowers_widening_cast_condition_through_nested_authoritative_join() {
    let nested_output = vec![
        typed_column("left_integer", SqlType::Integer),
        typed_column("right_bigint", SqlType::BigInt),
    ];
    let nested = RelExpr::Join {
        left: Box::new(RelExpr::TableScan {
            table: vec!["left_table".to_owned()],
            output: vec![typed_column("left_source", SqlType::Integer)],
        }),
        right: Box::new(RelExpr::TableScan {
            table: vec!["right_table".to_owned()],
            output: vec![typed_column("right_source", SqlType::BigInt)],
        }),
        join_type: JoinType::Inner,
        condition: scalar(equality_condition(
            integral_cast_input(0, "BIGINT"),
            ScalarAst::InputRef { index: 1 },
        )),
        correlations: Vec::new(),
        output: nested_output.clone(),
    };
    let comparison_output = vec![typed_column("comparison_bigint", SqlType::BigInt)];
    let mut output = nested_output;
    output.extend(comparison_output.clone());
    let query = Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(nested),
            right: Box::new(RelExpr::TableScan {
                table: vec!["comparison_table".to_owned()],
                output: comparison_output,
            }),
            join_type: JoinType::Inner,
            condition: scalar(equality_condition(
                integral_cast_input(0, "BIGINT"),
                ScalarAst::InputRef { index: 2 },
            )),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastInt32ToInt64")
    );
}

#[test]
fn join_runtime_risk_authority_rejects_stale_shape_and_narrowing() {
    let base_left = || RelExpr::TableScan {
        table: vec!["left_table".to_owned()],
        output: vec![typed_column("left_source", SqlType::Integer)],
    };
    let base_right = || RelExpr::TableScan {
        table: vec!["right_table".to_owned()],
        output: vec![typed_column("right_source", SqlType::BigInt)],
    };
    let comparison_bigint = RelExpr::TableScan {
        table: vec!["comparison_table".to_owned()],
        output: vec![typed_column("comparison_value", SqlType::BigInt)],
    };
    let widening = |right_index| {
        equality_condition(
            integral_cast_input(0, "BIGINT"),
            ScalarAst::InputRef { index: right_index },
        )
    };

    let stale_type = RelExpr::Join {
        left: Box::new(base_left()),
        right: Box::new(base_right()),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: vec![
            typed_column("stale_left", SqlType::BigInt),
            typed_column("right_bigint", SqlType::BigInt),
        ],
    };
    assert!(super::scalar::join_condition_may_raise_runtime(
        &stale_type,
        &comparison_bigint,
        &widening(2),
    ));

    let stale_arity = RelExpr::Join {
        left: Box::new(base_left()),
        right: Box::new(base_right()),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: vec![typed_column("left_integer", SqlType::Integer)],
    };
    assert!(super::scalar::join_condition_may_raise_runtime(
        &stale_arity,
        &comparison_bigint,
        &widening(1),
    ));

    let narrowing_nested = RelExpr::Join {
        left: Box::new(base_right()),
        right: Box::new(base_left()),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: vec![
            typed_column("left_bigint", SqlType::BigInt),
            typed_column("right_integer", SqlType::Integer),
        ],
    };
    let comparison_integer = RelExpr::TableScan {
        table: vec!["comparison_integer_table".to_owned()],
        output: vec![typed_column("comparison_integer", SqlType::Integer)],
    };
    let narrowing = equality_condition(
        integral_cast_input(0, "INTEGER"),
        ScalarAst::InputRef { index: 2 },
    );
    assert!(super::scalar::join_condition_may_raise_runtime(
        &narrowing_nested,
        &comparison_integer,
        &narrowing,
    ));
}

#[test]
fn runtime_risk_authority_crosses_only_exact_passthrough_project_and_union_all() {
    let source_scan = || RelExpr::TableScan {
        table: vec!["source_table".to_owned()],
        output: vec![typed_column("source_integer", SqlType::Integer)],
    };
    let projected = RelExpr::Project {
        input: Box::new(source_scan()),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![typed_column("projected_integer", SqlType::Integer)],
    };
    let aggregate = RelExpr::Aggregate {
        input: Box::new(source_scan()),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: Vec::new(),
        output: vec![typed_column("grouped_integer", SqlType::Integer)],
    };
    let set = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![source_scan(), source_scan()],
        output: vec![typed_column("union_integer", SqlType::Integer)],
    };
    let comparison_input = RelExpr::TableScan {
        table: vec!["comparison_table".to_owned()],
        output: vec![typed_column("comparison_bigint", SqlType::BigInt)],
    };
    let condition = equality_condition(
        integral_cast_input(0, "BIGINT"),
        ScalarAst::InputRef { index: 1 },
    );

    for (label, passthrough) in [("project", projected), ("union all", set)] {
        assert!(
            !super::scalar::join_condition_may_raise_runtime(
                &passthrough,
                &comparison_input,
                &condition,
            ),
            "{label} has exact source-type lineage for its bare input position"
        );
    }
    assert!(
        super::scalar::join_condition_may_raise_runtime(&aggregate, &comparison_input, &condition,),
        "aggregate output metadata must remain non-authoritative"
    );

    let computed_project = RelExpr::Project {
        input: Box::new(source_scan()),
        exprs: vec![scalar(integral_cast_input(0, "BIGINT"))],
        correlations: Vec::new(),
        output: vec![typed_column("forged_integer", SqlType::Integer)],
    };
    let correlated_project = RelExpr::Project {
        input: Box::new(source_scan()),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: vec![CorrelationBinding {
            correlation: "$cor0".to_owned(),
            output: vec![typed_column("source_integer", SqlType::Integer)],
        }],
        output: vec![typed_column("correlated_integer", SqlType::Integer)],
    };
    let union_distinct = RelExpr::Set {
        op: SetOp::Union,
        all: false,
        inputs: vec![source_scan(), source_scan()],
        output: vec![typed_column("union_integer", SqlType::Integer)],
    };
    let disagreeing_union = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![
            source_scan(),
            RelExpr::TableScan {
                table: vec!["bigint_source".to_owned()],
                output: vec![typed_column("source_bigint", SqlType::BigInt)],
            },
        ],
        output: vec![typed_column("stale_union_integer", SqlType::Integer)],
    };
    for (label, barrier) in [
        ("computed project", computed_project),
        ("correlated project", correlated_project),
        ("UNION DISTINCT", union_distinct),
        ("type-disagreeing UNION ALL", disagreeing_union),
    ] {
        assert!(
            super::scalar::join_condition_may_raise_runtime(
                &barrier,
                &comparison_input,
                &condition,
            ),
            "{label} must not create runtime-risk type authority"
        );
    }
}

#[test]
fn decimal_widening_authority_is_per_column_through_project_union_and_join() {
    let decimal_7_2 = SqlType::Decimal {
        precision: Some(7),
        scale: Some(2),
    };
    let decimal_12_2 = SqlType::Decimal {
        precision: Some(12),
        scale: Some(2),
    };
    let branch = |table: &str| RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec![table.to_owned()],
            output: vec![typed_column("wholesale_cost", decimal_7_2.clone())],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![typed_column("wholesale_cost", decimal_7_2.clone())],
    };
    let union = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![branch("catalog_sales"), branch("web_sales")],
        output: vec![typed_column("wholesale_cost", decimal_7_2.clone())],
    };
    let widening = integral_cast_input(1, "DECIMAL(12,2)");
    let narrowing = integral_cast_input(1, "DECIMAL(6,2)");

    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["store_sales".to_owned()],
            output: vec![typed_column("store_cost", decimal_7_2.clone())],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: Vec::new(),
        output: vec![typed_column("derived", SqlType::BigInt)],
    };
    let joined = RelExpr::Join {
        left: Box::new(aggregate),
        right: Box::new(union),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: vec![
            typed_column("derived", SqlType::BigInt),
            typed_column("wholesale_cost", decimal_7_2.clone()),
        ],
    };

    assert!(
        !super::scalar::scalar_ast_may_raise_runtime_for_input(&widening, &joined),
        "an exact DECIMAL(7,2) lineage proves DECIMAL(12,2) widening total even beside an unknown aggregate output"
    );
    assert!(
        super::scalar::scalar_ast_may_raise_runtime_for_input(&narrowing, &joined),
        "per-column authority must not make a narrowing DECIMAL cast total"
    );

    let stale_project = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["stale_source".to_owned()],
            output: vec![typed_column("wholesale_cost", decimal_12_2)],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![typed_column("forged_cost", decimal_7_2)],
    };
    assert!(super::scalar::scalar_ast_may_raise_runtime_for_input(
        &integral_cast_input(0, "DECIMAL(12,2)"),
        &stale_project,
    ));
}

#[test]
fn stale_nested_annotation_does_not_prove_widening_cast_total() {
    let nested = RelExpr::Join {
        left: Box::new(RelExpr::TableScan {
            table: vec!["left_table".to_owned()],
            output: vec![typed_column("left_integer", SqlType::Integer)],
        }),
        right: Box::new(RelExpr::TableScan {
            table: vec!["right_table".to_owned()],
            output: vec![typed_column("right_bigint", SqlType::BigInt)],
        }),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: vec![
            typed_column("left_integer", SqlType::Integer),
            typed_column("right_bigint", SqlType::BigInt),
        ],
    };
    let comparison_input = RelExpr::TableScan {
        table: vec!["comparison_table".to_owned()],
        output: vec![typed_column("comparison_bigint", SqlType::BigInt)],
    };
    let stale_arg = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::InputRef { index: 0 }),
        ty: "BIGINT".to_owned(),
    };
    let condition = equality_condition(
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![stale_arg],
            }),
            ty: "BIGINT".to_owned(),
        },
        ScalarAst::InputRef { index: 2 },
    );

    assert!(super::scalar::join_condition_may_raise_runtime(
        &nested,
        &comparison_input,
        &condition,
    ));
}

fn source_attested_false_filter(input: RelExpr) -> RelExpr {
    let output = input.output().to_vec();
    RelExpr::Filter {
        input: Box::new(input),
        predicate: scalar_with_source(
            ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "2".to_owned(),
                    },
                ],
            },
            source_node(
                "1 = 2",
                "EQUALS",
                Some("="),
                vec![
                    source_node("1", "LITERAL", None, Vec::new()),
                    source_node("2", "LITERAL", None, Vec::new()),
                ],
            ),
        ),
        correlations: Vec::new(),
        output,
    }
}

fn failing_integer_division() -> ScalarAst {
    ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    }
}

fn window_project_with_frame(input: RelExpr, frame: WindowFrameAst) -> RelExpr {
    let output = vec![typed_column("rn", SqlType::BigInt)];
    RelExpr::Project {
        input: Box::new(input),
        exprs: vec![scalar(ScalarAst::Window {
            parsed: WindowAst {
                function: "ROW_NUMBER".to_owned(),
                args: Vec::new(),
                partition_by: Vec::new(),
                order_by: Vec::new(),
                distinct: false,
                ignore_nulls: false,
                exclude: Some("EXCLUDE_NO_OTHER".to_owned()),
                frame: Some(frame),
            },
        })],
        correlations: Vec::new(),
        output,
    }
}

fn static_empty_inner_join_query(empty_input: RelExpr, condition: ScalarAst) -> Query {
    let left = source_attested_false_filter(empty_input);
    let right = RelExpr::TableScan {
        table: vec!["live_rows".to_owned()],
        output: vec![column("live_key")],
    };
    let mut output = left.output().to_vec();
    output.extend_from_slice(right.output());
    Query {
        source_sql: Some(
            "SELECT * FROM dead_rows d JOIN live_rows l ON true WHERE 1 = 2".to_owned(),
        ),
        rel: RelExpr::Join {
            left: Box::new(left),
            right: Box::new(right),
            join_type: JoinType::Inner,
            condition: scalar(condition),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

#[test]
fn declarative_window_rejects_unrepresented_frame_offset_expression() {
    let dead_window = window_project_with_frame(
        RelExpr::TableScan {
            table: vec!["dead_rows".to_owned()],
            output: vec![column("dead_key")],
        },
        WindowFrameAst {
            units: WindowFrameUnits::Rows,
            start: WindowFrameBoundAst::OffsetPreceding {
                raw: "/(1, 0)".to_owned(),
                expr: Box::new(failing_integer_division()),
            },
            end: Some(WindowFrameBoundAst::CurrentRow),
        },
    );
    let query = static_empty_inner_join_query(
        dead_window,
        ScalarAst::Literal {
            raw: "true".to_owned(),
        },
    );

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered_query_expr(&lowered).is_none());
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "window_shape_not_supported" && diagnostic.path.ends_with("exprs[0]")
        }),
        "{:#?}",
        lowered.diagnostics
    );
}

#[test]
fn declarative_window_rejects_nullable_row_number_metadata() {
    let dead_window = window_project_with_frame(
        RelExpr::TableScan {
            table: vec!["dead_rows".to_owned()],
            output: vec![column("dead_key")],
        },
        WindowFrameAst {
            units: WindowFrameUnits::Rows,
            start: WindowFrameBoundAst::UnboundedPreceding,
            end: Some(WindowFrameBoundAst::CurrentRow),
        },
    );
    let query = static_empty_inner_join_query(
        dead_window,
        ScalarAst::Literal {
            raw: "true".to_owned(),
        },
    );

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.query_expr.is_none());
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "row_number_output_type_not_supported"
            && diagnostic.path.ends_with("output[0]")
    }));
}

#[test]
fn declarative_window_rejects_invalid_window_frame_ordering() {
    let invalid_frames = [
        (
            "unbounded-following start",
            WindowFrameAst {
                units: WindowFrameUnits::Rows,
                start: WindowFrameBoundAst::UnboundedFollowing,
                end: Some(WindowFrameBoundAst::UnboundedFollowing),
            },
        ),
        (
            "unbounded-preceding end",
            WindowFrameAst {
                units: WindowFrameUnits::Range,
                start: WindowFrameBoundAst::UnboundedPreceding,
                end: Some(WindowFrameBoundAst::UnboundedPreceding),
            },
        ),
        (
            "reversed offset categories",
            WindowFrameAst {
                units: WindowFrameUnits::Rows,
                start: WindowFrameBoundAst::OffsetFollowing {
                    raw: "1".to_owned(),
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1".to_owned(),
                    }),
                },
                end: Some(WindowFrameBoundAst::OffsetPreceding {
                    raw: "1".to_owned(),
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1".to_owned(),
                    }),
                }),
            },
        ),
    ];
    for (label, frame) in invalid_frames {
        assert!(!frame.is_valid_postgres(), "{label}");
        let dead_window = window_project_with_frame(
            RelExpr::TableScan {
                table: vec!["dead_rows".to_owned()],
                output: vec![column("dead_key")],
            },
            frame,
        );
        let query = static_empty_inner_join_query(
            dead_window,
            ScalarAst::Literal {
                raw: "true".to_owned(),
            },
        );
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code == "window_shape_not_supported" }),
            "{label}: {:#?}",
            lowered.diagnostics
        );
    }
}

#[test]
fn logical_filter_over_inner_join_lowers_without_plan_admission() {
    let left = RelExpr::TableScan {
        table: vec!["left_rows".to_owned()],
        output: vec![column("left_value")],
    };
    let right = RelExpr::TableScan {
        table: vec!["right_rows".to_owned()],
        output: vec![column("right_value")],
    };
    let join_output = vec![column("left_value"), column("right_value")];
    let join = RelExpr::Join {
        left: Box::new(left),
        right: Box::new(right),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: join_output.clone(),
    };
    let total_side_local = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    let query = query_for_rel(
        RelExpr::Filter {
            input: Box::new(join),
            predicate: scalar(total_side_local),
            correlations: Vec::new(),
            output: join_output.clone(),
        },
        join_output,
    );
    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "total-side-local: {:#?}",
        lowered.diagnostics
    );
}

#[test]
fn lowers_outer_join_with_tied_top_one_as_one_native_child() {
    let left_output = vec![column("k"), column("payload")];
    let top_one = RelExpr::Sort {
        input: Box::new(RelExpr::Values {
            rows: vec![
                vec![
                    scalar(ScalarAst::Literal {
                        raw: "0".to_owned(),
                    }),
                    scalar(ScalarAst::Literal {
                        raw: "10".to_owned(),
                    }),
                ],
                vec![
                    scalar(ScalarAst::Literal {
                        raw: "0".to_owned(),
                    }),
                    scalar(ScalarAst::Literal {
                        raw: "20".to_owned(),
                    }),
                ],
            ],
            output: left_output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })),
        offset: None,
        output: left_output.clone(),
    };
    let right_output = vec![column("wanted")];
    let mut output = left_output.clone();
    output.extend(right_output.clone());
    let query = Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(top_one),
            right: Box::new(one_row_values(
                right_output,
                vec![ScalarAst::Literal {
                    raw: "10".to_owned(),
                }],
            )),
            join_type: JoinType::Left,
            condition: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 1 },
                    ScalarAst::InputRef { index: 2 },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Join {
        join_kind,
        left,
        right,
        ..
    }) = lowered.query_expr.as_ref()
    else {
        panic!("outer join should lower to one native join node");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Left);
    let FormalQueryExpr::Projection { input, .. } = left.as_ref() else {
        panic!("left child should have one alignment projection");
    };
    assert!(matches!(
        input.as_ref(),
        FormalQueryExpr::Fetch { count: 1, .. }
    ));
    assert!(matches!(right.as_ref(), FormalQueryExpr::Projection { .. }));
}

#[test]
fn outer_join_preserves_fixed_numeric_scale_for_downstream_division() {
    let left_output = vec![decimal_column("left_amount", 7, 2)];
    let right_output = vec![decimal_column("right_amount", 7, 2)];
    let mut join_output = left_output.clone();
    join_output.extend(right_output.clone());
    let result = vec![decimal_column_unconstrained("ratio")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::Join {
                left: Box::new(RelExpr::Sort {
                    input: Box::new(RelExpr::TableScan {
                        table: vec!["left_values".to_owned()],
                        output: left_output.clone(),
                    }),
                    collation: vec![logos_ir::ir::SortKey {
                        field_index: 0,
                        direction: SortDirection::Ascending,
                        null_direction: Some(SortNullDirection::Last),
                    }],
                    fetch: None,
                    offset: None,
                    output: left_output,
                }),
                right: Box::new(RelExpr::TableScan {
                    table: vec!["right_values".to_owned()],
                    output: right_output,
                }),
                join_type: JoinType::Left,
                condition: scalar(ScalarAst::Literal {
                    raw: "true".to_owned(),
                }),
                correlations: Vec::new(),
                output: join_output,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: result.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("expected ratio projection");
    };
    let FormalQueryExpr::Join {
        matched_select,
        left_select,
        right_select,
        ..
    } = input.as_ref()
    else {
        panic!("expected native declarative outer join");
    };
    for select in [matched_select, left_select, right_select] {
        assert!(
            select
                .iter()
                .all(|item| { item.numeric_dscale == Some(NumericDscaleProvenance::Exact(2)) })
        );
    }
}

#[test]
fn lowers_set_distinct_over_top_k_inputs_to_permutation_closed_operators() {
    let output = vec![column("a")];
    let top_k = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["l".to_owned()],
            output: output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "2".to_owned(),
        })),
        offset: None,
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Set {
            op: SetOp::Union,
            all: false,
            inputs: vec![
                top_k,
                RelExpr::TableScan {
                    table: vec!["r".to_owned()],
                    output: output.clone(),
                },
            ],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Distinct { input }) = lowered.query_expr.as_ref() else {
        panic!("UNION DISTINCT should retain an explicit permutation-closing duplicate operator");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Set { .. }));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Distinct"));
    assert!(module.rocq_module.contains("QExpr_Set Union"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
}

#[test]
fn lowers_group_over_top_k_input_to_permutation_closed_group() {
    let output = vec![column("a")];
    let top_k = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "2".to_owned(),
        })),
        offset: None,
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(top_k),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Group { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("grouping should remain an explicit permutation-closing operator");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Fetch { .. }));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
}

#[test]
fn lowers_grouping_sets_with_one_shared_child_and_typed_absent_key_nulls() {
    let input_output = vec![
        typed_column("small_key", SqlType::Integer),
        typed_column("large_key", SqlType::BigInt),
    ];
    let input = RelExpr::TableScan {
        table: vec!["grouping_values".to_owned()],
        output: input_output.clone(),
    };
    let query = Query {
        source_sql: Some(
            "SELECT small_key, large_key FROM grouping_values GROUP BY GROUPING SETS ((small_key, large_key), (small_key))"
                .to_owned(),
        ),
        rel: RelExpr::Aggregate {
            input: Box::new(input),
            group_keys: vec![0, 1],
            grouping_sets: vec![vec![0, 1], vec![0]],
            agg_calls: Vec::new(),
            output: input_output.clone(),
        },
                analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::GroupingSets {
        grouping_sets,
        input,
    }) = lowered_query_expr(&lowered)
    else {
        panic!("multiple grouping sets must use one shared-child node");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Table { .. }));
    assert_eq!(grouping_sets.len(), 2);
    let full = &grouping_sets[0];
    let partial = &grouping_sets[1];
    assert_eq!(full.group_by.len(), 2);
    assert_eq!(partial.group_by.len(), 1);
    assert!(matches!(
        &full.select[1].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    ty: FormalAttributeType::Int64,
                    ..
                }
            },
            ..
        }
    ));
    assert_eq!(partial.select[1].alias_ty, FormalAttributeType::Int64);
    assert!(matches!(
        &partial.select[1].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw,
                    ty: Some(FormalAttributeType::Int64),
                }
            },
            ..
        } if raw == "NULL"
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("QExpr_GroupingSets"));
    assert!(
        module
            .rocq_module
            .contains("eapply query_expr_admissible_with_outputs_grouping_sets.")
    );
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
    assert!(!module.rocq_module.contains("QExpr_Distinct"));
}

#[test]
fn empty_grouping_set_over_empty_input_uses_exact_global_group_semantics() {
    let input_output = vec![typed_column("group_key", SqlType::Integer)];
    let aggregate_output = vec![
        typed_column("group_key", SqlType::Integer),
        typed_column("row_count", SqlType::BigInt),
    ];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::Values {
            rows: Vec::new(),
            output: input_output,
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0], Vec::new()],
        agg_calls: vec![count_star_call()],
        output: aggregate_output.clone(),
    };
    let query = query_for_rel(aggregate.clone(), aggregate_output);

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::GroupingSets {
        grouping_sets,
        input,
    }) = lowered.query_expr.as_ref()
    else {
        panic!("mixed grouping sets should lower as one shared-child grouping-set node");
    };
    assert_eq!(grouping_sets.len(), 2);
    let empty_set = &grouping_sets[1];
    assert!(empty_set.group_by.is_empty());
    assert!(matches!(input.as_ref(), FormalQueryExpr::Empty { .. }));
    assert!(matches!(
        &empty_set.select[0].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw,
                    ty: Some(FormalAttributeType::Int32),
                },
            },
            ..
        } if raw == "NULL"
    ));
    assert!(matches!(
        empty_set.select[1].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::CountStar,
            ..
        }
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("QExpr_GroupingSets"));

    // The direct relational entry point must choose the same native shared
    // representation rather than falling back to branch replay.
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    assert!(matches!(
        context.lower_rel("rel", &aggregate),
        Some(FormalQueryExpr::GroupingSets { .. })
    ));
    assert!(context.diagnostics.is_empty());
}

#[test]
fn lowers_multiple_grouping_sets_over_nondeterministic_child_with_one_shared_input() {
    let output = vec![typed_column("key", SqlType::Integer)];
    let tied_top_one = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["grouping_values".to_owned()],
            output: output.clone(),
        }),
        collation: vec![SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })),
        offset: None,
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(tied_top_one),
            group_keys: vec![0],
            grouping_sets: vec![vec![0], Vec::new()],
            agg_calls: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(lowered.diagnostics.iter().all(|diagnostic| {
        diagnostic.code != "grouping_sets_shared_child_outcomes_not_supported"
    }));
    let Some(FormalQueryExpr::GroupingSets {
        grouping_sets,
        input,
    }) = lowered.query_expr.as_ref()
    else {
        panic!("multiple sets over a nondeterministic child need the shared-input constructor");
    };
    assert_eq!(grouping_sets.len(), 2);
    assert_eq!(grouping_sets[0].group_by.len(), 1);
    assert!(grouping_sets[1].group_by.is_empty());
    assert!(matches!(
        input.as_ref(),
        FormalQueryExpr::Fetch { count: 1, .. }
    ));
    assert!(matches!(
        &grouping_sets[1].select[0].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw,
                    ty: Some(FormalAttributeType::Int32),
                }
            },
            ..
        } if raw == "NULL"
    ));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_GroupingSets"));
    assert!(module.rocq_module.contains("QExpr_Fetch (1%nat)"));
}

#[test]
fn preserves_duplicate_grouping_sets_inside_one_shared_child_node() {
    let output = vec![column("key")];
    let query = Query {
        source_sql: Some(
            "SELECT key FROM grouping_values GROUP BY GROUPING SETS ((key), (key))".to_owned(),
        ),
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["grouping_values".to_owned()],
                output: output.clone(),
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0], vec![0]],
            agg_calls: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::GroupingSets {
        grouping_sets,
        input,
    }) = lowered_query_expr(&lowered)
    else {
        panic!("duplicate grouping sets must not be deduplicated during lowering");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Table { .. }));
    assert_eq!(
        grouping_sets.len(),
        2,
        "the duplicate grouping-set branch count was not preserved"
    );
    assert_eq!(
        grouping_sets[0], grouping_sets[1],
        "the duplicate grouping-set branch was not preserved"
    );

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("QExpr_GroupingSets"));
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
}

fn attested_grouping_marker(
    group_indexes: Vec<usize>,
    grouping_sets: Vec<Vec<usize>>,
) -> SourceGroupingProvenance {
    SourceGroupingProvenance {
        kind: "ROLLUP".to_owned(),
        query_block_id: "1:1-1:120".to_owned(),
        source_select_node_id: "1:1-1:120".to_owned(),
        source_select_sql:
            "SELECT a, b, GROUPING(a, b) AS g FROM grouping_values GROUP BY ROLLUP(a, b)".to_owned(),
        source_group_sql: "ROLLUP(a, b)".to_owned(),
        group_indexes,
        grouping_sets,
        source_has_where: false,
        source_has_having: false,
    }
}

fn generic_grouping_mask_query() -> Query {
    let grouping_sets = vec![vec![0, 1], vec![0], Vec::new()];
    let grouping = AggregateCall {
        raw: "GROUPING($0, $1)".to_owned(),
        function: "GROUPING".to_owned(),
        distinct: false,
        modifiers: AggregateModifiers {
            source: Some(source_node(
                "GROUPING(a, b)",
                "OTHER_FUNCTION",
                Some("GROUPING"),
                vec![
                    source_node("a", "IDENTIFIER", None, Vec::new()),
                    source_node("b", "IDENTIFIER", None, Vec::new()),
                ],
            )),
            source_distinct: Some(false),
            source_grouping: Some(attested_grouping_marker(vec![0, 1], grouping_sets.clone())),
            ..AggregateModifiers::default()
        },
        args: vec![
            scalar(ScalarAst::InputRef { index: 0 }),
            scalar(ScalarAst::InputRef { index: 1 }),
        ],
        filter: None,
    };
    let output = vec![
        column("a"),
        column("b"),
        typed_column("g", SqlType::Integer),
    ];
    query_for_rel(
        RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["grouping_values".to_owned()],
                output: vec![column("a"), column("b")],
            }),
            group_keys: vec![0, 1],
            grouping_sets,
            agg_calls: vec![grouping],
            output: output.clone(),
        },
        output,
    )
}

#[test]
fn source_attested_grouping_lowers_to_postgres_int4_branch_masks() {
    fn collect_select_mask(select: &[FormalScalarSelectItem], masks: &mut Vec<String>) {
        let item = select.iter().find(|item| item.alias == "g").unwrap();
        let FormalScalarExpr::Leaf {
            term:
                FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant { raw, ty },
                },
            ..
        } = &item.expr
        else {
            panic!("GROUPING must lower to a branch-local constant")
        };
        assert_eq!(*ty, Some(FormalAttributeType::Int32));
        masks.push(raw.clone());
    }

    fn collect_masks(query: &FormalQueryExpr, masks: &mut Vec<String>) {
        match query {
            FormalQueryExpr::Group { select, .. } => collect_select_mask(select, masks),
            FormalQueryExpr::GroupingSets { grouping_sets, .. } => {
                for set in grouping_sets {
                    collect_select_mask(&set.select, masks);
                }
            }
            FormalQueryExpr::Set { left, right, .. } => {
                collect_masks(left, masks);
                collect_masks(right, masks);
            }
            other => panic!("unexpected generic GROUPING result: {other:?}"),
        }
    }

    let query = generic_grouping_mask_query();
    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_ref().unwrap()[2].ty,
        FormalAttributeType::Int32
    );
    let mut masks = Vec::new();
    collect_masks(lowered.query_expr.as_ref().unwrap(), &mut masks);
    assert_eq!(masks, ["0", "1", "3"]);

    let mut missing = query.clone();
    let RelExpr::Aggregate { agg_calls, .. } = &mut missing.rel else {
        unreachable!()
    };
    agg_calls[0].modifiers.source_grouping = None;
    let blocked = lower_query(&missing);
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "grouping_source_sequence_not_attested")
    );

    let mut too_many = query;
    let RelExpr::Aggregate { agg_calls, .. } = &mut too_many.rel else {
        unreachable!()
    };
    agg_calls[0].args = (0..32)
        .map(|index| scalar(ScalarAst::InputRef { index: index % 2 }))
        .collect();
    let source = agg_calls[0].modifiers.source.as_mut().unwrap();
    source.operands = (0..32)
        .map(|index| {
            Some(source_node(
                if index % 2 == 0 { "a" } else { "b" },
                "IDENTIFIER",
                None,
                Vec::new(),
            ))
        })
        .collect();
    let blocked = lower_query(&too_many);
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "grouping_shape_not_supported")
    );
}

#[test]
fn rejects_malformed_grouping_set_keys_conservatively() {
    for (label, grouping_sets, expected_code) in [
        (
            "key outside complete group-key list",
            vec![vec![1]],
            "grouping_set_key_not_in_group_keys",
        ),
        (
            "duplicate key within one grouping set",
            vec![vec![0, 0]],
            "duplicate_grouping_set_key",
        ),
    ] {
        let input_output = vec![column("group_key"), column("nongrouped_value")];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["grouping_values".to_owned()],
                    output: input_output,
                }),
                group_keys: vec![0],
                grouping_sets,
                agg_calls: Vec::new(),
                output: vec![column("group_key")],
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);

        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(lowered.query_expr.is_none(), "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == expected_code),
            "{label}: {:?}",
            lowered.diagnostics
        );
    }
}

#[test]
fn overrides_stale_string_typmod_for_ordinary_and_absent_grouping_set_keys() {
    for (label, grouping_sets) in [
        ("ordinary grouping", vec![vec![0]]),
        ("absent grouping-set key", vec![Vec::new(), vec![0]]),
    ] {
        let input = vec![typed_column("key", SqlType::character(3))];
        let stale_output = vec![typed_column("key", SqlType::varchar(Some(3)))];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["grouping_values".to_owned()],
                    output: input,
                }),
                group_keys: vec![0],
                grouping_sets,
                agg_calls: Vec::new(),
                output: stale_output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);

        assert_eq!(lowered.status, LoweringStatus::Lowered, "{label}");
        assert!(lowered.query_expr.is_some(), "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code == "calcite_group_key_type_overridden" }),
            "{label}: {:?}",
            lowered.diagnostics
        );
        assert_eq!(
            lowered
                .output_signature
                .as_ref()
                .expect("group key signature")[0]
                .ty,
            FormalAttributeType::String {
                typmod: SqlStringType::Char { length: 3 },
            },
            "{label}"
        );
    }
}

#[test]
fn overrides_stale_cross_family_group_key_output_type() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["grouping_values".to_owned()],
                output: vec![typed_column("key", SqlType::Boolean)],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: Vec::new(),
            output: vec![typed_column("key", SqlType::Date)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_group_key_type_overridden")
    );
    assert_eq!(
        lowered
            .output_signature
            .as_ref()
            .expect("group key signature")[0]
            .ty,
        FormalAttributeType::Bool
    );
}

#[test]
fn rejects_string_sort_without_collation_semantics() {
    let output = vec![typed_column("name", SqlType::varchar(None))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Sort {
            input: Box::new(RelExpr::TableScan {
                table: vec!["names".to_owned()],
                output: output.clone(),
            }),
            collation: vec![logos_ir::ir::SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: None,
            offset: None,
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "string_collation_sort_not_supported")
    );
}

#[test]
fn lowers_string_sort_with_explicit_postgres_utf8_c_environment() {
    let output = vec![typed_column("name", SqlType::text())];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Sort {
            input: Box::new(RelExpr::TableScan {
                table: vec!["names".to_owned()],
                output: output.clone(),
            }),
            collation: vec![logos_ir::ir::SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: None,
            offset: None,
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_environment: SqlEnvironment::postgres_utf8_c(),
            ..LoweringConfig::default()
        },
    );
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::OrderBy { .. })
    ));
}

#[test]
fn lowers_nested_fetch_zero_to_explicit_declarative_query_expression() {
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Fetch { count: 0, input }) = lowered.query_expr else {
        panic!("FETCH 0 should remain an explicit declarative list operator");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::OrderBy { .. }));

    let mut nested_context = LoweringContext::new(LoweringConfig::default(), None);
    let nested = nested_context.lower_rel("rel", &nested_rel);
    assert!(nested.is_none());
    assert!(
        nested_context
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "query_order_behavior_analysis_mismatch" })
    );
}

#[test]
fn emits_native_empty_bag_relation() {
    let empty = FormalQueryExpr::Empty {
        columns: vec![FormalAttribute {
            name: "a".to_owned(),
            ty: FormalAttributeType::Z,
        }],
    };
    let module = emit_rocq_query_module(&empty.clone(), &empty);

    assert!(module.rocq_module.contains("QExpr_Values"));
    assert!(!module.rocq_module.contains("QExpr_Set Diff"));
}

#[test]
fn empty_tuple_admissibility_uses_the_precompiled_structural_certificate() {
    let module = emit_rocq_query_module(&FormalQueryExpr::EmptyTuple, &FormalQueryExpr::EmptyTuple);
    assert!(
        module
            .rocq_module
            .contains("apply query_expr_admissible_with_outputs_empty_tuple.")
    );
}

#[test]
fn lowers_count_star_as_explicit_aggregate() {
    let input_output = vec![column("a")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input_output,
                vec![ScalarAst::Literal {
                    raw: "1".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT()".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: Vec::new(),
                filter: None,
            }],
            output: vec![typed_column("c", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "count_star_argument_encoded")
    );
    let Some(FormalQueryExpr::Group { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("global aggregate should lower as an explicit logical Group");
    };
    assert!(matches!(
        select[0].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::CountStar,
            ..
        }
    ));

    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("COUNT(*) should have lowered"),
        lowered
            .query_expr
            .as_ref()
            .expect("COUNT(*) should have lowered"),
    );
    assert!(module.rocq_module.contains("ACountStar"));
}

#[test]
fn rejects_distinct_count_star() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                vec![column("a")],
                vec![ScalarAst::Literal {
                    raw: "1".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT(DISTINCT *)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: true,
                modifiers: AggregateModifiers::default(),
                args: Vec::new(),
                filter: None,
            }],
            output: vec![typed_column("c", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "count_star_distinct_not_supported")
    );
}

#[test]
fn lowers_distinct_aggregate_as_explicit_aggregate() {
    let input_output = vec![column("a")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(one_row_values(
                input_output,
                vec![ScalarAst::Literal {
                    raw: "1".to_owned(),
                }],
            )),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT(DISTINCT $0)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: true,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("c", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Group { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("global aggregate should lower as an explicit logical Group");
    };
    assert!(matches!(
        select[0].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Aggregate {
                quantifier: FormalAggregateQuantifier::Distinct,
                ..
            },
            ..
        }
    ));

    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("distinct aggregate should have lowered"),
        lowered
            .query_expr
            .as_ref()
            .expect("distinct aggregate should have lowered"),
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateCount AggregateDistinct")
    );
}

#[test]
fn lowers_integral_bitwise_aggregates_with_exact_type_and_distinct_symbols() {
    for (function, ty, distinct, expected_symbol) in [
        (
            "BIT_AND",
            SqlType::Integer,
            false,
            "AAggregate AggregateBitAndInt32 AggregateAll",
        ),
        (
            "BIT_OR",
            SqlType::BigInt,
            false,
            "AAggregate AggregateBitOrInt64 AggregateAll",
        ),
        (
            "BIT_AND",
            SqlType::BigInt,
            true,
            "AAggregate AggregateBitAndInt64 AggregateDistinct",
        ),
        (
            "BIT_OR",
            SqlType::Integer,
            true,
            "AAggregate AggregateBitOrInt32 AggregateDistinct",
        ),
    ] {
        let input = vec![typed_column("bits", ty.clone())];
        let output = vec![typed_column("combined", ty)];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: input,
                }),
                group_keys: Vec::new(),
                grouping_sets: vec![Vec::new()],
                agg_calls: vec![AggregateCall {
                    raw: format!("{function}($0)"),
                    function: function.to_owned(),
                    distinct,
                    modifiers: AggregateModifiers::default(),
                    args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                    filter: None,
                }],
                output: output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{function} distinct={distinct}: {:?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("bitwise aggregate"),
            lowered.query_expr.as_ref().expect("bitwise aggregate"),
        );
        assert!(
            module.rocq_module.contains(expected_symbol),
            "missing {expected_symbol} in {}",
            module.rocq_module
        );
    }
}

#[test]
fn overrides_stale_bitwise_aggregate_result_type() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("bits", SqlType::Integer)],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "BIT_AND($0)".to_owned(),
                function: "BIT_AND".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("combined", SqlType::BigInt)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_aggregate_type_overridden")
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("bitwise aggregate"),
        lowered.query_expr.as_ref().expect("bitwise aggregate"),
    );
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateBitAndInt32 AggregateAll")
    );
    assert!(
        !module
            .rocq_module
            .contains("AAggregate AggregateBitAndInt64")
    );
}

#[test]
fn rejects_distinct_aggregate_without_formal_sql_interpretation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("a", SqlType::Boolean)],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "BOOL_AND(DISTINCT $0)".to_owned(),
                function: "BOOL_AND".to_owned(),
                distinct: true,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("c", SqlType::Boolean)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "distinct_aggregate_function_not_supported" })
    );
}

#[test]
fn lowers_predicate_in_subquery_to_native_in() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "EMP".to_owned(),
                columns: vec![column("DEPTNO")],
                constraints: Default::default(),
            },
            Table {
                name: "DEPT".to_owned(),
                columns: vec![column("DEPTNO"), column("LOC")],
                constraints: Default::default(),
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
    assert!(
        query_expr_output_signature(&lowered).is_some(),
        "typed IN must retain an ordered output signature: {lowered:#?}"
    );
    let module = emit_rocq_query_module(&lowered.clone(), &lowered);

    assert!(module.rocq_module.contains("SExpr_In"));
    assert!(!module.rocq_module.contains("__logos_in_"));
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
}

#[test]
#[ignore = "requires the Java Calcite wrapper and frozen benchmark inputs"]
fn calcite_wrapper_wetune27_lowers_boolean_integer_equalities_to_analysis_error() {
    std::thread::Builder::new()
        .name("wetune27-analysis-error-wrapper".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(std::path::Path::parent)
                .expect("logos-solver crate should be nested under the repository root");
            let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/27");
            let schema_path = case.join("schema.sql");
            let config = LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            };

            for (sql_name, expected_markers) in [("sql1.sql", 1), ("sql2.sql", 2)] {
                let sql_path = case.join(sql_name);
                let output = Command::new(repo.join("scripts/calcite-ir"))
                    .arg("--schema")
                    .arg(&schema_path)
                    .arg("--sql")
                    .arg(&sql_path)
                    .arg("--default-collation")
                    .arg("C")
                    .arg("--character-classification")
                    .arg("C")
                    .arg("--locale-provider")
                    .arg("libc")
                    .arg("--server-encoding")
                    .arg("UTF8")
                    .output()
                    .expect("run Calcite frontend on wetune27");
                assert!(
                    output.status.success(),
                    "{sql_name}: wrapper failed\nstdout:\n{}\nstderr:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                let raw: CalciteFile =
                    serde_json::from_slice(&output.stdout).expect("parse wetune27 wrapper JSON");
                let ir = convert_raw_file(raw)
                    .unwrap_or_else(|error| panic!("{sql_name}: convert wetune27: {error}"));
                let [query] = ir.queries.as_slice() else {
                    panic!("{sql_name}: expected one query")
                };
                assert_eq!(
                    query_source_analysis_error_marker_count(query),
                    expected_markers,
                    "{sql_name}: exact source marker count"
                );
                assert_eq!(
                    query_boolean_integer_source_mismatch_count(query),
                    expected_markers,
                    "{sql_name}: Calcite mismatch count"
                );
                let lowered = lower_query_with_schema_config(query, &ir.schema, &config);
                assert_eq!(
                    lowered.status,
                    LoweringStatus::Lowered,
                    "{sql_name}: {:#?}",
                    lowered.diagnostics
                );
                assert!(matches!(
                    lowered.query_expr,
                    Some(FormalQueryExpr::Error {
                        error: FormalQueryError::UndefinedFunction,
                        ..
                    })
                ));
                let module = emit_rocq_query_module(
                    lowered.query_expr.as_ref().unwrap(),
                    lowered.query_expr.as_ref().unwrap(),
                );
                assert!(module.rocq_module.contains("QExpr_Error"));
                assert!(module.rocq_module.contains("UndefinedFunction"));
            }
        })
        .expect("spawn wetune27 wrapper test with bounded larger stack")
        .join()
        .expect("wetune27 wrapper test thread should not panic");
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and benchmark inputs"]
fn source_bound_invalid_int4_literals_lower_generically_to_analysis_error() {
    std::thread::Builder::new()
        .name("invalid-int4-source-binding-wrapper".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(std::path::Path::parent)
                .expect("logos-solver crate should be nested under the repository root");
            let cases = [
                (
                    repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/verieql-literature__conditional-fkPennTR-5"),
                    "scripts/calcite-ir",
                    false,
                ),
                (
                    repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/64"),
                    "scripts/calcite-ir-sqlglot",
                    true,
                ),
            ];
            let config = LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            };

            for (case, frontend, production) in cases {
                let schema_path = case.join("schema.sql");
                for sql_name in ["sql1.sql", "sql2.sql"] {
                    let sql_path = case.join(sql_name);
                    let mut command = Command::new(repo.join(frontend));
                    if production {
                        command
                            .arg("--read")
                            .arg("postgres")
                            .arg("--write")
                            .arg("postgres");
                    }
                    let output = command
                        .arg("--schema")
                        .arg(&schema_path)
                        .arg("--sql")
                        .arg(&sql_path)
                        .arg("--default-collation")
                        .arg("C")
                        .arg("--character-classification")
                        .arg("C")
                        .arg("--locale-provider")
                        .arg("libc")
                        .arg("--server-encoding")
                        .arg("UTF8")
                        .output()
                        .expect("run frontend");
                    assert!(
                        output.status.success(),
                        "{} failed: {}",
                        sql_path.display(),
                        String::from_utf8_lossy(&output.stderr)
                    );
                    let raw: CalciteFile =
                        serde_json::from_slice(&output.stdout).expect("parse frontend JSON");
                    let ir = convert_raw_file(raw).expect("convert frontend IR");
                    let [query] = ir.queries.as_slice() else {
                        panic!("expected one query")
                    };
                    assert_eq!(
                        rel_generated_invalid_int4_unknown_literal_count(&query.rel),
                        1
                    );
                    assert_eq!(
                        rel_source_attested_invalid_int4_unknown_literal_count(&query.rel),
                        1,
                        "{}",
                        sql_path.display()
                    );
                    let lowered = lower_query_with_schema_config(query, &ir.schema, &config);
                    assert_eq!(
                        lowered.status,
                        LoweringStatus::Lowered,
                        "{}: {:#?}",
                        sql_path.display(),
                        lowered.diagnostics
                    );
                    assert!(matches!(
                        lowered.query_expr,
                        Some(FormalQueryExpr::Error {
                            error: FormalQueryError::InvalidTextRepresentation,
                            ..
                        })
                    ));
                }
            }
        })
        .expect("spawn source-bound invalid-int4 test")
        .join()
        .expect("source-bound invalid-int4 test should not panic");
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_unaccounted_literal_casts_poison_query_wide_analysis_errors() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-computed-invalid-int4-poison-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(
        &schema_path,
        "create table t(b boolean, i integer, bi bigint, n decimal(10,2));\n",
    )
    .expect("write wrapper schema");
    fs::write(
        &query_path,
        "select i from t where i + 0 = 'ARCHIVED' and b = 0;\n\
         select i from t where 'ARCHIVED' = i + 0 and b = 0;\n\
         select bi from t where bi = 'ARCHIVED' and b = 0;\n\
         select bi from t where b = 0 and bi = 'ARCHIVED';\n\
         select n from t where n = 'ARCHIVED' and b = 0;\n\
         select n from t where b = 0 and n = 'ARCHIVED';\n",
    )
    .expect("write wrapper queries");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .arg("--default-collation")
        .arg("C")
        .arg("--character-classification")
        .arg("C")
        .arg("--locale-provider")
        .arg("libc")
        .arg("--server-encoding")
        .arg("UTF8")
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile = serde_json::from_slice(&output.stdout).expect("parse wrapper JSON");
    assert_eq!(raw.queries.len(), 6);
    for index in 0..raw.queries.len() {
        let mut singleton = raw.clone();
        singleton.queries = vec![raw.queries[index].clone()];
        let error = convert_raw_file(singleton)
            .expect_err("unaccounted generated literal CAST must fail closed before Logos IR");
        assert!(
            matches!(
                &error,
                logos_ir::Error::InvalidRelSourceProvenance(message)
                    if message.contains(
                        "source-absent generated CAST has no exact PostgreSQL coercion role"
                    )
            ),
            "query {index}: {error}"
        );
    }
    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrappers_tpch2_accept_total_singleton_scalar_under_ordered_fetch() {
    std::thread::Builder::new()
        .name("tpch2-singleton-scalar-wrapper".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(std::path::Path::parent)
                .expect("logos-solver crate should be nested under the repository root");
            let case =
                repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-tpch__query2");
            let schema_path = case.join("schema.sql");
            let config = LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            };

            for production in [false, true] {
                for sql_name in ["sql1.sql", "sql2.sql"] {
                    let sql_path = case.join(sql_name);
                    let mut command = Command::new(if production {
                        repo.join("scripts/calcite-ir-sqlglot")
                    } else {
                        repo.join("scripts/calcite-ir")
                    });
                    if production {
                        command
                            .arg("--read")
                            .arg("postgres")
                            .arg("--write")
                            .arg("postgres");
                    }
                    let output = command
                        .arg("--schema")
                        .arg(&schema_path)
                        .arg("--sql")
                        .arg(&sql_path)
                        .arg("--default-collation")
                        .arg("C")
                        .arg("--character-classification")
                        .arg("C")
                        .arg("--locale-provider")
                        .arg("libc")
                        .arg("--server-encoding")
                        .arg("UTF8")
                        .output()
                        .expect("run Calcite frontend on frozen TPCH2");
                    let frontend = if production { "production" } else { "direct" };
                    assert!(
                        output.status.success(),
                        "{frontend}/{sql_name}: wrapper failed\nstdout:\n{}\nstderr:\n{}",
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    );
                    let raw: CalciteFile =
                        serde_json::from_slice(&output.stdout).expect("parse TPCH2 wrapper JSON");
                    let ir = convert_raw_file(raw).unwrap_or_else(|error| {
                        panic!("{frontend}/{sql_name}: convert TPCH2: {error}")
                    });
                    let [query] = ir.queries.as_slice() else {
                        panic!("{frontend}/{sql_name}: expected one query")
                    };
                    let lowered = lower_query_with_schema_config(query, &ir.schema, &config);
                    assert_eq!(
                        lowered.status,
                        LoweringStatus::Lowered,
                        "{frontend}/{sql_name}: {:#?}",
                        lowered.diagnostics
                    );
                    let query_expr = lowered.query_expr.as_ref().unwrap();
                    let module = emit_rocq_query_module(query_expr, query_expr);
                    assert!(module.rocq_module.contains("SExpr_Subquery"));
                    assert!(
                        module
                            .rocq_module
                            .contains("AAggregate AggregateMinNumeric AggregateAll")
                    );
                    assert!(module.rocq_module.contains("QExpr_OrderBy"));
                    assert!(module.rocq_module.contains("QExpr_Fetch (100%nat)"));
                }
            }
        })
        .expect("spawn TPCH2 wrapper test with bounded larger stack")
        .join()
        .expect("TPCH2 wrapper test thread should not panic");
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrappers_tpcds_005_080_preserve_set_common_types_under_full_sort() {
    std::thread::Builder::new()
        .name("tpcds-005-080-set-types-wrapper".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(std::path::Path::parent)
                .expect("logos-solver crate should be nested under the repository root");
            let config = LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            };
            let expected_types = [
                FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                },
                FormalAttributeType::Numeric,
                FormalAttributeType::Numeric,
                FormalAttributeType::Numeric,
            ];

            for case_name in ["tpcds-variants__query005", "tpcds-variants__query080"] {
                let case = repo
                    .join("benchmarks/core/.generated/sqlsolver/nonwetune-flat")
                    .join(case_name);
                let schema_path = case.join("schema.sql");
                for production in [false, true] {
                    for sql_name in ["sql1.sql", "sql2.sql"] {
                        let sql_path = case.join(sql_name);
                        let mut command = Command::new(if production {
                            repo.join("scripts/calcite-ir-sqlglot")
                        } else {
                            repo.join("scripts/calcite-ir")
                        });
                        if production {
                            command
                                .arg("--read")
                                .arg("postgres")
                                .arg("--write")
                                .arg("postgres");
                        }
                        let output = command
                            .arg("--schema")
                            .arg(&schema_path)
                            .arg("--sql")
                            .arg(&sql_path)
                            .arg("--default-collation")
                            .arg("C")
                            .arg("--character-classification")
                            .arg("C")
                            .arg("--locale-provider")
                            .arg("libc")
                            .arg("--server-encoding")
                            .arg("UTF8")
                            .output()
                            .unwrap_or_else(|error| {
                                panic!("run {case_name}/{sql_name} Calcite frontend: {error}")
                            });
                        let frontend = if production { "production" } else { "direct" };
                        assert!(
                            output.status.success(),
                            "{case_name}/{frontend}/{sql_name}: wrapper failed\nstdout:\n{}\nstderr:\n{}",
                            String::from_utf8_lossy(&output.stdout),
                            String::from_utf8_lossy(&output.stderr)
                        );
                        let raw: CalciteFile = serde_json::from_slice(&output.stdout)
                            .unwrap_or_else(|error| {
                                panic!("parse {case_name}/{frontend}/{sql_name}: {error}")
                            });
                        let ir = convert_raw_file(raw).unwrap_or_else(|error| {
                            panic!("convert {case_name}/{frontend}/{sql_name}: {error}")
                        });
                        let [query] = ir.queries.as_slice() else {
                            panic!("{case_name}/{frontend}/{sql_name}: expected one query")
                        };
                        let lowered = lower_query_with_schema_config(query, &ir.schema, &config);
                        assert_eq!(
                            lowered.status,
                            LoweringStatus::Lowered,
                            "{case_name}/{frontend}/{sql_name}: {:#?}",
                            lowered.diagnostics
                        );
                        assert_eq!(
                            lowered
                                .output_signature
                                .as_deref()
                                .expect("lowered output signature")
                                .iter()
                                .map(|attribute| attribute.ty)
                                .collect::<Vec<_>>(),
                            expected_types,
                            "{case_name}/{frontend}/{sql_name}: PostgreSQL output types"
                        );
                        let Some(FormalQueryExpr::Fetch { count: 100, input }) =
                            lowered.query_expr.as_ref()
                        else {
                            panic!("{case_name}/{frontend}/{sql_name}: expected eager Fetch 100")
                        };
                        assert!(matches!(input.as_ref(), FormalQueryExpr::OrderBy { .. }));
                        let module = emit_rocq_query_module(
                            lowered.query_expr.as_ref().unwrap(),
                            lowered.query_expr.as_ref().unwrap(),
                        );
                        assert!(!module.rocq_module.trim().is_empty());
                        assert!(module.rocq_module.contains("ScalarStringConcat"));
                        assert!(
                            module
                                .rocq_module
                                .contains("AAggregate AggregateSumNumeric AggregateAll")
                        );
                        assert!(module.rocq_module.contains("QExpr_OrderBy"));
                        assert!(module.rocq_module.contains("QExpr_Fetch (100%nat)"));
                        assert!(!module.rocq_module.contains("QExpr_PgFetch"));
                        if sql_name == "sql2.sql" {
                            assert!(module.rocq_module.contains("QExpr_Distinct"));
                        }
                    }
                }
            }
        })
        .expect("spawn TPC-DS 005/080 wrapper test with bounded larger stack")
        .join()
        .expect("TPC-DS 005/080 wrapper test thread should not panic");
}

#[test]
#[ignore = "requires the Java Calcite wrapper, frozen query005, and the local Rocq switch"]
fn query005_generated_admissibility_certificates_stay_compact_and_compile_quickly() {
    std::thread::Builder::new()
        .name("query005-admissibility-compile".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(std::path::Path::parent)
                .expect("logos-solver crate should be nested under the repository root");
            let case = repo.join(
                "benchmarks/core/.generated/sqlsolver/nonwetune-flat/tpcds-variants__query005",
            );
            let schema_path = case.join("schema.sql");
            let config = LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            };
            let mut lowered_queries = Vec::new();
            let mut schema = None;
            for sql_name in ["sql1.sql", "sql2.sql"] {
                let output = Command::new(repo.join("scripts/calcite-ir"))
                    .arg("--schema")
                    .arg(&schema_path)
                    .arg("--sql")
                    .arg(case.join(sql_name))
                    .arg("--default-collation")
                    .arg("C")
                    .arg("--character-classification")
                    .arg("C")
                    .arg("--locale-provider")
                    .arg("libc")
                    .arg("--server-encoding")
                    .arg("UTF8")
                    .output()
                    .unwrap_or_else(|error| panic!("run query005/{sql_name}: {error}"));
                assert!(
                    output.status.success(),
                    "query005/{sql_name} wrapper failed\nstdout:\n{}\nstderr:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                let raw: CalciteFile = serde_json::from_slice(&output.stdout)
                    .unwrap_or_else(|error| panic!("parse query005/{sql_name}: {error}"));
                let ir = convert_raw_file(raw)
                    .unwrap_or_else(|error| panic!("convert query005/{sql_name}: {error}"));
                let [query] = ir.queries.as_slice() else {
                    panic!("query005/{sql_name}: expected one query")
                };
                let lowered = lower_query_with_schema_config(query, &ir.schema, &config);
                assert_eq!(
                    lowered.status,
                    LoweringStatus::Lowered,
                    "query005/{sql_name}: {:#?}",
                    lowered.diagnostics
                );
                if schema.is_none() {
                    schema = Some(ir.schema.clone());
                }
                lowered_queries.push(lowered);
            }

            let source = lowered_queries[0]
                .query_expr
                .as_ref()
                .expect("query005 source query expression");
            let target = lowered_queries[1]
                .query_expr
                .as_ref()
                .expect("query005 target query expression");
            let source_signature = lowered_queries[0]
                .output_signature
                .as_deref()
                .expect("query005 source output signature");
            let target_signature = lowered_queries[1]
                .output_signature
                .as_deref()
                .expect("query005 target output signature");
            let query_module = emit_rocq_bound_query_program_module_with_signatures(
                &[(
                    source,
                    source_signature,
                    lowered_queries[0].bindings.as_slice(),
                )],
                &[(
                    target,
                    target_signature,
                    lowered_queries[1].bindings.as_slice(),
                )],
            )
            .expect("query005 bound query program module");

            let lowered_schema =
                lower_schema_with_config(schema.as_ref().expect("query005 schema"), &config);
            assert_eq!(lowered_schema.status, LoweringStatus::Lowered);
            let schema_module = &lowered_schema
                .schema
                .as_ref()
                .expect("lowered query005 schema")
                .rocq_module;
            let temp = std::env::temp_dir().join(format!(
                "logos-query005-admissibility-compile-{}",
                std::process::id()
            ));
            if temp.exists() {
                fs::remove_dir_all(&temp).expect("remove stale query005 compile directory");
            }
            fs::create_dir_all(&temp).expect("create query005 compile directory");
            fs::write(temp.join("Schema.v"), schema_module).expect("write query005 Schema.v");
            fs::write(temp.join("Queries.v"), &query_module.rocq_module)
                .expect("write query005 Queries.v");
            assert!(
                query_module.rocq_module.len() <= 160 * 1024,
                "query005 Queries.v grew to {} bytes; retained at {}",
                query_module.rocq_module.len(),
                temp.join("Queries.v").display()
            );

            let rocq = repo.join(".opam-rocq/_opam/bin/rocq");
            for (module, timeout_seconds) in [("Schema.v", "15"), ("Queries.v", "30")] {
                let started = std::time::Instant::now();
                let output = Command::new("timeout")
                    .arg(timeout_seconds)
                    .arg(&rocq)
                    .arg("compile")
                    .arg("-Q")
                    .arg(repo.join("vendor/FormalSQL/src"))
                    .arg("SQLFS")
                    .arg("-Q")
                    .arg(repo.join("theories"))
                    .arg("Logos")
                    .arg("-Q")
                    .arg(&temp)
                    .arg("LogosGenerated")
                    .arg(temp.join(module))
                    .output()
                    .unwrap_or_else(|error| panic!("compile query005 {module}: {error}"));
                let elapsed = started.elapsed();
                assert!(
                    output.status.success(),
                    "query005 {module} failed after {elapsed:?}\nstdout:\n{}\nstderr:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                if module == "Queries.v" {
                    assert!(
                        elapsed < std::time::Duration::from_secs(30),
                        "query005 Queries.v compile exceeded 30 seconds: {elapsed:?}"
                    );
                }
            }
            fs::remove_dir_all(&temp).expect("remove query005 compile directory");
        })
        .expect("spawn query005 compile regression with bounded larger stack")
        .join()
        .expect("query005 compile regression thread should not panic");
}

#[test]
#[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
fn calcite_wrappers_wetune46_retain_reconstructed_in_subquery_order() {
    std::thread::Builder::new()
        .name("wetune46-reconstructed-order-wrapper".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(std::path::Path::parent)
                .expect("logos-solver crate should be nested under the repository root");
            let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/46");
            let schema_path = case.join("schema.sql");
            let config = LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            };

            for production in [false, true] {
                for sql_name in ["sql1.sql", "sql2.sql"] {
                    let sql_path = case.join(sql_name);
                    let mut command = Command::new(if production {
                        repo.join("scripts/calcite-ir-sqlglot")
                    } else {
                        repo.join("scripts/calcite-ir")
                    });
                    if production {
                        command
                            .arg("--read")
                            .arg("postgres")
                            .arg("--write")
                            .arg("postgres");
                    }
                    let output = command
                        .arg("--schema")
                        .arg(&schema_path)
                        .arg("--sql")
                        .arg(&sql_path)
                        .arg("--default-collation")
                        .arg("C")
                        .arg("--character-classification")
                        .arg("C")
                        .arg("--locale-provider")
                        .arg("libc")
                        .arg("--server-encoding")
                        .arg("UTF8")
                        .output()
                        .expect("run Calcite frontend on frozen wetune46");
                    let frontend = if production { "production" } else { "direct" };
                    assert!(
                        output.status.success(),
                        "{frontend}/{sql_name}: wrapper failed\nstdout:\n{}\nstderr:\n{}",
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    );
                    let raw: CalciteFile = serde_json::from_slice(&output.stdout)
                        .expect("parse wetune46 wrapper JSON");
                    let ir = convert_raw_file(raw).unwrap_or_else(|error| {
                        panic!("{frontend}/{sql_name}: convert wetune46: {error}")
                    });
                    let [query] = ir.queries.as_slice() else {
                        panic!("{frontend}/{sql_name}: expected one query")
                    };
                    let lowered = lower_query_with_schema_config(query, &ir.schema, &config);
                    assert_eq!(
                        lowered.status,
                        LoweringStatus::Lowered,
                        "{frontend}/{sql_name}: {:#?}",
                        lowered.diagnostics
                    );
                    let query_expr = lowered.query_expr.as_ref().unwrap();
                    let module = emit_rocq_query_module(query_expr, query_expr);
                    let inner_title_order =
                        "QExpr_OrderBy ([SortAscNullsLast (AttrString \"title\" (StringVarcharN 255))])";
                    let outer_id_order =
                        "QExpr_OrderBy ([SortDescNullsFirst (AttrInt32 \"id\")])";
                    if sql_name == "sql1.sql" {
                        assert!(
                            module.rocq_module.contains(inner_title_order),
                            "{frontend}: the reconstructed inner source order must remain"
                        );
                    } else {
                        assert!(!module.rocq_module.contains(inner_title_order));
                    }
                    assert!(
                        module.rocq_module.contains(outer_id_order),
                        "{frontend}/{sql_name}: the outer order must remain"
                    );
                }
            }
        })
        .expect("spawn wetune46 wrapper test with bounded larger stack")
        .join()
        .expect("wetune46 wrapper test thread should not panic");
}

#[test]
fn in_renaming_uses_actual_lowered_numeric_scope() {
    let outer_output = vec![decimal_column_unconstrained("amount")];
    let reported_inner_output = vec![decimal_column("candidate", 10, 2)];
    let subquery = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["inner_values".to_owned()],
            output: vec![decimal_column_unconstrained("candidate")],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: reported_inner_output,
    };
    let rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["outer_values".to_owned()],
            output: outer_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "IN".to_owned(),
            op: ScalarOp::In,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                },
            ],
        }),
        correlations: Vec::new(),
        output: outer_output,
    };

    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    let lowered = context
        .lower_rel("rel", &rel)
        .expect("numeric IN subquery should lower");

    let Some((predicate, _)) = selection_under_optional_output_restore(&lowered) else {
        panic!("expected relational selection");
    };
    let FormalScalarExpr::In { args, query } = predicate else {
        panic!("expected typed IN");
    };
    assert_eq!(args[0].value_type(), Some(FormalAttributeType::Numeric));
    assert_eq!(
        query_expr_output_signature(query).unwrap()[0].ty,
        FormalAttributeType::Numeric
    );
}

#[test]
fn lowers_in_subquery_with_nested_fetch_to_scalar_expr_in() {
    let scalar_output = vec![column("VALUE")];
    let sorted_output = vec![column("VALUE"), column("TIE_KEY")];
    let subquery = RelExpr::Project {
        input: Box::new(RelExpr::Sort {
            input: Box::new(RelExpr::TableScan {
                table: vec!["INNER_VALUES".to_owned()],
                output: sorted_output.clone(),
            }),
            collation: vec![logos_ir::ir::SortKey {
                field_index: 1,
                direction: SortDirection::Ascending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })),
            offset: None,
            output: sorted_output,
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: scalar_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: scalar_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "IN".to_owned(),
                op: ScalarOp::In,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::RelSubquery {
                        rel: Box::new(subquery),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: scalar_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("expected query-expression selection");
    };
    let FormalScalarExpr::In { args, query } = predicate else {
        panic!("expected exact query-expression IN");
    };
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].value_type(), Some(FormalAttributeType::Int32));
    let FormalQueryExpr::Projection { input, .. } = query.as_ref() else {
        panic!("expected original subquery projection");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Fetch { .. }));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_In"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
}

#[test]
fn lowers_row_valued_in_with_componentwise_three_valued_equality() {
    let output = vec![column("A"), column("B")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "IN".to_owned(),
                op: ScalarOp::In,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                    ScalarAst::RelSubquery {
                        rel: Box::new(RelExpr::TableScan {
                            table: vec!["INNER_VALUES".to_owned()],
                            output: output.clone(),
                        }),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("row-valued IN must use the exact query-expression selection");
    };
    let FormalScalarExpr::In { args, .. } = predicate else {
        panic!("expected exact row-valued IN");
    };
    assert_eq!(args.len(), 2);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("SExpr_In"));
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
}

#[test]
fn lowers_scalar_value_subquery_with_native_cardinality_semantics() {
    let subquery = RelExpr::TableScan {
        table: vec!["INNER_VALUES".to_owned()],
        output: vec![column("VALUE")],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: vec![column("VALUE")],
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "$SCALAR_QUERY".to_owned(),
                op: ScalarOp::ScalarQuery,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            })],
            correlations: Vec::new(),
            output: vec![column("RESULT")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let FormalQueryExpr::Projection { select, .. } = lowered
        .query_expr
        .as_ref()
        .expect("typed scalar projection")
    else {
        panic!("scalar subquery SELECT must use the canonical Projection");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::Subquery { .. },
            ..
        }]
    ));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Subquery"));
}

// Singleton scalar-subquery comparison has a deliberately separate boundary
// from value-level scalar-subquery projection above.  These tests keep its
// one-row proof, error propagation, and correlation handling explicit.

fn singleton_max_subquery(input: RelExpr) -> RelExpr {
    RelExpr::Aggregate {
        input: Box::new(input),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "MAX($0)".to_owned(),
            function: "MAX".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![column("MAX_VALUE")],
    }
}

fn scalar_subquery_filter_query(
    op: ScalarOp,
    outer: ScalarAst,
    subquery: RelExpr,
    correlations: Vec<CorrelationBinding>,
) -> Query {
    let output = vec![column("VALUE")];
    Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: match op {
                    ScalarOp::Eq => "=",
                    ScalarOp::Lt => "<",
                    ScalarOp::Lte => "<=",
                    ScalarOp::Gt => ">",
                    ScalarOp::Gte => ">=",
                    _ => "comparison",
                }
                .to_owned(),
                op,
                args: vec![
                    outer,
                    ScalarAst::Call {
                        operator: "$SCALAR_QUERY".to_owned(),
                        op: ScalarOp::ScalarQuery,
                        args: vec![ScalarAst::RelSubquery {
                            rel: Box::new(subquery),
                        }],
                    },
                ],
            }),
            correlations,
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

fn scalar_query_ast(rel: RelExpr) -> ScalarAst {
    ScalarAst::Call {
        operator: "$SCALAR_QUERY".to_owned(),
        op: ScalarOp::ScalarQuery,
        args: vec![ScalarAst::RelSubquery { rel: Box::new(rel) }],
    }
}

#[test]
fn scalar_query_runtime_risk_requires_possible_second_row_or_child_error() {
    let inner_table = || RelExpr::TableScan {
        table: vec!["INNER_VALUES".to_owned()],
        output: vec![column("VALUE")],
    };
    let outer = RelExpr::TableScan {
        table: vec!["OUTER_VALUES".to_owned()],
        output: vec![column("VALUE")],
    };

    let singleton = singleton_max_subquery(inner_table());
    assert!(!scalar_ast_may_raise_runtime_for_input(
        &scalar_query_ast(singleton.clone()),
        &outer
    ));
    let total_wrapper = RelExpr::Project {
        input: Box::new(singleton),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![column("MAX_VALUE")],
    };
    assert!(!scalar_ast_may_raise_runtime_for_input(
        &scalar_query_ast(total_wrapper),
        &outer
    ));

    assert!(scalar_ast_may_raise_runtime_for_input(
        &scalar_query_ast(inner_table()),
        &outer
    ));
    let grouped = RelExpr::Aggregate {
        input: Box::new(inner_table()),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: Vec::new(),
        output: vec![column("VALUE")],
    };
    assert!(scalar_ast_may_raise_runtime_for_input(
        &scalar_query_ast(grouped),
        &outer
    ));

    for function in ["COUNT", "SUM", "SINGLE_VALUE"] {
        let risky_singleton = RelExpr::Aggregate {
            input: Box::new(inner_table()),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: format!("{function}($0)"),
                function: function.to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![column("RESULT")],
        };
        assert!(
            scalar_ast_may_raise_runtime_for_input(&scalar_query_ast(risky_singleton), &outer),
            "{function} must retain its transition/finalization risk"
        );
    }

    let total_integral_avg = RelExpr::Aggregate {
        input: Box::new(inner_table()),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "AVG($0)".to_owned(),
            function: "AVG".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![decimal_column_unconstrained("RESULT")],
    };
    assert!(!scalar_ast_may_raise_runtime_for_input(
        &scalar_query_ast(total_integral_avg),
        &outer
    ));

    let risky_wrapper = RelExpr::Project {
        input: Box::new(singleton_max_subquery(inner_table())),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "10".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("RISKY_VALUE")],
    };
    assert!(scalar_ast_may_raise_runtime_for_input(
        &scalar_query_ast(risky_wrapper),
        &outer
    ));
    assert!(scalar_ast_may_raise_runtime_for_input(
        &ScalarAst::Call {
            operator: "$SCALAR_QUERY".to_owned(),
            op: ScalarOp::ScalarQuery,
            args: Vec::new(),
        },
        &outer
    ));
}

fn numeric_scale_factor(divisor: &str) -> ScalarAst {
    ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "95".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: divisor.to_owned(),
                }),
                ty: "DECIMAL(4,1)".to_owned(),
            },
        ],
    }
}

fn scaled_numeric_scalar_subquery_filter_query(factor: ScalarAst, subquery: RelExpr) -> Query {
    let output = vec![decimal_column_unconstrained("VALUE")];
    Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: ">".to_owned(),
                op: ScalarOp::Gt,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Call {
                        operator: "*".to_owned(),
                        op: ScalarOp::Multiply,
                        args: vec![
                            factor,
                            ScalarAst::Call {
                                operator: "$SCALAR_QUERY".to_owned(),
                                op: ScalarOp::ScalarQuery,
                                args: vec![ScalarAst::RelSubquery {
                                    rel: Box::new(subquery),
                                }],
                            },
                        ],
                    },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

fn singleton_max_numeric_subquery() -> RelExpr {
    RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![decimal_column("VALUE", 19, 2)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "MAX($0)".to_owned(),
            function: "MAX".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        // Calcite reports a fixed result typmod, but PostgreSQL MAX(numeric)
        // returns unconstrained numeric. Existing aggregate lowering verifies
        // and overrides this metadata.
        output: vec![decimal_column("MAX_VALUE", 19, 2)],
    }
}

#[test]
fn lowers_exact_scaled_numeric_singleton_subquery_by_projecting_over_its_result() {
    let query = scaled_numeric_scalar_subquery_filter_query(
        numeric_scale_factor("100.0"),
        singleton_max_numeric_subquery(),
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("expected query-expression selection");
    };
    let FormalScalarExpr::Predicate { args, .. } = predicate else {
        panic!("scaled singleton comparison must use the typed scalar predicate");
    };
    let FormalScalarExpr::Call {
        operator: ScalarOperator::Multiply(ScalarNumericKind::Numeric),
        args: multiply_args,
        ..
    } = &args[1]
    else {
        panic!("scale multiplication must contain the scalar subquery once");
    };
    let FormalScalarExpr::Subquery { query: child, .. } = &multiply_args[1] else {
        panic!("expected one typed scalar subquery operand");
    };
    assert!(matches!(child.as_ref(), FormalQueryExpr::Group { .. }));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Subquery"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("ScalarMultiply ScalarNumeric"));
    assert!(!module.rocq_module.contains("cast_numeric_to_decimal"));
}

#[test]
fn scaled_numeric_singleton_subquery_rejects_dynamic_factor() {
    let factor = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "95.0".to_owned(),
                }),
                ty: "NUMERIC".to_owned(),
            },
            ScalarAst::InputRef { index: 0 },
        ],
    };
    let lowered = lower_query(&scaled_numeric_scalar_subquery_filter_query(
        factor,
        singleton_max_numeric_subquery(),
    ));
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            matches!(
                diagnostic.code.as_str(),
                "decimal_mixed_arithmetic_not_supported"
                    | "scalar_value_subquery_not_supported"
                    | "cast_source_expression_not_supported"
                    | "numeric_display_scale_not_available"
            )
        }),
        "{:#?}",
        lowered.diagnostics
    );
}

#[test]
fn lowers_singleton_global_aggregate_scalar_comparison_to_quantified_predicate() {
    let subquery = singleton_max_subquery(RelExpr::TableScan {
        table: vec!["INNER_VALUES".to_owned()],
        output: vec![column("VALUE")],
    });
    let query = scalar_subquery_filter_query(
        ScalarOp::Eq,
        ScalarAst::InputRef { index: 0 },
        subquery,
        Vec::new(),
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("expected query-expression filter");
    };
    let FormalScalarExpr::Predicate { predicate, args } = predicate else {
        panic!("expected typed scalar-subquery comparison");
    };
    assert_eq!(*predicate, FormalPredicate::Eq);
    assert_eq!(args.len(), 2);
    let FormalScalarExpr::Subquery {
        query: subquery, ..
    } = &args[1]
    else {
        panic!("comparison must contain one typed scalar subquery");
    };
    assert!(matches!(subquery.as_ref(), FormalQueryExpr::Group { .. }));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("SExpr_Subquery"));
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateMaxInt32 AggregateAll")
    );
}

#[test]
fn scales_singleton_numeric_subquery_inside_quantified_comparison() {
    let query = scaled_numeric_scalar_subquery_filter_query(
        numeric_scale_factor("100.0"),
        singleton_max_numeric_subquery(),
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("expected query-expression filter");
    };
    let FormalScalarExpr::Predicate { args, .. } = predicate else {
        panic!("expected native scaled scalar-subquery comparison");
    };
    let FormalScalarExpr::Call {
        operator: ScalarOperator::Multiply(ScalarNumericKind::Numeric),
        args: multiply_args,
        ..
    } = &args[1]
    else {
        panic!("the multiplication must contain the singleton query once");
    };
    assert!(matches!(
        &multiply_args[1],
        FormalScalarExpr::Subquery { query, .. }
            if matches!(query.as_ref(), FormalQueryExpr::Group { .. })
    ));

    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("SExpr_Subquery"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("ScalarMultiply ScalarNumeric"));
    assert!(!module.rocq_module.contains("__logos_scaled_scalar_value"));
    assert!(!module.rocq_module.contains("cast_numeric_to_decimal"));
}

#[test]
fn scaled_scalar_subquery_preserves_runtime_errors_and_exact_cardinality() {
    for divisor in ["0.1", "100.0"] {
        let query = scaled_numeric_scalar_subquery_filter_query(
            numeric_scale_factor(divisor),
            singleton_max_numeric_subquery(),
        );
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{divisor}: {:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module_for_test(&query);
        assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
        assert!(module.rocq_module.contains("ScalarMultiply ScalarNumeric"));
        assert_no_physical_plan_constructs(&module);
    }

    let planner_error = lower_query(&scaled_numeric_scalar_subquery_filter_query(
        numeric_scale_factor("0.0"),
        singleton_max_numeric_subquery(),
    ));
    assert_eq!(planner_error.status, LoweringStatus::Blocked);
    assert!(
        planner_error.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "boolean_planner_constant_error_not_supported"
        })
    );

    let dynamic_factor = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "95".to_owned(),
                }),
                ty: "NUMERIC".to_owned(),
            },
            ScalarAst::InputRef { index: 0 },
        ],
    };
    let lowered = lower_query(&scaled_numeric_scalar_subquery_filter_query(
        dynamic_factor,
        singleton_max_numeric_subquery(),
    ));
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            matches!(
                diagnostic.code.as_str(),
                "decimal_mixed_arithmetic_not_supported"
                    | "scalar_value_subquery_not_supported"
                    | "cast_source_expression_not_supported"
                    | "numeric_display_scale_not_available"
            )
        }),
        "{:#?}",
        lowered.diagnostics
    );

    let grouped = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![decimal_column("VALUE", 19, 2)],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![AggregateCall {
            raw: "MAX($0)".to_owned(),
            function: "MAX".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![decimal_column("VALUE", 19, 2)],
    };
    let grouped_query =
        scaled_numeric_scalar_subquery_filter_query(numeric_scale_factor("100.0"), grouped);
    let lowered = lower_query(&grouped_query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "scalar_subquery_not_singleton_global_aggregate"
            || diagnostic.code == "aggregate_output_arity_mismatch"
    }));
}

#[test]
fn error_capable_scaled_factor_requires_runtime_total_scalar_subquery() {
    let risky_sum = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![decimal_column("VALUE", 19, 2)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "SUM($0)".to_owned(),
            function: "SUM".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![decimal_column_unconstrained("SUM_VALUE")],
    };
    let lowered = lower_query(&scaled_numeric_scalar_subquery_filter_query(
        numeric_scale_factor("0.0"),
        risky_sum,
    ));
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "scalar_subquery_argument_error_order_not_supported"
        }),
        "{:#?}",
        lowered.diagnostics
    );
}

#[test]
fn lowers_boolean_singleton_scalar_comparison_with_native_boolean_predicate() {
    let count_output = vec![typed_column("ROW_COUNT", SqlType::BigInt)];
    let boolean_output = vec![typed_column("NONEMPTY", SqlType::Boolean)];
    let subquery = RelExpr::Project {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["INNER_VALUES".to_owned()],
                output: vec![column("VALUE")],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![count_star_call()],
            output: count_output,
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: ">".to_owned(),
            op: ScalarOp::Gt,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "0".to_owned(),
                    }),
                    ty: "BIGINT".to_owned(),
                },
            ],
        })],
        correlations: Vec::new(),
        output: boolean_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: boolean_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Call {
                        operator: "$SCALAR_QUERY".to_owned(),
                        op: ScalarOp::ScalarQuery,
                        args: vec![ScalarAst::RelSubquery {
                            rel: Box::new(subquery),
                        }],
                    },
                ],
            }),
            correlations: Vec::new(),
            output: boolean_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("SExpr_Subquery"));
    assert!(module.rocq_module.contains("PredicateEq"));
}

#[test]
fn scalar_subquery_quantification_preserves_error_capable_result_project() {
    let aggregate = singleton_max_subquery(RelExpr::TableScan {
        table: vec!["INNER_VALUES".to_owned()],
        output: vec![column("VALUE")],
    });
    let subquery = RelExpr::Project {
        input: Box::new(aggregate),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("DIVIDED_VALUE")],
    };
    let query = scalar_subquery_filter_query(
        ScalarOp::Gt,
        ScalarAst::InputRef { index: 0 },
        subquery,
        Vec::new(),
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("SExpr_Subquery"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert!(module.rocq_module.contains("QExpr_Project"));
}

#[test]
fn lowers_correlated_singleton_scalar_subquery_by_bound_index() {
    let inner_filter = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: "VALUE".to_owned(),
                    index: Some(0),
                    ty: SqlType::BigInt,
                },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("VALUE")],
    };
    let query = scalar_subquery_filter_query(
        ScalarOp::Lt,
        ScalarAst::InputRef { index: 0 },
        singleton_max_subquery(inner_filter),
        vec![CorrelationBinding {
            correlation: "$cor0".to_owned(),
            output: vec![column("VALUE")],
        }],
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("SExpr_Subquery"));
    assert!(module.rocq_module.contains("__logos_cor_cor0_0"));
    assert!(
        module
            .rocq_module
            .contains("DotInt32 \"__logos_cor_cor0_0\"")
    );
}

#[test]
fn isolates_uncorrelated_subquery_owner_from_same_named_aggregate_inputs() {
    // Calcite's InputRef(1) in the inner Aggregate is local to INNER_VALUES.
    // FormalSQL attributes are nominal, so the outer row must be alpha-renamed
    // while the IN subquery is evaluated; otherwise tail-first aggregate
    // lookup can capture OUTER_VALUES.id.
    let inner_output = vec![column("ref_x"), column("max_id")];
    let inner = RelExpr::Project {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["INNER_VALUES".to_owned()],
                output: vec![column("ref_x"), column("id")],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![AggregateCall {
                raw: "MAX($1)".to_owned(),
                function: "MAX".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 1 })],
                filter: None,
            }],
            output: inner_output.clone(),
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 1 })],
        correlations: Vec::new(),
        output: vec![column("max_id")],
    };
    let outer_output = vec![column("ref_x"), column("id")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "IN".to_owned(),
                op: ScalarOp::In,
                args: vec![
                    ScalarAst::InputRef { index: 1 },
                    ScalarAst::RelSubquery {
                        rel: Box::new(inner),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: outer_output,
        },
        analysis_errors: Vec::new(),
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let query_expr = lowered.query_expr.as_ref().expect("lowered query");
    let signature = query_expr_output_signature(query_expr).expect("typed output signature");
    assert_eq!(
        signature
            .iter()
            .map(|attribute| attribute.name.as_str())
            .collect::<Vec<_>>(),
        vec!["ref_x", "id"]
    );
    let module = emit_rocq_query_module(query_expr, query_expr);
    assert!(
        module
            .rocq_module
            .contains("DotInt32 \"__logos_scope_0_1\"")
    );
    assert!(module.rocq_module.contains("DotInt32 \"id\""));
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateMaxInt32 AggregateAll")
    );
}

#[test]
fn scope_barrier_avoids_user_and_nested_reserved_name_collisions() {
    let colliding = "__logos_scope_0_0";
    let output = vec![column(colliding)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(RelExpr::TableScan {
                        table: vec!["INNER_VALUES".to_owned()],
                        output: vec![column(colliding)],
                    }),
                }],
            }),
            correlations: Vec::new(),
            output,
        },
        analysis_errors: Vec::new(),
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("__logos_scope_1_0"));
    let signature = query_expr_output_signature(lowered.query_expr.as_ref().unwrap()).unwrap();
    assert_eq!(signature[0].name, colliding);
}

#[test]
fn correlated_scope_falls_back_when_legacy_binding_name_is_not_fresh() {
    let colliding = "__logos_cor_cor0_0";
    let outer_output = vec![column(colliding)];
    let inner = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("value")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: colliding.to_owned(),
                    index: Some(0),
                    ty: SqlType::Integer,
                },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("value")],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(inner),
                }],
            }),
            correlations: vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: outer_output.clone(),
            }],
            output: outer_output,
        },
        analysis_errors: Vec::new(),
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("__logos_scope_0_0"));
    assert!(module.rocq_module.contains("PredicateEq"));
}

#[test]
fn source_attested_numeric_rewrite_uses_visible_name_after_scope_barrier() {
    let input_scope = Scope {
        attributes: vec![ScopeAttribute {
            name: "amount".to_owned(),
            visible_name: "amount".to_owned(),
            formal_ty: FormalAttributeType::Numeric,
            numeric_dscale: None,
        }],
    };
    let nested = ScalarAst::RelSubquery {
        rel: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("candidate")],
        }),
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    let names = context.allocate_scope_barrier_names(&input_scope, &[&nested]);
    let isolated = context
        .rename_scope_attributes("barrier", &input_scope, names)
        .expect("capture-avoiding scope");
    assert_ne!(isolated.attributes[0].name, "amount");
    assert_eq!(isolated.attributes[0].visible_name, "amount");

    let ast = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::InputRef { index: 0 }],
        }),
        ty: "NUMERIC(10,2)".to_owned(),
    };
    let source = source_node("amount", "IDENTIFIER", None, Vec::new());
    assert_eq!(
        super::rel::rewrite_source_disproved_numeric_coercions(&ast, Some(&source), &isolated,),
        ScalarAst::InputRef { index: 0 }
    );
}

#[test]
fn inner_and_outer_join_subquery_conditions_isolate_their_row_scopes() {
    let exists = || ScalarAst::Call {
        operator: "EXISTS".to_owned(),
        op: ScalarOp::Exists,
        args: vec![ScalarAst::RelSubquery {
            rel: Box::new(RelExpr::TableScan {
                table: vec!["INNER_VALUES".to_owned()],
                output: vec![column("id")],
            }),
        }],
    };
    let make_join = |join_type| Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(RelExpr::TableScan {
                table: vec!["LEFT_VALUES".to_owned()],
                output: vec![column("left_id")],
            }),
            right: Box::new(RelExpr::TableScan {
                table: vec!["RIGHT_VALUES".to_owned()],
                output: vec![column("right_id")],
            }),
            join_type,
            condition: scalar(exists()),
            correlations: Vec::new(),
            output: vec![column("left_id"), column("right_id")],
        },
        analysis_errors: Vec::new(),
    };

    let inner = lower_query(&make_join(JoinType::Inner));
    assert_eq!(
        inner.status,
        LoweringStatus::Lowered,
        "{:#?}",
        inner.diagnostics
    );
    let inner_module = emit_rocq_query_module(
        inner.query_expr.as_ref().unwrap(),
        inner.query_expr.as_ref().unwrap(),
    );
    assert!(inner_module.rocq_module.contains("__logos_scope_0_0"));

    let outer = lower_query(&make_join(JoinType::Left));
    assert_eq!(outer.status, LoweringStatus::Lowered, "{outer:#?}");
    let outer_module = emit_rocq_query_module(
        outer.query_expr.as_ref().unwrap(),
        outer.query_expr.as_ref().unwrap(),
    );
    assert!(outer_module.rocq_module.contains("QExpr_Join"));
    assert!(outer_module.rocq_module.contains("__logos_scope_0_0"));

    let semi = lower_query(&Query {
        source_sql: None,
        rel: RelExpr::Join {
            left: Box::new(RelExpr::TableScan {
                table: vec!["LEFT_VALUES".to_owned()],
                output: vec![column("left_id")],
            }),
            right: Box::new(RelExpr::TableScan {
                table: vec!["RIGHT_VALUES".to_owned()],
                output: vec![column("right_id")],
            }),
            join_type: JoinType::Semi,
            condition: scalar(exists()),
            correlations: Vec::new(),
            output: vec![column("left_id")],
        },
        analysis_errors: Vec::new(),
    });
    assert_eq!(semi.status, LoweringStatus::Blocked);
    assert!(semi.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "existence_join_subquery_scope_barrier_not_supported"
    }));
}

#[test]
fn native_having_subquery_capture_isolates_hidden_group_bindings() {
    let hidden_input = "__logos_filtered_aggregate_0";
    let aggregate_output = vec![column("outer_max")];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["OUTER_VALUES".to_owned()],
            output: vec![column(hidden_input)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "MAX($0)".to_owned(),
            function: "MAX".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: aggregate_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::NativeHaving {
            input: Box::new(aggregate),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(RelExpr::TableScan {
                        table: vec!["INNER_VALUES".to_owned()],
                        output: vec![column("id")],
                    }),
                }],
            }),
            correlations: Vec::new(),
            output: aggregate_output,
        },
        analysis_errors: Vec::new(),
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let debug = format!("{:?}", lowered.query_expr);
    assert!(debug.contains("Group"));
    assert!(debug.contains("Exists"));
    assert!(debug.contains("__logos_scope_"));
}

#[test]
fn generic_one_column_scalar_subqueries_use_exact_single_value_cardinality() {
    let base_aggregate = singleton_max_subquery(RelExpr::TableScan {
        table: vec!["INNER_VALUES".to_owned()],
        output: vec![column("VALUE")],
    });
    let filtered = RelExpr::Filter {
        input: Box::new(base_aggregate.clone()),
        predicate: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: vec![column("MAX_VALUE")],
    };
    let sorted = RelExpr::Sort {
        input: Box::new(base_aggregate.clone()),
        collation: Vec::new(),
        fetch: None,
        offset: None,
        output: vec![column("MAX_VALUE")],
    };
    let grouped = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![AggregateCall {
            raw: "MAX($0)".to_owned(),
            function: "MAX".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        // Metadata is intentionally one-column: the structural cardinality
        // proof must reject grouping independently of a later arity check.
        output: vec![column("MAX_VALUE")],
    };

    for (label, subquery) in [("filtered", filtered), ("sorted", sorted)] {
        let query = scalar_subquery_filter_query(
            ScalarOp::Eq,
            ScalarAst::InputRef { index: 0 },
            subquery,
            Vec::new(),
        );
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module_for_test(&query);
        assert!(
            module.rocq_module.contains("SExpr_Subquery"),
            "{label}: {}",
            module.rocq_module
        );
        assert!(!module.rocq_module.contains("AggregateSingleValueInt32"));
        assert_no_physical_plan_constructs(&module);
    }

    for op in [ScalarOp::Lte, ScalarOp::Gte] {
        let arbitrary_rows = RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        };
        let query = scalar_subquery_filter_query(
            op.clone(),
            ScalarAst::InputRef { index: 0 },
            arbitrary_rows,
            Vec::new(),
        );
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{op:?}: {:#?}",
            lowered.diagnostics
        );
        let module = emit_rocq_query_module_for_test(&query);
        assert!(module.rocq_module.contains("SExpr_Subquery"));
        assert!(!module.rocq_module.contains("AggregateSingleValueInt32"));
        assert_no_physical_plan_constructs(&module);
    }

    // This hand-built grouped fixture deliberately lies about its arity: a
    // grouped aggregate must expose its key before its aggregate result.
    // SINGLE_VALUE supplies exact scalar cardinality, but must not authorize
    // stale relational metadata.
    let malformed_grouped = scalar_subquery_filter_query(
        ScalarOp::Eq,
        ScalarAst::InputRef { index: 0 },
        grouped,
        Vec::new(),
    );
    let lowered = lower_query(&malformed_grouped);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "aggregate_output_arity_mismatch" })
    );
}

#[test]
fn native_risky_outer_operand_lowers_but_unbound_scalar_correlation_is_rejected() {
    let aggregate = || {
        singleton_max_subquery(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        })
    };
    let risky_outer = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
            ScalarAst::InputRef { index: 0 },
        ],
    };
    let lowered = lower_query(&scalar_subquery_filter_query(
        ScalarOp::Eq,
        risky_outer,
        aggregate(),
        Vec::new(),
    ));
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some((FormalScalarExpr::Predicate { args, .. }, _)) = lowered
        .query_expr
        .as_ref()
        .and_then(selection_under_optional_output_restore)
    else {
        panic!("risky outer operand must share one typed scalar evaluation");
    };
    assert!(
        matches!(
            args.as_slice(),
            [FormalScalarExpr::Call {
                operator: ScalarOperator::Divide(ScalarNumericKind::Int32),
                ..
            }, FormalScalarExpr::Subquery { query, .. }]
                if matches!(query.as_ref(), FormalQueryExpr::Group { .. })
        ),
        "{args:#?}"
    );

    let correlated_input = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::CorrelatedRef {
                    correlation: "$missing".to_owned(),
                    field: "VALUE".to_owned(),
                    index: Some(0),
                    ty: SqlType::Integer,
                },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("VALUE")],
    };
    let lowered = lower_query(&scalar_subquery_filter_query(
        ScalarOp::Eq,
        ScalarAst::InputRef { index: 0 },
        singleton_max_subquery(correlated_input),
        Vec::new(),
    ));
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "correlation_binding_missing")
    );
}

#[test]
fn native_having_scalar_subquery_uses_the_generic_scalar_group_path() {
    fn numeric_zero() -> ScalarAst {
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "0".to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                }],
            }),
            ty: "NUMERIC".to_owned(),
        }
    }

    fn query() -> Query {
        let sum_source = source_node(
            "SUM(outer_values.amount)",
            "OTHER_FUNCTION",
            Some("sum"),
            vec![source_node(
                "outer_values.amount",
                "IDENTIFIER",
                None,
                Vec::new(),
            )],
        );
        let sum_carrier_leaf = source_node(
            "SUM(outer_values.amount)",
            "OTHER_FUNCTION",
            Some("sum"),
            Vec::new(),
        );
        let sum_carrier = source_node(
            "SUM(outer_values.amount)",
            "OTHER_FUNCTION",
            Some("sum"),
            vec![sum_carrier_leaf],
        );
        let coalesce_source = source_node(
            "COALESCE(SUM(outer_values.amount), 0)",
            "OTHER_FUNCTION",
            Some("coalesce"),
            vec![
                sum_carrier.clone(),
                sum_carrier,
                source_node("0", "LITERAL", None, Vec::new()),
            ],
        );
        let subquery_source = source_node(
            "(SELECT MAX(inner_values.value) FROM inner_values)",
            "SELECT",
            Some("SELECT"),
            Vec::new(),
        );
        let predicate_source = source_node(
            "COALESCE(SUM(outer_values.amount), 0) > (SELECT MAX(inner_values.value) FROM inner_values)",
            "GREATER_THAN",
            Some(">"),
            vec![coalesce_source, subquery_source],
        );
        let aggregate_output = vec![
            column("grouped_key"),
            decimal_column_unconstrained("sum_value"),
        ];
        let aggregate = RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["outer_values".to_owned()],
                output: vec![column("key"), decimal_column("amount", 12, 2)],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![AggregateCall {
                raw: "SUM($1)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers {
                    source: Some(sum_source),
                    source_distinct: Some(false),
                    ..AggregateModifiers::default()
                },
                args: vec![scalar(ScalarAst::InputRef { index: 1 })],
                filter: None,
            }],
            output: aggregate_output.clone(),
        };
        let predicate = scalar_with_source(
            ScalarAst::Call {
                operator: ">".to_owned(),
                op: ScalarOp::Gt,
                args: vec![
                    ScalarAst::Call {
                        operator: "CASE".to_owned(),
                        op: ScalarOp::Case,
                        args: vec![
                            ScalarAst::Call {
                                operator: "IS NOT NULL".to_owned(),
                                op: ScalarOp::IsNotNull,
                                args: vec![ScalarAst::InputRef { index: 1 }],
                            },
                            ScalarAst::TypeAnnotation {
                                expr: Box::new(ScalarAst::Call {
                                    operator: "CAST".to_owned(),
                                    op: ScalarOp::Cast,
                                    args: vec![ScalarAst::InputRef { index: 1 }],
                                }),
                                ty: "DECIMAL(19,2)".to_owned(),
                            },
                            numeric_zero(),
                        ],
                    },
                    scalar_query_ast(singleton_max_numeric_subquery()),
                ],
            },
            predicate_source,
        );
        query_for_rel(
            RelExpr::NativeHaving {
                input: Box::new(aggregate),
                predicate,
                correlations: Vec::new(),
                output: aggregate_output.clone(),
            },
            aggregate_output,
        )
    }

    let lowered = lower_query(&query());
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let debug = format!("{:?}", lowered.query_expr);
    assert!(debug.contains("Group"));
    assert!(debug.contains("Subquery"));
}

#[test]
fn lowers_exists_subquery_to_exists_formula() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "EMP".to_owned(),
                columns: vec![column("DEPTNO")],
                constraints: Default::default(),
            },
            Table {
                name: "DEPT".to_owned(),
                columns: vec![column("DEPTNO")],
                constraints: Default::default(),
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
    assert!(
        query_expr_output_signature(&lowered).is_some(),
        "native EXISTS must retain an ordered output signature: {lowered:#?}"
    );
    let module = emit_rocq_query_module(&lowered.clone(), &lowered);

    assert!(module.rocq_module.contains("SExpr_Exists"));
}

#[test]
fn declarative_exists_preserves_error_capable_scalar_target_projection() {
    let outer_output = vec![column("ID")];
    let subquery_input = vec![column("NUMERATOR"), column("DENOMINATOR")];
    let subquery = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: subquery_input,
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 1 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("VALUE")],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: Vec::new(),
            output: outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("INNER_VALUES"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
}

fn scalar_exists_filter_query(subquery: RelExpr) -> Query {
    let output = vec![column("ID")];
    Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

fn scalar_exists_join_with_left_child(left: RelExpr) -> Query {
    let right_output = vec![typed_column("RIGHT_VALUE", SqlType::Integer)];
    let right = RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })]],
        output: right_output.clone(),
    };
    let output = left
        .output()
        .iter()
        .cloned()
        .chain(right_output)
        .collect::<Vec<_>>();
    scalar_exists_filter_query(RelExpr::Join {
        left: Box::new(left),
        right: Box::new(right),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output,
    })
}

#[test]
fn direct_exists_rejects_runtime_risky_union_below_transparent_projection() {
    let value = vec![typed_column("VALUE", SqlType::Integer)];
    let safe = RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })]],
        output: value.clone(),
    };
    let risky = RelExpr::Project {
        input: Box::new(RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "0".to_owned(),
            })]],
            output: vec![typed_column("DENOMINATOR", SqlType::Integer)],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: value.clone(),
    };
    let union = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![safe, risky],
        output: value.clone(),
    };
    let wrapped = RelExpr::Project {
        input: Box::new(union),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: value,
    };

    let lowered = lower_query(&scalar_exists_filter_query(wrapped));

    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "exists_capped_runtime_path_not_supported" })
    );
}

#[test]
fn direct_exists_rejects_runtime_risky_native_outer_join_but_allows_total_paths() {
    let left_output = vec![typed_column("LEFT_VALUE", SqlType::Integer)];
    let right_output = vec![typed_column("RIGHT_VALUE", SqlType::Integer)];
    let left = RelExpr::Values {
        rows: vec![
            vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })],
            vec![scalar(ScalarAst::Literal {
                raw: "0".to_owned(),
            })],
        ],
        output: left_output.clone(),
    };
    let right = RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })]],
        output: right_output.clone(),
    };
    let join_output = left_output
        .iter()
        .chain(&right_output)
        .cloned()
        .collect::<Vec<_>>();
    let join = |condition| RelExpr::Join {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
        join_type: JoinType::Left,
        condition: scalar(condition),
        correlations: Vec::new(),
        output: join_output.clone(),
    };
    let risky_condition = ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };

    let risky = lower_query(&scalar_exists_filter_query(join(risky_condition)));
    assert_eq!(risky.status, LoweringStatus::Blocked, "{risky:#?}");
    assert!(risky.query_expr.is_none());
    assert!(
        risky
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "exists_capped_runtime_path_not_supported" })
    );

    let total = lower_query(&scalar_exists_filter_query(join(ScalarAst::Literal {
        raw: "true".to_owned(),
    })));
    assert_eq!(total.status, LoweringStatus::Lowered, "{total:#?}");
    let module = emit_rocq_query_module(
        total.query_expr.as_ref().expect("total EXISTS query"),
        total.query_expr.as_ref().expect("total EXISTS query"),
    );
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Join"));
}

#[test]
fn direct_exists_rejects_inner_join_with_runtime_risky_dead_child_projection() {
    let left_input_output = vec![typed_column("X", SqlType::Integer)];
    let left_output = vec![typed_column("DEAD", SqlType::Integer)];
    let left = RelExpr::Project {
        input: Box::new(RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })]],
            output: left_input_output,
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::Call {
                    operator: "-".to_owned(),
                    op: ScalarOp::Minus,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::Literal {
                            raw: "1".to_owned(),
                        },
                    ],
                },
            ],
        })],
        correlations: Vec::new(),
        output: left_output.clone(),
    };
    let right_output = vec![typed_column("Y", SqlType::Integer)];
    let right = RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })]],
        output: right_output.clone(),
    };
    let join = RelExpr::Join {
        left: Box::new(left),
        right: Box::new(right),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Literal {
            raw: "true".to_owned(),
        }),
        correlations: Vec::new(),
        output: left_output
            .into_iter()
            .chain(right_output)
            .collect::<Vec<_>>(),
    };

    let lowered = lower_query(&scalar_exists_filter_query(join));

    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "exists_capped_runtime_path_not_supported" })
    );
}

fn direct_exists_window_join_child(function: &str) -> RelExpr {
    let input = vec![
        typed_column("PARTITION_KEY", SqlType::Integer),
        typed_column("ORDER_KEY", SqlType::Integer),
        typed_column("AMOUNT", SqlType::BigInt),
    ];
    let (window, output) = if function.eq_ignore_ascii_case("RANK") {
        (
            default_range_rank_window(
                vec![ScalarAst::InputRef { index: 0 }],
                ScalarAst::InputRef { index: 1 },
                SortDirection::Ascending,
                SortNullDirection::Last,
            ),
            Column {
                name: "WINDOW_VALUE".to_owned(),
                ty: SqlType::BigInt,
                nullable: false,
            },
        )
    } else {
        let args = if function.eq_ignore_ascii_case("ROW_NUMBER") {
            Vec::new()
        } else {
            vec![ScalarAst::InputRef { index: 2 }]
        };
        let output = if function.eq_ignore_ascii_case("SUM") {
            decimal_column_unconstrained("WINDOW_VALUE")
        } else {
            Column {
                name: "WINDOW_VALUE".to_owned(),
                ty: SqlType::BigInt,
                nullable: !function.eq_ignore_ascii_case("ROW_NUMBER"),
            }
        };
        (cumulative_rows_window(function, args), output)
    };
    RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["WINDOW_VALUES".to_owned()],
            output: input,
        }),
        exprs: vec![window],
        correlations: Vec::new(),
        output: vec![output],
    }
}

#[test]
fn direct_exists_rejects_intrinsically_risky_window_join_children() {
    for function in ["ROW_NUMBER", "SUM", "RANK"] {
        let child = direct_exists_window_join_child(function);
        assert!(
            rel_expr_may_raise_runtime(&child),
            "{function} must retain its intrinsic runtime error"
        );
        let lowered = lower_query(&scalar_exists_join_with_left_child(child));
        assert_eq!(
            lowered.status,
            LoweringStatus::Blocked,
            "{function}: {lowered:#?}"
        );
        assert!(lowered.query_expr.is_none(), "{function}");
        assert!(
            lowered.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "exists_capped_runtime_path_not_supported"
            }),
            "{function}: {:#?}",
            lowered.diagnostics
        );
    }

    let total_max = direct_exists_window_join_child("MAX");
    assert!(!rel_expr_may_raise_runtime(&total_max));
    let lowered = lower_query(&scalar_exists_join_with_left_child(total_max));
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "total MAX control: {lowered:#?}"
    );
    let module = emit_rocq_query_module_for_test(&scalar_exists_join_with_left_child(
        direct_exists_window_join_child("MAX"),
    ));
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("WindowAggregateItem"));
}

#[test]
fn direct_exists_rejects_error_capable_fixed_numeric_stddev_join_child() {
    let child = numeric_stddev_samp_query(attested_numeric_stddev_samp_call(), 12, 3).rel;
    assert!(rel_expr_may_raise_runtime(&child));

    let lowered = lower_query(&scalar_exists_join_with_left_child(child));
    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "exists_capped_runtime_path_not_supported" })
    );
}

#[test]
fn aggregate_runtime_risk_classifier_matches_active_overloads() {
    for function in ["COUNT", "SUM", "SINGLE_VALUE"] {
        let input = RelExpr::TableScan {
            table: vec!["VALUES".to_owned()],
            output: vec![typed_column("VALUE", SqlType::Integer)],
        };
        let rel = RelExpr::Aggregate {
            input: Box::new(input),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: format!("{function}($0)"),
                function: function.to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("RESULT", SqlType::Integer)],
        };
        assert!(
            rel_expr_may_raise_runtime(&rel),
            "{function} has an admitted error-capable overload"
        );
    }

    for function in [
        "AVG",
        "VAR_POP",
        "VAR_SAMP",
        "VARIANCE",
        "STDDEV_POP",
        "STDDEV_SAMP",
        "STDDEV",
        "MIN",
        "MAX",
        "BIT_AND",
        "BIT_OR",
    ] {
        let input = RelExpr::TableScan {
            table: vec!["VALUES".to_owned()],
            output: vec![typed_column("VALUE", SqlType::Integer)],
        };
        let rel = RelExpr::Aggregate {
            input: Box::new(input),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: format!("{function}($0)"),
                function: function.to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("RESULT", SqlType::Integer)],
        };
        assert!(
            !rel_expr_may_raise_runtime(&rel),
            "{function}'s admitted INTEGER callback is total"
        );
    }

    let float_avg = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["VALUES".to_owned()],
            output: vec![typed_column("VALUE", SqlType::Float)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "AVG($0)".to_owned(),
            function: "AVG".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![typed_column("RESULT", SqlType::Double)],
    };
    assert!(
        rel_expr_may_raise_runtime(&float_avg),
        "floating AVG retains its range-error callback"
    );

    let numeric_avg = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["VALUES".to_owned()],
            output: vec![decimal_column("VALUE", 12, 3)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "AVG($0)".to_owned(),
            function: "AVG".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![decimal_column_unconstrained("RESULT")],
    };
    assert!(
        rel_expr_may_raise_runtime(&numeric_avg),
        "fixed-NUMERIC AVG retains its FormalSQL finalization error path"
    );
}

#[test]
fn direct_exists_allows_total_integral_avg_join_child() {
    let child = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INTEGER_VALUES".to_owned()],
            output: vec![typed_column("VALUE", SqlType::Integer)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "AVG($0)".to_owned(),
            function: "AVG".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![decimal_column_unconstrained("AVERAGE_VALUE")],
    };
    assert!(!rel_expr_may_raise_runtime(&child));

    let query = scalar_exists_join_with_left_child(child);
    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| { diagnostic.code != "exists_capped_runtime_path_not_supported" })
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("AggregateAverageInt32Numeric"));
}

#[test]
fn declarative_exists_preserves_error_capable_target_and_logical_filter() {
    let inner_output = vec![column("VALUE"), column("KEEP")];
    let filtered = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: inner_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 1 },
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: inner_output,
    };
    let target = RelExpr::Project {
        input: Box::new(filtered),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("IGNORED")],
    };
    let query = scalar_exists_filter_query(target);

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Filter"));
    assert!(module.rocq_module.contains("DotInt32 \"KEEP\""));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));
}

#[test]
fn declarative_exists_preserves_error_capable_target_under_row_slicing() {
    let input = vec![column("VALUE")];
    let target = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: input,
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("IGNORED")],
    };
    let sliced = RelExpr::Sort {
        input: Box::new(target),
        collation: vec![SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "0".to_owned(),
        })),
        offset: Some(Box::new(scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        }))),
        output: vec![column("IGNORED")],
    };
    let query = scalar_exists_filter_query(sliced);

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some((FormalScalarExpr::Exists { query: exists }, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("outer filter should retain its declarative EXISTS predicate");
    };
    let FormalQueryExpr::Fetch { count: 0, input } = exists.as_ref() else {
        panic!("EXISTS target should retain FETCH 0 explicitly");
    };
    let FormalQueryExpr::Offset { count: 1, input } = input.as_ref() else {
        panic!("EXISTS target should retain OFFSET 1 explicitly");
    };
    let FormalQueryExpr::OrderBy { input, .. } = input.as_ref() else {
        panic!("EXISTS target should retain declarative ORDER BY explicitly");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Projection { .. }));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
    assert!(module.rocq_module.contains("QExpr_Offset (1%nat)"));
}

#[test]
fn declarative_exists_does_not_use_target_shape_erasure_for_window() {
    let target = window_project_with_frame(
        RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        },
        WindowFrameAst {
            units: WindowFrameUnits::Rows,
            start: WindowFrameBoundAst::UnboundedPreceding,
            end: Some(WindowFrameBoundAst::CurrentRow),
        },
    );
    let lowered = lower_query(&scalar_exists_filter_query(target));
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| { diagnostic.code != "exists_target_shape_not_supported" })
    );
}

#[test]
fn declarative_exists_preserves_error_capable_window_frame_offset() {
    let target = window_project_with_frame(
        RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE")],
        },
        WindowFrameAst {
            units: WindowFrameUnits::Rows,
            start: WindowFrameBoundAst::OffsetPreceding {
                raw: "/(1, 0)".to_owned(),
                expr: Box::new(failing_integer_division()),
            },
            end: Some(WindowFrameBoundAst::CurrentRow),
        },
    );
    let lowered = lower_query(&scalar_exists_filter_query(target));
    assert_eq!(lowered.status, LoweringStatus::Blocked, "{lowered:#?}");
    assert!(lowered_query_expr(&lowered).is_none());
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "window_shape_not_supported"),
        "{:#?}",
        lowered.diagnostics
    );
}

#[test]
fn exists_over_global_aggregate_preserves_aggregate_argument_evaluation() {
    let outer_output = vec![column("ID")];
    let subquery = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("DENOMINATOR")],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "COUNT(10 / $0)".to_owned(),
            function: "COUNT".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            filter: None,
        }],
        output: vec![typed_column("COUNT", SqlType::BigInt)],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: Vec::new(),
            output: outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateCount AggregateAll")
    );
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
}

#[test]
fn exists_over_global_aggregate_preserves_unused_risky_child_projection() {
    let outer_output = vec![column("ID")];
    let subquery_input = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("VALUE"), column("DENOMINATOR")],
        }),
        exprs: vec![
            scalar(ScalarAst::InputRef { index: 0 }),
            scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::InputRef { index: 1 },
                ],
            }),
        ],
        correlations: Vec::new(),
        output: vec![column("VALUE"), column("UNUSED_RISK")],
    };
    let subquery = RelExpr::Aggregate {
        input: Box::new(subquery_input),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "COUNT($0)".to_owned(),
            function: "COUNT".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 0 })],
            filter: None,
        }],
        output: vec![typed_column("COUNT", SqlType::BigInt)],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["OUTER_VALUES".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: Vec::new(),
            output: outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateCount AggregateAll")
    );
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));
}

#[test]
fn exists_preserves_having_runtime_expression() {
    let aggregate_output = vec![typed_column("ROW_COUNT", SqlType::BigInt)];
    let subquery = RelExpr::NativeHaving {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["INNER_VALUES".to_owned()],
                output: vec![column("VALUE")],
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![count_star_call()],
            output: aggregate_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: ">".to_owned(),
            op: ScalarOp::Gt,
            args: vec![
                ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::Literal {
                            raw: "10".to_owned(),
                        },
                        ScalarAst::InputRef { index: 0 },
                    ],
                },
                ScalarAst::Literal {
                    raw: "0".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: aggregate_output,
    };
    let query = scalar_exists_filter_query(subquery);

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt64"));
}

#[test]
fn exists_preserves_value_dependent_set_operand_targets() {
    fn risky_operand(table: &str) -> RelExpr {
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec![table.to_owned()],
                output: vec![column("DENOMINATOR")],
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![column("VALUE")],
        }
    }
    let subquery = RelExpr::Set {
        op: SetOp::Intersect,
        all: false,
        inputs: vec![risky_operand("LEFT_VALUES"), risky_operand("RIGHT_VALUES")],
        output: vec![column("VALUE")],
    };
    let query = scalar_exists_filter_query(subquery);

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
}

#[test]
fn declarative_exists_preserves_error_capable_all_column_grouping() {
    let projected = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("DENOMINATOR")],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "10".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("VALUE")],
    };
    let subquery = RelExpr::Aggregate {
        input: Box::new(projected),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: Vec::new(),
        output: vec![column("VALUE")],
    };

    let query = scalar_exists_filter_query(subquery);
    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some((FormalScalarExpr::Exists { query: exists }, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("outer filter should retain its declarative EXISTS predicate");
    };
    let FormalQueryExpr::Group {
        select,
        group_by,
        input,
        ..
    } = exists.as_ref()
    else {
        panic!("all-column logical grouping should remain an exact Group: {exists:#?}");
    };
    assert_eq!(select.len(), 1);
    assert_eq!(group_by.len(), 1);
    assert!(matches!(input.as_ref(), FormalQueryExpr::Projection { .. }));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));
    assert!(
        lowered.diagnostics.iter().all(|diagnostic| {
            diagnostic.code != "exists_distinct_grouping_origin_not_attested"
        })
    );
}

#[test]
fn declarative_exists_preserves_source_distinct_as_native_distinct() {
    let projected = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["INNER_VALUES".to_owned()],
            output: vec![column("DENOMINATOR")],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "10".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("VALUE")],
    };
    let subquery = RelExpr::Distinct {
        input: Box::new(projected),
        output: vec![column("VALUE")],
    };

    let query = scalar_exists_filter_query(subquery);
    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some((FormalScalarExpr::Exists { query: exists }, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("outer filter should retain its declarative EXISTS predicate");
    };
    assert!(
        matches!(exists.as_ref(), FormalQueryExpr::Distinct { input }
        if matches!(input.as_ref(), FormalQueryExpr::Projection { .. }))
    );

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Distinct"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert!(!module.rocq_module.contains("QExpr_Group"));
}

#[test]
fn accepts_checked_constant_arithmetic_inside_boolean_connectives() {
    fn typed_literal(raw: &str, ty: &str) -> ScalarAst {
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: raw.to_owned(),
            }),
            ty: ty.to_owned(),
        }
    }

    let comparisons = vec![
        ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::Call {
                    operator: "+".to_owned(),
                    op: ScalarOp::Plus,
                    args: vec![
                        ScalarAst::Literal {
                            raw: "5".to_owned(),
                        },
                        ScalarAst::Literal {
                            raw: "10".to_owned(),
                        },
                    ],
                },
                ScalarAst::Literal {
                    raw: "15".to_owned(),
                },
            ],
        },
        ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::Call {
                    operator: "+".to_owned(),
                    op: ScalarOp::Plus,
                    args: vec![
                        typed_literal("0.06", "DECIMAL(3, 2)"),
                        typed_literal("0.01", "DECIMAL(3, 2)"),
                    ],
                },
                typed_literal("0.07", "DECIMAL(3, 2)"),
            ],
        },
        ScalarAst::Call {
            operator: "<".to_owned(),
            op: ScalarOp::Lt,
            args: vec![
                typed_literal("8766", "DATE"),
                ScalarAst::Call {
                    operator: "+".to_owned(),
                    op: ScalarOp::Plus,
                    args: vec![
                        typed_literal("8766", "DATE"),
                        typed_literal("1", "INTERVAL YEAR"),
                    ],
                },
            ],
        },
    ];
    let output = vec![column("a")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "AND".to_owned(),
                op: ScalarOp::And,
                args: comparisons,
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:?}",
        lowered.diagnostics
    );
}

#[test]
fn total_constant_numeric_division_retains_runtime_divide_and_operand_dscale() {
    let division = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "95".to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                },
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "100.0".to_owned(),
                    }),
                    ty: "DECIMAL(4,1)".to_owned(),
                },
            ],
        }),
        ty: "DECIMAL(19,2)".to_owned(),
    };
    let output = vec![decimal_column_unconstrained("ratio")];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(division)],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(module.rocq_module.contains("CstDecimal (4) (1) (1000)"));
}

#[test]
fn constant_totality_proof_keeps_overflow_and_zero_division_risky() {
    let overflow = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![
            ScalarAst::Literal {
                raw: i32::MAX.to_string(),
            },
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
        ],
    };
    let division_by_zero = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::Literal {
                raw: "1".to_owned(),
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };

    assert!(super::scalar::scalar_ast_may_raise_runtime(&overflow));
    assert!(super::scalar::scalar_ast_may_raise_runtime(
        &division_by_zero
    ));

    let date_outside_timestamp_range = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "106762940".to_owned(),
                }),
                ty: "DATE".to_owned(),
            },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "0".to_owned(),
                }),
                ty: "INTERVAL DAY".to_owned(),
            },
        ],
    };
    assert!(super::scalar::scalar_ast_may_raise_runtime(
        &date_outside_timestamp_range
    ));
}

#[test]
fn keeps_case_branch_runtime_errors_under_modeled_lazy_case_semantics() {
    let input = vec![
        typed_column("CONDITION", SqlType::Boolean),
        column("NUMERATOR"),
        column("DENOMINATOR"),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["VALUES".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Call {
                        operator: "/".to_owned(),
                        op: ScalarOp::Divide,
                        args: vec![
                            ScalarAst::InputRef { index: 1 },
                            ScalarAst::InputRef { index: 2 },
                        ],
                    },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![column("RESULT")],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
}

#[test]
fn lowers_correlated_exists_by_binding_index_not_field_name() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "DEPT".to_owned(),
                columns: vec![column("DEPTNO")],
                constraints: Default::default(),
            },
            Table {
                name: "EMP".to_owned(),
                columns: vec![column("DEPTNO")],
                constraints: Default::default(),
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
    let module = emit_rocq_query_module(&lowered.clone(), &lowered);

    assert!(module.rocq_module.contains("__logos_cor_cor0_0"));
    assert!(module.rocq_module.contains("PredicateEq"));
}

#[test]
fn correlated_exact_input_uses_actual_numeric_scope_not_stale_decimal_metadata() {
    let reported_outer_output = vec![decimal_column("amount", 10, 2)];
    let outer_project = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["outer_values".to_owned()],
            output: vec![decimal_column_unconstrained("amount")],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: reported_outer_output.clone(),
    };
    let ordered_outer = RelExpr::Sort {
        input: Box::new(outer_project),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: None,
        offset: None,
        output: reported_outer_output.clone(),
    };
    let subquery = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["inner_values".to_owned()],
            output: vec![decimal_column_unconstrained("candidate")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: "amount".to_owned(),
                    index: Some(0),
                    ty: SqlType::decimal(Some(10), Some(2)),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        }),
        correlations: Vec::new(),
        output: vec![decimal_column_unconstrained("candidate")],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(ordered_outer),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: reported_outer_output.clone(),
            }],
            output: reported_outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Projection { .. })
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AttrNumeric \"__logos_cor_cor0_0\"")
    );
    assert!(module.rocq_module.contains("PredicateEq"));
    assert!(module.rocq_module.contains("candidate"));
    assert!(
        !module
            .rocq_module
            .contains("AttrDecimal \"__logos_cor_cor0_0\"")
    );
}

#[test]
fn declarative_exists_preserves_correlated_narrowing_target_with_stale_metadata() {
    let reported_outer_output = vec![decimal_column("amount", 7, 2)];
    let outer_project = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["outer_values".to_owned()],
            output: vec![decimal_column_unconstrained("amount")],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: reported_outer_output.clone(),
    };
    let ordered_outer = RelExpr::Sort {
        input: Box::new(outer_project),
        collation: vec![SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: None,
        offset: None,
        output: reported_outer_output.clone(),
    };
    let cast_output = vec![decimal_column("amount_cast", 7, 1)];
    let correlated_cast = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["inner_values".to_owned()],
            output: vec![column("dummy")],
        }),
        exprs: vec![scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: "amount".to_owned(),
                    index: Some(0),
                    // Calcite reports a bounded DECIMAL here, but the actual
                    // enclosing scope above lowers this value as NUMERIC.
                    ty: SqlType::decimal(Some(7), Some(2)),
                }],
            }),
            ty: "DECIMAL(7, 1)".to_owned(),
        })],
        correlations: Vec::new(),
        output: cast_output.clone(),
    };
    let sliced_subquery = RelExpr::Sort {
        input: Box::new(correlated_cast),
        collation: Vec::new(),
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })),
        offset: None,
        output: cast_output,
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(ordered_outer),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(sliced_subquery),
                }],
            }),
            correlations: vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: reported_outer_output.clone(),
            }],
            output: reported_outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(module.rocq_module.contains("QExpr_Fetch (1%nat)"));
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumericTypmod ScalarSourceNumeric")
    );
    assert!(!module.rocq_module.contains("QExpr_Pg"));
}

#[test]
fn lowers_correlated_join_output_after_calcite_renaming() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "a".to_owned(),
                columns: vec![column("id"), column("x")],
                constraints: Default::default(),
            },
            Table {
                name: "b".to_owned(),
                columns: vec![column("id"), column("y")],
                constraints: Default::default(),
            },
            Table {
                name: "c".to_owned(),
                columns: vec![column("id")],
                constraints: Default::default(),
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
    let module = emit_rocq_query_module(&lowered.clone(), &lowered);

    assert!(module.rocq_module.contains("__logos_cor_cor0_2"));
    assert!(module.rocq_module.contains("PredicateEq"));
}

#[test]
fn lowers_empty_values_rows_to_typed_empty_bag() {
    let rel = RelExpr::Values {
        rows: vec![],
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("empty VALUES should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("empty VALUES should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered_query_expr(&lowered),
        Some(FormalQueryExpr::Empty { .. })
    ));
    assert!(module.rocq_module.contains("QExpr_Values"));
    assert!(!module.rocq_module.contains("QExpr_Set Diff"));
}

#[test]
fn lowers_values_rows_with_additive_bag_union() {
    let rel = RelExpr::Values {
        rows: vec![
            vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })],
            vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })],
        ],
        output: vec![column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("VALUES rows should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("VALUES rows should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("QExpr_Set Union"));
}

#[test]
fn values_admits_only_exact_integral_constants_coerced_to_numeric() {
    let integral_numeric = |raw: &str, ty: &str| {
        scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: ty.to_owned(),
                }],
            }),
            ty: "NUMERIC".to_owned(),
        })
    };
    let output = vec![decimal_column_unconstrained("n")];
    let exact = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![
                vec![integral_numeric("0", "INTEGER")],
                vec![integral_numeric("2147483648", "BIGINT")],
                vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "2.1".to_owned(),
                    }),
                    ty: "NUMERIC".to_owned(),
                })],
            ],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };
    let lowered = lower_query(&exact);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("exact numeric VALUES"),
        lowered.query_expr.as_ref().expect("exact numeric VALUES"),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumeric ScalarSourceInt32")
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumeric ScalarSourceInt64")
    );

    let arbitrary_functions = [
        ScalarAst::Call {
            operator: "+".to_owned(),
            op: ScalarOp::Plus,
            args: vec![
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1.0".to_owned(),
                    }),
                    ty: "NUMERIC".to_owned(),
                },
                ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "2.0".to_owned(),
                    }),
                    ty: "NUMERIC".to_owned(),
                },
            ],
        },
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "0".to_owned(),
                    }),
                    ty: "DOUBLE".to_owned(),
                }],
            }),
            ty: "NUMERIC".to_owned(),
        },
    ];
    for (index, ast) in arbitrary_functions.into_iter().enumerate() {
        let rejected = lower_query(&Query {
            source_sql: None,
            rel: RelExpr::Values {
                rows: vec![vec![scalar(ast)]],
                output: output.clone(),
            },
            analysis_errors: vec![],
        });
        assert_eq!(rejected.status, LoweringStatus::Blocked, "case {index}");
        assert!(
            rejected.diagnostics.iter().any(|diagnostic| {
                matches!(
                    diagnostic.code.as_str(),
                    "values_expression_not_supported"
                        | "values_integral_numeric_cast_not_supported"
                        | "cast_source_type_mismatch"
                        | "cast_not_supported"
                )
            }),
            "case {index}: {:#?}",
            rejected.diagnostics
        );
    }
}

#[test]
fn lowers_explicit_varchar_literal_casts_in_values() {
    let cast = |raw: &str| {
        scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: "TEXT".to_owned(),
                }],
            }),
            ty: "VARCHAR(2)".to_owned(),
        })
    };
    let output = vec![typed_column("A", SqlType::varchar(Some(2)))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![vec![cast("'abcd'")], vec![cast("'b'")]],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let query_expr = lowered
        .query_expr
        .as_ref()
        .expect("explicit VARCHAR VALUES casts should lower");
    let module = emit_rocq_query_module(query_expr, query_expr);
    assert!(
        module.rocq_module.contains("StringVarcharN 2"),
        "{}",
        module.rocq_module
    );
    assert!(
        module
            .rocq_module
            .contains("CstString (StringVarcharN 2) \"abcd\""),
        "{}",
        module.rocq_module
    );
}

#[test]
fn coerces_mixed_character_values_to_typmodless_bpchar() {
    let cast = |raw: &str, target: &str| {
        scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: "TEXT".to_owned(),
                }],
            }),
            ty: target.to_owned(),
        })
    };
    let output = vec![typed_column("A", SqlType::bpchar())];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![
                vec![cast("'a'", "CHAR(2)")],
                vec![cast("'b'", "VARCHAR(2)")],
            ],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    let query_expr = lowered.query_expr.as_ref().expect("VALUES should lower");
    let module = emit_rocq_query_module(query_expr, query_expr);
    assert!(module.rocq_module.contains("ScalarCoerceStringImplicit"));
    assert!(module.rocq_module.contains("StringBpchar"));
    assert!(module.rocq_module.contains("StringChar 2"));
    assert!(module.rocq_module.contains("StringVarcharN 2"));
}

#[test]
fn lowers_values_null_using_inferred_column_type() {
    let rel = RelExpr::Values {
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
        output: vec![typed_column("A", SqlType::Null)],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Set { op, left, right }) = lowered_query_expr(&lowered) else {
        panic!("two VALUES rows should lower to a bag union");
    };
    assert_eq!(*op, FormalSetOp::Union);
    let (Some(null_ty), Some(one_ty)) = (
        singleton_constant_type(left, "NULL"),
        singleton_constant_type(right, "1"),
    ) else {
        panic!("VALUES rows should lower to typed singleton constants");
    };
    assert_eq!(null_ty, FormalAttributeType::Int32);
    assert_eq!(one_ty, FormalAttributeType::Int32);
}

#[test]
fn lowers_values_null_using_concrete_output_type() {
    let rel = RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "NULL".to_owned(),
        })]],
        output: vec![column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(ty) =
        lowered_query_expr(&lowered).and_then(|query| singleton_constant_type(query, "NULL"))
    else {
        panic!("concrete VALUES output type should type bare NULL");
    };
    assert_eq!(ty, FormalAttributeType::Int32);
}

#[test]
fn resolves_untyped_all_null_values_column_as_postgres_text() {
    let rel = RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "NULL".to_owned(),
        })]],
        output: vec![typed_column("A", SqlType::Null)],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(ty) =
        lowered_query_expr(&lowered).and_then(|query| singleton_constant_type(query, "NULL"))
    else {
        panic!("fallback VALUES output type should type bare NULL");
    };
    assert_eq!(
        ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Text,
        }
    );
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "unresolved_null_resolved_as_text")
    );
}

#[test]
fn lowers_both_sides_and_warns_when_positional_output_types_differ() {
    let source_query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "NULL".to_owned(),
            })]],
            output: vec![typed_column("source_name", SqlType::Null)],
        },
        analysis_errors: vec![],
    };
    let target_query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "NULL".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            })]],
            output: vec![typed_column("target_name", SqlType::Integer)],
        },
        analysis_errors: vec![],
    };
    let mut source = lower_query(&source_query);
    let mut target = lower_query(&target_query);

    finalize_output_pair(&mut source, &mut target);

    assert_eq!(
        source.output_signature.as_ref().unwrap()[0].name,
        "__logos_output_0"
    );
    assert_eq!(
        target.output_signature.as_ref().unwrap()[0].name,
        "__logos_output_0"
    );

    for lowered in [source, target] {
        assert_eq!(lowered.status, LoweringStatus::Lowered);
        assert!(lowered_query_expr(&lowered).is_some());
        assert!(lowered.query_expr.is_some());
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "output_type_mismatch"
                    && diagnostic.severity == DiagnosticSeverity::Warning)
        );
    }
}

#[test]
fn canonicalizes_label_only_mismatch_at_the_observation_boundary() {
    let query = |name: &str| Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })]],
            output: vec![column(name)],
        },
        analysis_errors: vec![],
    };
    let mut source = lower_query(&query("source_label"));
    let mut target = lower_query(&query("target_label"));

    finalize_output_pair(&mut source, &mut target);

    assert_eq!(
        source.output_signature,
        Some(vec![FormalAttribute {
            name: "__logos_output_0".to_owned(),
            ty: FormalAttributeType::Int32,
        }])
    );
    assert_eq!(
        target.output_signature,
        Some(vec![FormalAttribute {
            name: "__logos_output_0".to_owned(),
            ty: FormalAttributeType::Int32,
        }])
    );
    for lowered in [&source, &target] {
        assert_eq!(lowered.status, LoweringStatus::Lowered);
        assert!(lowered_query_expr(lowered).is_some());
        assert!(matches!(
            lowered.query_expr.as_ref(),
            Some(FormalQueryExpr::Projection { .. })
        ));
        assert_eq!(
            query_expr_output_signature(lowered.query_expr.as_ref().unwrap())
                .unwrap()
                .into_iter()
                .map(|attribute| attribute.name)
                .collect::<Vec<_>>(),
            vec!["__logos_output_0"]
        );
        assert!(
            lowered
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code != "output_label_mismatch")
        );
    }
    let module = emit_rocq_query_module_with_signatures(
        source.query_expr.as_ref().unwrap(),
        source.output_signature.as_deref().unwrap(),
        target.query_expr.as_ref().unwrap(),
        target.output_signature.as_deref().unwrap(),
    );
    assert!(module.rocq_module.contains(
        "Definition source_output_signature : list (Tuple.attribute TNull) :=\n  [AttrInt32 \"__logos_output_0\"]."
    ));
    assert!(module.rocq_module.contains(
        "Definition target_output_signature : list (Tuple.attribute TNull) :=\n  [AttrInt32 \"__logos_output_0\"]."
    ));
    assert!(emitted_definition_shape(&module, "source_query_expr").starts_with("QExpr_Project("));
    assert!(emitted_definition_shape(&module, "target_query_expr").starts_with("QExpr_Project("));
}

#[test]
fn case_predicates_select_exact_query_semantics_without_pair_normalization() {
    let predicate = ScalarAst::Call {
        operator: "CASE".to_owned(),
        op: ScalarOp::Case,
        args: vec![
            ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1000".to_owned(),
                        }),
                        ty: "INTEGER".to_owned(),
                    },
                ],
            },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "TRUE".to_owned(),
                }),
                ty: "BOOLEAN".to_owned(),
            },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "FALSE".to_owned(),
                }),
                ty: "BOOLEAN".to_owned(),
            },
        ],
    };
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["emp".to_owned()],
                output: vec![typed_column("sal", SqlType::Integer)],
            }),
            predicate: scalar(predicate),
            correlations: Vec::new(),
            output: vec![typed_column("sal", SqlType::Integer)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Selection {
            input,
            ..
        }) if matches!(input.as_ref(), FormalQueryExpr::Table { .. })
    ));
}

#[test]
fn lowers_both_sides_and_warns_when_output_arities_differ() {
    let query = |names: &[&str]| Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![
                (0..names.len())
                    .map(|index| {
                        scalar(ScalarAst::Literal {
                            raw: (index + 1).to_string(),
                        })
                    })
                    .collect(),
            ],
            output: names.iter().map(|name| column(name)).collect(),
        },
        analysis_errors: vec![],
    };
    let mut source = lower_query(&query(&["a"]));
    let mut target = lower_query(&query(&["a", "b"]));

    finalize_output_pair(&mut source, &mut target);

    assert_eq!(source.status, LoweringStatus::Lowered);
    assert_eq!(target.status, LoweringStatus::Lowered);
    assert_eq!(source.output_signature.as_ref().unwrap().len(), 1);
    assert_eq!(target.output_signature.as_ref().unwrap().len(), 2);
    for lowered in [&source, &target] {
        assert!(lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "output_arity_mismatch"
                && diagnostic.severity == DiagnosticSeverity::Warning
        }));
    }
    let module = emit_rocq_query_module_with_signatures(
        source.query_expr.as_ref().unwrap(),
        source.output_signature.as_deref().unwrap(),
        target.query_expr.as_ref().unwrap(),
        target.output_signature.as_deref().unwrap(),
    );
    assert!(module.rocq_module.contains(
        "Definition source_output_signature : list (Tuple.attribute TNull) :=\n  [AttrInt32 \"__logos_output_0\"]."
    ));
    assert!(module.rocq_module.contains(
        "Definition target_output_signature : list (Tuple.attribute TNull) :=\n  [AttrInt32 \"__logos_output_0\"; AttrInt32 \"__logos_output_1\"]."
    ));
}

#[test]
fn preserves_string_typmods_in_unequal_output_signatures() {
    let query = |name: &str, length: u32| Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "'a'".to_owned(),
            })]],
            output: vec![typed_column(name, SqlType::varchar(Some(length)))],
        },
        analysis_errors: vec![],
    };
    let mut source = lower_query(&query("left", 2));
    let mut target = lower_query(&query("right", 3));

    finalize_output_pair(&mut source, &mut target);

    assert_eq!(
        source.output_signature.as_ref().unwrap()[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length: Some(2) },
        }
    );
    assert_eq!(
        target.output_signature.as_ref().unwrap()[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length: Some(3) },
        }
    );
    for lowered in [&source, &target] {
        assert!(lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "output_type_mismatch"
                && diagnostic.severity == DiagnosticSeverity::Warning
        }));
    }
    let module = emit_rocq_query_module_with_signatures(
        source.query_expr.as_ref().unwrap(),
        source.output_signature.as_deref().unwrap(),
        target.query_expr.as_ref().unwrap(),
        target.output_signature.as_deref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AttrString \"left\" (StringVarcharN 2)")
    );
    assert!(
        module
            .rocq_module
            .contains("AttrString \"right\" (StringVarcharN 3)")
    );
}

#[test]
fn lowers_ordered_query_programs_without_flattening_statement_signatures() {
    let source_program = vec![
        program_values_query("source_first", 6),
        program_values_query("source_second", 12),
    ];
    let target_program = vec![
        program_values_query("target_first", 6),
        program_values_query("target_second", 12),
    ];
    let input = VerificationIr {
        sql_environment: Default::default(),
        schema: Schema { tables: Vec::new() },
        source_program,
        target_program,
    };

    let report = lower_verification_input(&input);

    assert_eq!(report.source.status, LoweringStatus::Lowered);
    assert_eq!(report.target.status, LoweringStatus::Lowered);
    assert_eq!(report.source.statements.len(), 2);
    assert_eq!(report.target.statements.len(), 2);
    assert_eq!(
        report
            .source
            .statements
            .iter()
            .map(|statement| statement.output_signature.as_ref().unwrap().len())
            .collect::<Vec<_>>(),
        vec![6, 12]
    );
    let query_module = report.query_module.as_ref().unwrap();
    let module = &query_module.rocq_module;
    assert!(module.contains("Definition source_query_expr_0 : QueryExpr"));
    assert!(module.contains("Definition source_query_expr_1 : QueryExpr"));
    assert!(module.contains("Definition target_query_expr_0 : QueryExpr"));
    assert!(module.contains("Definition target_query_expr_1 : QueryExpr"));
    assert!(module.contains(
        "Definition source_query_program : list QueryExpr :=\n  [source_query_expr_0; source_query_expr_1]."
    ));
    assert!(module.contains(
        "Definition target_query_program : list QueryExpr :=\n  [target_query_expr_0; target_query_expr_1]."
    ));
    assert!(module.contains(
        "Definition source_program_output_signatures : list (list (Tuple.attribute TNull)) :=\n  [source_output_signature_0; source_output_signature_1]."
    ));
    assert!(module.contains(
        "Definition target_program_output_signatures : list (list (Tuple.attribute TNull)) :=\n  [target_output_signature_0; target_output_signature_1]."
    ));
    assert_eq!(
        query_module
            .definition_graph
            .source_statements
            .iter()
            .map(|statement| (
                statement.statement_index,
                statement.root_symbol.as_str(),
                statement.output_signature_symbol.as_str(),
            ))
            .collect::<Vec<_>>(),
        vec![
            (1, "source_query_expr_0", "source_output_signature_0"),
            (2, "source_query_expr_1", "source_output_signature_1"),
        ]
    );
    assert_eq!(
        query_module
            .definition_graph
            .target_statements
            .iter()
            .map(|statement| statement.root_symbol.as_str())
            .collect::<Vec<_>>(),
        vec!["target_query_expr_0", "target_query_expr_1"]
    );
}

#[test]
fn paired_root_analysis_errors_survive_output_normalization_and_emit_modules() {
    let query = |output_name: &str| Query {
        source_sql: Some("select 1 as x order by x + 1".to_owned()),
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            })]],
            output: vec![typed_column(output_name, SqlType::Integer)],
        },
        analysis_errors: vec![
            QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                sql_state: "42703".to_owned(),
                query_block_id: "query-0".to_owned(),
                source_order_item_node_id: "query-0/order-0".to_owned(),
                source_order_item_sql: "x + 1".to_owned(),
                output_alias: "x".to_owned(),
            },
        ],
    };
    let input = VerificationIr {
        sql_environment: Default::default(),
        schema: Schema { tables: Vec::new() },
        source_program: vec![query("source_x")],
        target_program: vec![query("target_x")],
    };

    let report = lower_verification_input_with_mode(
        &input,
        &LoweringConfig::default(),
        VerificationMode::OutcomeUnconditional,
    );

    assert_eq!(report.source.status, LoweringStatus::Lowered);
    assert_eq!(report.target.status, LoweringStatus::Lowered);
    for statement in [&report.source.statements[0], &report.target.statements[0]] {
        let Some(FormalQueryExpr::Error { columns, error }) = statement.query_expr.as_ref() else {
            panic!("query-wide SQL error must remain at the normalized root: {statement:#?}");
        };
        assert_eq!(*error, FormalQueryError::UndefinedColumn);
        assert_eq!(columns, statement.output_signature.as_ref().unwrap());
        assert_eq!(columns[0].name, "__logos_output_0");
    }
    let query_module = report
        .query_module
        .as_ref()
        .expect("paired root errors must retain generated query authority");
    assert_eq!(query_module.rocq_module.matches("QExpr_Error").count(), 2);
    assert!(!query_module.rocq_module.contains("QExpr_Projection"));
    assert!(
        query_module
            .rocq_module
            .contains("TNullQueryExprAdmissibleWithOutputs")
    );
    assert!(report.proof_module.is_some());
}

#[test]
fn unequal_program_lengths_remain_fully_emitted_and_cannot_be_truncated() {
    let input = VerificationIr {
        sql_environment: Default::default(),
        schema: Schema { tables: Vec::new() },
        source_program: vec![
            program_values_query("source_0", 1),
            program_values_query("source_1", 2),
            program_values_query("source_2", 3),
        ],
        target_program: vec![program_values_query("target_0", 1)],
    };

    let report = lower_verification_input(&input);

    assert_eq!(report.source.status, LoweringStatus::Lowered);
    assert_eq!(report.target.status, LoweringStatus::Lowered);
    assert_eq!(report.source.statements.len(), 3);
    assert_eq!(report.target.statements.len(), 1);
    assert!(
        report
            .source
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "statement_count_mismatch" })
    );
    let module = &report.query_module.as_ref().unwrap().rocq_module;
    assert!(module.contains("[source_query_expr_0; source_query_expr_1; source_query_expr_2]."));
    assert!(module.contains("[target_query_expr]."));
    assert!(
        report
            .proof_module
            .as_ref()
            .unwrap()
            .rocq_module
            .contains("generated_query_program_equiv db\n        (source_query_program)\n        (target_query_program)")
    );
}

#[test]
fn blocked_program_statement_prevents_partial_rocq_module_emission() {
    let safe = program_values_query("safe", 1);
    let blocked = Query {
        source_sql: Some("select exp(x) from t".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![typed_column("x", SqlType::Double)],
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "EXP".to_owned(),
                op: ScalarOp::Exp,
                args: vec![ScalarAst::InputRef { index: 0 }],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("result", SqlType::Double)],
        },
        analysis_errors: vec![],
    };
    let input = VerificationIr {
        sql_environment: Default::default(),
        schema: Schema {
            tables: vec![Table {
                name: "t".to_owned(),
                columns: vec![typed_column("x", SqlType::Double)],
                constraints: Default::default(),
            }],
        },
        source_program: vec![safe.clone(), blocked],
        target_program: vec![safe.clone(), safe],
    };

    let report = lower_verification_input(&input);

    assert_eq!(report.source.statements.len(), 2);
    assert_eq!(report.source.statements[0].status, LoweringStatus::Lowered);
    assert_eq!(report.source.statements[1].status, LoweringStatus::Blocked);
    assert_eq!(report.source.status, LoweringStatus::Blocked);
    assert_eq!(report.target.status, LoweringStatus::Lowered);
    assert!(report.query_module.is_none());
    assert!(report.proof_module.is_none());
}

fn program_values_query(label_prefix: &str, arity: usize) -> Query {
    let output = (0..arity)
        .map(|index| column(&format!("{label_prefix}_{index}")))
        .collect::<Vec<_>>();
    let row = (0..arity)
        .map(|index| {
            scalar(ScalarAst::Literal {
                raw: (index + 1).to_string(),
            })
        })
        .collect::<Vec<_>>();
    Query {
        source_sql: Some(format!("select {label_prefix}")),
        rel: RelExpr::Values {
            rows: vec![row],
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

#[test]
fn derives_output_signature_from_authoritative_query_syntax() {
    let actual_output = vec![typed_column("actual", SqlType::Integer)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })]],
            output: actual_output,
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(
        lowered.output_signature,
        Some(vec![FormalAttribute {
            name: "actual".to_owned(),
            ty: FormalAttributeType::Int32,
        }])
    );
    assert_eq!(
        query_expr_output_signature(lowered.query_expr.as_ref().unwrap()).unwrap(),
        lowered.output_signature.unwrap()
    );
}

fn schema_bound_scan_query(relation: &str, output: Vec<Column>) -> Query {
    Query {
        source_sql: None,
        rel: RelExpr::TableScan {
            table: vec![relation.to_owned()],
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

fn one_column_schema(relation: &str, column: Column) -> Schema {
    Schema {
        tables: vec![Table {
            name: relation.to_owned(),
            columns: vec![column],
            constraints: Default::default(),
        }],
    }
}

#[test]
fn schema_bound_direct_scan_carries_authoritative_ordered_columns() {
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: vec![
                typed_column("a", SqlType::Integer),
                typed_column("label", SqlType::varchar(Some(7))),
            ],
            constraints: Default::default(),
        }],
    };
    let query = schema_bound_scan_query(
        "t",
        vec![
            typed_column("a", SqlType::Integer),
            typed_column("label", SqlType::varchar(Some(7))),
        ],
    );
    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(
        lowered.output_signature,
        Some(vec![
            FormalAttribute {
                name: "a".to_owned(),
                ty: FormalAttributeType::Int32,
            },
            FormalAttribute {
                name: "label".to_owned(),
                ty: FormalAttributeType::String {
                    typmod: SqlStringType::Varchar { length: Some(7) },
                },
            },
        ])
    );

    let Some(FormalQueryExpr::Table { relation, columns }) = lowered_query_expr(&lowered) else {
        panic!("schema-bound scan should carry its exact ordered table columns");
    };
    assert_eq!(relation, "t");
    assert_eq!(columns, lowered.output_signature.as_ref().unwrap());
}

#[test]
fn schema_bound_scan_rejects_stale_base_type_metadata() {
    let schema = one_column_schema("t", typed_column("a", SqlType::Integer));
    let query = schema_bound_scan_query("t", vec![typed_column("a", SqlType::Double)]);

    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered_query_expr(&lowered).is_none());
    assert!(lowered.query_expr.is_none());
    assert!(lowered.output_signature.is_none());
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "table_scan_schema_type_mismatch"
            && diagnostic.severity == DiagnosticSeverity::Error
    }));
}

#[test]
fn schema_bound_scan_rejects_stale_column_name_metadata() {
    let schema = one_column_schema("t", typed_column("a", SqlType::Integer));
    let query = schema_bound_scan_query("t", vec![typed_column("stale", SqlType::Integer)]);

    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "table_scan_schema_name_mismatch"
            && diagnostic.severity == DiagnosticSeverity::Error
    }));
}

#[test]
fn schema_bound_scan_rejects_stale_arity_metadata() {
    let schema = one_column_schema("t", typed_column("a", SqlType::Integer));
    let query = schema_bound_scan_query(
        "t",
        vec![
            typed_column("a", SqlType::Integer),
            typed_column("extra", SqlType::Integer),
        ],
    );

    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "table_scan_schema_arity_mismatch"
            && diagnostic.severity == DiagnosticSeverity::Error
    }));
}

#[test]
fn schema_bound_scan_rejects_stale_typmod_metadata() {
    let schema = one_column_schema("t", typed_column("name", SqlType::varchar(Some(4))));
    let query = schema_bound_scan_query("t", vec![typed_column("name", SqlType::varchar(Some(5)))]);

    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "table_scan_schema_type_mismatch"
            && diagnostic.message.contains("typmods")
    }));
}

#[test]
fn schema_bound_scan_rejects_unknown_relation_identity() {
    let schema = one_column_schema("t", typed_column("a", SqlType::Integer));
    let query = schema_bound_scan_query("other", vec![typed_column("a", SqlType::Integer)]);

    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "table_scan_relation_not_in_schema"
            && diagnostic.severity == DiagnosticSeverity::Error
    }));
}

#[test]
fn schema_bound_formal_table_scope_uses_authoritative_types() {
    let schema = one_column_schema("t", typed_column("a", SqlType::Integer));
    let mut context = LoweringContext::new(LoweringConfig::default(), Some(&schema));

    let scope = context
        .scope_from_lowered_query(
            "scope",
            &FormalQueryExpr::Table {
                relation: "t".to_owned(),
                columns: vec![formal_attribute("a", FormalAttributeType::Int32)],
            },
        )
        .expect("authoritative schema table scope");

    assert_eq!(scope.attributes.len(), 1);
    assert_eq!(scope.attributes[0].name, "a");
    assert_eq!(scope.attributes[0].formal_ty, FormalAttributeType::Int32);
}

#[test]
fn preserves_typed_empty_result_ordered_shape() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            rows: Vec::new(),
            output: vec![typed_column("empty_name", SqlType::varchar(Some(4)))],
        },
        analysis_errors: vec![],
    };
    let lowered = lower_query(&query);

    let output = FormalAttribute {
        name: "empty_name".to_owned(),
        ty: FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length: Some(4) },
        },
    };
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(lowered.output_signature, Some(vec![output.clone()]));
    assert!(matches!(
        lowered_query_expr(&lowered),
        Some(FormalQueryExpr::Empty { columns }) if columns == &vec![output]
    ));
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Empty { .. })
    ));
}

#[test]
fn rejects_absent_or_mismatched_ordered_output_signatures_before_rocq_emission() {
    let query = FormalQueryExpr::Set {
        op: FormalSetOp::Union,
        left: Box::new(FormalQueryExpr::Empty {
            columns: vec![formal_attribute("value", FormalAttributeType::Int32)],
        }),
        right: Box::new(FormalQueryExpr::Empty {
            columns: vec![formal_attribute("value", FormalAttributeType::Bool)],
        }),
    };
    assert!(query_expr_output_signature(&query).is_none());
    assert!(try_emit_rocq_query_module(&query, &query).is_none());

    let query = FormalQueryExpr::Empty {
        columns: vec![formal_attribute("value", FormalAttributeType::Int32)],
    };
    let wrong = vec![formal_attribute("other", FormalAttributeType::Int32)];
    assert!(
        emit_rocq_query_program_module_with_signatures(&[(&query, &wrong)], &[(&query, &wrong)],)
            .is_none()
    );
}

#[test]
fn lowers_untyped_null_values_filter_without_static_empty_rewrite() {
    let output = vec![
        typed_column("A", SqlType::Null),
        typed_column("B", SqlType::Null),
    ];
    let values = RelExpr::Values {
        rows: vec![vec![
            scalar(ScalarAst::Literal {
                raw: "NULL".to_owned(),
            }),
            scalar(ScalarAst::Literal {
                raw: "NULL".to_owned(),
            }),
        ]],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .query_expr
            .as_ref()
            .expect("filtered VALUES should lower"),
        lowered
            .query_expr
            .as_ref()
            .expect("filtered VALUES should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered_query_expr(&lowered),
        Some(FormalQueryExpr::Selection { .. })
    ));
    assert!(module.rocq_module.contains("QExpr_Filter"));
    assert!(module.rocq_module.contains("NullString"));
    assert!(module.rocq_module.contains("AttrString \"A\""));
    assert!(!module.rocq_module.contains("EmptyRelation"));
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "unresolved_null_resolved_as_text")
    );
}

#[test]
fn rejects_conflicting_inferred_values_column_types() {
    let rel = RelExpr::Values {
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
        output: vec![typed_column("A", SqlType::Any)],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
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
        rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: "'x'".to_owned(),
            }),
            ty: "VARCHAR".to_owned(),
        })]],
        output: vec![column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
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
        rows: vec![vec![
            scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            }),
            scalar(ScalarAst::Literal {
                raw: "2".to_owned(),
            }),
        ]],
        output: vec![column("A"), column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
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

fn attested_substring_group_full_sort_query() -> Query {
    let raw_output = vec![
        typed_column(
            "description",
            SqlType::String(SqlStringType::Char { length: 100 }),
        ),
        typed_column("quantity", SqlType::Integer),
        decimal_column("refunded_cash", 7, 2),
        decimal_column("fee", 7, 2),
    ];
    let input_sources = [
        source_node("description", "IDENTIFIER", None, Vec::new()),
        source_node("quantity", "IDENTIFIER", None, Vec::new()),
        source_node("refunded_cash", "IDENTIFIER", None, Vec::new()),
        source_node("fee", "IDENTIFIER", None, Vec::new()),
    ];
    let aggregate_input = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["sales_and_returns".to_owned()],
            output: raw_output.clone(),
        }),
        exprs: input_sources
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, source)| scalar_with_source(ScalarAst::InputRef { index }, source))
            .collect(),
        correlations: Vec::new(),
        output: raw_output,
    };
    let avg_source = |name: &str| {
        source_node(
            &format!("AVG({name})"),
            "OTHER_FUNCTION",
            Some("AVG"),
            vec![source_node(name, "IDENTIFIER", None, Vec::new())],
        )
    };
    let avg_call = |index: usize, name: &str| {
        let modifiers = AggregateModifiers {
            source: Some(avg_source(name)),
            source_distinct: Some(false),
            ..Default::default()
        };
        AggregateCall {
            raw: format!("AVG(${index})"),
            function: "AVG".to_owned(),
            distinct: false,
            modifiers,
            args: vec![scalar(ScalarAst::InputRef { index })],
            filter: None,
        }
    };
    let aggregate_output = vec![
        typed_column(
            "description",
            SqlType::String(SqlStringType::Char { length: 100 }),
        ),
        typed_column("avg_quantity", SqlType::Integer),
        decimal_column("avg_refunded_cash", 7, 2),
        decimal_column("avg_fee", 7, 2),
    ];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(aggregate_input),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![
            avg_call(1, "quantity"),
            avg_call(2, "refunded_cash"),
            avg_call(3, "fee"),
        ],
        output: aggregate_output,
    };
    let substring_source = source_node(
        "SUBSTRING(description, 1, 20)",
        "OTHER_FUNCTION",
        Some("SUBSTRING"),
        vec![
            input_sources[0].clone(),
            source_node("1", "LITERAL", None, Vec::new()),
            source_node("20", "LITERAL", None, Vec::new()),
        ],
    );
    let projected_output = vec![
        typed_column(
            "description_prefix",
            SqlType::String(SqlStringType::Varchar { length: None }),
        ),
        typed_column("avg_quantity", SqlType::Integer),
        decimal_column("avg_refunded_cash", 7, 2),
        decimal_column("avg_fee", 7, 2),
    ];
    let project = RelExpr::Project {
        input: Box::new(aggregate),
        exprs: vec![
            scalar_with_source(
                ScalarAst::Call {
                    operator: "SUBSTRING".to_owned(),
                    op: ScalarOp::Substring,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "1".to_owned(),
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "20".to_owned(),
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                    ],
                },
                substring_source,
            ),
            scalar_with_source(ScalarAst::InputRef { index: 1 }, avg_source("quantity")),
            scalar_with_source(
                ScalarAst::InputRef { index: 2 },
                avg_source("refunded_cash"),
            ),
            scalar_with_source(ScalarAst::InputRef { index: 3 }, avg_source("fee")),
        ],
        correlations: Vec::new(),
        output: projected_output.clone(),
    };
    query_for_rel(
        RelExpr::Sort {
            input: Box::new(project),
            collation: vec![
                SortKey {
                    field_index: 0,
                    direction: SortDirection::Descending,
                    null_direction: Some(SortNullDirection::First),
                },
                SortKey {
                    field_index: 1,
                    direction: SortDirection::Ascending,
                    null_direction: Some(SortNullDirection::Last),
                },
                SortKey {
                    field_index: 2,
                    direction: SortDirection::Descending,
                    null_direction: Some(SortNullDirection::Last),
                },
                SortKey {
                    field_index: 3,
                    direction: SortDirection::Ascending,
                    null_direction: Some(SortNullDirection::First),
                },
            ],
            fetch: Some(scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "100".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            })),
            offset: None,
            output: projected_output.clone(),
        },
        projected_output,
    )
}

#[test]
fn attested_substring_group_key_with_complete_sort_forces_all_aggregate_groups() {
    let query = attested_substring_group_full_sort_query();
    assert!(rel_expr_may_raise_runtime(&query.rel));
    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_environment: SqlEnvironment::postgres_utf8_c(),
            ..LoweringConfig::default()
        },
    );
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Fetch { count: 100, input }) = lowered.query_expr.as_ref() else {
        panic!("the source-attested full sort must use eager Fetch")
    };
    let FormalQueryExpr::OrderBy { keys, input } = input.as_ref() else {
        panic!("the source-attested pathkey mismatch must retain a full OrderBy")
    };
    assert_eq!(keys.len(), 4);
    assert_eq!(keys[0].direction, FormalSortDirection::Desc);
    assert_eq!(keys[0].null_direction, FormalNullDirection::First);
    assert_eq!(keys[3].direction, FormalSortDirection::Asc);
    assert_eq!(keys[3].null_direction, FormalNullDirection::First);
    assert!(matches!(
        input.as_ref(),
        FormalQueryExpr::Group { .. } | FormalQueryExpr::Projection { .. }
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
    assert!(module.rocq_module.contains("ScalarSubstringNonnegative"));
    assert!(module.rocq_module.contains("AggregateAverageInt32Numeric"));
    assert!(
        module
            .rocq_module
            .contains("AggregateAverageNumericAtScale")
            || module.rocq_module.contains("AggregateAverageNumericFixed")
    );
    assert!(!module.rocq_module.contains("QExpr_PgFetch"));
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_exact_dsb_085_uses_source_attested_full_sort_exhaustion() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let case = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-dsb__query085");

    for sql_name in ["sql1.sql", "sql2.sql"] {
        let output = Command::new(repo.join("scripts/calcite-ir"))
            .arg("--schema")
            .arg(case.join("schema.sql"))
            .arg("--sql")
            .arg(case.join(sql_name))
            .output()
            .expect("run Calcite wrapper on exact DSB query-085 input");
        assert!(
            output.status.success(),
            "{sql_name}: calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let raw: CalciteFile =
            serde_json::from_slice(&output.stdout).expect("parse exact wrapper JSON output");
        let ir = convert_raw_file(raw).expect("convert exact DSB query-085 IR");
        let [query] = ir.queries.as_slice() else {
            panic!("{sql_name}: expected one query")
        };
        let RelExpr::Sort {
            input,
            collation,
            fetch,
            offset,
            ..
        } = &query.rel
        else {
            panic!("{sql_name}: expected top Sort")
        };
        assert_eq!(collation.len(), 4);
        assert_eq!(
            collation
                .iter()
                .map(|key| key.field_index)
                .collect::<Vec<_>>(),
            [0, 1, 2, 3]
        );
        assert!(fetch.as_ref().is_some_and(|fetch| fetch.raw == "100"));
        assert!(offset.is_none());
        let RelExpr::Project {
            input,
            exprs,
            correlations,
            ..
        } = input.as_ref()
        else {
            panic!("{sql_name}: expected post-group Project")
        };
        assert!(correlations.is_empty());
        assert!(matches!(
            exprs[0].parsed,
            ScalarAst::Call {
                op: ScalarOp::Substring,
                ..
            }
        ));
        assert!(exprs[0].source.as_ref().is_some_and(|source| {
            source
                .operator
                .as_deref()
                .is_some_and(|operator| operator.eq_ignore_ascii_case("SUBSTRING"))
                && source.operands.len() == 3
        }));
        let RelExpr::Aggregate {
            group_keys,
            grouping_sets,
            agg_calls,
            ..
        } = input.as_ref()
        else {
            panic!("{sql_name}: expected one ordinary Aggregate")
        };
        assert_eq!(group_keys, &[0]);
        assert_eq!(grouping_sets.as_slice(), [vec![0]].as_slice());
        assert_eq!(agg_calls.len(), 3);
        assert!(
            agg_calls
                .iter()
                .all(|call| call.function.eq_ignore_ascii_case("AVG"))
        );

        let lowered = lower_query_with_config(
            query,
            &LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            },
        );
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{sql_name}: {:#?}",
            lowered.diagnostics
        );
        let Some(FormalQueryExpr::Fetch { count: 100, input }) = lowered.query_expr.as_ref() else {
            panic!("{sql_name}: exact query must use eager Fetch")
        };
        let FormalQueryExpr::OrderBy { keys, .. } = input.as_ref() else {
            panic!("{sql_name}: exact query must retain the full OrderBy")
        };
        assert_eq!(keys.len(), 4);
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("query expression"),
            lowered.query_expr.as_ref().expect("query expression"),
        );
        assert!(!module.rocq_module.trim().is_empty());
        assert!(module.rocq_module.contains("QExpr_OrderBy"));
        assert!(module.rocq_module.contains("QExpr_Fetch"));
        assert!(!module.rocq_module.contains("QExpr_PgFetch"));
    }
}

fn attested_dsb18_rollup_full_sort_query() -> Query {
    let table = |name: &str, output: Vec<Column>| RelExpr::TableScan {
        table: vec![name.to_owned()],
        output,
    };
    let join = |left: RelExpr, right: RelExpr| {
        let mut output = left.output().to_vec();
        output.extend_from_slice(right.output());
        RelExpr::Join {
            left: Box::new(left),
            right: Box::new(right),
            join_type: JoinType::Inner,
            condition: scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "true".to_owned(),
                }),
                ty: "BOOLEAN".to_owned(),
            }),
            correlations: Vec::new(),
            output,
        }
    };
    let mut joined = join(
        table(
            "catalog_sales",
            vec![
                typed_column("cs_quantity", SqlType::Integer),
                decimal_column("cs_list_price", 7, 2),
                decimal_column("cs_coupon_amt", 7, 2),
                decimal_column("cs_sales_price", 7, 2),
                decimal_column("cs_net_profit", 7, 2),
            ],
        ),
        table(
            "customer_demographics",
            vec![typed_column("cd_demo_sk", SqlType::Integer)],
        ),
    );
    joined = join(
        joined,
        table(
            "customer",
            vec![typed_column("c_birth_year", SqlType::Integer)],
        ),
    );
    joined = join(
        joined,
        table(
            "customer_address",
            vec![
                typed_column(
                    "ca_country",
                    SqlType::String(SqlStringType::Varchar { length: Some(20) }),
                ),
                typed_column(
                    "ca_state",
                    SqlType::String(SqlStringType::Char { length: 2 }),
                ),
                typed_column(
                    "ca_county",
                    SqlType::String(SqlStringType::Varchar { length: Some(30) }),
                ),
            ],
        ),
    );
    joined = join(
        joined,
        table(
            "date_dim",
            vec![typed_column("d_date_sk", SqlType::Integer)],
        ),
    );
    joined = join(
        joined,
        table(
            "item",
            vec![typed_column(
                "i_item_id",
                SqlType::String(SqlStringType::Char { length: 16 }),
            )],
        ),
    );
    let joined_output = joined.output().to_vec();
    let safe_predicate_index = joined_output
        .iter()
        .position(|column| column.name == "cs_quantity")
        .expect("test predicate input");
    let predicate_args = (0..13)
        .map(|_| ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef {
                    index: safe_predicate_index,
                },
                ScalarAst::InputRef {
                    index: safe_predicate_index,
                },
            ],
        })
        .collect::<Vec<_>>();
    let predicate_sources = (0..13)
        .map(|_| {
            source_node(
                "`cs_quantity` = `cs_quantity`",
                "EQUALS",
                Some("="),
                vec![
                    source_node("cs_quantity", "IDENTIFIER", None, Vec::new()),
                    source_node("cs_quantity", "IDENTIFIER", None, Vec::new()),
                ],
            )
        })
        .collect::<Vec<_>>();
    let filtered = RelExpr::Filter {
        input: Box::new(joined),
        predicate: scalar_with_source(
            ScalarAst::Call {
                operator: "AND".to_owned(),
                op: ScalarOp::And,
                args: predicate_args,
            },
            source_node(
                &std::iter::repeat_n("`cs_quantity` = `cs_quantity`", 13)
                    .collect::<Vec<_>>()
                    .join(" AND "),
                "AND",
                Some("AND"),
                predicate_sources,
            ),
        ),
        correlations: Vec::new(),
        output: joined_output.clone(),
    };

    let group_specs = [
        (
            "i_item_id",
            SqlType::String(SqlStringType::Char { length: 16 }),
        ),
        (
            "ca_country",
            SqlType::String(SqlStringType::Varchar { length: Some(20) }),
        ),
        (
            "ca_state",
            SqlType::String(SqlStringType::Char { length: 2 }),
        ),
        (
            "ca_county",
            SqlType::String(SqlStringType::Varchar { length: Some(30) }),
        ),
    ];
    let avg_names = [
        "cs_quantity",
        "cs_list_price",
        "cs_coupon_amt",
        "cs_sales_price",
        "cs_net_profit",
        "c_birth_year",
    ];
    let position = |name: &str| {
        joined_output
            .iter()
            .position(|column| column.name == name)
            .expect("test input column")
    };
    let mut project_exprs = group_specs
        .iter()
        .map(|(name, _)| {
            scalar_with_source(
                ScalarAst::InputRef {
                    index: position(name),
                },
                source_node(name, "IDENTIFIER", None, Vec::new()),
            )
        })
        .collect::<Vec<_>>();
    let mut project_output = group_specs
        .iter()
        .map(|(name, ty)| typed_column(name, ty.clone()))
        .collect::<Vec<_>>();
    for (index, name) in avg_names.iter().enumerate() {
        let identifier = source_node(name, "IDENTIFIER", None, Vec::new());
        let cast_sql = format!("CAST(`{name}` AS DECIMAL(12, 2))");
        project_exprs.push(scalar_with_source(
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef {
                        index: position(name),
                    }],
                }),
                ty: "DECIMAL(12,2)".to_owned(),
            },
            source_node(&cast_sql, "CAST", Some("CAST"), vec![identifier]),
        ));
        project_output.push(decimal_column(&format!("$f{}", index + 4), 12, 2));
    }
    let aggregate_input = RelExpr::Project {
        input: Box::new(filtered),
        exprs: project_exprs,
        correlations: Vec::new(),
        output: project_output,
    };

    let agg_calls = avg_names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            let identifier = source_node(name, "IDENTIFIER", None, Vec::new());
            let cast_sql = format!("CAST(`{name}` AS DECIMAL(12, 2))");
            let source_cast = source_node(
                &cast_sql,
                "CAST",
                Some("CAST"),
                vec![
                    identifier,
                    source_node("DECIMAL(12, 2)", "OTHER", None, Vec::new()),
                ],
            );
            let modifiers = AggregateModifiers {
                source: Some(source_node(
                    &format!("AVG({cast_sql})"),
                    "OTHER_FUNCTION",
                    Some("avg"),
                    vec![source_cast],
                )),
                source_distinct: Some(false),
                ..Default::default()
            };
            AggregateCall {
                raw: format!("AVG(${})", index + 4),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers,
                args: vec![scalar(ScalarAst::InputRef { index: index + 4 })],
                filter: None,
            }
        })
        .collect::<Vec<_>>();
    let mut aggregate_output = group_specs
        .iter()
        .map(|(name, ty)| typed_column(name, ty.clone()))
        .collect::<Vec<_>>();
    aggregate_output.extend((1..=6).map(|index| decimal_column(&format!("agg{index}"), 12, 2)));
    let aggregate = RelExpr::Aggregate {
        input: Box::new(aggregate_input),
        group_keys: vec![0, 1, 2, 3],
        grouping_sets: vec![
            vec![0, 1, 2, 3],
            vec![0, 1, 2],
            vec![0, 1],
            vec![0],
            Vec::new(),
        ],
        agg_calls,
        output: aggregate_output.clone(),
    };
    query_for_rel(
        RelExpr::Sort {
            input: Box::new(aggregate),
            collation: [1, 2, 3, 0]
                .into_iter()
                .map(|field_index| SortKey {
                    field_index,
                    direction: SortDirection::Ascending,
                    null_direction: Some(SortNullDirection::Last),
                })
                .collect(),
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "100".to_owned(),
            })),
            offset: None,
            output: aggregate_output.clone(),
        },
        aggregate_output,
    )
}

#[test]
fn attested_dsb18_rollup_permutation_forces_complete_grouping_sets_sort() {
    let query = attested_dsb18_rollup_full_sort_query();
    assert!(rel_expr_may_raise_runtime(&query.rel));
    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_environment: SqlEnvironment::postgres_utf8_c(),
            ..LoweringConfig::default()
        },
    );
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Fetch { count: 100, input }) = lowered.query_expr.as_ref() else {
        panic!("the exact DSB18 full sort must retain eager Fetch")
    };
    let FormalQueryExpr::OrderBy { keys, input } = input.as_ref() else {
        panic!("the exact DSB18 pathkey permutation must retain OrderBy")
    };
    assert_eq!(keys.len(), 4);
    assert!(matches!(
        input.as_ref(),
        FormalQueryExpr::GroupingSets { grouping_sets, .. } if grouping_sets.len() == 5
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_GroupingSets"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(!module.rocq_module.contains("QExpr_PgFetch"));
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_wrapper_exact_dsb_018_uses_source_attested_rollup_full_sort() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let case = repo.join("benchmarks/core/.generated/sqlsolver/nonwetune-flat/rbot-dsb__query018");

    for sql_name in ["sql1.sql", "sql2.sql"] {
        let output = Command::new(repo.join("scripts/calcite-ir"))
            .arg("--schema")
            .arg(case.join("schema.sql"))
            .arg("--sql")
            .arg(case.join(sql_name))
            .output()
            .expect("run Calcite wrapper on exact DSB query-018 input");
        assert!(
            output.status.success(),
            "{sql_name}: calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let raw: CalciteFile =
            serde_json::from_slice(&output.stdout).expect("parse exact wrapper JSON output");
        let ir = convert_raw_file(raw).expect("convert exact DSB query-018 IR");
        let [query] = ir.queries.as_slice() else {
            panic!("{sql_name}: expected one query")
        };
        let RelExpr::Sort {
            input,
            collation,
            fetch,
            offset,
            ..
        } = &query.rel
        else {
            panic!("{sql_name}: expected top Sort")
        };
        assert_eq!(
            collation
                .iter()
                .map(|key| key.field_index)
                .collect::<Vec<_>>(),
            [1, 2, 3, 0]
        );
        assert!(fetch.as_ref().is_some_and(|fetch| fetch.raw == "100"));
        assert!(offset.is_none());
        let RelExpr::Aggregate {
            input: aggregate_input,
            group_keys,
            grouping_sets,
            agg_calls,
            ..
        } = input.as_ref()
        else {
            panic!("{sql_name}: expected grouping-sets Aggregate")
        };
        assert_eq!(group_keys, &[0, 1, 2, 3]);
        assert_eq!(
            grouping_sets.as_slice(),
            [
                vec![0, 1, 2, 3],
                vec![0, 1, 2],
                vec![0, 1],
                vec![0],
                Vec::new(),
            ]
            .as_slice()
        );
        assert_eq!(agg_calls.len(), 6);
        let RelExpr::Project { exprs, .. } = aggregate_input.as_ref() else {
            panic!("{sql_name}: expected pre-aggregate Project")
        };
        for (index, call) in agg_calls.iter().enumerate() {
            assert!(call.function.eq_ignore_ascii_case("AVG"));
            let source = call.modifiers.source.as_ref().expect("AVG source node");
            assert_eq!(source.operands.len(), 1);
            let call_cast = source.operands[0].as_ref().expect("AVG CAST source");
            assert!(
                call_cast
                    .operator
                    .as_deref()
                    .is_some_and(|operator| operator.eq_ignore_ascii_case("CAST"))
            );
            assert!(source_nodes_identical(
                call_cast,
                exprs[index + 4]
                    .source
                    .as_ref()
                    .expect("Project CAST source")
            ));
        }

        let lowered = lower_query_with_config(
            query,
            &LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            },
        );
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{sql_name}: {:#?}",
            lowered.diagnostics
        );
        let Some(FormalQueryExpr::Fetch { count: 100, input }) = lowered.query_expr.as_ref() else {
            panic!("{sql_name}: exact query must use eager Fetch")
        };
        let FormalQueryExpr::OrderBy { input, .. } = input.as_ref() else {
            panic!("{sql_name}: exact query must retain full OrderBy")
        };
        assert!(matches!(
            input.as_ref(),
            FormalQueryExpr::GroupingSets { grouping_sets, .. } if grouping_sets.len() == 5
        ));
    }
}

#[test]
fn positive_fetch_ordered_by_aggregate_result_forces_complete_sort_input() {
    let aggregate_output = vec![
        column("group_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("group_key")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![count_star_call()],
        output: aggregate_output,
    };
    let projected_output = vec![
        typed_column("row_count", SqlType::BigInt),
        column("group_key"),
    ];
    let project = RelExpr::Project {
        input: Box::new(aggregate),
        exprs: vec![
            scalar(ScalarAst::InputRef { index: 1 }),
            scalar(ScalarAst::InputRef { index: 0 }),
        ],
        correlations: Vec::new(),
        output: projected_output.clone(),
    };
    let query = query_for_rel(
        RelExpr::Sort {
            input: Box::new(project),
            collation: vec![SortKey {
                field_index: 0,
                direction: SortDirection::Descending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })),
            offset: None,
            output: projected_output.clone(),
        },
        projected_output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Fetch { count: 1, input }) = lowered.query_expr.as_ref() else {
        panic!("positive LIMIT over the forced aggregate sort should use eager Fetch");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::OrderBy { .. }));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Fetch"));
    assert!(module.rocq_module.contains("QExpr_OrderBy"));
    assert!(!module.rocq_module.contains("QExpr_PgFetch"));
}

fn nulls_first_grouping_sets_fetch_query() -> Query {
    let mut channel = typed_column("group_0", SqlType::text());
    channel.nullable = false;
    let input_output = vec![channel, column("group_1"), column("value")];
    let aggregate_output = vec![
        typed_column("group_0", SqlType::text()),
        column("group_1"),
        typed_column("sum_value", SqlType::BigInt),
    ];
    let literal_branch = |table: &str, literal: &str| RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec![table.to_owned()],
            output: vec![column("group_1"), column("value")],
        }),
        exprs: vec![
            scalar_with_source(
                ScalarAst::Literal {
                    raw: literal.to_owned(),
                },
                source_node(literal, "LITERAL", None, Vec::new()),
            ),
            scalar(ScalarAst::InputRef { index: 0 }),
            scalar(ScalarAst::InputRef { index: 1 }),
        ],
        correlations: Vec::new(),
        output: input_output.clone(),
    };
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![
                literal_branch("left_items", "'left channel'"),
                literal_branch("right_items", "'right channel'"),
            ],
            output: input_output,
        }),
        group_keys: vec![0, 1],
        grouping_sets: vec![vec![0, 1], vec![0], Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "SUM($2)".to_owned(),
            function: "SUM".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers {
                source_grouping: Some(SourceGroupingProvenance {
                    kind: "ROLLUP".to_owned(),
                    query_block_id: "1:1-1:200".to_owned(),
                    source_select_node_id: "1:1-1:200".to_owned(),
                    source_select_sql:
                        "SELECT group_0, group_1, SUM(value) FROM channels GROUP BY ROLLUP(group_0, group_1)"
                            .to_owned(),
                    source_group_sql: "ROLLUP(group_0, group_1)".to_owned(),
                    group_indexes: vec![0, 1],
                    grouping_sets: vec![vec![0, 1], vec![0], Vec::new()],
                    source_has_where: false,
                    source_has_having: false,
                }),
                ..AggregateModifiers::default()
            },
            args: vec![scalar(ScalarAst::InputRef { index: 2 })],
            filter: None,
        }],
        output: aggregate_output.clone(),
    };
    query_for_rel(
        RelExpr::Sort {
            input: Box::new(aggregate),
            collation: vec![
                SortKey {
                    field_index: 0,
                    direction: SortDirection::Ascending,
                    null_direction: Some(SortNullDirection::First),
                },
                SortKey {
                    field_index: 1,
                    direction: SortDirection::Ascending,
                    null_direction: Some(SortNullDirection::First),
                },
            ],
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "100".to_owned(),
            })),
            offset: None,
            output: aggregate_output.clone(),
        },
        aggregate_output,
    )
}

fn risky_grouped_set_branch(table: &str) -> RelExpr {
    let output = vec![
        column("group_0"),
        typed_column("sum_value", SqlType::BigInt),
    ];
    RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec![table.to_owned()],
            output: vec![column("group_0"), column("value")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![AggregateCall {
            raw: "SUM($1)".to_owned(),
            function: "SUM".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::InputRef { index: 1 })],
            filter: None,
        }],
        output,
    }
}

fn nulls_first_union_distinct_fetch_query(all: bool) -> Query {
    let set_output = vec![
        column("group_0"),
        typed_column("sum_value", SqlType::BigInt),
    ];
    let set = RelExpr::Set {
        op: SetOp::Union,
        all,
        inputs: vec![
            risky_grouped_set_branch("left_items"),
            risky_grouped_set_branch("right_items"),
        ],
        output: set_output.clone(),
    };
    let project = RelExpr::Project {
        input: Box::new(set),
        exprs: vec![
            scalar(ScalarAst::InputRef { index: 0 }),
            scalar(ScalarAst::InputRef { index: 1 }),
        ],
        correlations: Vec::new(),
        output: set_output.clone(),
    };
    query_for_rel(
        RelExpr::Sort {
            input: Box::new(project),
            collation: vec![SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: Some(SortNullDirection::First),
            }],
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "100".to_owned(),
            })),
            offset: None,
            output: set_output.clone(),
        },
        set_output,
    )
}

#[test]
fn nulls_first_over_grouping_sets_or_union_distinct_forces_complete_sort() {
    for (label, query) in [
        ("grouping sets", nulls_first_grouping_sets_fetch_query()),
        (
            "union distinct",
            nulls_first_union_distinct_fetch_query(false),
        ),
    ] {
        let lowered = lower_query_with_config(
            &query,
            &LoweringConfig {
                sql_environment: SqlEnvironment::postgres_utf8_c(),
                ..LoweringConfig::default()
            },
        );
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        let Some(FormalQueryExpr::Fetch { count: 100, input }) = lowered.query_expr.as_ref() else {
            panic!("{label}: forced full sort must use eager Fetch")
        };
        assert!(matches!(input.as_ref(), FormalQueryExpr::OrderBy { .. }));
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().unwrap(),
            lowered.query_expr.as_ref().unwrap(),
        );
        assert!(module.rocq_module.contains("QExpr_Fetch (100%nat)"));
        assert!(module.rocq_module.contains("QExpr_OrderBy"));
        assert!(module.rocq_module.contains("AggregateSumInt32"));
        assert!(!module.rocq_module.contains("QExpr_PgFetch"));
    }
}

#[test]
fn aggregate_result_sort_exhausts_every_union_all_branch() {
    let output = vec![
        column("group_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let aggregate_branch = |table: &str| RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec![table.to_owned()],
            output: vec![column("group_key")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![count_star_call()],
        output: output.clone(),
    };
    let query = query_for_rel(
        RelExpr::Sort {
            input: Box::new(RelExpr::Set {
                op: SetOp::Union,
                all: true,
                inputs: vec![
                    aggregate_branch("left_items"),
                    aggregate_branch("right_items"),
                ],
                output: output.clone(),
            }),
            collation: vec![SortKey {
                field_index: 1,
                direction: SortDirection::Descending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })),
            offset: None,
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Fetch { .. })
    ));
}

#[test]
fn keeps_zero_offset_over_error_capable_child() {
    let input_output = vec![column("NUMERATOR"), column("DENOMINATOR")];
    let output = vec![column("QUOTIENT")];
    let rel = RelExpr::Sort {
        input: Box::new(RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["VALUES".to_owned()],
                output: input_output,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: output.clone(),
        }),
        collation: Vec::new(),
        fetch: None,
        offset: Some(Box::new(scalar(ScalarAst::Literal {
            raw: "0".to_owned(),
        }))),
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Offset { count: 0, .. })
    ));
}

#[test]
fn keeps_aggregate_referenced_through_dynamic_outer_case() {
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["employees".to_owned()],
            output: vec![typed_column("sal", SqlType::Integer)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![
            AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            },
            count_star_call(),
            AggregateCall {
                raw: "SUM($0)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            },
        ],
        output: vec![
            decimal_column_unconstrained("average_sal"),
            typed_column("row_count", SqlType::BigInt),
            typed_column("sum_sal", SqlType::BigInt),
        ],
    };
    let guarded_sum = ScalarAst::Call {
        operator: "CASE".to_owned(),
        op: ScalarOp::Case,
        args: vec![
            ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 1 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "0".to_owned(),
                        }),
                        ty: "BIGINT".to_owned(),
                    },
                ],
            },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "NULL".to_owned(),
                }),
                ty: "BIGINT".to_owned(),
            },
            ScalarAst::InputRef { index: 2 },
        ],
    };
    let output = vec![
        decimal_column_unconstrained("average_sal"),
        typed_column("guarded_sum", SqlType::BigInt),
    ];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(aggregate),
            exprs: vec![
                scalar(ScalarAst::InputRef { index: 0 }),
                scalar(guarded_sum),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "diagnostics: {:#?}",
        lowered.diagnostics
    );
}

#[test]
fn keeps_aggregate_referenced_through_binary_subtraction() {
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![typed_column("x", SqlType::Integer)],
        }),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![AggregateCall {
            raw: "COUNT(10 / x)".to_owned(),
            function: "COUNT".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            filter: None,
        }],
        output: vec![typed_column("risky_count", SqlType::BigInt)],
    };
    let output = vec![typed_column("difference", SqlType::BigInt)];
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(aggregate),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "-".to_owned(),
                op: ScalarOp::Minus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
}

#[test]
fn keeps_demanded_union_all_value_and_value_sensitive_union_distinct() {
    let union_output = vec![column("y")];
    let inputs = || {
        vec![
            runtime_risky_unary_project("t", "x", "y"),
            one_row_values(
                union_output.clone(),
                vec![ScalarAst::Literal {
                    raw: "1".to_owned(),
                }],
            ),
        ]
    };

    let union_all = query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: inputs(),
            output: union_output.clone(),
        },
        union_output.clone(),
    );
    assert_eq!(lower_query(&union_all).status, LoweringStatus::Lowered);

    let union_distinct = RelExpr::Set {
        op: SetOp::Union,
        all: false,
        inputs: inputs(),
        output: union_output.clone(),
    };
    let count = RelExpr::Aggregate {
        input: Box::new(union_distinct),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![count_star_call()],
        output: vec![typed_column("row_count", SqlType::BigInt)],
    };
    let distinct_count = query_for_rel(count, vec![typed_column("row_count", SqlType::BigInt)]);
    assert_eq!(lower_query(&distinct_count).status, LoweringStatus::Lowered);
}

#[test]
fn keeps_intrinsic_filter_error_when_cardinality_is_demanded() {
    let filtered = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![column("x")],
        }),
        predicate: division_is_positive(),
        correlations: Vec::new(),
        output: vec![column("x")],
    };
    let count = RelExpr::Aggregate {
        input: Box::new(filtered),
        group_keys: Vec::new(),
        grouping_sets: vec![Vec::new()],
        agg_calls: vec![count_star_call()],
        output: vec![typed_column("row_count", SqlType::BigInt)],
    };
    let query = query_for_rel(count, vec![typed_column("row_count", SqlType::BigInt)]);

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
}

#[test]
fn keeps_provably_total_numeric_casts_under_fetch() {
    let cases = [
        (
            decimal_column("amount", 7, 2),
            decimal_column("amount_cast", 12, 2),
            "DECIMAL(12, 2)",
            "ScalarCastToNumericTypmod ScalarSourceNumeric",
        ),
        (
            column("amount"),
            decimal_column("amount_cast", 12, 2),
            "DECIMAL(12, 2)",
            "ScalarCastToNumericTypmod ScalarSourceInt32",
        ),
        (
            decimal_column("amount", 7, 2),
            decimal_column("amount_cast", 7, 1),
            "DECIMAL(7, 1)",
            "ScalarCastToNumericTypmod ScalarSourceNumeric",
        ),
    ];

    for (input_column, output_column, target, operator) in cases {
        let project = numeric_cast_project(input_column, output_column.clone(), target);
        let output = vec![output_column];
        let query = Query {
            source_sql: None,
            rel: RelExpr::Sort {
                input: Box::new(project),
                collation: Vec::new(),
                fetch: Some(scalar(ScalarAst::Literal {
                    raw: "1".to_owned(),
                })),
                offset: None,
                output: output.clone(),
            },
            analysis_errors: vec![],
        };

        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Lowered, "{operator}");
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("query expression"),
            lowered.query_expr.as_ref().expect("query expression"),
        );
        assert!(module.rocq_module.contains(operator), "{operator}");
    }
}

#[test]
fn lowers_total_int32_to_double_cast_under_offset() {
    let output = vec![typed_column("amount_cast", SqlType::Double)];
    let project = numeric_cast_project(column("amount"), output[0].clone(), "DOUBLE");
    let query = Query {
        source_sql: None,
        rel: RelExpr::Sort {
            input: Box::new(project),
            collation: vec![SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: Some(SortNullDirection::Last),
            }],
            fetch: None,
            offset: Some(Box::new(scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            }))),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastInt32ToDouble")
    );
}

#[test]
fn native_exists_preserves_dead_target_syntax_without_evaluating_it() {
    let subquery = numeric_cast_project(
        decimal_column("amount", 7, 2),
        decimal_column("amount_cast", 12, 2),
        "DECIMAL(12, 2)",
    );
    let outer_output = vec![column("id")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["outer_values".to_owned()],
                output: outer_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "EXISTS".to_owned(),
                op: ScalarOp::Exists,
                args: vec![ScalarAst::RelSubquery {
                    rel: Box::new(subquery),
                }],
            }),
            correlations: Vec::new(),
            output: outer_output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("SExpr_Exists"));
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumericTypmod ScalarSourceNumeric")
    );
    assert!(!module.rocq_module.contains("QExpr_Set Union"));
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
        analysis_errors: vec![],
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Group {
        group_by, input, ..
    }) = lowered_query_expr(&lowered)
    else {
        panic!("UNION DISTINCT should lower to duplicate elimination over bag union");
    };
    assert_eq!(group_by.len(), 1);
    assert!(matches!(
        input.as_ref(),
        FormalQueryExpr::Set {
            op: FormalSetOp::Union,
            ..
        }
    ));
}

#[test]
fn set_common_type_uses_child_numeric_types_and_models_typmod_erasure() {
    let output = vec![decimal_column("sales", 17, 2)];
    let union = |inputs| RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs,
        output: output.clone(),
    };

    let lowered = lower_query(&query_for_rel(
        union(vec![
            set_numeric_product_branch(None),
            set_numeric_product_branch(None),
        ]),
        output.clone(),
    ));
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_set_numeric_type_overridden" })
    );
    assert!(matches!(
        lowered.output_signature.as_deref(),
        Some([FormalAttribute {
            ty: FormalAttributeType::Numeric,
            ..
        }])
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("numeric UNION ALL"),
        lowered.query_expr.as_ref().expect("numeric UNION ALL"),
    );
    assert!(module.rocq_module.contains("QExpr_Set Union"));
    assert!(module.rocq_module.contains("ScalarMultiply ScalarNumeric"));
    assert!(
        !module
            .rocq_module
            .contains("ScalarCastToNumericTypmod ScalarSourceNumeric")
    );

    let explicit = lower_query(&query_for_rel(
        union(vec![
            set_numeric_product_branch(Some("DECIMAL(17, 2)")),
            set_numeric_product_branch(Some("DECIMAL(17, 2)")),
        ]),
        output.clone(),
    ));
    assert_eq!(
        explicit.status,
        LoweringStatus::Lowered,
        "{:#?}",
        explicit.diagnostics
    );
    assert!(
        !explicit
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_set_numeric_type_overridden" })
    );
    let module = emit_rocq_query_module(
        explicit
            .query_expr
            .as_ref()
            .expect("explicit-cast UNION ALL"),
        explicit
            .query_expr
            .as_ref()
            .expect("explicit-cast UNION ALL"),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumericTypmod ScalarSourceNumeric")
    );

    let mixed = lower_query(&query_for_rel(
        union(vec![
            set_numeric_product_branch(None),
            set_numeric_product_branch(Some("DECIMAL(17, 2)")),
        ]),
        output,
    ));
    assert_eq!(
        mixed.status,
        LoweringStatus::Lowered,
        "{:#?}",
        mixed.diagnostics
    );
    assert!(
        mixed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "calcite_set_numeric_type_overridden"),
        "{:#?}",
        mixed.diagnostics
    );
    assert!(matches!(
        mixed.output_signature.as_deref(),
        Some([FormalAttribute {
            ty: FormalAttributeType::Numeric,
            ..
        }])
    ));
    let module = emit_rocq_query_module(
        mixed.query_expr.as_ref().expect("mixed numeric UNION ALL"),
        mixed.query_expr.as_ref().expect("mixed numeric UNION ALL"),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCastToNumericTypmod ScalarSourceNumeric")
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast (ScalarCastToNumeric ScalarSourceNumeric)")
    );
}

#[test]
fn set_string_common_type_is_binary_ordered_and_typmod_exact() {
    let cases = [
        (
            "text then char",
            SqlType::text(),
            SqlType::character(3),
            FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
            true,
        ),
        (
            "char then text",
            SqlType::character(3),
            SqlType::text(),
            FormalAttributeType::String {
                typmod: SqlStringType::Bpchar,
            },
            true,
        ),
        (
            "different varchar typmods",
            SqlType::varchar(Some(2)),
            SqlType::varchar(Some(3)),
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: None },
            },
            true,
        ),
        (
            "different char typmods",
            SqlType::character(2),
            SqlType::character(3),
            FormalAttributeType::String {
                typmod: SqlStringType::Bpchar,
            },
            true,
        ),
        (
            "identical varchar typmods",
            SqlType::varchar(Some(2)),
            SqlType::varchar(Some(2)),
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: Some(2) },
            },
            false,
        ),
        (
            "identical char typmods",
            SqlType::character(2),
            SqlType::character(2),
            FormalAttributeType::String {
                typmod: SqlStringType::Char { length: 2 },
            },
            false,
        ),
    ];

    for (label, left_ty, right_ty, expected, needs_coercion) in cases {
        let output = vec![typed_column("value", SqlType::text())];
        let query = query_for_rel(
            RelExpr::Set {
                op: SetOp::Union,
                all: true,
                inputs: vec![
                    singleton_string_values("left_value", left_ty, "'a'"),
                    singleton_string_values("right_value", right_ty, "'b'"),
                ],
                output: output.clone(),
            },
            output,
        );
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert!(
            lowered_query_expr(&lowered).is_some(),
            "{label}: unified relational path"
        );
        assert!(
            lowered.query_expr.is_some(),
            "{label}: query-expression path"
        );
        assert_eq!(
            lowered
                .output_signature
                .as_deref()
                .and_then(|signature| signature.first())
                .map(|attribute| attribute.ty),
            Some(expected),
            "{label}"
        );
        let module = emit_rocq_query_module(
            lowered.query_expr.as_ref().expect("set query expression"),
            lowered.query_expr.as_ref().expect("set query expression"),
        );
        assert_eq!(
            module.rocq_module.contains("ScalarCoerceStringImplicit"),
            needs_coercion,
            "{label}"
        );
    }
}

#[test]
fn set_unknown_null_uses_source_provenance_and_drops_common_typmod() {
    let varchar_3 = SqlType::varchar(Some(3));
    let output = vec![typed_column("value", varchar_3.clone())];
    let query = query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: false,
            inputs: vec![
                source_unknown_null_project(varchar_3.clone(), true),
                singleton_string_values("known", varchar_3, "'abc'"),
            ],
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_deref(),
        Some(
            [FormalAttribute {
                name: "value".to_owned(),
                ty: FormalAttributeType::String {
                    typmod: SqlStringType::Varchar { length: None },
                },
            }]
            .as_slice()
        )
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("unknown set query"),
        lowered.query_expr.as_ref().expect("unknown set query"),
    );
    assert!(module.rocq_module.contains("NullString StringVarchar"));
    assert!(module.rocq_module.contains("ScalarCoerceStringImplicit"));

    let mut missing = query;
    let RelExpr::Set { inputs, .. } = &mut missing.rel else {
        unreachable!("test query is a set")
    };
    let RelExpr::Project { exprs, .. } = &mut inputs[0] else {
        unreachable!("unknown branch is a project")
    };
    exprs[0].source = None;
    let blocked = lower_query(&missing);
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_unknown_literal_provenance_required")
    );

    let explicit_output = vec![typed_column("value", SqlType::varchar(Some(3)))];
    let explicit = lower_query(&query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![
                explicitly_typed_null_project(SqlType::varchar(Some(3)), "VARCHAR(3)"),
                singleton_string_values("known", SqlType::varchar(Some(3)), "'abc'"),
            ],
            output: explicit_output.clone(),
        },
        explicit_output,
    ));
    assert_eq!(explicit.status, LoweringStatus::Lowered);
    assert_eq!(
        explicit.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length: Some(3) },
        }
    );
}

#[test]
fn set_unknown_string_uses_source_provenance_and_postgres_candidate_order() {
    let cases = [
        (
            "unknown then varchar",
            true,
            SqlType::varchar(Some(3)),
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: None },
            },
        ),
        (
            "varchar then unknown",
            false,
            SqlType::varchar(Some(3)),
            FormalAttributeType::String {
                typmod: SqlStringType::Varchar { length: None },
            },
        ),
        (
            "unknown then char",
            true,
            SqlType::character(3),
            FormalAttributeType::String {
                typmod: SqlStringType::Bpchar,
            },
        ),
        (
            "text then unknown",
            false,
            SqlType::text(),
            FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
        ),
        (
            "unknown then text",
            true,
            SqlType::text(),
            FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
        ),
    ];

    for (label, unknown_left, known_ty, expected) in cases {
        let unknown = source_unknown_string_project(SqlType::text(), "'x'", true);
        let known = singleton_string_values("known", known_ty, "'y'");
        let inputs = if unknown_left {
            vec![unknown, known]
        } else {
            vec![known, unknown]
        };
        let output = vec![typed_column("value", SqlType::text())];
        let lowered = lower_query(&query_for_rel(
            RelExpr::Set {
                op: SetOp::Union,
                all: true,
                inputs,
                output: output.clone(),
            },
            output,
        ));
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert!(
            lowered_query_expr(&lowered).is_some(),
            "{label}: unified relational path"
        );
        assert!(
            lowered.query_expr.is_some(),
            "{label}: query-expression path"
        );
        assert_eq!(
            lowered.output_signature.as_deref().unwrap()[0].ty,
            expected,
            "{label}"
        );
    }

    let output = vec![typed_column("value", SqlType::varchar(None))];
    let mut missing = query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![
                source_unknown_string_project(SqlType::text(), "'x'", false),
                singleton_string_values("known", SqlType::varchar(Some(3)), "'y'"),
            ],
            output: output.clone(),
        },
        output.clone(),
    );
    let blocked = lower_query(&missing);
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_unknown_literal_provenance_required")
    );

    let attested_unknown_query = || {
        query_for_rel(
            RelExpr::Set {
                op: SetOp::Union,
                all: true,
                inputs: vec![
                    source_unknown_string_project(SqlType::text(), "'x'", true),
                    singleton_string_values("known", SqlType::varchar(Some(3)), "'y'"),
                ],
                output: output.clone(),
            },
            output.clone(),
        )
    };

    let mut forged_operands = attested_unknown_query();
    let RelExpr::Set { inputs, .. } = &mut forged_operands.rel else {
        unreachable!("test query is a set")
    };
    let RelExpr::Project { exprs, .. } = &mut inputs[0] else {
        unreachable!("unknown branch is a project")
    };
    exprs[0]
        .source
        .as_mut()
        .unwrap()
        .operands
        .push(Some(source_node("seed", "IDENTIFIER", None, Vec::new())));
    let blocked = lower_query(&forged_operands);
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_unknown_literal_provenance_required")
    );

    let mut forged_ownership = attested_unknown_query();
    let RelExpr::Set { inputs, .. } = &mut forged_ownership.rel else {
        unreachable!("test query is a set")
    };
    let RelExpr::Project { exprs, .. } = &mut inputs[0] else {
        unreachable!("unknown branch is a project")
    };
    exprs[0].source.as_mut().unwrap().clause_ownership = Some(ScalarSourceClauseOwnership {
        kind: SourceClauseKind::Where,
        query_block_id: "1:1-1:40".to_owned(),
        source_node_id: "1:20-1:23".to_owned(),
        source_sql: "'x'".to_owned(),
        analysis_errors: Vec::new(),
    });
    let blocked = lower_query(&forged_ownership);
    assert_eq!(blocked.status, LoweringStatus::Blocked);
    assert!(
        blocked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_unknown_literal_provenance_required")
    );

    let RelExpr::Set { inputs, .. } = &mut missing.rel else {
        unreachable!("test query is a set")
    };
    inputs[0] = RelExpr::Project {
        input: Box::new(source_unknown_string_project(SqlType::text(), "'x'", true)),
        exprs: vec![scalar_with_source(
            ScalarAst::InputRef { index: 0 },
            source_node("value", "IDENTIFIER", None, Vec::new()),
        )],
        correlations: Vec::new(),
        output: vec![typed_column("value", SqlType::text())],
    };
    let propagated = lower_query(&missing);
    assert_eq!(propagated.status, LoweringStatus::Blocked);
    assert!(
        propagated
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_unknown_literal_provenance_required")
    );

    let integer_output = vec![typed_column("value", SqlType::Integer)];
    let non_string = lower_query(&query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![
                source_unknown_string_project(SqlType::text(), "'1'", true),
                RelExpr::Values {
                    rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1".to_owned(),
                        }),
                        ty: "INTEGER".to_owned(),
                    })]],
                    output: integer_output.clone(),
                },
            ],
            output: integer_output.clone(),
        },
        integer_output,
    ));
    assert_eq!(non_string.status, LoweringStatus::Blocked);
    assert!(
        non_string
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_unknown_string_target_not_supported")
    );
}

#[test]
fn set_unknown_string_resolution_preserves_nested_binary_association() {
    let unknown = || source_unknown_string_project(SqlType::text(), "'x'", true);
    let known = || singleton_string_values("known", SqlType::varchar(Some(3)), "'y'");

    let left_output = vec![typed_column("value", SqlType::text())];
    let left_associative = lower_query(&query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![unknown(), unknown(), known()],
            output: left_output.clone(),
        },
        left_output,
    ));
    assert_eq!(
        left_associative.status,
        LoweringStatus::Lowered,
        "{:#?}",
        left_associative.diagnostics
    );
    assert_eq!(
        left_associative.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Text,
        }
    );

    let right_output = vec![typed_column("value", SqlType::varchar(None))];
    let right_pair = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![unknown(), known()],
        output: right_output.clone(),
    };
    let right_associative = lower_query(&query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![unknown(), right_pair],
            output: right_output.clone(),
        },
        right_output,
    ));
    assert_eq!(
        right_associative.status,
        LoweringStatus::Lowered,
        "{:#?}",
        right_associative.diagnostics
    );
    assert_eq!(
        right_associative.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length: None },
        }
    );
}

#[test]
fn set_unknown_resolution_preserves_binary_tree_nesting() {
    let integer_output = vec![typed_column("value", SqlType::Integer)];
    let unknown = || source_unknown_null_project(SqlType::Integer, true);
    let integer = || RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })]],
        output: vec![typed_column("known", SqlType::Integer)],
    };

    let left_associative = lower_query(&query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![unknown(), unknown(), integer()],
            output: integer_output.clone(),
        },
        integer_output.clone(),
    ));
    assert_eq!(left_associative.status, LoweringStatus::Blocked);
    assert!(
        left_associative
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_input_type_override_not_supported")
    );

    let right_pair = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![unknown(), integer()],
        output: integer_output.clone(),
    };
    let right_associative = lower_query(&query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: true,
            inputs: vec![unknown(), right_pair],
            output: integer_output.clone(),
        },
        integer_output,
    ));
    assert_eq!(
        right_associative.status,
        LoweringStatus::Lowered,
        "{:#?}",
        right_associative.diagnostics
    );
    assert_eq!(
        right_associative.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::Int32
    );
}

#[test]
fn nested_union_distinct_propagates_child_derived_concat_text() {
    let stale_output = vec![typed_column("id", SqlType::character(28))];
    let inner = RelExpr::Set {
        op: SetOp::Union,
        all: true,
        inputs: vec![concat_text_branch("store"), concat_text_branch("web_site")],
        output: stale_output.clone(),
    };
    let query = query_for_rel(
        RelExpr::Set {
            op: SetOp::Union,
            all: false,
            inputs: vec![
                inner,
                source_unknown_null_project(SqlType::character(28), true),
            ],
            output: stale_output.clone(),
        },
        stale_output,
    );
    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Text,
        }
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("nested concat set"),
        lowered.query_expr.as_ref().expect("nested concat set"),
    );
    assert!(module.rocq_module.contains("ScalarStringConcat"));
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(module.rocq_module.contains("AttrString \"id\" StringText"));
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
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Set {
        op: FormalSetOp::Diff,
        left,
        right,
    }) = lowered_query_expr(&lowered)
    else {
        panic!("EXCEPT DISTINCT should lower to bag difference over deduplicated inputs");
    };
    assert!(matches!(left.as_ref(), FormalQueryExpr::Group { .. }));
    assert!(matches!(right.as_ref(), FormalQueryExpr::Group { .. }));
}

#[test]
fn aligns_set_inputs_by_position_before_intersection() {
    let rel = RelExpr::Set {
        op: SetOp::Intersect,
        all: true,
        inputs: vec![
            RelExpr::TableScan {
                table: vec!["left_table".to_owned()],
                output: vec![column("a")],
            },
            RelExpr::TableScan {
                table: vec!["right_table".to_owned()],
                output: vec![column("b")],
            },
        ],
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Set { left, right, .. }) = lowered_query_expr(&lowered) else {
        panic!("INTERSECT ALL should lower to a set query");
    };
    for input in [left, right] {
        let FormalQueryExpr::Projection { select, .. } = input.as_ref() else {
            panic!("each set input must be positionally aligned");
        };
        assert_eq!(select[0].alias, "a");
    }
}

#[test]
fn lowers_not_in_as_three_valued_negation_of_native_in() {
    let subquery = one_row_values(
        vec![column("candidate")],
        vec![ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: "1".to_owned(),
            }),
            ty: "INTEGER".to_owned(),
        }],
    );
    let output = vec![column("value")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "NOT".to_owned(),
                op: ScalarOp::Not,
                args: vec![ScalarAst::Call {
                    operator: "IN".to_owned(),
                    op: ScalarOp::In,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::RelSubquery {
                            rel: Box::new(subquery),
                        },
                    ],
                }],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some((predicate, _)) =
        selection_under_optional_output_restore(lowered.query_expr.as_ref().unwrap())
    else {
        panic!("expected relational selection");
    };
    assert!(matches!(
        predicate,
        FormalScalarExpr::Not { expression }
            if matches!(expression.as_ref(), FormalScalarExpr::In { .. })
    ));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().unwrap(),
        lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("@SExpr_Not TNull relname (@SExpr_In TNull relname")
    );
}

#[test]
fn rejects_limit_outside_postgres_bigint_range() {
    let output = vec![column("value")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Sort {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            collation: Vec::new(),
            fetch: Some(scalar(ScalarAst::Literal {
                raw: "9223372036854775808".to_owned(),
            })),
            offset: None,
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "row_count_out_of_bigint_range")
    );
}

#[test]
fn fetch_zero_does_not_bypass_oversized_offset_validation() {
    let output = vec![column("value")];
    let rel = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: output.clone(),
        }),
        collation: Vec::new(),
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "0".to_owned(),
        })),
        offset: Some(Box::new(scalar(ScalarAst::Literal {
            raw: "9223372036854775808".to_owned(),
        }))),
        output: output.clone(),
    };
    let query = Query {
        source_sql: Some(
            "SELECT value FROM t OFFSET 9223372036854775808 ROWS FETCH NEXT 0 ROWS ONLY".to_owned(),
        ),
        rel: rel.clone(),
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered_query_expr(&lowered).is_none());
    assert!(lowered.query_expr.is_none());
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "row_count_out_of_bigint_range")
    );

    // Exercise the unified relational lowering entry point directly as well: callers
    // cannot use FETCH 0 to skip OFFSET validation even when bypassing the
    // query-expression effect analysis.
    let mut context = LoweringContext::new(LoweringConfig::default(), None);
    assert!(context.lower_rel("rel", &rel).is_none());
    assert!(
        context
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "row_count_out_of_bigint_range")
    );
}

#[test]
fn rejects_numeric_table_scan_when_generating_schema_bound_proofs() {
    let output = vec![decimal_column_unconstrained("amount")];
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: output.clone(),
            constraints: Default::default(),
        }],
    };
    let rel = RelExpr::TableScan {
        table: vec!["t".to_owned()],
        output,
    };
    let mut context = LoweringContext::new(LoweringConfig::default(), Some(&schema));

    assert!(context.lower_rel("rel", &rel).is_none());
    assert!(
        context
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "numeric_table_special_values_not_supported" })
    );
}

#[test]
fn lowers_constrained_decimal_table_scan_with_schema_bound_proofs() {
    let output = vec![decimal_column("amount", 7, 2)];
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: output.clone(),
            constraints: Default::default(),
        }],
    };
    let query = schema_bound_scan_query("t", output);

    let lowered = lower_query_with_schema_config(&query, &schema, &LoweringConfig::default());

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(
        lowered.output_signature,
        Some(vec![FormalAttribute {
            name: "amount".to_owned(),
            ty: FormalAttributeType::Decimal {
                precision: 7,
                scale: 2,
            },
        }])
    );
    assert!(lowered_query_expr(&lowered).is_some());
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| { diagnostic.code != "numeric_table_special_values_not_supported" })
    );
}

#[test]
fn rejects_time_rounding_typmod_annotation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(one_row_values(Vec::new(), Vec::new())),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'12:34:56.789123'".to_owned(),
                    }],
                }),
                ty: "TIME(0)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("clock", SqlType::Time)],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "time_precision_semantics_not_supported" })
    );
}

#[test]
fn lowers_length_constrained_varchar_cast() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(one_row_values(Vec::new(), Vec::new())),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'abcdef'".to_owned(),
                    }],
                }),
                ty: "VARCHAR(2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::varchar(Some(2)))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("ScalarCastStringExplicit"));
    assert!(module.rocq_module.contains("StringVarcharN 2"));
}

#[test]
fn lowers_fixed_char_cast_with_explicit_typmod() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(one_row_values(Vec::new(), Vec::new())),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'ab  '".to_owned(),
                    }],
                }),
                ty: "CHAR(4)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::character(4))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("ScalarCastStringExplicit"));
    assert!(module.rocq_module.contains("(StringChar 4)"));
}

#[test]
fn lowers_typed_string_null_without_turning_it_into_text() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(one_row_values(Vec::new(), Vec::new())),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "NULL".to_owned(),
                        }),
                        ty: "TEXT".to_owned(),
                    }],
                }),
                ty: "VARCHAR(2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::varchar(Some(2)))],
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("NullString (StringVarcharN 2)"));
    assert!(
        !module
            .rocq_module
            .contains("CstString (StringVarcharN 2) \"null\"")
    );
}

#[test]
fn comparison_context_types_an_unknown_literal_as_typmodless_bpchar() {
    let output = vec![typed_column("c", SqlType::character(2))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "'a '".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("CstString StringBpchar \"a \""));
    assert!(!module.rocq_module.contains("CstString (StringChar 2)"));
}

#[test]
fn comparison_context_does_not_truncate_unknown_varchar_literal() {
    let output = vec![typed_column("v", SqlType::varchar(Some(2)))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "'abc'".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module_for_test(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("CstString StringText \"abc\""));
    assert!(
        !module
            .rocq_module
            .contains("CstString (StringVarcharN 2) \"abc\"")
    );
}

#[test]
fn lowers_attested_plain_group_key_having_with_positional_alias_substitution() {
    let scan_output = vec![column("manager"), column("department")];
    let project_output = vec![column("mgr_alias"), column("dept_alias")];
    let aggregate_output = vec![
        column("grouped_manager"),
        column("grouped_department"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["employees".to_owned()],
                output: scan_output,
            }),
            exprs: vec![
                scalar(ScalarAst::InputRef { index: 0 }),
                scalar(ScalarAst::InputRef { index: 1 }),
            ],
            correlations: Vec::new(),
            output: project_output,
        }),
        group_keys: vec![0, 1],
        grouping_sets: vec![vec![0, 1]],
        agg_calls: vec![count_star_call()],
        output: aggregate_output.clone(),
    };
    let query = query_for_rel(
        RelExpr::NativeHaving {
            input: Box::new(aggregate),
            predicate: group_key_equals_literal(1, "100"),
            correlations: Vec::new(),
            output: aggregate_output.clone(),
        },
        aggregate_output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Group { having, .. }) = lowered.query_expr.as_ref() else {
        panic!("attested ordinary HAVING should install in the logical Group");
    };
    let FormalScalarExpr::Predicate { args, .. } = having else {
        panic!("expected the group-key equality as Group HAVING");
    };
    assert!(matches!(
        args.first(),
        Some(FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute { name, ty }
            },
            ..
        }) if name == "dept_alias" && *ty == FormalAttributeType::Int32
    ));
    assert!(
        !format!("{having:?}").contains("grouped_department"),
        "the post-Aggregate alias must be replaced by the exact input group-key term"
    );
}

#[test]
fn derived_group_outer_where_stays_a_logical_selection() {
    let aggregate_output = vec![column("dname"), typed_column("cnt", SqlType::BigInt)];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["dept".to_owned()],
                output: vec![column("deptno"), column("name")],
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 1 })],
            correlations: Vec::new(),
            output: vec![column("dname")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![count_star_call()],
        output: aggregate_output.clone(),
    };
    let outer_output = vec![column("dname"), typed_column("c", SqlType::BigInt)];
    let outer_project = |input| RelExpr::Project {
        input: Box::new(input),
        exprs: vec![
            scalar(ScalarAst::InputRef { index: 0 }),
            scalar(ScalarAst::InputRef { index: 1 }),
        ],
        correlations: Vec::new(),
        output: outer_output.clone(),
    };
    let query = query_for_rel(
        outer_project(RelExpr::Filter {
            input: Box::new(aggregate),
            predicate: group_key_equals_literal(0, "10"),
            correlations: Vec::new(),
            output: aggregate_output,
        }),
        outer_output,
    );
    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("expected outer projection");
    };
    let FormalQueryExpr::Selection { input, .. } = input.as_ref() else {
        panic!("the derived-table outer WHERE must remain a logical Selection");
    };
    assert!(matches!(input.as_ref(), FormalQueryExpr::Group { .. }));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("QExpr_Filter"));
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));
}

#[test]
fn lowers_default_collation_text_group_key_having() {
    let output = vec![
        typed_column("grouped_name", SqlType::text()),
        typed_column("row_count", SqlType::BigInt),
    ];
    let query = query_for_rel(
        RelExpr::NativeHaving {
            input: Box::new(RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["departments".to_owned()],
                    output: vec![typed_column("name", SqlType::text())],
                }),
                group_keys: vec![0],
                grouping_sets: vec![vec![0]],
                agg_calls: vec![count_star_call()],
                output: output.clone(),
            }),
            predicate: group_key_equals_literal(0, "'Charlie'"),
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("CstString StringText \"Charlie\"")
    );
}

#[test]
fn declarative_having_accepts_aggregate_and_compound_predicates() {
    let output = vec![
        column("grouped_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let aggregate = || RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("key")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![count_star_call()],
        output: output.clone(),
    };
    let aggregate_predicate = scalar(ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::InputRef { index: 1 },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    });
    let compound_predicate = scalar(ScalarAst::Call {
        operator: "AND".to_owned(),
        op: ScalarOp::And,
        args: vec![
            group_key_equals_literal(0, "1").parsed,
            ScalarAst::Literal {
                raw: "true".to_owned(),
            },
        ],
    });

    for (label, predicate) in [
        ("aggregate-output", aggregate_predicate),
        ("compound", compound_predicate),
    ] {
        let query = query_for_rel(
            RelExpr::NativeHaving {
                input: Box::new(aggregate()),
                predicate,
                correlations: Vec::new(),
                output: output.clone(),
            },
            output.clone(),
        );
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert!(matches!(
            lowered.query_expr,
            Some(FormalQueryExpr::Group { .. })
        ));
        assert!(!format!("{:?}", lowered.query_expr).contains("PgGroup"));
    }
}

#[test]
fn native_having_filters_nonordinary_grouping_set_outputs() {
    let output = vec![
        column("grouped_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    for grouping_sets in [vec![vec![0], Vec::new()], vec![Vec::new()]] {
        let query = query_for_rel(
            RelExpr::NativeHaving {
                input: Box::new(RelExpr::Aggregate {
                    input: Box::new(RelExpr::TableScan {
                        table: vec!["items".to_owned()],
                        output: vec![column("key")],
                    }),
                    group_keys: vec![0],
                    grouping_sets,
                    agg_calls: vec![count_star_call()],
                    output: output.clone(),
                }),
                predicate: group_key_equals_literal(0, "1"),
                correlations: Vec::new(),
                output: output.clone(),
            },
            output.clone(),
        );
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
        assert!(matches!(
            lowered.query_expr,
            Some(FormalQueryExpr::Selection { .. })
        ));
    }
}

#[test]
fn declarative_having_does_not_require_pushdown_safe_group_key_provenance() {
    let computed = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("key")],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "IS NULL".to_owned(),
            op: ScalarOp::IsNull,
            args: vec![ScalarAst::InputRef { index: 0 }],
        })],
        correlations: Vec::new(),
        output: vec![typed_column("computed_key", SqlType::Boolean)],
    };
    let correlated_identity = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("key")],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: vec![CorrelationBinding {
            correlation: "$cor0".to_owned(),
            output: vec![column("outer_key")],
        }],
        output: vec![column("identity_key")],
    };

    for (label, input, output, literal) in [
        (
            "computed",
            computed,
            vec![typed_column("grouped_key", SqlType::Boolean)],
            "true",
        ),
        (
            "correlated-identity",
            correlated_identity,
            vec![column("grouped_key")],
            "1",
        ),
    ] {
        let aggregate = RelExpr::Aggregate {
            input: Box::new(input),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: Vec::new(),
            output: output.clone(),
        };
        let query = query_for_rel(
            RelExpr::NativeHaving {
                input: Box::new(aggregate),
                predicate: group_key_equals_literal(0, literal),
                correlations: Vec::new(),
                output: output.clone(),
            },
            output.clone(),
        );
        let lowered = lower_query(&query);
        assert_eq!(
            lowered.status,
            LoweringStatus::Lowered,
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert!(matches!(
            lowered.query_expr,
            Some(FormalQueryExpr::Group { .. })
        ));
    }

    let output = vec![column("grouped_key")];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("key")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: Vec::new(),
        output: output.clone(),
    };
    let query = query_for_rel(
        RelExpr::NativeHaving {
            input: Box::new(aggregate),
            predicate: group_key_equals_literal(0, "1"),
            correlations: vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: vec![column("outer_key")],
            }],
            output: output.clone(),
        },
        output,
    );
    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "correlated_native_having_not_supported")
    );
}

#[test]
fn declarative_having_preserves_an_unused_risky_aggregate_term() {
    let aggregate_output = vec![
        column("grouped_key"),
        typed_column("unused_count", SqlType::BigInt),
    ];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("key"), column("denominator")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![AggregateCall {
            raw: "COUNT(10 / denominator)".to_owned(),
            function: "COUNT".to_owned(),
            distinct: false,
            modifiers: AggregateModifiers::default(),
            args: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            filter: None,
        }],
        output: aggregate_output.clone(),
    };
    let having = RelExpr::NativeHaving {
        input: Box::new(aggregate),
        predicate: group_key_equals_literal(0, "1"),
        correlations: Vec::new(),
        output: aggregate_output,
    };
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(having),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![column("grouped_key")],
        },
        vec![column("grouped_key")],
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let lowered_debug = format!("{:?}", lowered.query_expr);
    assert!(lowered_debug.contains("function: Count"));
    assert!(lowered_debug.contains("Divide(Int32)"));
    assert!(!lowered_debug.contains("PgGroup"));
}

#[test]
fn declarative_having_accepts_a_runtime_risky_aggregate_child() {
    let project_output = vec![column("key"), column("risky_group_key")];
    let aggregate_output = project_output.clone();
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["items".to_owned()],
                output: vec![column("key"), column("denominator")],
            }),
            exprs: vec![
                scalar(ScalarAst::InputRef { index: 0 }),
                scalar(ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::Literal {
                            raw: "10".to_owned(),
                        },
                        ScalarAst::InputRef { index: 1 },
                    ],
                }),
            ],
            correlations: Vec::new(),
            output: project_output,
        }),
        group_keys: vec![0, 1],
        grouping_sets: vec![vec![0, 1]],
        agg_calls: Vec::new(),
        output: aggregate_output.clone(),
    };
    let query = query_for_rel(
        RelExpr::NativeHaving {
            input: Box::new(aggregate),
            predicate: group_key_equals_literal(0, "1"),
            correlations: Vec::new(),
            output: aggregate_output.clone(),
        },
        aggregate_output,
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Group { .. })
    ));
    assert!(format!("{:?}", lowered.query_expr).contains("Divide(Int32)"));
}

#[test]
fn declarative_native_having_is_a_logical_group_below_its_target_projection() {
    let aggregate_output = vec![
        column("grouped_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let native = RelExpr::NativeHaving {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["items".to_owned()],
                output: vec![column("key")],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![count_star_call()],
            output: aggregate_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: ">".to_owned(),
            op: ScalarOp::Gt,
            args: vec![
                ScalarAst::InputRef { index: 1 },
                ScalarAst::Literal {
                    raw: "0".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: aggregate_output,
    };
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(native),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![column("grouped_key")],
        },
        vec![column("grouped_key")],
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let FormalQueryExpr::Projection {
        select: target_select,
        input,
    } = lowered.query_expr.as_ref().unwrap()
    else {
        panic!("the source target list must remain a logical post-HAVING projection");
    };
    let FormalQueryExpr::Group { select, having, .. } = input.as_ref() else {
        panic!("ordinary source HAVING must be installed in one logical Group");
    };
    assert_eq!(target_select.len(), 1);
    assert_eq!(select.len(), 2);
    assert!(matches!(
        select[1].expr,
        FormalScalarExpr::Leaf {
            term: FormalAggregateTerm::CountStar,
            ..
        }
    ));
    assert!(format!("{having:?}").contains("CountStar"));
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("QExpr_Project"));
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));
}

#[test]
#[ignore = "requires the Java Calcite wrapper and Maven bootstrap"]
fn calcite_148_mixed_having_reaches_logical_group_without_having_pushdown() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("logos-solver crate should be nested under the repository root");
    let temp = std::env::temp_dir().join(format!(
        "logos-solver-calcite-148-mixed-having-e2e-{}",
        std::process::id()
    ));
    if temp.exists() {
        fs::remove_dir_all(&temp).expect("remove stale wrapper test directory");
    }
    fs::create_dir_all(&temp).expect("create wrapper test directory");
    let schema_path = temp.join("schema.sql");
    let query_path = temp.join("query.sql");
    fs::write(
        &schema_path,
        "create table dept(deptno integer, name text);\n",
    )
    .expect("write wrapper schema");
    fs::write(
        &query_path,
        "select name as c1 from dept where name > 'b' group by name \
         having name > 'c' and (count(*) > 30 or name < 'z');\n",
    )
    .expect("write wrapper query");

    let output = Command::new(repo.join("scripts/calcite-ir"))
        .arg("--schema")
        .arg(&schema_path)
        .arg("--sql")
        .arg(&query_path)
        .arg("--default-collation")
        .arg("C")
        .arg("--character-classification")
        .arg("C")
        .arg("--locale-provider")
        .arg("libc")
        .arg("--server-encoding")
        .arg("UTF8")
        .output()
        .expect("run Calcite wrapper");
    assert!(
        output.status.success(),
        "calcite wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let raw: CalciteFile =
        serde_json::from_slice(&output.stdout).expect("parse wrapper JSON output");
    let ir = convert_raw_file(raw).expect("convert exact mixed-HAVING provenance");
    assert_eq!(ir.environment, SqlEnvironment::postgres_utf8_c());
    let RelExpr::Project { input, .. } = &ir.queries[0].rel else {
        panic!("calcite-148 must retain its final Project");
    };
    let RelExpr::NativeHaving {
        input, predicate, ..
    } = input.as_ref()
    else {
        panic!("the complete original HAVING must remain native");
    };
    assert!(matches!(
        &predicate.parsed,
        ScalarAst::Call {
            op: ScalarOp::And,
            ..
        }
    ));
    let RelExpr::Aggregate {
        input: aggregate_input,
        ..
    } = input.as_ref()
    else {
        panic!("native HAVING must remain directly over Aggregate");
    };
    let aggregate_input_debug = format!("{aggregate_input:?}");
    assert!(aggregate_input_debug.contains("'b'"));
    assert!(!aggregate_input_debug.contains("'c'"));

    let lowered = lower_query_with_config(
        &ir.queries[0],
        &LoweringConfig {
            sql_environment: SqlEnvironment::postgres_utf8_c(),
            ..LoweringConfig::default()
        },
    );
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { input, .. }) = lowered.query_expr.as_ref() else {
        panic!("calcite-148 must retain its post-HAVING target projection");
    };
    let FormalQueryExpr::Group { having, input, .. } = input.as_ref() else {
        panic!("calcite-148 must lower to one logical Group");
    };
    let having_debug = format!("{having:?}");
    assert!(having_debug.contains("CountStar"));
    assert!(having_debug.contains("'c'"));
    let input_debug = format!("{input:?}");
    assert!(input_debug.contains("'b'"));
    assert!(!input_debug.contains("'c'"));
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("query expression"),
        lowered.query_expr.as_ref().expect("query expression"),
    );
    assert!(module.rocq_module.contains("QExpr_Group"));
    assert!(!module.rocq_module.contains("QExpr_Pg"));

    fs::remove_dir_all(&temp).expect("remove wrapper test directory");
}

#[test]
fn declarative_native_having_keeps_target_evaluation_after_the_group() {
    let aggregate_output = vec![
        column("grouped_key"),
        typed_column("risky_count", SqlType::BigInt),
    ];
    let risky_division = ScalarAst::Call {
        operator: "/".to_owned(),
        op: ScalarOp::Divide,
        args: vec![
            ScalarAst::Literal {
                raw: "10".to_owned(),
            },
            ScalarAst::InputRef { index: 1 },
        ],
    };
    let native = RelExpr::NativeHaving {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["items".to_owned()],
                output: vec![column("grouped_key"), column("denominator")],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![AggregateCall {
                raw: "COUNT(10 / denominator)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(risky_division)],
                filter: None,
            }],
            output: aggregate_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: ">".to_owned(),
            op: ScalarOp::Gt,
            args: vec![
                ScalarAst::InputRef { index: 1 },
                ScalarAst::Literal {
                    raw: "0".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: aggregate_output,
    };
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(native),
            // A zero key in an early group makes this target expression fail,
            // while a later group's denominator can independently make the
            // registered COUNT argument fail during aggregate finalization.
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![column("target_value")],
        },
        vec![column("target_value")],
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let FormalQueryExpr::Projection { select, input } = lowered.query_expr.as_ref().unwrap() else {
        panic!("the target expression must remain a logical projection after HAVING");
    };
    assert_eq!(select.len(), 1);
    let FormalQueryExpr::Group {
        select: aggregate_select,
        ..
    } = input.as_ref()
    else {
        panic!("native HAVING must remain one logical Group");
    };
    assert_eq!(aggregate_select.len(), 2);
    assert!(
        format!("{:?}", aggregate_select[1].expr).contains("Divide(Int32)"),
        "{:?}",
        aggregate_select[1].expr
    );
    assert!(
        format!("{:?}", select[0].expr).contains("Divide(Int32)"),
        "{:?}",
        select[0].expr
    );
}

#[test]
fn native_having_preserves_logical_project_composition() {
    let aggregate_output = vec![
        column("grouped_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let native = RelExpr::NativeHaving {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["items".to_owned()],
                output: vec![column("key")],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![count_star_call()],
            output: aggregate_output.clone(),
        }),
        predicate: scalar(ScalarAst::Call {
            operator: ">".to_owned(),
            op: ScalarOp::Gt,
            args: vec![
                ScalarAst::InputRef { index: 1 },
                ScalarAst::Literal {
                    raw: "0".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: aggregate_output,
    };
    let first_project = RelExpr::Project {
        input: Box::new(native),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![column("renamed_key")],
    };
    let second_project = RelExpr::Project {
        input: Box::new(first_project),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![column("renamed_key_again")],
    };
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(second_project),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![column("final_key")],
        },
        vec![column("final_key")],
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let Some(FormalQueryExpr::Projection { select, input }) = lowered.query_expr.as_ref() else {
        panic!("the final target must remain a logical Projection")
    };
    assert_eq!(select.len(), 1);
    assert_eq!(select[0].alias, "final_key");
    assert!(format!("{:?}", select[0].expr).contains("Divide(Int32)"));
    let lowered_debug = format!("{input:?}");
    assert!(lowered_debug.contains("Group"));
    assert!(lowered_debug.contains("CountStar"));
    assert!(!lowered_debug.contains("PgGroup"));
}

#[test]
fn native_having_allows_a_logical_post_group_correlation_scope() {
    let aggregate_output = vec![
        column("grouped_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let native = RelExpr::NativeHaving {
        input: Box::new(RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["items".to_owned()],
                output: vec![column("key")],
            }),
            group_keys: vec![0],
            grouping_sets: vec![vec![0]],
            agg_calls: vec![count_star_call()],
            output: aggregate_output.clone(),
        }),
        predicate: group_key_equals_literal(0, "1"),
        correlations: Vec::new(),
        output: aggregate_output,
    };
    let first_project = RelExpr::Project {
        input: Box::new(native),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![column("renamed_key")],
    };
    let query = query_for_rel(
        RelExpr::Project {
            input: Box::new(first_project),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: vec![column("outer_key")],
            }],
            output: vec![column("final_key")],
        },
        vec![column("final_key")],
    );

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Projection { .. })
    ));
    assert!(!format!("{:?}", lowered.query_expr).contains("PgGroup"));
}

#[test]
fn native_grouping_sets_having_filters_the_shared_aggregate_output() {
    let query = generic_grouping_sets_native_having_query();

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Selection { input, .. })
            if matches!(*input, FormalQueryExpr::GroupingSets { .. })
    ));
}

#[test]
fn grouping_sets_native_having_accepts_other_typed_key_predicates() {
    let mut query = generic_grouping_sets_native_having_query();
    let RelExpr::NativeHaving { predicate, .. } = &mut query.rel else {
        unreachable!()
    };
    let ScalarAst::Call { args, .. } = &mut predicate.parsed else {
        unreachable!()
    };
    args[1] = ScalarAst::Literal {
        raw: "'archived'".to_owned(),
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered, "{lowered:#?}");
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Selection { .. })
    ));
}

fn generic_grouping_sets_native_having_query() -> Query {
    let scan_output = vec![
        typed_column("category", SqlType::text()),
        typed_column("region", SqlType::Integer),
    ];
    let aggregate_output = vec![
        typed_column("category", SqlType::text()),
        typed_column("region", SqlType::Integer),
        typed_column("row_count", SqlType::BigInt),
    ];
    let predicate = scalar(ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Literal {
                raw: "'active'".to_owned(),
            },
        ],
    });
    query_for_rel(
        RelExpr::NativeHaving {
            input: Box::new(RelExpr::Aggregate {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["inventory".to_owned()],
                    output: scan_output,
                }),
                group_keys: vec![0, 1],
                grouping_sets: vec![vec![0], vec![0, 1], Vec::new()],
                agg_calls: vec![count_star_call()],
                output: aggregate_output.clone(),
            }),
            predicate,
            correlations: Vec::new(),
            output: aggregate_output.clone(),
        },
        aggregate_output,
    )
}

#[test]
fn native_having_admission_rejects_correlation_and_changed_output_shape() {
    let aggregate_output = vec![
        column("grouped_key"),
        typed_column("row_count", SqlType::BigInt),
    ];
    let aggregate = RelExpr::Aggregate {
        input: Box::new(RelExpr::TableScan {
            table: vec!["items".to_owned()],
            output: vec![column("key")],
        }),
        group_keys: vec![0],
        grouping_sets: vec![vec![0]],
        agg_calls: vec![count_star_call()],
        output: aggregate_output.clone(),
    };
    for (label, correlations, output, code) in [
        (
            "correlated",
            vec![CorrelationBinding {
                correlation: "$cor0".to_owned(),
                output: vec![column("outer_key")],
            }],
            aggregate_output.clone(),
            "correlated_native_having_not_supported",
        ),
        (
            "changed-output",
            Vec::new(),
            vec![
                column("renamed_key"),
                typed_column("row_count", SqlType::BigInt),
            ],
            "native_having_output_shape_changed",
        ),
    ] {
        let query = query_for_rel(
            RelExpr::NativeHaving {
                input: Box::new(aggregate.clone()),
                predicate: group_key_equals_literal(0, "1"),
                correlations,
                output: output.clone(),
            },
            output,
        );
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == code),
            "{label}: {:#?}",
            lowered.diagnostics
        );
    }
}

fn group_key_equals_literal(index: usize, raw: &str) -> ScalarExpr {
    scalar(ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index },
            ScalarAst::Literal {
                raw: raw.to_owned(),
            },
        ],
    })
}

fn complementary_string_order_ast(
    first_index: usize,
    second_index: usize,
    first_literal: &str,
    second_literal: &str,
    first_op: ScalarOp,
    second_op: ScalarOp,
) -> ScalarAst {
    let comparison = |index, raw: &str, op: ScalarOp| ScalarAst::Call {
        operator: match op {
            ScalarOp::Lt => "<",
            ScalarOp::Lte => "<=",
            ScalarOp::Gt => ">",
            ScalarOp::Gte => ">=",
            _ => "unknown",
        }
        .to_owned(),
        op,
        args: vec![
            ScalarAst::InputRef { index },
            ScalarAst::Literal {
                raw: raw.to_owned(),
            },
        ],
    };
    ScalarAst::Call {
        operator: "OR".to_owned(),
        op: ScalarOp::Or,
        args: vec![
            comparison(first_index, first_literal, first_op),
            comparison(second_index, second_literal, second_op),
        ],
    }
}

fn special_aggregate_query(function: &str, input_ty: SqlType, output_ty: SqlType) -> Query {
    let input_output = vec![typed_column("value", input_ty)];
    let output = vec![typed_column("result", output_ty)];
    Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: format!("{function}($0)"),
                function: function.to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: output.clone(),
        },
        analysis_errors: vec![],
    }
}

#[test]
fn lowers_any_value_integer_as_exact_arbitrary_nonnull_choice() {
    let query = special_aggregate_query("ANY_VALUE", SqlType::Integer, SqlType::Integer);
    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Fetch { count: 1, input }) = lowered.query_expr.as_ref() else {
        panic!("ANY_VALUE must choose one row from a permutation-closed candidate bag");
    };
    let FormalQueryExpr::Join {
        join_kind,
        left,
        right,
        left_select,
        ..
    } = input.as_ref()
    else {
        panic!("ANY_VALUE must use a left-join seed for the empty/all-NULL fallback");
    };
    assert_eq!(*join_kind, FormalQueryJoinKind::Left);
    assert!(matches!(left.as_ref(), FormalQueryExpr::EmptyTuple));
    assert!(matches!(
        right.as_ref(),
        FormalQueryExpr::Projection { input, .. }
            if matches!(input.as_ref(), FormalQueryExpr::Selection { .. })
    ));
    assert!(matches!(
        left_select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant { raw, ty: Some(FormalAttributeType::Int32) }
                },
                ..
            },
            ..
        }] if raw.eq_ignore_ascii_case("NULL")
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("QExpr_Fetch (1%nat)"));
    assert!(module.rocq_module.contains("QExpr_Join QueryJoinLeft"));
    assert!(module.rocq_module.contains("PredicateIsNotNull"));
    assert!(!module.rocq_module.contains("AAggregate AggregateAnyValue"));
}

#[test]
fn lowers_single_value_integer_with_cardinality_error_aggregate() {
    let query = special_aggregate_query("SINGLE_VALUE", SqlType::Integer, SqlType::Integer);
    assert!(rel_expr_may_raise_runtime(&query.rel));

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQueryExpr::Group { select, .. }) = lowered.query_expr.as_ref() else {
        panic!("SINGLE_VALUE must remain an error-aware global aggregate");
    };
    assert!(matches!(
        select.as_slice(),
        [FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                term: FormalAggregateTerm::Aggregate { function, .. },
                ..
            },
            alias_ty: FormalAttributeType::Int32,
            ..
        }] if *function == FormalAggregateFunction::SingleValueInt32
    ));

    let module = emit_rocq_query_module_for_test(&query);
    assert!(
        module
            .rocq_module
            .contains("AAggregate AggregateSingleValueInt32 AggregateAll")
    );
}

#[test]
fn special_aggregates_reject_unsupported_types_and_shapes() {
    for function in ["ANY_VALUE", "SINGLE_VALUE"] {
        let wrong_type = special_aggregate_query(function, SqlType::BigInt, SqlType::BigInt);
        let lowered = lower_query(&wrong_type);
        assert_eq!(lowered.status, LoweringStatus::Blocked);
        assert!(lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "any_value_argument_type_not_supported"
                || diagnostic.code == "single_value_argument_type_not_supported"
        }));

        let mut expression = special_aggregate_query(function, SqlType::Integer, SqlType::Integer);
        let RelExpr::Aggregate { agg_calls, .. } = &mut expression.rel else {
            unreachable!();
        };
        agg_calls[0].args[0] = scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        });
        let lowered = lower_query(&expression);
        assert_eq!(lowered.status, LoweringStatus::Blocked);
        assert!(lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "special_aggregate_argument_shape_not_supported"
        }));

        let mut distinct = special_aggregate_query(function, SqlType::Integer, SqlType::Integer);
        let RelExpr::Aggregate { agg_calls, .. } = &mut distinct.rel else {
            unreachable!();
        };
        agg_calls[0].distinct = true;
        let lowered = lower_query(&distinct);
        assert_eq!(lowered.status, LoweringStatus::Blocked);
        assert!(
            lowered.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "special_aggregate_modifier_not_supported"
            })
        );

        let mut grouped = special_aggregate_query(function, SqlType::Integer, SqlType::Integer);
        let RelExpr::Aggregate {
            group_keys,
            grouping_sets,
            output,
            ..
        } = &mut grouped.rel
        else {
            unreachable!();
        };
        *group_keys = vec![0];
        *grouping_sets = vec![vec![0]];
        output.insert(0, typed_column("value", SqlType::Integer));
        let lowered = lower_query(&grouped);
        assert_eq!(lowered.status, LoweringStatus::Blocked);
        assert!(lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "special_aggregate_select_shape_not_supported"
                || diagnostic.code == "special_aggregate_grouping_shape_not_supported"
        }));
    }
}

#[test]
fn single_value_preserves_error_capable_logical_child() {
    let mut query = special_aggregate_query("SINGLE_VALUE", SqlType::Integer, SqlType::Integer);
    let RelExpr::Aggregate { input, .. } = &mut query.rel else {
        unreachable!();
    };
    **input = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![column("value")],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column("value")],
    };

    let lowered = lower_query(&query);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let module = emit_rocq_query_module_for_test(&query);
    assert!(module.rocq_module.contains("AggregateSingleValueInt32"));
    assert!(module.rocq_module.contains("ScalarDivide ScalarInt32"));
    assert_no_physical_plan_constructs(&module);
}

fn column(name: &str) -> Column {
    typed_column(name, SqlType::Integer)
}

fn one_row_values(output: Vec<Column>, values: Vec<ScalarAst>) -> RelExpr {
    RelExpr::Values {
        rows: vec![values.into_iter().map(scalar).collect()],
        output,
    }
}

fn typed_column(name: &str, ty: SqlType) -> Column {
    Column {
        name: name.to_owned(),
        ty,
        nullable: true,
    }
}

fn singleton_constant_type(query: &FormalQueryExpr, raw: &str) -> Option<FormalAttributeType> {
    let FormalQueryExpr::Projection { select, input } = query else {
        return None;
    };
    if !matches!(**input, FormalQueryExpr::EmptyTuple) {
        return None;
    }
    let [item] = select.as_slice() else {
        return None;
    };
    let FormalScalarExpr::Leaf {
        term:
            FormalAggregateTerm::Expr {
                term:
                    FormalFunctionTerm::Constant {
                        raw: constant_raw,
                        ty: Some(ty),
                    },
            },
        ..
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

fn scalar(parsed: ScalarAst) -> ScalarExpr {
    ScalarExpr {
        raw: String::new(),
        parsed,
        source: None,
    }
}

fn source_node(
    sql: &str,
    kind: &str,
    operator: Option<&str>,
    operands: Vec<ScalarSourceProvenance>,
) -> ScalarSourceProvenance {
    ScalarSourceProvenance {
        sql: Some(sql.to_owned()),
        node_id: Some(format!("test:{sql}")),
        text: Some(sql.to_owned()),
        kind: Some(kind.to_owned()),
        operator: operator.map(str::to_owned),
        clause_ownership: None,
        operands: operands.into_iter().map(Some).collect(),
    }
}

fn exact_source_node(
    sql: &str,
    node_id: &str,
    kind: &str,
    operator: Option<&str>,
    operands: Vec<ScalarSourceProvenance>,
) -> ScalarSourceProvenance {
    ScalarSourceProvenance {
        sql: Some(sql.to_owned()),
        node_id: Some(node_id.to_owned()),
        text: Some(sql.to_owned()),
        kind: Some(kind.to_owned()),
        operator: operator.map(str::to_owned),
        clause_ownership: None,
        operands: operands.into_iter().map(Some).collect(),
    }
}

fn scalar_with_source(parsed: ScalarAst, source: ScalarSourceProvenance) -> ScalarExpr {
    let mut expr = scalar(parsed);
    expr.source = Some(source);
    expr
}

fn partition_peer_complete_count_window(key_index: usize) -> ScalarExpr {
    let raw = format!("COUNT() OVER (PARTITION BY ${key_index} ORDER BY ${key_index})");
    ScalarExpr {
        raw: raw.clone(),
        parsed: ScalarAst::Window {
            parsed: WindowAst {
                function: "COUNT".to_owned(),
                args: Vec::new(),
                partition_by: vec![ScalarAst::InputRef { index: key_index }],
                order_by: vec![WindowOrderKey {
                    expr: ScalarAst::InputRef { index: key_index },
                    direction: Some(SortDirection::Ascending),
                    null_direction: Some(SortNullDirection::Last),
                }],
                distinct: false,
                ignore_nulls: false,
                exclude: Some("EXCLUDE_NO_OTHER".to_owned()),
                frame: Some(WindowFrameAst {
                    units: WindowFrameUnits::Range,
                    start: WindowFrameBoundAst::UnboundedPreceding,
                    end: Some(WindowFrameBoundAst::CurrentRow),
                }),
            },
        },
        source: None,
    }
}

fn global_full_count_window(arg_index: usize) -> ScalarExpr {
    let raw = format!("COUNT(${arg_index}) OVER ()");
    ScalarExpr {
        raw: raw.clone(),
        parsed: ScalarAst::Window {
            parsed: WindowAst {
                function: "COUNT".to_owned(),
                args: vec![ScalarAst::InputRef { index: arg_index }],
                partition_by: Vec::new(),
                order_by: Vec::new(),
                distinct: false,
                ignore_nulls: false,
                exclude: Some("EXCLUDE_NO_OTHER".to_owned()),
                frame: Some(WindowFrameAst {
                    units: WindowFrameUnits::Range,
                    start: WindowFrameBoundAst::UnboundedPreceding,
                    end: Some(WindowFrameBoundAst::UnboundedFollowing),
                }),
            },
        },
        source: None,
    }
}

fn cumulative_rows_window(function: &str, args: Vec<ScalarAst>) -> ScalarExpr {
    let raw = format!("{function}(...) OVER (PARTITION BY $0 ORDER BY $1)");
    ScalarExpr {
        raw: raw.clone(),
        parsed: ScalarAst::Window {
            parsed: WindowAst {
                function: function.to_owned(),
                args,
                partition_by: vec![ScalarAst::InputRef { index: 0 }],
                order_by: vec![WindowOrderKey {
                    expr: ScalarAst::InputRef { index: 1 },
                    direction: Some(SortDirection::Ascending),
                    null_direction: Some(SortNullDirection::First),
                }],
                distinct: false,
                ignore_nulls: false,
                exclude: Some("EXCLUDE_NO_OTHER".to_owned()),
                frame: Some(WindowFrameAst {
                    units: WindowFrameUnits::Rows,
                    start: WindowFrameBoundAst::UnboundedPreceding,
                    end: Some(WindowFrameBoundAst::CurrentRow),
                }),
            },
        },
        source: None,
    }
}

#[test]
fn runtime_risk_tracks_error_capable_window_functions() {
    let input = RelExpr::TableScan {
        table: vec!["measurements".to_owned()],
        output: vec![
            typed_column("partition_key", SqlType::Integer),
            typed_column("order_key", SqlType::Integer),
            typed_column("value", SqlType::Integer),
        ],
    };

    for (function, args) in [
        ("COUNT", vec![ScalarAst::InputRef { index: 2 }]),
        ("SUM", vec![ScalarAst::InputRef { index: 2 }]),
        ("ROW_NUMBER", Vec::new()),
        ("RANK", Vec::new()),
    ] {
        let window = cumulative_rows_window(function, args);
        assert!(
            scalar_ast_may_raise_runtime_for_input(&window.parsed, &input),
            "{function} must retain its transition/position error path"
        );
    }

    for function in ["AVG", "MIN", "MAX"] {
        let window = cumulative_rows_window(function, vec![ScalarAst::InputRef { index: 2 }]);
        assert!(
            !scalar_ast_may_raise_runtime_for_input(&window.parsed, &input),
            "{function} over total keys and arguments has no intrinsic runtime error"
        );
    }
}

fn default_range_rank_window(
    partition_by: Vec<ScalarAst>,
    order_expr: ScalarAst,
    direction: SortDirection,
    null_direction: SortNullDirection,
) -> ScalarExpr {
    let raw = "RANK() OVER (...)".to_owned();
    ScalarExpr {
        raw: raw.clone(),
        parsed: ScalarAst::Window {
            parsed: WindowAst {
                function: "RANK".to_owned(),
                args: Vec::new(),
                partition_by,
                order_by: vec![WindowOrderKey {
                    expr: order_expr,
                    direction: Some(direction),
                    null_direction: Some(null_direction),
                }],
                distinct: false,
                ignore_nulls: false,
                exclude: Some("EXCLUDE_NO_OTHER".to_owned()),
                frame: Some(WindowFrameAst {
                    units: WindowFrameUnits::Range,
                    start: WindowFrameBoundAst::UnboundedPreceding,
                    end: Some(WindowFrameBoundAst::CurrentRow),
                }),
            },
        },
        source: None,
    }
}

fn query_with_default_rank_window(window: ScalarExpr, rank_nullable: bool) -> Query {
    let input = vec![
        typed_column("department", SqlType::Integer),
        typed_column("total", SqlType::BigInt),
    ];
    let output = vec![
        typed_column("department", SqlType::Integer),
        typed_column("total", SqlType::BigInt),
        Column {
            name: "ranking".to_owned(),
            ty: SqlType::BigInt,
            nullable: rank_nullable,
        },
    ];
    query_for_rel(
        RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["department_totals".to_owned()],
                output: input,
            }),
            exprs: vec![
                scalar(ScalarAst::InputRef { index: 0 }),
                scalar(ScalarAst::InputRef { index: 1 }),
                window,
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
    )
}

fn count_star_call() -> AggregateCall {
    AggregateCall {
        raw: "COUNT()".to_owned(),
        function: "COUNT".to_owned(),
        distinct: false,
        modifiers: AggregateModifiers::default(),
        args: Vec::new(),
        filter: None,
    }
}

fn attested_numeric_product_expr(explicit_typmod: Option<&str>) -> ScalarExpr {
    let product = ScalarAst::Call {
        operator: "*".to_owned(),
        op: ScalarOp::Multiply,
        args: vec![
            ScalarAst::InputRef { index: 1 },
            ScalarAst::InputRef { index: 2 },
        ],
    };
    let product_source = source_node(
        "quantity * amount",
        "TIMES",
        Some("*"),
        vec![
            source_node("quantity", "IDENTIFIER", None, Vec::new()),
            source_node("amount", "IDENTIFIER", None, Vec::new()),
        ],
    );
    match explicit_typmod {
        Some(target) => scalar_with_source(
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![product],
                }),
                ty: target.to_owned(),
            },
            source_node(
                &format!("CAST(quantity * amount AS {target})"),
                "CAST",
                Some("CAST"),
                vec![product_source],
            ),
        ),
        None => scalar_with_source(product, product_source),
    }
}

fn grouped_numeric_product_input(
    amount_ty: SqlType,
    product_ty: SqlType,
    explicit_typmod: Option<&str>,
) -> RelExpr {
    RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["inner_sales".to_owned()],
            output: vec![
                column("topic_id"),
                typed_column("quantity", SqlType::Integer),
                typed_column("amount", amount_ty),
            ],
        }),
        exprs: vec![
            scalar(ScalarAst::InputRef { index: 0 }),
            attested_numeric_product_expr(explicit_typmod),
        ],
        correlations: Vec::new(),
        output: vec![column("topic_id"), typed_column("sales", product_ty)],
    }
}

fn set_numeric_product_branch(explicit_typmod: Option<&str>) -> RelExpr {
    let grouped = grouped_numeric_product_input(
        SqlType::decimal(Some(7), Some(2)),
        SqlType::decimal(Some(17), Some(2)),
        explicit_typmod,
    );
    let RelExpr::Project {
        input,
        mut exprs,
        correlations,
        ..
    } = grouped
    else {
        unreachable!("numeric product helper always builds a Project")
    };
    RelExpr::Project {
        input,
        exprs: vec![exprs.remove(1)],
        correlations,
        output: vec![decimal_column("sales", 17, 2)],
    }
}

fn singleton_string_values(name: &str, ty: SqlType, raw: &str) -> RelExpr {
    let target = match &ty {
        SqlType::String(SqlStringType::Text) => "TEXT".to_owned(),
        SqlType::String(SqlStringType::Varchar { length: None }) => "VARCHAR".to_owned(),
        SqlType::String(SqlStringType::Varchar {
            length: Some(length),
        }) => format!("VARCHAR({length})"),
        SqlType::String(SqlStringType::Char { length }) => format!("CHAR({length})"),
        SqlType::String(SqlStringType::Bpchar) => "BPCHAR".to_owned(),
        other => panic!("singleton string VALUES requires a string type, got {other:?}"),
    };
    RelExpr::Values {
        rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: raw.to_owned(),
            }),
            ty: target,
        })]],
        output: vec![typed_column(name, ty)],
    }
}

fn source_unknown_null_project(output_ty: SqlType, attested: bool) -> RelExpr {
    let seed_output = vec![typed_column("seed", SqlType::Integer)];
    let mut expr = scalar(ScalarAst::Literal {
        raw: "NULL".to_owned(),
    });
    if attested {
        expr.source = Some(source_node("NULL", "LITERAL", None, Vec::new()));
    }
    RelExpr::Project {
        input: Box::new(RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })]],
            output: seed_output,
        }),
        exprs: vec![expr],
        correlations: Vec::new(),
        output: vec![typed_column("value", output_ty)],
    }
}

fn source_unknown_string_project(output_ty: SqlType, raw: &str, attested: bool) -> RelExpr {
    let seed_output = vec![typed_column("seed", SqlType::Integer)];
    let mut expr = scalar(ScalarAst::Literal {
        raw: raw.to_owned(),
    });
    if attested {
        expr.source = Some(source_node(raw, "LITERAL", None, Vec::new()));
    }
    RelExpr::Project {
        input: Box::new(RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })]],
            output: seed_output,
        }),
        exprs: vec![expr],
        correlations: Vec::new(),
        output: vec![typed_column("value", output_ty)],
    }
}

fn explicitly_typed_null_project(output_ty: SqlType, target: &str) -> RelExpr {
    let seed_output = vec![typed_column("seed", SqlType::Integer)];
    RelExpr::Project {
        input: Box::new(RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "1".to_owned(),
            })]],
            output: seed_output,
        }),
        exprs: vec![scalar_with_source(
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "NULL".to_owned(),
                }),
                ty: target.to_owned(),
            },
            source_node(
                &format!("CAST(NULL AS {target})"),
                "CAST",
                Some("CAST"),
                vec![source_node("NULL", "LITERAL", None, Vec::new())],
            ),
        )],
        correlations: Vec::new(),
        output: vec![typed_column("value", output_ty)],
    }
}

fn concat_text_branch(prefix: &str) -> RelExpr {
    let input = vec![typed_column("source_id", SqlType::character(16))];
    RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec![format!("{prefix}_ids")],
            output: input,
        }),
        exprs: vec![scalar_with_source(
            ScalarAst::Call {
                operator: "||".to_owned(),
                op: ScalarOp::StringConcat,
                args: vec![
                    ScalarAst::Literal {
                        raw: format!("'{prefix}'"),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            },
            source_node(
                &format!("'{prefix}' || source_id"),
                "CONCAT",
                Some("||"),
                vec![
                    source_node(&format!("'{prefix}'"), "LITERAL", None, Vec::new()),
                    source_node("source_id", "IDENTIFIER", None, Vec::new()),
                ],
            ),
        )],
        correlations: Vec::new(),
        output: vec![typed_column("id", SqlType::character(28))],
    }
}

fn division_is_positive() -> ScalarExpr {
    scalar(ScalarAst::Call {
        operator: ">".to_owned(),
        op: ScalarOp::Gt,
        args: vec![
            ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    })
}

fn query_for_rel(rel: RelExpr, output: Vec<Column>) -> Query {
    assert_eq!(
        rel.output(),
        output.as_slice(),
        "test fixture output must match its authoritative relation output"
    );
    Query {
        source_sql: None,
        rel,
        analysis_errors: Vec::new(),
    }
}

fn z_select_item(name: &str) -> FormalScalarSelectItem {
    FormalScalarSelectItem {
        expr: FormalScalarExpr::Leaf {
            result_ty: FormalAttributeType::Z,
            term: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: name.to_owned(),
                    ty: FormalAttributeType::Z,
                },
            },
        },
        alias: name.to_owned(),
        alias_ty: FormalAttributeType::Z,
        numeric_dscale: Some(NumericDscaleProvenance::Exact(0)),
    }
}

fn runtime_risky_unary_project(table: &str, input_name: &str, output_name: &str) -> RelExpr {
    RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec![table.to_owned()],
            output: vec![column(input_name)],
        }),
        exprs: vec![scalar(ScalarAst::Call {
            operator: "/".to_owned(),
            op: ScalarOp::Divide,
            args: vec![
                ScalarAst::Literal {
                    raw: "10".to_owned(),
                },
                ScalarAst::InputRef { index: 0 },
            ],
        })],
        correlations: Vec::new(),
        output: vec![column(output_name)],
    }
}

fn numeric_cast_project(input_column: Column, output_column: Column, target: &str) -> RelExpr {
    RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["numeric_values".to_owned()],
            output: vec![input_column],
        }),
        exprs: vec![scalar(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::InputRef { index: 0 }],
            }),
            ty: target.to_owned(),
        })],
        correlations: Vec::new(),
        output: vec![output_column],
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
        analysis_errors: vec![],
    }
}

#[test]
fn rejects_local_invalid_integer_text_without_root_attestation() {
    let output = vec![typed_column("status", SqlType::Integer)];
    let query = Query {
        source_sql: Some(
            "SELECT status FROM projects WHERE projects.status <> 'ARCHIVED'".to_owned(),
        ),
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["projects".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar_with_source(
                ScalarAst::Call {
                    operator: "<>".to_owned(),
                    op: ScalarOp::NotEq,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Call {
                                operator: "CAST".to_owned(),
                                op: ScalarOp::Cast,
                                args: vec![ScalarAst::Literal {
                                    raw: "'ARCHIVED'".to_owned(),
                                }],
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                    ],
                },
                source_node(
                    "projects.status <> 'ARCHIVED'",
                    "NOT_EQUALS",
                    Some("<>"),
                    vec![
                        source_node("projects.status", "IDENTIFIER", None, Vec::new()),
                        source_node(
                            "'ARCHIVED'",
                            "LITERAL",
                            None,
                            vec![source_node("'ARCHIVED'", "LITERAL", None, Vec::new())],
                        ),
                    ],
                ),
            ),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "invalid_int4_unknown_literal_analysis_error_not_attested"
        }),
        "{:#?}",
        lowered.diagnostics
    );
    assert!(!matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Error { .. })
    ));

    let mut alternate_base = query.clone();
    alternate_base.source_sql =
        Some("SELECT status FROM projects WHERE projects.status <> '0x10'".to_owned());
    let RelExpr::Filter { predicate, .. } = &mut alternate_base.rel else {
        unreachable!()
    };
    let ScalarAst::Call { args, .. } = &mut predicate.parsed else {
        unreachable!()
    };
    let ScalarAst::TypeAnnotation { expr, .. } = &mut args[1] else {
        unreachable!()
    };
    let ScalarAst::Call { args, .. } = expr.as_mut() else {
        unreachable!()
    };
    let [ScalarAst::Literal { raw }] = args.as_mut_slice() else {
        unreachable!()
    };
    *raw = "'0x10'".to_owned();
    predicate.source.as_mut().unwrap().sql = Some("projects.status <> '0x10'".to_owned());
    let literal_source = predicate
        .source
        .as_mut()
        .and_then(|source| source.operands.get_mut(1))
        .and_then(Option::as_mut)
        .unwrap();
    literal_source.sql = Some("'0x10'".to_owned());
    literal_source.operands[0].as_mut().unwrap().sql = Some("'0x10'".to_owned());
    assert_eq!(
        attested_postgres_query_analysis_error(&alternate_base),
        None,
        "valid PostgreSQL alternate-base int4 input must not become a syntax error"
    );
    let alternate_base_lowered = lower_query(&alternate_base);
    assert_eq!(
        alternate_base_lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        alternate_base_lowered.diagnostics
    );
    let module = emit_rocq_query_module(
        alternate_base_lowered.query_expr.as_ref().unwrap(),
        alternate_base_lowered.query_expr.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("ScalarCast ScalarCastStringToInt32")
    );
}

#[test]
fn bare_string_literal_attestation_accepts_only_a_source_leaf() {
    let leaf = source_node("'ARCHIVED'", "LITERAL", None, Vec::new());
    assert!(source_is_bare_string_literal(&leaf, "'ARCHIVED'"));

    let wrapped = source_node("'ARCHIVED'", "LITERAL", None, vec![leaf.clone()]);
    assert!(!source_is_bare_string_literal(&wrapped, "'ARCHIVED'"));

    let mut changed_child = wrapped.clone();
    changed_child.operands[0].as_mut().unwrap().sql = Some("'ACTIVE'".to_owned());
    assert!(!source_is_bare_string_literal(&changed_child, "'ARCHIVED'"));

    let mut nested_child = wrapped.clone();
    nested_child.operands[0]
        .as_mut()
        .unwrap()
        .operands
        .push(Some(leaf.clone()));
    assert!(!source_is_bare_string_literal(&nested_child, "'ARCHIVED'"));

    let mut extra_child = wrapped.clone();
    extra_child.operands.push(Some(leaf));
    assert!(!source_is_bare_string_literal(&extra_child, "'ARCHIVED'"));

    let explicit_cast = source_node("CAST('ARCHIVED' AS TEXT)", "CAST", Some("CAST"), Vec::new());
    assert!(!source_is_bare_string_literal(&explicit_cast, "'ARCHIVED'"));

    for invalid in ["", "ARCHIVED", " SECURITY ", "+ARCHIVED", "-ARCHIVED"] {
        assert!(
            int32_text_is_definitely_invalid(invalid),
            "expected a closed invalid-int4 spelling: {invalid:?}"
        );
    }
    for not_proven_invalid in ["0x10", "0o20", "0b10000", "1_000", "2147483648", "123junk"] {
        assert!(
            !int32_text_is_definitely_invalid(not_proven_invalid),
            "alternate, range-sensitive, or trailing syntax must remain conservative: {not_proven_invalid:?}"
        );
    }
}

#[test]
fn exact_source_attestation_rejects_lexical_operator_and_identity_drift() {
    let mut decimal_zero = exact_source_node("0.00", "test:decimal-zero", "LITERAL", None, vec![]);
    decimal_zero.sql = Some("0".to_owned());
    assert!(
        !source_is_bare_integer_literal(&decimal_zero, "0"),
        "a rendered 0 must not erase the exact 0.00 token spelling"
    );

    let left = exact_source_node("users.id", "test:left", "IDENTIFIER", None, vec![]);
    let right = exact_source_node("1", "test:right", "LITERAL", None, vec![]);
    let mut comparison = exact_source_node(
        "users.id = 1",
        "test:comparison",
        "EQUALS",
        Some("="),
        vec![left.clone(), right],
    );
    comparison.sql = Some("users.id <> 1".to_owned());
    assert!(
        source_binary_operator_matches(Some(&comparison), ScalarOp::Eq),
        "rendered operator drift is diagnostic-only"
    );
    comparison.operator = Some("<>".to_owned());
    assert!(
        !source_binary_operator_matches(Some(&comparison), ScalarOp::NotEq),
        "operator metadata cannot override the exact equality token"
    );

    let mut borrowed_id = left.clone();
    borrowed_id.text = Some("users.other_id".to_owned());
    assert!(
        !source_nodes_identical(&left, &borrowed_id),
        "borrowing a node ID cannot substitute different exact text"
    );
    let mut borrowed_text = left.clone();
    borrowed_text.node_id = Some("test:unrelated".to_owned());
    assert!(
        !source_nodes_identical(&left, &borrowed_text),
        "equal text from a different exact node is not the same source identity"
    );

    let mut malformed = left;
    malformed.node_id = Some("borrowed-node-without-a-real-span".to_owned());
    assert!(!source_has_exact_binding(&malformed));
    assert!(
        validate_exact_source_pair(
            Some("SELECT users.id"),
            malformed.node_id.as_deref(),
            malformed.text.as_deref(),
            "test.source",
            false,
        )
        .is_err(),
        "a nonempty but malformed or borrowed node ID must fail closed"
    );
    assert!(
        validate_exact_source_pair(
            Some("SELECT users.id"),
            Some("1:8-1:15"),
            Some("users.id"),
            "test.source",
            false,
        )
        .is_ok()
    );
    assert!(
        validate_exact_source_pair(
            Some("SELECT users.id"),
            Some("1:1-1:6"),
            Some("users.id"),
            "test.source",
            false,
        )
        .is_err(),
        "a real span borrowed from a different source node cannot attest the text"
    );

    let output = vec![typed_column("id", SqlType::Integer)];
    let forged_query = Query {
        source_sql: Some("SELECT users.id FROM users".to_owned()),
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["users".to_owned()],
                output: output.clone(),
            }),
            exprs: vec![scalar_with_source(
                ScalarAst::InputRef { index: 0 },
                exact_source_node("users.id", "1:1-1:6", "IDENTIFIER", None, vec![]),
            )],
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };
    let lowered = lower_query(&forged_query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "scalar_source_provenance_not_bound_to_query" })
    );
}

#[test]
fn clause_ownership_accepts_only_one_exact_trailing_query_predicate_close() {
    assert!(exact_single_query_predicate_close_completion(
        "x NOT IN (SELECT y FROM u)"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "NOT EXISTS (SELECT y FROM u)"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN ((SELECT y FROM u) UNION (SELECT z FROM v))"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN ((SELECT y FROM u) UNION ALL (SELECT z FROM v))"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT 1 UNION ALL SELECT ALL 2)"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT ON (k) k FROM t UNION SELECT 1)"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT ($$)$$))"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT $tag$) UNION ($tag$)"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT ($é$)$é$))"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT (E'\\\')'))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN ((1), (2))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN ((SELECT 1) + 0)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "\"exists\" (SELECT y FROM u)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "schema.\"exists\" (SELECT y FROM u)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "schema.exists (SELECT y FROM u)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "catalog.schema.exists (SELECT y FROM u)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "schema.in (SELECT y FROM u)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x\u{00a0}IN((SELECT 7))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "xéIN((SELECT 9))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "1 IN (selecté(1))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT UNION SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT UNION SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT ALL UNION SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN ((SELECT DISTINCT) UNION (SELECT 1))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT ON (k) UNION SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN ((SELECT DISTINCT ON (k)) UNION (SELECT 1))"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT ON () 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT ON (k) FROM t UNION SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT DISTINCT FROM t UNION SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT FROM t)"
    ));
    for clause in [
        "AS", "INTO", "WHERE", "GROUP", "HAVING", "WINDOW", "ORDER", "LIMIT", "OFFSET", "FETCH",
        "FOR", "WITH",
    ] {
        assert!(!exact_single_query_predicate_close_completion(&format!(
            "x IN (SELECT {clause} x)"
        )));
    }
    assert!(!exact_single_query_predicate_close_completion(
        "(x IN (SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x) IN (SELECT 1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT ($$)$$)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT $tag$)$TAG$)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT ($é$)$é$)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT 1$tag$)$tag$)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT array[1)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT ([1)])"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT a[UNION SELECT 1])"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT 1) --c\r OR (false)"
    ));
    assert!(exact_single_query_predicate_close_completion(
        "x IN (SELECT 1 --c\r)"
    ));
    assert!(!exact_single_query_predicate_close_completion(
        "x IN (SELECT (E'\\\')')"
    ));
    let statement = "SELECT x FROM t WHERE x IN (SELECT y FROM u)";
    let predicate_start = statement.find("x IN").unwrap();
    let predicate = &statement[predicate_start..];
    let span = |start: usize, end: usize| format!("1:{}-1:{end}", start + 1);
    let mut source = ScalarSourceProvenance {
        sql: Some(predicate.to_owned()),
        node_id: Some(span(predicate_start, statement.len())),
        text: Some(predicate.to_owned()),
        kind: Some("IN".to_owned()),
        operator: Some("IN".to_owned()),
        clause_ownership: Some(ScalarSourceClauseOwnership {
            kind: SourceClauseKind::Where,
            query_block_id: span(0, statement.len()),
            source_node_id: span(predicate_start, statement.len() - 1),
            source_sql: predicate.to_owned(),
            analysis_errors: Vec::new(),
        }),
        operands: Vec::new(),
    };
    assert!(
        validate_scalar_source_binding_tree(&source, Some(statement), "predicate", false).is_ok()
    );

    let set_statement = "SELECT x FROM t WHERE x IN ((SELECT y FROM u) UNION (SELECT z FROM v))";
    let set_predicate_start = set_statement.find("x IN").unwrap();
    let set_predicate = &set_statement[set_predicate_start..];
    let set_span = |start: usize, end: usize| format!("1:{}-1:{end}", start + 1);
    let set_source = ScalarSourceProvenance {
        sql: Some(set_predicate.to_owned()),
        node_id: Some(set_span(set_predicate_start, set_statement.len())),
        text: Some(set_predicate.to_owned()),
        kind: Some("IN".to_owned()),
        operator: Some("IN".to_owned()),
        clause_ownership: Some(ScalarSourceClauseOwnership {
            kind: SourceClauseKind::Where,
            query_block_id: set_span(0, set_statement.len()),
            source_node_id: set_span(set_predicate_start, set_statement.len() - 1),
            source_sql: set_predicate.to_owned(),
            analysis_errors: Vec::new(),
        }),
        operands: Vec::new(),
    };
    assert!(
        validate_scalar_source_binding_tree(
            &set_source,
            Some(set_statement),
            "setPredicate",
            false,
        )
        .is_ok()
    );

    let mut borrowed_start = source.clone();
    borrowed_start
        .clause_ownership
        .as_mut()
        .unwrap()
        .source_node_id = span(predicate_start + 1, statement.len() - 1);
    assert!(
        validate_scalar_source_binding_tree(&borrowed_start, Some(statement), "predicate", false)
            .is_err()
    );

    let mut truncated_text = source.clone();
    truncated_text.clause_ownership.as_mut().unwrap().source_sql =
        predicate[..predicate.len() - 1].to_owned();
    assert!(
        validate_scalar_source_binding_tree(&truncated_text, Some(statement), "predicate", false)
            .is_err()
    );

    let mut more_than_close = source.clone();
    more_than_close
        .clause_ownership
        .as_mut()
        .unwrap()
        .source_node_id = span(predicate_start, statement.len() - 2);
    assert!(
        validate_scalar_source_binding_tree(&more_than_close, Some(statement), "predicate", false)
            .is_err()
    );

    let mut escaped_query_block = source.clone();
    escaped_query_block
        .clause_ownership
        .as_mut()
        .unwrap()
        .query_block_id = span(0, statement.len() - 1);
    assert!(
        validate_scalar_source_binding_tree(
            &escaped_query_block,
            Some(statement),
            "predicate",
            false
        )
        .is_err()
    );

    source.text = Some("x = (SELECT y FROM u)".to_owned());
    assert!(
        validate_scalar_source_binding_tree(&source, Some(statement), "predicate", false).is_err()
    );
    assert!(!exact_single_query_predicate_close_completion(
        "x = (SELECT y FROM u)"
    ));
}

#[test]
fn invalid_integer_poison_is_order_independent_for_mixed_analysis_errors() {
    let output = vec![typed_column("i", SqlType::Integer)];
    let invalid_literal_cast = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Call {
            operator: "CAST".to_owned(),
            op: ScalarOp::Cast,
            args: vec![ScalarAst::Literal {
                raw: "'ARCHIVED'".to_owned(),
            }],
        }),
        ty: "INTEGER".to_owned(),
    };
    let invalid_int4 = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            invalid_literal_cast.clone(),
        ],
    };
    let computed_integer = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::Literal {
                raw: "0".to_owned(),
            },
        ],
    };
    let invalid_computed_left = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![computed_integer.clone(), invalid_literal_cast.clone()],
    };
    let invalid_computed_right = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![invalid_literal_cast, computed_integer],
    };
    let explicit_varchar = ScalarAst::Call {
        operator: "=".to_owned(),
        op: ScalarOp::Eq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'x'".to_owned(),
                    }],
                }),
                ty: "VARCHAR".to_owned(),
            },
        ],
    };

    for (label, args) in [
        (
            "earlier explicit VARCHAR cast",
            vec![explicit_varchar.clone(), invalid_int4.clone()],
        ),
        (
            "earlier invalid INT4 cast",
            vec![invalid_int4.clone(), explicit_varchar.clone()],
        ),
        (
            "computed integer before invalid literal",
            vec![invalid_computed_left.clone(), explicit_varchar.clone()],
        ),
        (
            "invalid literal before computed integer",
            vec![invalid_computed_right, explicit_varchar.clone()],
        ),
        (
            "computed invalid comparison after another analysis error",
            vec![explicit_varchar, invalid_computed_left],
        ),
    ] {
        let query = Query {
            source_sql: Some(format!("mixed PostgreSQL analysis errors: {label}")),
            rel: RelExpr::Filter {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: output.clone(),
                }),
                predicate: scalar(ScalarAst::Call {
                    operator: "AND".to_owned(),
                    op: ScalarOp::And,
                    args,
                }),
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        };
        let lowered = lower_query(&query);
        assert_eq!(lowered.status, LoweringStatus::Blocked, "{label}");
        assert!(
            lowered.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == "invalid_int4_unknown_literal_analysis_error_not_attested"
            }),
            "{label}: {:#?}",
            lowered.diagnostics
        );
        assert!(
            !matches!(lowered.query_expr, Some(FormalQueryExpr::Error { .. })),
            "{label} must not choose a query-wide SQLSTATE from local evidence"
        );
    }
}

#[test]
fn order_by_alias_analysis_error_is_terminal_before_relational_lowering() {
    let output = vec![typed_column("x", SqlType::Integer)];
    let mut query = Query {
        source_sql: Some("select 1 as x order by x + 1".to_owned()),
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1".to_owned(),
                }),
                ty: "INTEGER".to_owned(),
            })]],
            output: output.clone(),
        },
        analysis_errors: vec![
            QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                sql_state: "42703".to_owned(),
                query_block_id: "query-0".to_owned(),
                source_order_item_node_id: "query-0/order-0".to_owned(),
                source_order_item_sql: "x + 1".to_owned(),
                output_alias: "x".to_owned(),
            },
        ],
    };

    let schema = Schema { tables: Vec::new() };
    let config = LoweringConfig::default();
    let lowered = lower_query_with_schema_config(&query, &schema, &config);
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Error {
            error: FormalQueryError::UndefinedColumn,
            ..
        })
    ));

    let mut multiply_attested = query.clone();
    multiply_attested
        .analysis_errors
        .push(query.analysis_errors[0].clone());
    let multiply_attested = lower_query_with_schema_config(&multiply_attested, &schema, &config);
    assert_eq!(multiply_attested.status, LoweringStatus::Blocked);
    assert!(
        multiply_attested
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "multiple_query_analysis_errors_not_supported")
    );

    query.analysis_errors.retain(|error| {
        !matches!(
            error,
            QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn { .. }
        )
    });
    let unmarked = lower_query_with_schema_config(&query, &schema, &config);
    assert_eq!(unmarked.status, LoweringStatus::Lowered);
    assert!(
        !matches!(unmarked.query_expr, Some(FormalQueryExpr::Error { .. })),
        "without the validated query-analysis marker, the ordinary relation must not become a fabricated SQL error"
    );
}

#[test]
fn order_by_alias_analysis_error_rejects_competing_conversion_errors() {
    let output = vec![typed_column("x", SqlType::Integer)];
    let query = Query {
        source_sql: Some(
            "select cast('ARCHIVED' as integer) as x order by x + missing_name".to_owned(),
        ),
        rel: RelExpr::Values {
            rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'ARCHIVED'".to_owned(),
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })]],
            output: output.clone(),
        },
        analysis_errors: vec![
            QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                sql_state: "42703".to_owned(),
                query_block_id: "query-0".to_owned(),
                source_order_item_node_id: "query-0/order-0".to_owned(),
                source_order_item_sql: "x + missing_name".to_owned(),
                output_alias: "x".to_owned(),
            },
        ],
    };

    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "query_analysis_error_competition_not_supported"
        })
    );
    assert!(!matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Error { .. })
    ));
}

#[test]
fn analysis_error_attestation_rejects_explicit_text_cast_and_cross_scope_token_match() {
    let output = vec![typed_column("status", SqlType::Integer)];
    let predicate_ast = ScalarAst::Call {
        operator: "<>".to_owned(),
        op: ScalarOp::NotEq,
        args: vec![
            ScalarAst::InputRef { index: 0 },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'ARCHIVED'".to_owned(),
                    }],
                }),
                ty: "INTEGER".to_owned(),
            },
        ],
    };
    let query_with = |source_sql: &str, source: ScalarSourceProvenance| Query {
        source_sql: Some(source_sql.to_owned()),
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["projects".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar_with_source(predicate_ast.clone(), source),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let explicit_text_cast = query_with(
        "SELECT status FROM projects WHERE projects.status <> 'ARCHIVED'::text",
        source_node(
            "projects.status <> CAST('ARCHIVED' AS TEXT)",
            "NOT_EQUALS",
            Some("<>"),
            vec![
                source_node("projects.status", "IDENTIFIER", None, Vec::new()),
                source_node(
                    "CAST('ARCHIVED' AS TEXT)",
                    "CAST",
                    Some("CAST"),
                    vec![source_node("'ARCHIVED'", "LITERAL", None, Vec::new())],
                ),
            ],
        ),
    );
    assert_eq!(
        attested_postgres_query_analysis_error(&explicit_text_cast),
        None,
        "a source text cast selects text comparison semantics, not int4 input conversion"
    );

    let cross_scope = query_with(
        "SELECT status FROM projects WHERE projects.status <> projects.other_status AND EXISTS (SELECT 1 FROM archived WHERE archived.status <> 'ARCHIVED')",
        source_node(
            "projects.status <> projects.other_status",
            "NOT_EQUALS",
            Some("<>"),
            vec![
                source_node("projects.status", "IDENTIFIER", None, Vec::new()),
                source_node("projects.other_status", "IDENTIFIER", None, Vec::new()),
            ],
        ),
    );
    assert_eq!(
        attested_postgres_query_analysis_error(&cross_scope),
        None,
        "same-spelled literal and column tokens in a nested scope cannot attest the outer Rex node"
    );
}

#[test]
fn lowers_only_closed_postgres_boolean_integer_equality_analysis_error_marker() {
    let output = vec![typed_column("ghost", SqlType::Boolean)];
    let marker =
        || SourceAnalysisErrorProvenance::PostgresBooleanIntegerEqualityUndefinedFunction {
            rex_path: "$".to_owned(),
            identifier_operand: 0,
            literal_operand: 1,
            generated_comparison_sql: "=($0, false)".to_owned(),
            input_index: 0,
            base_table: vec!["users".to_owned()],
            table_field_index: 0,
            base_field_name: "ghost".to_owned(),
            source_literal_canonical_value: "0".to_owned(),
            generated_literal_canonical_value: "false".to_owned(),
        };
    let query_with = |analysis_errors: Vec<SourceAnalysisErrorProvenance>| {
        let mut predicate = scalar_with_source(
            ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "false".to_owned(),
                        }),
                        ty: "BOOLEAN".to_owned(),
                    },
                ],
            },
            source_node(
                "users.ghost = 0",
                "EQUALS",
                Some("="),
                vec![
                    source_node("users.ghost", "IDENTIFIER", None, Vec::new()),
                    source_node("0", "LITERAL", None, Vec::new()),
                ],
            ),
        );
        predicate.source.as_mut().unwrap().clause_ownership = Some(ScalarSourceClauseOwnership {
            kind: SourceClauseKind::Where,
            query_block_id: "1:1-1:60".to_owned(),
            source_node_id: "1:33-1:48".to_owned(),
            source_sql: "users.ghost = 0".to_owned(),
            analysis_errors,
        });
        Query {
            source_sql: Some("SELECT ghost FROM users WHERE users.ghost = 0".to_owned()),
            rel: RelExpr::Filter {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["users".to_owned()],
                    output: output.clone(),
                }),
                predicate,
                correlations: Vec::new(),
                output: output.clone(),
            },
            analysis_errors: vec![],
        }
    };

    let query = query_with(vec![marker()]);
    assert_eq!(query_boolean_integer_source_mismatch_count(&query), 1);
    assert_eq!(query_source_analysis_error_marker_count(&query), 1);
    assert_eq!(
        attested_postgres_query_analysis_error(&query),
        Some(FormalQueryError::UndefinedFunction)
    );
    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Error {
            error: FormalQueryError::UndefinedFunction,
            ..
        })
    ));

    let unmarked = query_with(Vec::new());
    assert_eq!(attested_postgres_query_analysis_error(&unmarked), None);
    let rejected = lower_query(&unmarked);
    assert_eq!(rejected.status, LoweringStatus::Blocked);
    assert!(
        rejected
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "source_analysis_error_attestation_drift")
    );

    let mut path_drift = query.clone();
    let RelExpr::Filter { predicate, .. } = &mut path_drift.rel else {
        unreachable!()
    };
    let ownership = predicate
        .source
        .as_mut()
        .and_then(|source| source.clause_ownership.as_mut())
        .unwrap();
    let SourceAnalysisErrorProvenance::PostgresBooleanIntegerEqualityUndefinedFunction {
        rex_path,
        ..
    } = &mut ownership.analysis_errors[0];
    *rex_path = "$.0".to_owned();
    assert_eq!(attested_postgres_query_analysis_error(&path_drift), None);
    assert_eq!(lower_query(&path_drift).status, LoweringStatus::Blocked);

    let mut rendered_qualifier_drift = query.clone();
    let RelExpr::Filter { predicate, .. } = &mut rendered_qualifier_drift.rel else {
        unreachable!()
    };
    let source = predicate.source.as_mut().unwrap();
    source.sql = Some("other.ghost = 0".to_owned());
    source.operands[0].as_mut().unwrap().sql = Some("other.ghost".to_owned());
    assert_eq!(
        attested_postgres_query_analysis_error(&rendered_qualifier_drift),
        Some(FormalQueryError::UndefinedFunction),
        "rendered scalar SQL is diagnostic-only"
    );
    assert_eq!(
        lower_query(&rendered_qualifier_drift).status,
        LoweringStatus::Lowered
    );

    let mut exact_qualifier_drift = query.clone();
    let RelExpr::Filter { predicate, .. } = &mut exact_qualifier_drift.rel else {
        unreachable!()
    };
    let source = predicate.source.as_mut().unwrap();
    source.node_id = Some("test:other.ghost = 0".to_owned());
    source.text = Some("other.ghost = 0".to_owned());
    let identifier = source.operands[0].as_mut().unwrap();
    identifier.node_id = Some("test:other.ghost".to_owned());
    identifier.text = Some("other.ghost".to_owned());
    assert_eq!(
        attested_postgres_query_analysis_error(&exact_qualifier_drift),
        None,
        "the exact source node/text pair, not the rendered echo, owns identifier semantics"
    );
    assert_eq!(
        lower_query(&exact_qualifier_drift).status,
        LoweringStatus::Blocked
    );

    let mut duplicate = query;
    let RelExpr::Filter { predicate, .. } = &mut duplicate.rel else {
        unreachable!()
    };
    predicate
        .source
        .as_mut()
        .and_then(|source| source.clause_ownership.as_mut())
        .unwrap()
        .analysis_errors
        .push(marker());
    assert_eq!(attested_postgres_query_analysis_error(&duplicate), None);
    assert_eq!(lower_query(&duplicate).status, LoweringStatus::Blocked);
}

#[test]
fn lowers_attested_varchar_integer_operator_lookup_failure() {
    let output = vec![typed_column("commit_id", SqlType::varchar(Some(255)))];
    let query = Query {
        source_sql: Some(
            "SELECT commit_id FROM notes WHERE notes.commit_id IN (2044708959)".to_owned(),
        ),
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["notes".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar_with_source(
                ScalarAst::Call {
                    operator: "=".to_owned(),
                    op: ScalarOp::Eq,
                    args: vec![
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Call {
                                operator: "CAST".to_owned(),
                                op: ScalarOp::Cast,
                                args: vec![ScalarAst::InputRef { index: 0 }],
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "2044708959".to_owned(),
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                    ],
                },
                source_node(
                    "notes.commit_id IN (2044708959)",
                    "IN",
                    Some("IN"),
                    vec![
                        source_node("notes.commit_id", "IDENTIFIER", None, Vec::new()),
                        source_node("2044708959", "LITERAL", None, Vec::new()),
                    ],
                ),
            ),
            correlations: Vec::new(),
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    assert_eq!(
        attested_postgres_query_analysis_error(&query),
        Some(FormalQueryError::UndefinedFunction)
    );
    let mut explicitly_cast = query.clone();
    explicitly_cast.source_sql = Some(
        "SELECT commit_id FROM notes WHERE CAST(notes.commit_id AS INTEGER) = 2044708959"
            .to_owned(),
    );
    let RelExpr::Filter { predicate, .. } = &mut explicitly_cast.rel else {
        unreachable!()
    };
    predicate.source = Some(source_node(
        "CAST(notes.commit_id AS INTEGER) = 2044708959",
        "EQUALS",
        Some("="),
        vec![
            source_node(
                "CAST(notes.commit_id AS INTEGER)",
                "CAST",
                Some("CAST"),
                vec![source_node(
                    "notes.commit_id",
                    "IDENTIFIER",
                    None,
                    Vec::new(),
                )],
            ),
            source_node("2044708959", "LITERAL", None, Vec::new()),
        ],
    ));
    assert_eq!(
        attested_postgres_query_analysis_error(&explicitly_cast),
        None,
        "an explicit PostgreSQL cast is a runtime cast, not operator lookup failure"
    );
}

#[test]
fn lowers_attested_two_argument_count_distinct_lookup_failure() {
    let input = vec![
        typed_column("left_name", SqlType::text()),
        typed_column("right_name", SqlType::text()),
    ];
    let output = vec![typed_column("count", SqlType::BigInt)];
    let project_exprs = vec![
        scalar_with_source(
            ScalarAst::InputRef { index: 0 },
            source_node("left_name", "IDENTIFIER", None, Vec::new()),
        ),
        scalar_with_source(
            ScalarAst::InputRef { index: 1 },
            source_node("right_name", "IDENTIFIER", None, Vec::new()),
        ),
    ];
    let aggregate_input = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["names".to_owned()],
            output: input.clone(),
        }),
        exprs: project_exprs,
        correlations: Vec::new(),
        output: input,
    };
    let modifiers = AggregateModifiers {
        source: Some(source_node(
            "COUNT(DISTINCT left_name, right_name)",
            "OTHER_FUNCTION",
            Some("COUNT"),
            vec![
                source_node("left_name", "IDENTIFIER", None, Vec::new()),
                source_node("right_name", "IDENTIFIER", None, Vec::new()),
            ],
        )),
        source_distinct: Some(true),
        ..Default::default()
    };
    let query = Query {
        source_sql: Some("SELECT COUNT(DISTINCT left_name, right_name) FROM names".to_owned()),
        rel: RelExpr::Aggregate {
            input: Box::new(aggregate_input),
            group_keys: Vec::new(),
            grouping_sets: vec![Vec::new()],
            agg_calls: vec![AggregateCall {
                raw: "COUNT(DISTINCT $0, $1)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: true,
                modifiers,
                args: vec![
                    scalar(ScalarAst::InputRef { index: 0 }),
                    scalar(ScalarAst::InputRef { index: 1 }),
                ],
                filter: None,
            }],
            output: output.clone(),
        },
        analysis_errors: vec![],
    };

    let RelExpr::Aggregate {
        input, agg_calls, ..
    } = &query.rel
    else {
        unreachable!()
    };
    let aggregate_source = agg_calls[0].modifiers.source.as_ref().unwrap();
    assert_eq!(aggregate_source.operands.len(), 2);
    assert!(source_nodes_identical(
        source_operand(Some(aggregate_source), 0).unwrap(),
        aggregate_input_source(input, 0).unwrap()
    ));
    assert!(source_nodes_identical(
        source_operand(Some(aggregate_source), 1).unwrap(),
        aggregate_input_source(input, 1).unwrap()
    ));
    assert!(attested_two_argument_count_distinct(&agg_calls[0], input));
    let mut rendered_drift = agg_calls[0].clone();
    rendered_drift.modifiers.source.as_mut().unwrap().sql =
        Some("COUNT(left_name, right_name)".to_owned());
    assert!(
        attested_two_argument_count_distinct(&rendered_drift, input),
        "the rendered aggregate echo is diagnostic-only"
    );
    let mut exact_distinct_drift = agg_calls[0].clone();
    exact_distinct_drift.modifiers.source.as_mut().unwrap().text =
        Some("COUNT(left_name, right_name)".to_owned());
    assert!(
        !attested_two_argument_count_distinct(&exact_distinct_drift, input),
        "the exact source text must contain DISTINCT"
    );
    let mut borrowed_operand = agg_calls[0].clone();
    borrowed_operand.modifiers.source.as_mut().unwrap().operands[0]
        .as_mut()
        .unwrap()
        .node_id = Some("test:borrowed-left-name".to_owned());
    assert!(
        !attested_two_argument_count_distinct(&borrowed_operand, input),
        "equal text from a borrowed node ID cannot attest aggregate identity"
    );
    assert_eq!(
        attested_postgres_query_analysis_error(&query),
        Some(FormalQueryError::UndefinedFunction)
    );
    let lowered = lower_query(&query);
    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(
        lowered.query_expr,
        Some(FormalQueryExpr::Error {
            error: FormalQueryError::UndefinedFunction,
            ..
        })
    ));
}

#[test]
fn lowers_guarded_integral_statistic_ratio_from_derived_positions() {
    fn statistic_source(function: &str, argument: &str) -> ScalarSourceProvenance {
        source_node(
            &format!("{function}({argument})"),
            "OTHER_FUNCTION",
            Some(function),
            vec![source_node(argument, "IDENTIFIER", None, Vec::new())],
        )
    }

    fn guarded_case_source(
        null_when_zero: bool,
        expanded_definitions: bool,
        stddev_definition: &ScalarSourceProvenance,
        avg_definition: &ScalarSourceProvenance,
    ) -> ScalarSourceProvenance {
        let zero_text = if null_when_zero { "null" } else { "0" };
        let case_text = format!("case mean when 0 then {zero_text} else stdev/mean end");
        let avg_reference = if expanded_definitions {
            avg_definition.clone()
        } else {
            source_node("mean", "IDENTIFIER", None, Vec::new())
        };
        let stddev_reference = if expanded_definitions {
            stddev_definition.clone()
        } else {
            source_node("stdev", "IDENTIFIER", None, Vec::new())
        };
        let mut condition = source_node(
            "mean = 0",
            "EQUALS",
            Some("="),
            vec![
                avg_reference.clone(),
                source_node("0", "LITERAL", None, Vec::new()),
            ],
        );
        condition.node_id = Some(format!("test:{case_text}"));
        condition.text = Some(case_text.clone());
        ScalarSourceProvenance {
            sql: Some(case_text.clone()),
            node_id: Some(format!("test:{case_text}")),
            text: Some(case_text),
            kind: Some("CASE".to_owned()),
            operator: Some("CASE".to_owned()),
            clause_ownership: None,
            operands: vec![
                Some(condition),
                Some(source_node(zero_text, "LITERAL", None, Vec::new())),
                Some(source_node(
                    "stdev/mean",
                    "DIVIDE",
                    Some("/"),
                    vec![stddev_reference, avg_reference],
                )),
            ],
        }
    }

    fn searched_guarded_case_source(
        null_when_zero: bool,
        expanded_definitions: bool,
        qualifier: Option<&str>,
        stddev_definition: &ScalarSourceProvenance,
        avg_definition: &ScalarSourceProvenance,
    ) -> ScalarSourceProvenance {
        let zero_text = if null_when_zero { "null" } else { "0" };
        let qualify = |name: &str| {
            qualifier
                .map(|qualifier| format!("{qualifier}.{name}"))
                .unwrap_or_else(|| name.to_owned())
        };
        let avg_name = qualify("mean");
        let stddev_name = qualify("stdev");
        let avg_reference = if expanded_definitions {
            avg_definition.clone()
        } else {
            source_node(&avg_name, "IDENTIFIER", None, Vec::new())
        };
        let stddev_reference = if expanded_definitions {
            stddev_definition.clone()
        } else {
            source_node(&stddev_name, "IDENTIFIER", None, Vec::new())
        };
        let condition = source_node(
            &format!("{avg_name} = 0"),
            "EQUALS",
            Some("="),
            vec![
                avg_reference.clone(),
                source_node("0", "LITERAL", None, Vec::new()),
            ],
        );
        let division = source_node(
            &format!("{stddev_name} / {avg_name}"),
            "DIVIDE",
            Some("/"),
            vec![stddev_reference, avg_reference],
        );
        source_node(
            &format!(
                "CASE WHEN {avg_name} = 0 THEN {zero_text} ELSE {stddev_name} / {avg_name} END"
            ),
            "CASE",
            Some("CASE"),
            vec![
                condition,
                source_node(zero_text, "LITERAL", None, Vec::new()),
                division,
            ],
        )
    }

    fn guarded_case_ast(stddev_index: usize, avg_index: usize, null_when_zero: bool) -> ScalarAst {
        ScalarAst::Call {
            operator: "CASE".to_owned(),
            op: ScalarOp::Case,
            args: vec![
                ScalarAst::Call {
                    operator: "=".to_owned(),
                    op: ScalarOp::Eq,
                    args: vec![
                        ScalarAst::InputRef { index: avg_index },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "0".to_owned(),
                            }),
                            ty: "INTEGER".to_owned(),
                        },
                    ],
                },
                if null_when_zero {
                    ScalarAst::Literal {
                        raw: "NULL".to_owned(),
                    }
                } else {
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "0".to_owned(),
                        }),
                        ty: "INTEGER".to_owned(),
                    }
                },
                ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::InputRef {
                            index: stddev_index,
                        },
                        ScalarAst::InputRef { index: avg_index },
                    ],
                },
            ],
        }
    }

    fn query(avg_argument: usize) -> Query {
        let input = vec![column("g0"), column("g1"), column("value")];
        let avg_argument_name = input[avg_argument].name.clone();
        let avg_definition = statistic_source("avg", &avg_argument_name);
        let stddev_definition = statistic_source("stddev_samp", "value");
        let avg_modifiers = AggregateModifiers {
            source_distinct: Some(false),
            source: Some(avg_definition.clone()),
            ..Default::default()
        };
        let stddev_modifiers = AggregateModifiers {
            source_distinct: Some(false),
            source: Some(stddev_definition.clone()),
            ..Default::default()
        };
        let aggregate_output = vec![
            column("g0"),
            column("g1"),
            decimal_column_unconstrained("mean"),
            decimal_column_unconstrained("stdev"),
        ];
        let aggregate = RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            group_keys: vec![0, 1],
            grouping_sets: vec![vec![0, 1]],
            // AVG deliberately precedes STDDEV, so neither output occupies
            // the historical q039 positions.
            agg_calls: vec![
                AggregateCall {
                    raw: format!("AVG(${avg_argument})"),
                    function: "AVG".to_owned(),
                    distinct: false,
                    modifiers: avg_modifiers,
                    args: vec![scalar(ScalarAst::InputRef {
                        index: avg_argument,
                    })],
                    filter: None,
                },
                AggregateCall {
                    raw: "STDDEV_SAMP($2)".to_owned(),
                    function: "STDDEV_SAMP".to_owned(),
                    distinct: false,
                    modifiers: stddev_modifiers,
                    args: vec![scalar(ScalarAst::InputRef { index: 2 })],
                    filter: None,
                },
            ],
            output: aggregate_output.clone(),
        };
        let filter_case = guarded_case_ast(3, 2, false);
        let filter_case_source =
            guarded_case_source(false, false, &stddev_definition, &avg_definition);
        let predicate = scalar_with_source(
            ScalarAst::Call {
                operator: ">".to_owned(),
                op: ScalarOp::Gt,
                args: vec![
                    filter_case,
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "-1".to_owned(),
                        }),
                        ty: "INTEGER".to_owned(),
                    },
                ],
            },
            source_node(
                "case mean when 0 then 0 else stdev/mean end > -1",
                "GREATER_THAN",
                Some(">"),
                vec![
                    filter_case_source,
                    source_node("-1", "LITERAL", None, Vec::new()),
                ],
            ),
        );
        let filtered = RelExpr::Filter {
            input: Box::new(aggregate),
            predicate,
            correlations: Vec::new(),
            output: aggregate_output,
        };
        // One complete permutation of the Aggregate outputs surrounds the
        // ratio at position zero.
        let output = vec![
            decimal_column_unconstrained("cov"),
            decimal_column_unconstrained("stdev"),
            column("g0"),
            decimal_column_unconstrained("mean"),
            column("g1"),
        ];
        let rel = RelExpr::Project {
            input: Box::new(filtered),
            exprs: vec![
                scalar_with_source(
                    guarded_case_ast(3, 2, true),
                    guarded_case_source(true, true, &stddev_definition, &avg_definition),
                ),
                scalar(ScalarAst::InputRef { index: 3 }),
                scalar(ScalarAst::InputRef { index: 0 }),
                scalar(ScalarAst::InputRef { index: 2 }),
                scalar(ScalarAst::InputRef { index: 1 }),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        };
        query_for_rel(rel, output)
    }

    fn install_aggregate_permutation_bridge(query: &mut Query, mapping: &[usize]) {
        let RelExpr::Project {
            input: filter,
            exprs: outer_exprs,
            output: outer_output,
            ..
        } = &mut query.rel
        else {
            unreachable!()
        };
        let RelExpr::Filter {
            input: aggregate_input,
            predicate,
            output: filter_output,
            ..
        } = filter.as_mut()
        else {
            unreachable!()
        };
        let aggregate = aggregate_input.as_ref().clone();
        let RelExpr::Aggregate {
            group_keys,
            agg_calls,
            output: aggregate_output,
            ..
        } = &aggregate
        else {
            unreachable!()
        };
        assert_eq!(mapping.len(), aggregate_output.len());
        let bridge_output = mapping
            .iter()
            .map(|index| aggregate_output[*index].clone())
            .collect::<Vec<_>>();
        let bridge_exprs = mapping
            .iter()
            .map(|index| {
                let source = if *index < group_keys.len() {
                    source_node(
                        &aggregate_output[*index].name,
                        "IDENTIFIER",
                        None,
                        Vec::new(),
                    )
                } else {
                    agg_calls[*index - group_keys.len()]
                        .modifiers
                        .source
                        .clone()
                        .expect("statistic aggregate source")
                };
                scalar_with_source(ScalarAst::InputRef { index: *index }, source)
            })
            .collect::<Vec<_>>();
        let visible_stddev = mapping.iter().position(|index| *index == 3).unwrap();
        let visible_avg = mapping.iter().position(|index| *index == 2).unwrap();
        let ScalarAst::Call {
            op: ScalarOp::Gt,
            args: predicate_args,
            ..
        } = &mut predicate.parsed
        else {
            unreachable!()
        };
        predicate_args[0] = guarded_case_ast(visible_stddev, visible_avg, false);
        outer_exprs[0].parsed = guarded_case_ast(visible_stddev, visible_avg, true);
        let stddev_definition = agg_calls
            .iter()
            .find(|call| call.function.eq_ignore_ascii_case("STDDEV_SAMP"))
            .and_then(|call| call.modifiers.source.as_ref())
            .expect("STDDEV source")
            .clone();
        let avg_definition = agg_calls
            .iter()
            .find(|call| call.function.eq_ignore_ascii_case("AVG"))
            .and_then(|call| call.modifiers.source.as_ref())
            .expect("AVG source")
            .clone();
        outer_exprs[0].source = Some(searched_guarded_case_source(
            true,
            true,
            None,
            &stddev_definition,
            &avg_definition,
        ));
        let searched_filter_case = searched_guarded_case_source(
            false,
            false,
            Some("derived"),
            &stddev_definition,
            &avg_definition,
        );
        predicate.source = Some(source_node(
            "CASE WHEN derived.mean = 0 THEN 0 ELSE derived.stdev / derived.mean END > -1",
            "GREATER_THAN",
            Some(">"),
            vec![
                searched_filter_case,
                source_node("-1", "LITERAL", None, Vec::new()),
            ],
        ));
        outer_output[0].ty = SqlType::Integer;
        for (position, aggregate_index) in [3, 0, 2, 1].into_iter().enumerate() {
            outer_exprs[position + 1] = scalar(ScalarAst::InputRef {
                index: mapping
                    .iter()
                    .position(|index| *index == aggregate_index)
                    .unwrap(),
            });
        }
        *filter_output = bridge_output.clone();
        *aggregate_input = Box::new(RelExpr::Project {
            input: Box::new(aggregate),
            exprs: bridge_exprs,
            correlations: Vec::new(),
            output: bridge_output,
        });
    }

    let schema = Schema {
        tables: vec![Table {
            name: "measurements".to_owned(),
            columns: vec![column("g0"), column("g1"), column("value")],
            constraints: Default::default(),
        }],
    };
    let baseline = query(2);
    let lowered = lower_query_with_schema_config(&baseline, &schema, &LoweringConfig::default());
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    let lowered_expr = lowered
        .query_expr
        .as_ref()
        .expect("lowered ratio expression");
    let module = emit_rocq_query_module(lowered_expr, lowered_expr);
    assert!(
        module
            .rocq_module
            .contains("AggregateNumericDisplayScale NumericAverageInt32")
    );
    assert!(
        module
            .rocq_module
            .contains("AggregateNumericDisplayScale NumericStddevSampleInt32")
    );
    assert!(module.rocq_module.contains("ScalarDivide ScalarNumeric"));
    assert!(
        !module
            .rocq_module
            .contains("AggregateStddevSampleOverAverageInt32")
    );
    assert!(module.rocq_module.contains("-1"));
    assert_no_physical_plan_constructs(&module);

    let mut bridged = baseline.clone();
    install_aggregate_permutation_bridge(&mut bridged, &[1, 3, 0, 2]);
    let bridged_lowered =
        lower_query_with_schema_config(&bridged, &schema, &LoweringConfig::default());
    assert_eq!(
        bridged_lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        bridged_lowered.diagnostics
    );
    assert_eq!(
        bridged_lowered.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::Numeric
    );
    assert!(bridged_lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "calcite_integral_stddev_avg_ratio_type_overridden"
    }));
    let bridged_module = emit_rocq_query_module(
        bridged_lowered
            .query_expr
            .as_ref()
            .expect("lowered bridged ratio"),
        bridged_lowered
            .query_expr
            .as_ref()
            .expect("lowered bridged ratio"),
    );
    assert!(
        bridged_module
            .rocq_module
            .contains("AggregateNumericDisplayScale NumericAverageInt32")
    );
    assert!(
        bridged_module
            .rocq_module
            .contains("AggregateNumericDisplayScale NumericStddevSampleInt32")
    );

    let mut borrowed_bridge_source = bridged.clone();
    let RelExpr::Project { input, .. } = &mut borrowed_bridge_source.rel else {
        unreachable!()
    };
    let RelExpr::Filter { input, .. } = input.as_mut() else {
        unreachable!()
    };
    let RelExpr::Project { exprs, .. } = input.as_mut() else {
        unreachable!()
    };
    exprs[1].source.as_mut().unwrap().node_id = Some("test:borrowed-stddev".to_owned());
    assert_eq!(
        lower_query_with_schema_config(
            &borrowed_bridge_source,
            &schema,
            &LoweringConfig::default(),
        )
        .status,
        LoweringStatus::Blocked,
        "a borrowed aggregate definition cannot attest a transparent permutation"
    );

    let mut duplicate_bridge_position = bridged.clone();
    let RelExpr::Project { input, .. } = &mut duplicate_bridge_position.rel else {
        unreachable!()
    };
    let RelExpr::Filter { input, .. } = input.as_mut() else {
        unreachable!()
    };
    let RelExpr::Project { exprs, .. } = input.as_mut() else {
        unreachable!()
    };
    exprs[0].parsed = exprs[1].parsed.clone();
    assert_eq!(
        lower_query_with_schema_config(
            &duplicate_bridge_position,
            &schema,
            &LoweringConfig::default(),
        )
        .status,
        LoweringStatus::Blocked,
        "a duplicate/missing bridge position is not a transparent permutation"
    );

    let mut bridge_type_drift = bridged;
    let RelExpr::Project { input, .. } = &mut bridge_type_drift.rel else {
        unreachable!()
    };
    let RelExpr::Filter { input, .. } = input.as_mut() else {
        unreachable!()
    };
    let RelExpr::Project { output, .. } = input.as_mut() else {
        unreachable!()
    };
    output[0].nullable = !output[0].nullable;
    assert_eq!(
        lower_query_with_schema_config(&bridge_type_drift, &schema, &LoweringConfig::default(),)
            .status,
        LoweringStatus::Blocked,
        "the bridge must preserve each Aggregate output's exact type/nullability"
    );

    let mut duplicate_passthrough = baseline.clone();
    let RelExpr::Project { exprs, .. } = &mut duplicate_passthrough.rel else {
        unreachable!()
    };
    exprs[4] = scalar(ScalarAst::InputRef { index: 0 });
    assert_eq!(
        lower_query_with_schema_config(
            &duplicate_passthrough,
            &schema,
            &LoweringConfig::default(),
        )
        .status,
        LoweringStatus::Blocked,
        "a duplicate/missing Aggregate-output permutation must not use the compositional ratio lowering"
    );

    assert_eq!(
        lower_query_with_schema_config(&query(1), &schema, &LoweringConfig::default()).status,
        LoweringStatus::Blocked,
        "STDDEV and AVG over different INTEGER arguments must not use the compositional ratio lowering"
    );
}

#[test]
fn repeated_group_identifier_lineage_is_qualified_and_block_local() {
    let grouping = SourceGroupingProvenance {
        kind: "GROUP_BY".to_owned(),
        query_block_id: "12:1-12:100".to_owned(),
        source_select_node_id: "12:1-12:100".to_owned(),
        source_select_sql: "SELECT AVG(inventory0.value0) FROM inventory AS inventory0".to_owned(),
        source_group_sql: "GROUP BY inventory0.group0".to_owned(),
        group_indexes: vec![0],
        grouping_sets: vec![vec![0]],
        source_has_where: false,
        source_has_having: false,
    };
    let mut aggregate_source = source_node("inventory0.value0", "IDENTIFIER", None, Vec::new());
    aggregate_source.node_id = Some("12:40-12:58".to_owned());
    let mut input_source = source_node("inventory0.value0", "IDENTIFIER", None, Vec::new());
    input_source.node_id = Some("12:20-12:38".to_owned());
    assert!(exact_repeated_group_identifier_lineage(
        &aggregate_source,
        &input_source,
        &grouping,
    ));

    let mut cross_block = input_source.clone();
    cross_block.node_id = Some("13:20-13:38".to_owned());
    assert!(
        !exact_repeated_group_identifier_lineage(&aggregate_source, &cross_block, &grouping,),
        "equal qualified text borrowed from another query block must be rejected"
    );

    let mut other_occurrence = input_source.clone();
    other_occurrence.text = Some("inventory1.value0".to_owned());
    assert!(
        !exact_repeated_group_identifier_lineage(&aggregate_source, &other_occurrence, &grouping,),
        "a different relation occurrence cannot attest the Aggregate input"
    );

    let mut borrowed_grouping = grouping;
    borrowed_grouping.source_select_node_id = "11:1-11:100".to_owned();
    assert!(
        !exact_repeated_group_identifier_lineage(
            &aggregate_source,
            &input_source,
            &borrowed_grouping,
        ),
        "the grouping owner and selected query block must agree exactly"
    );
}

#[test]
fn repeated_group_aggregate_definition_is_exact_and_having_local() {
    let grouping = SourceGroupingProvenance {
        kind: "GROUP_BY".to_owned(),
        query_block_id: "12:1-12:100".to_owned(),
        source_select_node_id: "12:1-12:100".to_owned(),
        source_select_sql: "SELECT SUM(t.amount) FROM t GROUP BY t.key HAVING SUM(t.amount) > 0"
            .to_owned(),
        source_group_sql: "GROUP BY t.key".to_owned(),
        group_indexes: vec![0],
        grouping_sets: vec![vec![0]],
        source_has_where: false,
        source_has_having: true,
    };
    let mut aggregate = source_node(
        "SUM(t.amount)",
        "OTHER_FUNCTION",
        Some("sum"),
        vec![source_node("t.amount", "IDENTIFIER", None, Vec::new())],
    );
    aggregate.node_id = Some("12:8-12:20".to_owned());
    let mut repeated = source_node(
        "SUM(t.amount)",
        "OTHER_FUNCTION",
        Some("sum"),
        vec![source_node(
            "SUM(t.amount)",
            "OTHER_FUNCTION",
            Some("sum"),
            Vec::new(),
        )],
    );
    repeated.node_id = Some("12:60-12:72".to_owned());
    assert!(exact_repeated_group_aggregate_definition(
        &repeated, &aggregate, &grouping,
    ));

    let mut cross_block = repeated.clone();
    cross_block.node_id = Some("13:60-13:72".to_owned());
    assert!(!exact_repeated_group_aggregate_definition(
        &cross_block,
        &aggregate,
        &grouping,
    ));

    let mut borrowed_definition = repeated.clone();
    borrowed_definition.text = Some("SUM(other.amount)".to_owned());
    assert!(!exact_repeated_group_aggregate_definition(
        &borrowed_definition,
        &aggregate,
        &grouping,
    ));

    let mut no_having_owner = grouping;
    no_having_owner.source_has_having = false;
    assert!(!exact_repeated_group_aggregate_definition(
        &repeated,
        &aggregate,
        &no_having_owner,
    ));
}

#[test]
fn lowers_source_closed_numeric_coalesce_after_ir_typmod_repair() {
    fn numeric_zero() -> ScalarAst {
        ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "0".to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                }],
            }),
            ty: "NUMERIC".to_owned(),
        }
    }

    fn coalesce_source() -> ScalarSourceProvenance {
        let leaf = source_node("returns", "IDENTIFIER", None, Vec::new());
        let carrier = source_node("returns", "IDENTIFIER", None, vec![leaf]);
        source_node(
            "COALESCE(returns, 0)",
            "OTHER_FUNCTION",
            Some("coalesce"),
            vec![
                carrier.clone(),
                carrier,
                source_node("0", "LITERAL", None, Vec::new()),
            ],
        )
    }

    let parenthesized_binary = source_node(
        "(profit - COALESCE(returns, 0))",
        "MINUS",
        Some("-"),
        vec![
            source_node("profit", "IDENTIFIER", None, Vec::new()),
            coalesce_source(),
        ],
    );
    assert!(exact_source_binary_operands_match(
        &parenthesized_binary,
        AttestedSqlToken::Minus,
    ));
    let mut partial_parentheses = parenthesized_binary.clone();
    partial_parentheses.text = Some("(profit) - COALESCE(returns, 0)".to_owned());
    assert!(!exact_source_binary_operands_match(
        &partial_parentheses,
        AttestedSqlToken::Minus,
    ));

    fn query(then_index: usize) -> Query {
        let table_output = vec![
            decimal_column("returns", 10, 2),
            decimal_column("other_returns", 10, 2),
        ];
        let aggregate_output = vec![
            decimal_column_unconstrained("returns"),
            decimal_column_unconstrained("other_returns"),
        ];
        let output = vec![decimal_column("coalesced_returns", 19, 2)];
        query_for_rel(
            RelExpr::Project {
                input: Box::new(RelExpr::Aggregate {
                    input: Box::new(RelExpr::TableScan {
                        table: vec!["returns_table".to_owned()],
                        output: table_output,
                    }),
                    group_keys: Vec::new(),
                    grouping_sets: vec![Vec::new()],
                    agg_calls: (0..2)
                        .map(|index| AggregateCall {
                            raw: format!("SUM(${index})"),
                            function: "SUM".to_owned(),
                            distinct: false,
                            modifiers: AggregateModifiers::default(),
                            args: vec![scalar(ScalarAst::InputRef { index })],
                            filter: None,
                        })
                        .collect(),
                    output: aggregate_output,
                }),
                exprs: vec![scalar_with_source(
                    ScalarAst::Call {
                        operator: "CASE".to_owned(),
                        op: ScalarOp::Case,
                        args: vec![
                            ScalarAst::Call {
                                operator: "IS NOT NULL".to_owned(),
                                op: ScalarOp::IsNotNull,
                                args: vec![ScalarAst::InputRef { index: 0 }],
                            },
                            ScalarAst::InputRef { index: then_index },
                            numeric_zero(),
                        ],
                    },
                    coalesce_source(),
                )],
                correlations: Vec::new(),
                output: output.clone(),
            },
            output,
        )
    }

    let schema = Schema {
        tables: vec![Table {
            name: "returns_table".to_owned(),
            columns: vec![
                decimal_column("returns", 10, 2),
                decimal_column("other_returns", 10, 2),
            ],
            constraints: Default::default(),
        }],
    };
    let lowered = lower_query_with_schema_config(&query(0), &schema, &LoweringConfig::default());
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::Numeric
    );
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "calcite_coalesce_numeric_type_overridden" })
    );
    let module = emit_rocq_query_module(
        lowered.query_expr.as_ref().expect("lowered COALESCE"),
        lowered.query_expr.as_ref().expect("lowered COALESCE"),
    );
    assert!(module.rocq_module.contains("AttrNumeric \"returns\""));
    assert!(
        !module
            .rocq_module
            .contains("ScalarCastToNumericTypmod ScalarSourceNumeric")
    );

    let drift = lower_query_with_schema_config(&query(1), &schema, &LoweringConfig::default());
    assert_eq!(drift.status, LoweringStatus::Blocked);
    assert!(
        drift
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "numeric_coalesce_source_provenance_drift" })
    );

    let mut legacy_bigint_zero = query(0);
    let RelExpr::Project { exprs, .. } = &mut legacy_bigint_zero.rel else {
        unreachable!()
    };
    let ScalarAst::Call { args, .. } = &mut exprs[0].parsed else {
        unreachable!()
    };
    args[2] = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: "0".to_owned(),
        }),
        ty: "BIGINT".to_owned(),
    };
    let legacy_bigint_zero =
        lower_query_with_schema_config(&legacy_bigint_zero, &schema, &LoweringConfig::default());
    assert_eq!(legacy_bigint_zero.status, LoweringStatus::Blocked);
    assert!(
        legacy_bigint_zero
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.code == "numeric_coalesce_source_provenance_drift" })
    );

    fn explicit_fixed_decimal_case_query() -> Query {
        let condition_attribute = source_node("r.returns", "IDENTIFIER", None, Vec::new());
        let then_attribute = source_node("r.returns", "IDENTIFIER", None, Vec::new());
        let condition = source_node(
            "r.returns IS NOT NULL",
            "IS_NOT_NULL",
            Some("IS NOT NULL"),
            vec![condition_attribute],
        );
        let then_source = source_node(
            "CAST(r.returns AS DECIMAL(12, 2))",
            "CAST",
            Some("CAST"),
            vec![then_attribute],
        );
        let source = source_node(
            "CASE WHEN r.returns IS NOT NULL THEN CAST(r.returns AS DECIMAL(12, 2)) ELSE 0 END",
            "CASE",
            Some("CASE"),
            vec![
                condition,
                then_source,
                source_node("0", "LITERAL", None, Vec::new()),
            ],
        );
        let output = vec![decimal_column("normalized_returns", 12, 2)];
        query_for_rel(
            RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["fixed_case_table".to_owned()],
                    output: vec![decimal_column("returns", 12, 2)],
                }),
                exprs: vec![scalar_with_source(
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
                                ty: "DECIMAL(12,2)".to_owned(),
                            },
                            numeric_zero(),
                        ],
                    },
                    source,
                )],
                correlations: Vec::new(),
                output: output.clone(),
            },
            output,
        )
    }

    let fixed_case_schema = Schema {
        tables: vec![Table {
            name: "fixed_case_table".to_owned(),
            columns: vec![decimal_column("returns", 12, 2)],
            constraints: Default::default(),
        }],
    };
    let explicit_case = lower_query_with_schema_config(
        &explicit_fixed_decimal_case_query(),
        &fixed_case_schema,
        &LoweringConfig::default(),
    );
    assert_eq!(
        explicit_case.status,
        LoweringStatus::Lowered,
        "an exact source-written fixed-DECIMAL CASE is not generated COALESCE: {:#?}",
        explicit_case.diagnostics
    );
    assert_eq!(
        explicit_case.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::Numeric
    );
    assert!(
        explicit_case
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "calcite_coalesce_numeric_type_overridden")
    );

    let mut missing_case_source = explicit_fixed_decimal_case_query();
    let RelExpr::Project { exprs, .. } = &mut missing_case_source.rel else {
        unreachable!()
    };
    exprs[0].source = None;
    assert_eq!(
        lower_query_with_schema_config(
            &missing_case_source,
            &fixed_case_schema,
            &LoweringConfig::default(),
        )
        .status,
        LoweringStatus::Blocked,
        "a generated-looking CASE without exact source authority remains fail-closed"
    );

    let mut mismatched_case_source = explicit_fixed_decimal_case_query();
    let RelExpr::Project { exprs, .. } = &mut mismatched_case_source.rel else {
        unreachable!()
    };
    exprs[0].source.as_mut().unwrap().operands[0]
        .as_mut()
        .unwrap()
        .operands[0]
        .as_mut()
        .unwrap()
        .text = Some("r.other_returns".to_owned());
    assert_eq!(
        lower_query_with_schema_config(
            &mismatched_case_source,
            &fixed_case_schema,
            &LoweringConfig::default(),
        )
        .status,
        LoweringStatus::Blocked,
        "a CASE operand borrowed from another column cannot bypass COALESCE drift checking"
    );

    fn aggregate_bound_coalesce_query() -> Query {
        let mut query = query(0);
        let RelExpr::Project {
            input,
            exprs,
            output,
            ..
        } = &mut query.rel
        else {
            unreachable!()
        };
        let RelExpr::Aggregate { agg_calls, .. } = input.as_mut() else {
            unreachable!()
        };
        let sum_source = source_node(
            "SUM(returns)",
            "OTHER_FUNCTION",
            Some("sum"),
            vec![source_node("returns", "IDENTIFIER", None, Vec::new())],
        );
        agg_calls[0].modifiers.source = Some(sum_source.clone());
        agg_calls[0].modifiers.source_distinct = Some(false);

        let sum_carrier_leaf =
            source_node("SUM(returns)", "OTHER_FUNCTION", Some("sum"), Vec::new());
        let sum_carrier = source_node(
            "SUM(returns)",
            "OTHER_FUNCTION",
            Some("sum"),
            vec![sum_carrier_leaf],
        );
        exprs[0].source = Some(source_node(
            "COALESCE(SUM(returns), 0)",
            "OTHER_FUNCTION",
            Some("coalesce"),
            vec![
                sum_carrier.clone(),
                sum_carrier,
                source_node("0", "LITERAL", None, Vec::new()),
            ],
        ));
        let ScalarAst::Call { args, .. } = &mut exprs[0].parsed else {
            unreachable!()
        };
        args[1] = ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Call {
                operator: "CAST".to_owned(),
                op: ScalarOp::Cast,
                args: vec![ScalarAst::InputRef { index: 0 }],
            }),
            ty: "DECIMAL(19,4)".to_owned(),
        };
        output[0] = decimal_column("coalesced_returns", 19, 4);
        query
    }

    let aggregate_bound = aggregate_bound_coalesce_query();
    let lowered =
        lower_query_with_schema_config(&aggregate_bound, &schema, &LoweringConfig::default());
    assert_eq!(
        lowered.status,
        LoweringStatus::Lowered,
        "{:#?}",
        lowered.diagnostics
    );
    assert_eq!(
        lowered.output_signature.as_deref().unwrap()[0].ty,
        FormalAttributeType::Numeric,
        "the exact source SUM binding disproves Calcite's generated DECIMAL(19,4) carrier"
    );

    let mut borrowed_sum = aggregate_bound.clone();
    let RelExpr::Project { input, .. } = &mut borrowed_sum.rel else {
        unreachable!()
    };
    let RelExpr::Aggregate { agg_calls, .. } = input.as_mut() else {
        unreachable!()
    };
    agg_calls[0].modifiers.source.as_mut().unwrap().node_id = Some("test:borrowed-sum".to_owned());
    let borrowed_sum =
        lower_query_with_schema_config(&borrowed_sum, &schema, &LoweringConfig::default());
    assert_eq!(borrowed_sum.status, LoweringStatus::Blocked);
    assert!(
        borrowed_sum
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "numeric_coalesce_source_provenance_drift")
    );

    let mut output_typmod_drift = aggregate_bound;
    let RelExpr::Project { output, .. } = &mut output_typmod_drift.rel else {
        unreachable!()
    };
    output[0] = decimal_column("coalesced_returns", 19, 2);
    assert_eq!(
        lower_query_with_schema_config(&output_typmod_drift, &schema, &LoweringConfig::default(),)
            .status,
        LoweringStatus::Blocked,
        "the generated CASE annotation must agree exactly with Calcite's reported output typmod"
    );
}
