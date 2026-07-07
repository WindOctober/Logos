use super::*;
use logos_ir::ir::ScalarOp;

use logos_ir::ir::{
    Column, Feature, JoinType, Query, RelExpr, ScalarAst, ScalarClass, ScalarExpr, Schema, SetOp,
    SqlType, Table, ValuesTuples,
};

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
            ],
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(
        lowered.schema.as_ref().unwrap().tables[0].attributes.len(),
        4
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
                .contains("Attr_Z \"EMPNO\" :: Attr_string \"ENAME\" :: Attr_bool \"SLACKER\" :: Attr_date \"HIREDATE\" :: nil")
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
        "schema-only lowering should not warn for supported DATE columns"
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

    let module = emit_rocq_query_module(&source, &target);

    assert!(
        module
            .rocq_module
            .starts_with("From Logos Require Import FormalSQL.TNullSyntax.")
    );
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
        lowered.query.as_ref().expect("left join should lower"),
        lowered.query.as_ref().expect("left join should lower"),
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
        semi_lowered.query.as_ref().expect("semi join should lower"),
        semi_lowered.query.as_ref().expect("semi join should lower"),
    );
    let anti_module = emit_rocq_query_module(
        anti_lowered.query.as_ref().expect("anti join should lower"),
        anti_lowered.query.as_ref().expect("anti join should lower"),
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
    let module = emit_rocq_proof_module();

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
fn rejects_sort_because_formal_sql_is_bag_valued() {
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

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert_eq!(lowered.query, None);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "sort_limit_offset_not_supported")
    );
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
