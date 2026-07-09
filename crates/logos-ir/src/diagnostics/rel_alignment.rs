use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::Serialize;

use crate::calcite::sort_semantics::calcite_text_sort_null_direction;
use crate::convert_file;
use crate::diagnostics::features::{ScanFailure, calcite_ir_files};
use crate::ir::{
    LogosIrFile, Query, RelExpr, SetOp, TextRelNode, TextRelNodeKind, TextRelShape, ValuesTuples,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelPlanAlignmentSummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub compared_queries: usize,
    pub aligned_queries: usize,
    pub missing_text_plan_queries: usize,
    pub mismatched_queries: usize,
    pub mismatches: Vec<RelPlanMismatchSummaryRow>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelPlanMismatchSummaryRow {
    pub mismatch: RelPlanMismatchKind,
    pub queries: usize,
    pub occurrences: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub example: Option<RelPlanMismatchExample>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelPlanMismatchExample {
    pub path: String,
    pub query_index: usize,
    pub rel_path: String,
    pub detail: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum RelPlanMismatchKind {
    MissingTextPlan,
    NodeKind,
    InputArity,
    TablePath,
    ProjectExprCount,
    ProjectExprText,
    FilterCondition,
    JoinType,
    JoinCondition,
    AggregateGroupKeys,
    AggregateGroupingSets,
    AggregateCallCount,
    SortKeyCount,
    SortNullDirection,
    SortFetch,
    SortOffset,
    SetOp,
    SetAll,
    ValuesTupleShape,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RelPlanMismatch {
    kind: RelPlanMismatchKind,
    rel_path: String,
    detail: String,
}

pub fn summarize_rel_plan_alignment(root: impl AsRef<Path>) -> RelPlanAlignmentSummary {
    let mut converted = Vec::new();
    let mut failures = Vec::new();
    let paths = calcite_ir_files(root.as_ref());

    for path in &paths {
        match convert_file(path) {
            Ok(ir) => converted.push((path.display().to_string(), ir)),
            Err(error) => failures.push(ScanFailure {
                path: path.display().to_string(),
                error: error.to_string(),
            }),
        }
    }

    summarize_converted_rel_plan_alignment(paths.len(), converted.iter(), failures)
}

fn summarize_converted_rel_plan_alignment<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = &'a (String, LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> RelPlanAlignmentSummary {
    let mut total_queries = 0usize;
    let mut compared_queries = 0usize;
    let mut aligned_queries = 0usize;
    let mut missing_text_plan_queries = 0usize;
    let mut mismatched_queries = 0usize;
    let mut mismatch_query_counts = BTreeMap::<RelPlanMismatchKind, usize>::new();
    let mut mismatch_occurrence_counts = BTreeMap::<RelPlanMismatchKind, usize>::new();
    let mut mismatch_examples = BTreeMap::<RelPlanMismatchKind, RelPlanMismatchExample>::new();

    for (path, ir) in files {
        for (query_index, query) in ir.queries.iter().enumerate() {
            total_queries += 1;
            let mismatches = align_query(query);
            if query.calcite_rel_plan.is_some() {
                compared_queries += 1;
            }
            if mismatches.is_empty() {
                aligned_queries += 1;
            } else {
                mismatched_queries += 1;
            }

            let query_mismatch_kinds: BTreeSet<_> =
                mismatches.iter().map(|mismatch| mismatch.kind).collect();
            for kind in query_mismatch_kinds {
                *mismatch_query_counts.entry(kind).or_default() += 1;
            }
            for mismatch in mismatches {
                *mismatch_occurrence_counts.entry(mismatch.kind).or_default() += 1;
                if mismatch.kind == RelPlanMismatchKind::MissingTextPlan {
                    missing_text_plan_queries += 1;
                }
                mismatch_examples
                    .entry(mismatch.kind)
                    .or_insert_with(|| RelPlanMismatchExample {
                        path: path.clone(),
                        query_index,
                        rel_path: mismatch.rel_path,
                        detail: mismatch.detail,
                    });
            }
        }
    }

    let all_mismatches: BTreeSet<_> = mismatch_query_counts
        .keys()
        .chain(mismatch_occurrence_counts.keys())
        .copied()
        .collect();
    let mismatches = all_mismatches
        .into_iter()
        .map(|mismatch| RelPlanMismatchSummaryRow {
            mismatch,
            queries: mismatch_query_counts
                .get(&mismatch)
                .copied()
                .unwrap_or_default(),
            occurrences: mismatch_occurrence_counts
                .get(&mismatch)
                .copied()
                .unwrap_or_default(),
            example: mismatch_examples.get(&mismatch).cloned(),
        })
        .collect();

    RelPlanAlignmentSummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        compared_queries,
        aligned_queries,
        missing_text_plan_queries,
        mismatched_queries,
        mismatches,
        failures,
    }
}

fn align_query(query: &Query) -> Vec<RelPlanMismatch> {
    let Some(plan) = &query.calcite_rel_plan else {
        return vec![RelPlanMismatch {
            kind: RelPlanMismatchKind::MissingTextPlan,
            rel_path: "root".to_owned(),
            detail: "query has no parsed calcite_rel_plan".to_owned(),
        }];
    };

    let mut mismatches = Vec::new();
    compare_rel_to_text_plan(&query.rel, plan, "root", &mut mismatches);
    mismatches
}

fn compare_rel_to_text_plan(
    rel: &RelExpr,
    plan: &TextRelNode,
    path: &str,
    out: &mut Vec<RelPlanMismatch>,
) {
    let rel_kind = rel_plan_kind(rel);
    let plan_kind = text_plan_kind(plan);
    if rel_kind != plan_kind {
        out.push(RelPlanMismatch {
            kind: RelPlanMismatchKind::NodeKind,
            rel_path: path.to_owned(),
            detail: format!("RelExpr kind {rel_kind:?} != text plan kind {plan_kind:?}"),
        });
        return;
    }

    compare_node_attrs(rel, plan, path, out);

    let rel_inputs = rel_children(rel);
    if rel_inputs.len() != plan.inputs.len() {
        out.push(RelPlanMismatch {
            kind: RelPlanMismatchKind::InputArity,
            rel_path: path.to_owned(),
            detail: format!(
                "RelExpr input count {} != text plan input count {}",
                rel_inputs.len(),
                plan.inputs.len()
            ),
        });
    }

    for (index, (rel_input, plan_input)) in rel_inputs.iter().zip(&plan.inputs).enumerate() {
        compare_rel_to_text_plan(rel_input, plan_input, &format!("{path}.input{index}"), out);
    }
}

fn compare_node_attrs(
    rel: &RelExpr,
    plan: &TextRelNode,
    path: &str,
    out: &mut Vec<RelPlanMismatch>,
) {
    match (rel, &plan.shape) {
        (RelExpr::TableScan { table, .. }, TextRelShape::TableScan { table: text_table }) => {
            if table != text_table {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::TablePath,
                    rel_path: path.to_owned(),
                    detail: format!("RelExpr table {table:?} != text plan table {text_table:?}"),
                });
            }
        }
        (
            RelExpr::Project { exprs, .. },
            TextRelShape::Project {
                exprs: text_exprs, ..
            },
        ) => {
            if exprs.len() != text_exprs.len() {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::ProjectExprCount,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr project expr count {} != text plan expr count {}",
                        exprs.len(),
                        text_exprs.len()
                    ),
                });
            }
            for (index, (expr, text_expr)) in exprs.iter().zip(text_exprs).enumerate() {
                if expr.raw != text_expr.expr.raw {
                    out.push(RelPlanMismatch {
                        kind: RelPlanMismatchKind::ProjectExprText,
                        rel_path: format!("{path}.project{index}"),
                        detail: format!(
                            "RelExpr project expr {:?} != text plan expr {:?}",
                            expr.raw, text_expr.expr.raw
                        ),
                    });
                }
            }
        }
        (
            RelExpr::Filter { predicate, .. },
            TextRelShape::Filter {
                condition: text_condition,
                ..
            },
        ) => {
            if text_condition
                .as_deref()
                .is_none_or(|text_condition| text_condition.raw != predicate.raw)
            {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::FilterCondition,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr filter condition {:?} != text plan condition {:?}",
                        predicate.raw,
                        text_condition.as_deref().map(|expr| expr.raw.as_str())
                    ),
                });
            }
        }
        (
            RelExpr::Join {
                join_type,
                condition,
                ..
            },
            TextRelShape::Join {
                join_type: text_join_type,
                condition: text_condition,
            },
        ) => {
            if Some(*join_type) != *text_join_type {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::JoinType,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr join type {join_type:?} != text plan join type {text_join_type:?}"
                    ),
                });
            }
            if text_condition
                .as_deref()
                .is_none_or(|text_condition| text_condition.raw != condition.raw)
            {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::JoinCondition,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr join condition {:?} != text plan condition {:?}",
                        condition.raw,
                        text_condition.as_deref().map(|expr| expr.raw.as_str())
                    ),
                });
            }
        }
        (
            RelExpr::Aggregate {
                group_keys,
                grouping_sets,
                agg_calls,
                ..
            },
            TextRelShape::Aggregate {
                group_keys: text_group_keys,
                grouping_sets: text_grouping_sets,
                agg_calls: text_agg_calls,
                ..
            },
        ) => {
            if Some(group_keys.as_slice()) != text_group_keys.as_deref() {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::AggregateGroupKeys,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr group keys {group_keys:?} != text plan group keys {text_group_keys:?}"
                    ),
                });
            }
            let effective_text_grouping_sets = text_grouping_sets
                .clone()
                .or_else(|| text_group_keys.clone().map(|group_keys| vec![group_keys]));
            if grouping_sets.as_ref() != effective_text_grouping_sets.as_ref() {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::AggregateGroupingSets,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr grouping sets {grouping_sets:?} != text plan grouping sets {effective_text_grouping_sets:?}"
                    ),
                });
            }
            if agg_calls.len() != text_agg_calls.len() {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::AggregateCallCount,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr aggregate call count {} != text plan call count {}",
                        agg_calls.len(),
                        text_agg_calls.len()
                    ),
                });
            }
        }
        (
            RelExpr::Sort {
                collation,
                fetch,
                offset,
                ..
            },
            TextRelShape::Sort {
                sort_keys,
                fetch: text_fetch,
                offset: text_offset,
            },
        ) => {
            if collation.len() != sort_keys.len() {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::SortKeyCount,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr sort key count {} != text plan key count {}",
                        collation.len(),
                        sort_keys.len()
                    ),
                });
            }
            for (index, (key, text_key)) in collation.iter().zip(sort_keys).enumerate() {
                let text_null_direction =
                    calcite_text_sort_null_direction(text_key.direction.as_deref(), key.direction);
                if key.null_direction != text_null_direction {
                    out.push(RelPlanMismatch {
                        kind: RelPlanMismatchKind::SortNullDirection,
                        rel_path: format!("{path}.sort{index}"),
                        detail: format!(
                            "RelExpr null direction {:?} != text plan null direction {:?}",
                            key.null_direction, text_null_direction
                        ),
                    });
                }
            }
            compare_optional_scalar_text(
                fetch.as_ref().map(|expr| expr.raw.as_str()),
                text_fetch.as_deref().map(|expr| expr.raw.as_str()),
                RelPlanMismatchKind::SortFetch,
                path,
                "fetch",
                out,
            );
            compare_optional_scalar_text(
                offset.as_ref().map(|expr| expr.raw.as_str()),
                text_offset.as_deref().map(|expr| expr.raw.as_str()),
                RelPlanMismatchKind::SortOffset,
                path,
                "offset",
                out,
            );
        }
        (RelExpr::Set { op, all, .. }, TextRelShape::Set { all: text_all }) => {
            let text_op = match plan.kind {
                TextRelNodeKind::Union => Some(SetOp::Union),
                TextRelNodeKind::Intersect => Some(SetOp::Intersect),
                TextRelNodeKind::Minus => Some(SetOp::Except),
                _ => None,
            };
            if Some(*op) != text_op {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::SetOp,
                    rel_path: path.to_owned(),
                    detail: format!("RelExpr set op {op:?} != text plan set op {text_op:?}"),
                });
            }
            if Some(*all) != *text_all {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::SetAll,
                    rel_path: path.to_owned(),
                    detail: format!("RelExpr all {all:?} != text plan all {text_all:?}"),
                });
            }
        }
        (
            RelExpr::Values {
                tuples: ValuesTuples::Rows { rows },
                ..
            },
            TextRelShape::Values {
                tuples: Some(text_rows),
            },
        ) => {
            if rows.len() != text_rows.len()
                || rows
                    .iter()
                    .zip(text_rows)
                    .any(|(row, text_row)| row.len() != text_row.len())
            {
                out.push(RelPlanMismatch {
                    kind: RelPlanMismatchKind::ValuesTupleShape,
                    rel_path: path.to_owned(),
                    detail: format!(
                        "RelExpr values row shape {:?} != text plan row shape {:?}",
                        rows.iter().map(Vec::len).collect::<Vec<_>>(),
                        text_rows.iter().map(Vec::len).collect::<Vec<_>>()
                    ),
                });
            }
        }
        _ => {}
    }
}

fn compare_optional_scalar_text(
    rel: Option<&str>,
    text: Option<&str>,
    kind: RelPlanMismatchKind,
    path: &str,
    label: &str,
    out: &mut Vec<RelPlanMismatch>,
) {
    if rel != text {
        out.push(RelPlanMismatch {
            kind,
            rel_path: path.to_owned(),
            detail: format!("RelExpr {label} {rel:?} != text plan {label} {text:?}"),
        });
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RelPlanNodeKind {
    TableScan,
    Project,
    Filter,
    Join,
    Aggregate,
    Sort,
    Set,
    Values,
    Other,
}

fn rel_plan_kind(rel: &RelExpr) -> RelPlanNodeKind {
    match rel {
        RelExpr::TableScan { .. } => RelPlanNodeKind::TableScan,
        RelExpr::Project { .. } => RelPlanNodeKind::Project,
        RelExpr::Filter { .. } => RelPlanNodeKind::Filter,
        RelExpr::Join { .. } => RelPlanNodeKind::Join,
        RelExpr::Aggregate { .. } => RelPlanNodeKind::Aggregate,
        RelExpr::Sort { .. } => RelPlanNodeKind::Sort,
        RelExpr::Set { .. } => RelPlanNodeKind::Set,
        RelExpr::Values { .. } => RelPlanNodeKind::Values,
    }
}

fn text_plan_kind(plan: &TextRelNode) -> RelPlanNodeKind {
    match plan.kind {
        TextRelNodeKind::TableScan => RelPlanNodeKind::TableScan,
        TextRelNodeKind::Project => RelPlanNodeKind::Project,
        TextRelNodeKind::Filter => RelPlanNodeKind::Filter,
        TextRelNodeKind::Join => RelPlanNodeKind::Join,
        TextRelNodeKind::Aggregate => RelPlanNodeKind::Aggregate,
        TextRelNodeKind::Sort => RelPlanNodeKind::Sort,
        TextRelNodeKind::Union | TextRelNodeKind::Intersect | TextRelNodeKind::Minus => {
            RelPlanNodeKind::Set
        }
        TextRelNodeKind::Values => RelPlanNodeKind::Values,
        TextRelNodeKind::Other { .. } => RelPlanNodeKind::Other,
    }
}

fn rel_children(rel: &RelExpr) -> Vec<&RelExpr> {
    match rel {
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => Vec::new(),
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::Aggregate { input, .. }
        | RelExpr::Sort { input, .. } => vec![input.as_ref()],
        RelExpr::Join { left, right, .. } => vec![left.as_ref(), right.as_ref()],
        RelExpr::Set { inputs, .. } => inputs.iter().collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::scalar::calcite_scalar;
    use crate::calcite::text_plan::parse_calcite_text_plan;
    use crate::ir::{Column, Feature, ScalarExpr, SqlType};

    fn column(name: &str) -> Column {
        Column {
            name: name.to_owned(),
            ty: SqlType::Integer,
            nullable: true,
            precision: None,
        }
    }

    fn scalar(raw: &str) -> ScalarExpr {
        calcite_scalar(raw)
    }

    #[test]
    fn aligns_matching_project_filter_scan() {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::Filter {
                    input: Box::new(RelExpr::TableScan {
                        table: vec!["EMP".to_owned()],
                        output: vec![column("EMPNO")],
                    }),
                    predicate: scalar("<($0, 20)"),
                    correlations: Vec::new(),
                    output: vec![column("EMPNO")],
                }),
                exprs: vec![scalar("$0")],
                correlations: Vec::new(),
                output: vec![column("EMPNO")],
            },
            output: vec![column("EMPNO")],
            features: vec![Feature::Projection],
            calcite_rel_text: Some(
                "LogicalProject(EMPNO=[$0])\n  LogicalFilter(condition=[<($0, 20)])\n    LogicalTableScan(table=[[EMP]])"
                    .to_owned(),
            ),
            calcite_rel_plan: parse_calcite_text_plan(
                "LogicalProject(EMPNO=[$0])\n  LogicalFilter(condition=[<($0, 20)])\n    LogicalTableScan(table=[[EMP]])",
            ),
        };

        assert!(align_query(&query).is_empty());
    }

    #[test]
    fn reports_project_expression_mismatch() {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["EMP".to_owned()],
                    output: vec![column("EMPNO")],
                }),
                exprs: vec![scalar("$1")],
                correlations: Vec::new(),
                output: vec![column("EMPNO")],
            },
            output: vec![column("EMPNO")],
            features: vec![Feature::Projection],
            calcite_rel_text: Some(
                "LogicalProject(EMPNO=[$0])\n  LogicalTableScan(table=[[EMP]])".to_owned(),
            ),
            calcite_rel_plan: parse_calcite_text_plan(
                "LogicalProject(EMPNO=[$0])\n  LogicalTableScan(table=[[EMP]])",
            ),
        };

        let mismatches = align_query(&query);
        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].kind, RelPlanMismatchKind::ProjectExprText);
    }
}
