use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::Serialize;

use crate::convert_file;
use crate::diagnostics::features::{ScanFailure, calcite_ir_files};
use crate::ir::{
    LogosIrFile, Query, RelExpr, ScalarAst, ScalarExpr, TextRelNode, TextRelShape, ValuesTuples,
};
use crate::semantic::walk::query_scalars;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelShapeSummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub total_rel_nodes: usize,
    pub rel_nodes: Vec<RelNodeSummaryRow>,
    pub markers: Vec<RelMarkerSummaryRow>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelNodeSummaryRow {
    pub node: RelNodeKind,
    pub files: usize,
    pub queries: usize,
    pub occurrences: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelMarkerSummaryRow {
    pub marker: RelStructuralMarker,
    pub files: usize,
    pub queries: usize,
    pub occurrences: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub example: Option<RelMarkerExample>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RelMarkerExample {
    pub path: String,
    pub query_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum RelNodeKind {
    TableScan,
    Project,
    Filter,
    Join,
    Aggregate,
    Sort,
    Set,
    Values,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum RelStructuralMarker {
    AggregateGroupingSetsUnavailable,
    AggregateGroupingSetsHydrated,
    ValuesTuplesUnavailable,
    ValuesTuplesHydrated,
    SortOrderSensitive,
    SortNullDirectionHydrated,
    SortNullDirectionMissing,
    QueryRelPlanParsed,
    QueryRelPlanUnparsed,
    QueryRelPlanShapeKnown,
    QueryRelPlanShapeUnknown,
    QueryRelValuesTuplesParsed,
    QueryRelValuesTuplesMissing,
    ScalarWindowStructured,
    ScalarWindowTextParsed,
    ScalarWindowParsed,
    ScalarEmbeddedRelStructured,
    ScalarSarg,
    ScalarSargParsed,
}

pub fn summarize_rel_shapes(root: impl AsRef<Path>) -> RelShapeSummary {
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

    summarize_converted_rel_shapes(paths.len(), converted.iter(), failures)
}

pub fn query_rel_structural_markers(query: &Query) -> Vec<RelStructuralMarker> {
    let mut markers = Vec::new();
    collect_rel_markers(query, &mut markers);
    markers
}

fn summarize_converted_rel_shapes<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = &'a (String, LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> RelShapeSummary {
    let mut node_file_counts = BTreeMap::<RelNodeKind, usize>::new();
    let mut node_query_counts = BTreeMap::<RelNodeKind, usize>::new();
    let mut node_occurrence_counts = BTreeMap::<RelNodeKind, usize>::new();
    let mut marker_file_counts = BTreeMap::<RelStructuralMarker, usize>::new();
    let mut marker_query_counts = BTreeMap::<RelStructuralMarker, usize>::new();
    let mut marker_occurrence_counts = BTreeMap::<RelStructuralMarker, usize>::new();
    let mut marker_examples = BTreeMap::<RelStructuralMarker, RelMarkerExample>::new();
    let mut total_queries = 0usize;
    let mut total_rel_nodes = 0usize;

    for (path, ir) in files {
        let mut file_nodes = BTreeSet::new();
        let mut file_markers = BTreeSet::new();

        for (query_index, query) in ir.queries.iter().enumerate() {
            total_queries += 1;
            let mut query_nodes = Vec::new();
            collect_rel_node_kinds(&query.rel, &mut query_nodes);
            total_rel_nodes += query_nodes.len();
            let query_node_set: BTreeSet<_> = query_nodes.iter().copied().collect();
            for node in &query_node_set {
                *node_query_counts.entry(*node).or_default() += 1;
            }
            for node in query_nodes {
                *node_occurrence_counts.entry(node).or_default() += 1;
            }
            file_nodes.extend(query_node_set);

            let mut query_markers = Vec::new();
            collect_rel_markers(query, &mut query_markers);
            let query_marker_set: BTreeSet<_> = query_markers.iter().copied().collect();
            for marker in &query_marker_set {
                *marker_query_counts.entry(*marker).or_default() += 1;
                marker_examples
                    .entry(*marker)
                    .or_insert_with(|| RelMarkerExample {
                        path: path.clone(),
                        query_index,
                    });
            }
            for marker in query_markers {
                *marker_occurrence_counts.entry(marker).or_default() += 1;
            }
            file_markers.extend(query_marker_set);
        }

        for node in file_nodes {
            *node_file_counts.entry(node).or_default() += 1;
        }
        for marker in file_markers {
            *marker_file_counts.entry(marker).or_default() += 1;
        }
    }

    let all_nodes: BTreeSet<_> = node_file_counts
        .keys()
        .chain(node_query_counts.keys())
        .chain(node_occurrence_counts.keys())
        .copied()
        .collect();
    let rel_nodes = all_nodes
        .into_iter()
        .map(|node| RelNodeSummaryRow {
            node,
            files: node_file_counts.get(&node).copied().unwrap_or_default(),
            queries: node_query_counts.get(&node).copied().unwrap_or_default(),
            occurrences: node_occurrence_counts
                .get(&node)
                .copied()
                .unwrap_or_default(),
        })
        .collect();

    let all_markers: BTreeSet<_> = marker_file_counts
        .keys()
        .chain(marker_query_counts.keys())
        .chain(marker_occurrence_counts.keys())
        .copied()
        .collect();
    let markers = all_markers
        .into_iter()
        .map(|marker| RelMarkerSummaryRow {
            marker,
            files: marker_file_counts.get(&marker).copied().unwrap_or_default(),
            queries: marker_query_counts
                .get(&marker)
                .copied()
                .unwrap_or_default(),
            occurrences: marker_occurrence_counts
                .get(&marker)
                .copied()
                .unwrap_or_default(),
            example: marker_examples.get(&marker).cloned(),
        })
        .collect();

    RelShapeSummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        total_rel_nodes,
        rel_nodes,
        markers,
        failures,
    }
}

fn collect_rel_node_kinds(rel: &RelExpr, out: &mut Vec<RelNodeKind>) {
    out.push(rel_node_kind(rel));
    match rel {
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::Aggregate { input, .. }
        | RelExpr::Sort { input, .. } => collect_rel_node_kinds(input, out),
        RelExpr::Join { left, right, .. } => {
            collect_rel_node_kinds(left, out);
            collect_rel_node_kinds(right, out);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_rel_node_kinds(input, out);
            }
        }
    }
}

fn rel_node_kind(rel: &RelExpr) -> RelNodeKind {
    match rel {
        RelExpr::TableScan { .. } => RelNodeKind::TableScan,
        RelExpr::Project { .. } => RelNodeKind::Project,
        RelExpr::Filter { .. } => RelNodeKind::Filter,
        RelExpr::Join { .. } => RelNodeKind::Join,
        RelExpr::Aggregate { .. } => RelNodeKind::Aggregate,
        RelExpr::Sort { .. } => RelNodeKind::Sort,
        RelExpr::Set { .. } => RelNodeKind::Set,
        RelExpr::Values { .. } => RelNodeKind::Values,
    }
}

fn collect_rel_markers(query: &Query, out: &mut Vec<RelStructuralMarker>) {
    collect_rel_structural_markers(&query.rel, out);
    collect_query_text_plan_markers(query, out);
    for scalar in query_scalars(query) {
        collect_scalar_structural_markers(scalar, out);
    }
}

fn collect_query_text_plan_markers(query: &Query, out: &mut Vec<RelStructuralMarker>) {
    match (&query.calcite_rel_text, &query.calcite_rel_plan) {
        (Some(_), Some(plan)) => {
            out.push(RelStructuralMarker::QueryRelPlanParsed);
            if text_rel_plan_has_only_known_shapes(plan) {
                out.push(RelStructuralMarker::QueryRelPlanShapeKnown);
            } else {
                out.push(RelStructuralMarker::QueryRelPlanShapeUnknown);
            }
            collect_text_rel_value_markers(plan, out);
        }
        (Some(_), None) => out.push(RelStructuralMarker::QueryRelPlanUnparsed),
        (None, _) => {}
    }
}

fn collect_rel_structural_markers(rel: &RelExpr, out: &mut Vec<RelStructuralMarker>) {
    match rel {
        RelExpr::TableScan { .. } => {}
        RelExpr::Project { input, .. } | RelExpr::Filter { input, .. } => {
            collect_rel_structural_markers(input, out);
        }
        RelExpr::Join { left, right, .. } => {
            collect_rel_structural_markers(left, out);
            collect_rel_structural_markers(right, out);
        }
        RelExpr::Aggregate {
            input,
            grouping_sets,
            ..
        } => {
            match grouping_sets {
                None => out.push(RelStructuralMarker::AggregateGroupingSetsUnavailable),
                Some(_) => out.push(RelStructuralMarker::AggregateGroupingSetsHydrated),
            }
            collect_rel_structural_markers(input, out);
        }
        RelExpr::Sort {
            input,
            collation,
            fetch,
            offset,
            ..
        } => {
            if !collation.is_empty() || fetch.is_some() || offset.is_some() {
                out.push(RelStructuralMarker::SortOrderSensitive);
            }
            for key in collation {
                if key.null_direction.is_some() {
                    out.push(RelStructuralMarker::SortNullDirectionHydrated);
                } else {
                    out.push(RelStructuralMarker::SortNullDirectionMissing);
                }
            }
            collect_rel_structural_markers(input, out);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_rel_structural_markers(input, out);
            }
        }
        RelExpr::Values { tuples, .. } => match tuples {
            ValuesTuples::UnavailableFromCalcite => {
                out.push(RelStructuralMarker::ValuesTuplesUnavailable);
            }
            ValuesTuples::Rows { .. } => {
                out.push(RelStructuralMarker::ValuesTuplesHydrated);
            }
        },
    }
}

fn collect_scalar_structural_markers(scalar: &ScalarExpr, out: &mut Vec<RelStructuralMarker>) {
    collect_scalar_ast_markers(&scalar.parsed, out);
}

fn collect_scalar_ast_markers(ast: &ScalarAst, out: &mut Vec<RelStructuralMarker>) {
    match ast {
        ScalarAst::Window { structured, .. } => {
            if *structured {
                out.push(RelStructuralMarker::ScalarWindowStructured);
            } else {
                out.push(RelStructuralMarker::ScalarWindowTextParsed);
            }
            out.push(RelStructuralMarker::ScalarWindowParsed);
        }
        ScalarAst::RelSubquery { .. } => {
            out.push(RelStructuralMarker::ScalarEmbeddedRelStructured);
        }
        ScalarAst::Sarg { .. } => {
            out.push(RelStructuralMarker::ScalarSarg);
            out.push(RelStructuralMarker::ScalarSargParsed);
        }
        ScalarAst::Call { args, .. } => {
            for arg in args {
                collect_scalar_ast_markers(arg, out);
            }
        }
        ScalarAst::TypeAnnotation { expr, .. } => collect_scalar_ast_markers(expr, out),
        ScalarAst::InputRef { .. } | ScalarAst::Literal { .. } | ScalarAst::Flag { .. } => {}
    }
}

fn text_rel_plan_has_only_known_shapes(plan: &TextRelNode) -> bool {
    !matches!(plan.shape, TextRelShape::Other)
        && plan.inputs.iter().all(text_rel_plan_has_only_known_shapes)
}

fn collect_text_rel_value_markers(plan: &TextRelNode, out: &mut Vec<RelStructuralMarker>) {
    if let TextRelShape::Values { tuples } = &plan.shape {
        if tuples.is_some() {
            out.push(RelStructuralMarker::QueryRelValuesTuplesParsed);
        } else {
            out.push(RelStructuralMarker::QueryRelValuesTuplesMissing);
        }
    }
    for input in &plan.inputs {
        collect_text_rel_value_markers(input, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::scalar::calcite_scalar;
    use crate::ir::{Column, SetOp, SqlType};

    #[test]
    fn summarizes_rel_nodes_and_structural_markers() {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::Aggregate {
                    input: Box::new(RelExpr::Values {
                        tuples: ValuesTuples::UnavailableFromCalcite,
                        output: vec![column("v")],
                    }),
                    group_keys: vec![0],
                    grouping_sets: None,
                    agg_calls: Vec::new(),
                    output: vec![column("v")],
                }),
                exprs: vec![calcite_scalar("ROW_NUMBER() OVER ()")],
                output: vec![column("v")],
            },
            output: vec![column("v")],
            features: Vec::new(),
            calcite_rel_text: None,
            calcite_rel_plan: None,
        };
        let ir = LogosIrFile {
            schema: crate::ir::Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_rel_shapes(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert_eq!(summary.failed_files, 0);
        assert_eq!(summary.total_queries, 1);
        assert_eq!(summary.total_rel_nodes, 3);
        assert_eq!(
            node_row(&summary, RelNodeKind::Project)
                .unwrap()
                .occurrences,
            1
        );
        assert_eq!(
            marker_row(&summary, RelStructuralMarker::ValuesTuplesUnavailable)
                .unwrap()
                .occurrences,
            1
        );
        assert_eq!(
            marker_row(
                &summary,
                RelStructuralMarker::AggregateGroupingSetsUnavailable
            )
            .unwrap()
            .occurrences,
            1
        );
        assert_eq!(
            marker_row(&summary, RelStructuralMarker::ScalarWindowTextParsed)
                .unwrap()
                .occurrences,
            1
        );
    }

    #[test]
    fn counts_set_nodes() {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Set {
                op: SetOp::Union,
                all: true,
                inputs: vec![
                    RelExpr::TableScan {
                        table: vec!["t".to_owned()],
                        output: Vec::new(),
                    },
                    RelExpr::TableScan {
                        table: vec!["u".to_owned()],
                        output: Vec::new(),
                    },
                ],
                output: Vec::new(),
            },
            output: Vec::new(),
            features: Vec::new(),
            calcite_rel_text: None,
            calcite_rel_plan: None,
        };
        let ir = LogosIrFile {
            schema: crate::ir::Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_rel_shapes(
            1,
            [("case/after.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert_eq!(node_row(&summary, RelNodeKind::Set).unwrap().occurrences, 1);
        assert_eq!(
            node_row(&summary, RelNodeKind::TableScan)
                .unwrap()
                .occurrences,
            2
        );
    }

    fn column(name: &str) -> Column {
        Column {
            name: name.to_owned(),
            ty: SqlType::Integer,
            nullable: true,
            precision: None,
        }
    }

    fn node_row(summary: &RelShapeSummary, node: RelNodeKind) -> Option<&RelNodeSummaryRow> {
        summary.rel_nodes.iter().find(|row| row.node == node)
    }

    fn marker_row(
        summary: &RelShapeSummary,
        marker: RelStructuralMarker,
    ) -> Option<&RelMarkerSummaryRow> {
        summary.markers.iter().find(|row| row.marker == marker)
    }
}
