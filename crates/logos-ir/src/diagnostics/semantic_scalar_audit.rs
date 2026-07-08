use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::Serialize;

use crate::convert_file;
use crate::diagnostics::features::{ScanFailure, calcite_ir_files};
use crate::ir::{LogosIrFile, ScalarAst, ScalarExpr, ScalarOp};
use crate::semantic::scalar::{
    SemanticScalarClass, SemanticScalarUnsupported, classify_semantic_scalar,
};
use crate::semantic::walk::query_scalars;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticScalarSummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub total_scalar_exprs: usize,
    pub parsed_scalar_exprs: usize,
    pub unparsed_scalar_exprs: usize,
    pub core_value_exprs: usize,
    pub core_predicate_exprs: usize,
    pub unsupported_exprs: usize,
    pub unsupported_reasons: Vec<SemanticScalarUnsupportedRow>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticScalarUnsupportedRow {
    pub reason: SemanticScalarUnsupported,
    pub files: usize,
    pub queries: usize,
    pub expressions: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticScalarExamples {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub total_scalar_exprs: usize,
    pub unparsed_scalar_exprs: usize,
    pub unsupported_exprs: usize,
    pub examples: Vec<SemanticScalarExample>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticScalarExample {
    pub path: String,
    pub query_index: usize,
    pub scalar_index: usize,
    pub reason: SemanticScalarExampleReason,
    pub raw: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum SemanticScalarExampleReason {
    Unparsed,
    Unsupported { reason: SemanticScalarUnsupported },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticScalarExampleFilter {
    All,
    Unparsed,
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticScalarExampleGroups {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub total_scalar_exprs: usize,
    pub unparsed_scalar_exprs: usize,
    pub unsupported_exprs: usize,
    pub groups: Vec<SemanticScalarExampleGroup>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SemanticScalarExampleGroup {
    pub reason: SemanticScalarExampleReason,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_op: Option<ScalarOp>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub first_failing_op: Option<ScalarOp>,
    pub expressions: usize,
    pub example: SemanticScalarExample,
}

pub fn summarize_semantic_scalars(root: impl AsRef<Path>) -> SemanticScalarSummary {
    let mut converted = Vec::new();
    let mut failures = Vec::new();
    let paths = calcite_ir_files(root.as_ref());

    for path in &paths {
        match convert_file(path) {
            Ok(ir) => converted.push((path.clone(), ir)),
            Err(error) => failures.push(ScanFailure {
                path: path.display().to_string(),
                error: error.to_string(),
            }),
        }
    }

    summarize_converted_semantic_scalars(
        paths.len(),
        converted.iter().map(|(path, ir)| (path.as_path(), ir)),
        failures,
    )
}

pub fn semantic_scalar_examples(
    root: impl AsRef<Path>,
    limit: usize,
    filter: SemanticScalarExampleFilter,
) -> SemanticScalarExamples {
    let mut converted = Vec::new();
    let mut failures = Vec::new();
    let paths = calcite_ir_files(root.as_ref());

    for path in &paths {
        match convert_file(path) {
            Ok(ir) => converted.push((path.clone(), ir)),
            Err(error) => failures.push(ScanFailure {
                path: path.display().to_string(),
                error: error.to_string(),
            }),
        }
    }

    converted_semantic_scalar_examples(
        paths.len(),
        converted.iter().map(|(path, ir)| (path.as_path(), ir)),
        failures,
        limit,
        filter,
    )
}

pub fn semantic_scalar_example_groups(
    root: impl AsRef<Path>,
    limit: usize,
    filter: SemanticScalarExampleFilter,
) -> SemanticScalarExampleGroups {
    let mut converted = Vec::new();
    let mut failures = Vec::new();
    let paths = calcite_ir_files(root.as_ref());

    for path in &paths {
        match convert_file(path) {
            Ok(ir) => converted.push((path.clone(), ir)),
            Err(error) => failures.push(ScanFailure {
                path: path.display().to_string(),
                error: error.to_string(),
            }),
        }
    }

    converted_semantic_scalar_example_groups(
        paths.len(),
        converted.iter().map(|(path, ir)| (path.as_path(), ir)),
        failures,
        limit,
        filter,
    )
}

fn summarize_converted_semantic_scalars<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = (&'a Path, &'a LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> SemanticScalarSummary {
    let mut total_queries = 0usize;
    let mut total_scalar_exprs = 0usize;
    let mut parsed_scalar_exprs = 0usize;
    let unparsed_scalar_exprs = 0usize;
    let mut core_value_exprs = 0usize;
    let mut core_predicate_exprs = 0usize;
    let mut unsupported_exprs = 0usize;
    let mut reason_file_counts = BTreeMap::<SemanticScalarUnsupported, usize>::new();
    let mut reason_query_counts = BTreeMap::<SemanticScalarUnsupported, usize>::new();
    let mut reason_expr_counts = BTreeMap::<SemanticScalarUnsupported, usize>::new();

    for (_, ir) in files {
        let mut file_reasons = BTreeSet::new();
        for query in &ir.queries {
            total_queries += 1;
            let mut query_reasons = BTreeSet::new();
            for scalar in query_scalars(query) {
                total_scalar_exprs += 1;
                parsed_scalar_exprs += 1;
                match classify_semantic_scalar(&scalar.parsed) {
                    SemanticScalarClass::CoreValue => core_value_exprs += 1,
                    SemanticScalarClass::CorePredicate => core_predicate_exprs += 1,
                    SemanticScalarClass::Unsupported { reason } => {
                        unsupported_exprs += 1;
                        *reason_expr_counts.entry(reason).or_default() += 1;
                        query_reasons.insert(reason);
                        file_reasons.insert(reason);
                    }
                }
            }
            for reason in query_reasons {
                *reason_query_counts.entry(reason).or_default() += 1;
            }
        }
        for reason in file_reasons {
            *reason_file_counts.entry(reason).or_default() += 1;
        }
    }

    let all_reasons: BTreeSet<_> = reason_file_counts
        .keys()
        .chain(reason_query_counts.keys())
        .chain(reason_expr_counts.keys())
        .copied()
        .collect();
    let unsupported_reasons = all_reasons
        .into_iter()
        .map(|reason| SemanticScalarUnsupportedRow {
            reason,
            files: reason_file_counts.get(&reason).copied().unwrap_or_default(),
            queries: reason_query_counts
                .get(&reason)
                .copied()
                .unwrap_or_default(),
            expressions: reason_expr_counts.get(&reason).copied().unwrap_or_default(),
        })
        .collect();

    SemanticScalarSummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        total_scalar_exprs,
        parsed_scalar_exprs,
        unparsed_scalar_exprs,
        core_value_exprs,
        core_predicate_exprs,
        unsupported_exprs,
        unsupported_reasons,
        failures,
    }
}

fn converted_semantic_scalar_examples<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = (&'a Path, &'a LogosIrFile)>,
    failures: Vec<ScanFailure>,
    limit: usize,
    filter: SemanticScalarExampleFilter,
) -> SemanticScalarExamples {
    let mut total_queries = 0usize;
    let mut total_scalar_exprs = 0usize;
    let unparsed_scalar_exprs = 0usize;
    let mut unsupported_exprs = 0usize;
    let mut examples = Vec::new();

    for (path, ir) in files {
        for (query_index, query) in ir.queries.iter().enumerate() {
            total_queries += 1;
            for (scalar_index, scalar) in query_scalars(query).into_iter().enumerate() {
                total_scalar_exprs += 1;
                let reason = match classify_semantic_scalar(&scalar.parsed) {
                    SemanticScalarClass::CoreValue | SemanticScalarClass::CorePredicate => {
                        continue;
                    }
                    SemanticScalarClass::Unsupported { reason } => {
                        unsupported_exprs += 1;
                        SemanticScalarExampleReason::Unsupported { reason }
                    }
                };

                if examples.len() < limit && filter.matches(&reason) {
                    examples.push(SemanticScalarExample {
                        path: path.display().to_string(),
                        query_index,
                        scalar_index,
                        reason,
                        raw: scalar.raw.clone(),
                    });
                }
            }
        }
    }

    SemanticScalarExamples {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        total_scalar_exprs,
        unparsed_scalar_exprs,
        unsupported_exprs,
        examples,
        failures,
    }
}

fn converted_semantic_scalar_example_groups<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = (&'a Path, &'a LogosIrFile)>,
    failures: Vec<ScanFailure>,
    limit: usize,
    filter: SemanticScalarExampleFilter,
) -> SemanticScalarExampleGroups {
    let mut total_queries = 0usize;
    let mut total_scalar_exprs = 0usize;
    let unparsed_scalar_exprs = 0usize;
    let mut unsupported_exprs = 0usize;
    let mut groups = BTreeMap::<
        (SemanticScalarExampleReason, Option<ScalarOp>),
        SemanticScalarExampleGroup,
    >::new();

    for (path, ir) in files {
        for (query_index, query) in ir.queries.iter().enumerate() {
            total_queries += 1;
            for (scalar_index, scalar) in query_scalars(query).into_iter().enumerate() {
                total_scalar_exprs += 1;
                let Some(reason) = scalar_gap_reason(scalar) else {
                    continue;
                };
                unsupported_exprs += 1;
                if !filter.matches(&reason) {
                    continue;
                }

                let root_op = root_scalar_op(scalar);
                let first_failing_op = first_failing_op(scalar);
                let key = (reason.clone(), first_failing_op.clone());
                groups
                    .entry(key)
                    .and_modify(|group| group.expressions += 1)
                    .or_insert_with(|| SemanticScalarExampleGroup {
                        reason: reason.clone(),
                        root_op,
                        first_failing_op,
                        expressions: 1,
                        example: SemanticScalarExample {
                            path: path.display().to_string(),
                            query_index,
                            scalar_index,
                            reason,
                            raw: scalar.raw.clone(),
                        },
                    });
            }
        }
    }

    SemanticScalarExampleGroups {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        total_scalar_exprs,
        unparsed_scalar_exprs,
        unsupported_exprs,
        groups: groups.into_values().take(limit).collect(),
        failures,
    }
}

fn scalar_gap_reason(scalar: &ScalarExpr) -> Option<SemanticScalarExampleReason> {
    match classify_semantic_scalar(&scalar.parsed) {
        SemanticScalarClass::CoreValue | SemanticScalarClass::CorePredicate => None,
        SemanticScalarClass::Unsupported { reason } => {
            Some(SemanticScalarExampleReason::Unsupported { reason })
        }
    }
}

fn root_scalar_op(scalar: &ScalarExpr) -> Option<ScalarOp> {
    root_ast_op(&scalar.parsed)
}

fn first_failing_op(scalar: &ScalarExpr) -> Option<ScalarOp> {
    first_failing_ast_op(&scalar.parsed)
}

fn root_ast_op(ast: &ScalarAst) -> Option<ScalarOp> {
    match ast {
        ScalarAst::Call { op, .. } => Some(op.clone()),
        ScalarAst::TypeAnnotation { expr, .. } => root_ast_op(expr),
        ScalarAst::InputRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::Window { .. }
        | ScalarAst::RelSubquery { .. }
        | ScalarAst::Sarg { .. } => None,
    }
}

fn first_failing_ast_op(ast: &ScalarAst) -> Option<ScalarOp> {
    match ast {
        ScalarAst::Call { op, args, .. } => {
            for arg in args {
                if matches!(
                    classify_semantic_scalar(arg),
                    SemanticScalarClass::Unsupported { .. }
                ) {
                    return first_failing_ast_op(arg).or_else(|| root_ast_op(arg));
                }
            }
            Some(op.clone())
        }
        ScalarAst::TypeAnnotation { expr, .. } => {
            if matches!(
                classify_semantic_scalar(expr),
                SemanticScalarClass::Unsupported { .. }
            ) {
                first_failing_ast_op(expr).or_else(|| root_ast_op(expr))
            } else {
                None
            }
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::Window { .. }
        | ScalarAst::RelSubquery { .. }
        | ScalarAst::Sarg { .. } => None,
    }
}

impl SemanticScalarExampleFilter {
    fn matches(self, reason: &SemanticScalarExampleReason) -> bool {
        matches!(
            (self, reason),
            (SemanticScalarExampleFilter::All, _)
                | (
                    SemanticScalarExampleFilter::Unparsed,
                    SemanticScalarExampleReason::Unparsed
                )
                | (
                    SemanticScalarExampleFilter::Unsupported,
                    SemanticScalarExampleReason::Unsupported { .. }
                )
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::scalar::calcite_scalar;
    use crate::ir::{Feature, Query, RelExpr, ScalarOp, Schema, ValuesTuples};

    #[test]
    fn summarizes_semantic_scalar_readiness() {
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![Query {
                source_sql: None,
                rel: RelExpr::Filter {
                    input: Box::new(RelExpr::Values {
                        tuples: ValuesTuples::Rows {
                            rows: vec![vec![calcite_scalar("CAST('x')")]],
                        },
                        output: Vec::new(),
                    }),
                    predicate: calcite_scalar("AND(=($0, 1), IS NOT NULL($1))"),
                    output: Vec::new(),
                },
                output: Vec::new(),
                features: vec![Feature::Selection],
                calcite_rel_text: None,
                calcite_rel_plan: None,
            }],
        };

        let summary = summarize_converted_semantic_scalars(
            1,
            [(Path::new("case/before.calcite-ir.json"), &ir)].into_iter(),
            Vec::new(),
        );

        assert_eq!(summary.scanned_files, 1);
        assert_eq!(summary.total_scalar_exprs, 2);
        assert_eq!(summary.parsed_scalar_exprs, 2);
        assert_eq!(summary.core_predicate_exprs, 1);
        assert_eq!(summary.unsupported_exprs, 1);
        assert_eq!(
            summary.unsupported_reasons,
            vec![SemanticScalarUnsupportedRow {
                reason: SemanticScalarUnsupported::UnsupportedOperator,
                files: 1,
                queries: 1,
                expressions: 1,
            }]
        );
    }

    #[test]
    fn reports_unsupported_scalar_examples() {
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![Query {
                source_sql: None,
                rel: RelExpr::Filter {
                    input: Box::new(RelExpr::Values {
                        tuples: ValuesTuples::Rows {
                            rows: vec![vec![calcite_scalar("CAST('x')")]],
                        },
                        output: Vec::new(),
                    }),
                    predicate: calcite_scalar("=($0, 1)"),
                    output: Vec::new(),
                },
                output: Vec::new(),
                features: vec![Feature::Selection],
                calcite_rel_text: None,
                calcite_rel_plan: None,
            }],
        };

        let examples = converted_semantic_scalar_examples(
            1,
            [(Path::new("case/before.calcite-ir.json"), &ir)].into_iter(),
            Vec::new(),
            10,
            SemanticScalarExampleFilter::All,
        );

        assert_eq!(examples.scanned_files, 1);
        assert_eq!(examples.failed_files, 0);
        assert_eq!(examples.total_queries, 1);
        assert_eq!(examples.total_scalar_exprs, 2);
        assert_eq!(examples.unparsed_scalar_exprs, 0);
        assert_eq!(examples.unsupported_exprs, 1);
        assert_eq!(
            examples.examples,
            vec![SemanticScalarExample {
                path: "case/before.calcite-ir.json".to_owned(),
                query_index: 0,
                scalar_index: 1,
                reason: SemanticScalarExampleReason::Unsupported {
                    reason: SemanticScalarUnsupported::UnsupportedOperator
                },
                raw: "CAST('x')".to_owned(),
            }]
        );
    }

    #[test]
    fn filters_semantic_scalar_examples_by_kind() {
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![Query {
                source_sql: None,
                rel: RelExpr::Values {
                    tuples: ValuesTuples::Rows {
                        rows: vec![vec![calcite_scalar("CAST('x')")]],
                    },
                    output: Vec::new(),
                },
                output: Vec::new(),
                features: Vec::new(),
                calcite_rel_text: None,
                calcite_rel_plan: None,
            }],
        };

        let examples = converted_semantic_scalar_examples(
            1,
            [(Path::new("case/before.calcite-ir.json"), &ir)].into_iter(),
            Vec::new(),
            10,
            SemanticScalarExampleFilter::Unsupported,
        );

        assert_eq!(examples.unparsed_scalar_exprs, 0);
        assert_eq!(examples.unsupported_exprs, 1);
        assert_eq!(examples.examples.len(), 1);
        assert_eq!(
            examples.examples[0].reason,
            SemanticScalarExampleReason::Unsupported {
                reason: SemanticScalarUnsupported::UnsupportedOperator
            }
        );
    }

    #[test]
    fn groups_semantic_scalar_examples_by_reason_and_first_failing_op() {
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![Query {
                source_sql: None,
                rel: RelExpr::Values {
                    tuples: ValuesTuples::Rows {
                        rows: vec![vec![calcite_scalar("AND(=($0, 1), =(CAST('x'), 'abc'))")]],
                    },
                    output: Vec::new(),
                },
                output: Vec::new(),
                features: Vec::new(),
                calcite_rel_text: None,
                calcite_rel_plan: None,
            }],
        };

        let groups = converted_semantic_scalar_example_groups(
            1,
            [(Path::new("case/before.calcite-ir.json"), &ir)].into_iter(),
            Vec::new(),
            10,
            SemanticScalarExampleFilter::All,
        );

        assert_eq!(groups.unparsed_scalar_exprs, 0);
        assert_eq!(groups.unsupported_exprs, 1);
        assert_eq!(groups.groups.len(), 1);
        let cast_group = group_by_failing_op(
            &groups,
            SemanticScalarUnsupported::UnsupportedOperator,
            Some(ScalarOp::Cast),
        )
        .unwrap();
        assert_eq!(cast_group.root_op, Some(ScalarOp::And));
        assert_eq!(cast_group.expressions, 1);
    }

    fn group_by_failing_op(
        groups: &SemanticScalarExampleGroups,
        reason: SemanticScalarUnsupported,
        first_failing_op: Option<ScalarOp>,
    ) -> Option<&SemanticScalarExampleGroup> {
        groups.groups.iter().find(|group| {
            group.reason == SemanticScalarExampleReason::Unsupported { reason }
                && group.first_failing_op == first_failing_op
        })
    }
}
