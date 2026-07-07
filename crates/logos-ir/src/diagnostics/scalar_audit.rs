use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::Serialize;

use crate::convert_file;
use crate::diagnostics::features::{ScanFailure, calcite_ir_files};
use crate::ir::{LogosIrFile, ScalarAst, ScalarOp};
use crate::semantic::walk::query_scalars;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ScalarOpSummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub total_scalar_exprs: usize,
    pub parsed_scalar_exprs: usize,
    pub unparsed_scalar_exprs: usize,
    pub ops: Vec<ScalarOpSummaryRow>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ScalarOpSummaryRow {
    pub op: ScalarOp,
    pub files: usize,
    pub queries: usize,
    pub occurrences: usize,
}

pub fn summarize_scalar_ops(root: impl AsRef<Path>) -> ScalarOpSummary {
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

    summarize_converted_scalar_ops(
        paths.len(),
        converted.iter().map(|(path, ir)| (path.as_path(), ir)),
        failures,
    )
}

fn summarize_converted_scalar_ops<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = (&'a Path, &'a LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> ScalarOpSummary {
    let mut file_counts = BTreeMap::<ScalarOp, usize>::new();
    let mut query_counts = BTreeMap::<ScalarOp, usize>::new();
    let mut occurrence_counts = BTreeMap::<ScalarOp, usize>::new();
    let mut total_queries = 0usize;
    let mut total_scalar_exprs = 0usize;
    let mut parsed_scalar_exprs = 0usize;
    let unparsed_scalar_exprs = 0usize;

    for (_, ir) in files {
        let mut file_ops = BTreeSet::new();
        for query in &ir.queries {
            total_queries += 1;
            let scalars = query_scalars(query);
            let mut query_ops = BTreeSet::new();
            for scalar in scalars {
                total_scalar_exprs += 1;
                parsed_scalar_exprs += 1;
                collect_ast_ops(&scalar.parsed, &mut |op| {
                    *occurrence_counts.entry(op.clone()).or_default() += 1;
                    query_ops.insert(op.clone());
                    file_ops.insert(op.clone());
                });
            }
            for op in query_ops {
                *query_counts.entry(op).or_default() += 1;
            }
        }
        for op in file_ops {
            *file_counts.entry(op).or_default() += 1;
        }
    }

    let all_ops: BTreeSet<_> = file_counts
        .keys()
        .chain(query_counts.keys())
        .chain(occurrence_counts.keys())
        .cloned()
        .collect();
    let ops = all_ops
        .into_iter()
        .map(|op| ScalarOpSummaryRow {
            files: file_counts.get(&op).copied().unwrap_or_default(),
            queries: query_counts.get(&op).copied().unwrap_or_default(),
            occurrences: occurrence_counts.get(&op).copied().unwrap_or_default(),
            op,
        })
        .collect();

    ScalarOpSummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        total_scalar_exprs,
        parsed_scalar_exprs,
        unparsed_scalar_exprs,
        ops,
        failures,
    }
}

fn collect_ast_ops(ast: &ScalarAst, visit: &mut impl FnMut(&ScalarOp)) {
    match ast {
        ScalarAst::InputRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::Window { .. }
        | ScalarAst::RelText { .. }
        | ScalarAst::Sarg { .. } => {}
        ScalarAst::Call { op, args, .. } => {
            visit(op);
            for arg in args {
                collect_ast_ops(arg, visit);
            }
        }
        ScalarAst::TypeAnnotation { expr, .. } => collect_ast_ops(expr, visit),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::scalar::calcite_scalar;
    use crate::ir::{Feature, Query, RelExpr, Schema, ValuesTuples};

    #[test]
    fn summarizes_scalar_operator_counts() {
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![Query {
                source_sql: None,
                rel: RelExpr::Filter {
                    input: Box::new(RelExpr::Values {
                        tuples: ValuesTuples::Rows {
                            rows: vec![vec![calcite_scalar("+(1, 2)")]],
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

        let summary = summarize_converted_scalar_ops(
            1,
            [(Path::new("case/before.calcite-ir.json"), &ir)].into_iter(),
            Vec::new(),
        );

        assert_eq!(summary.scanned_files, 1);
        assert_eq!(summary.failed_files, 0);
        assert_eq!(summary.total_queries, 1);
        assert_eq!(summary.total_scalar_exprs, 2);
        assert_eq!(summary.parsed_scalar_exprs, 2);
        assert_eq!(summary.unparsed_scalar_exprs, 0);
        assert_eq!(row(&summary, &ScalarOp::And).unwrap().occurrences, 1);
        assert_eq!(row(&summary, &ScalarOp::Eq).unwrap().occurrences, 1);
        assert_eq!(row(&summary, &ScalarOp::IsNotNull).unwrap().occurrences, 1);
        assert_eq!(row(&summary, &ScalarOp::Plus).unwrap().occurrences, 1);
    }

    fn row<'a>(summary: &'a ScalarOpSummary, op: &ScalarOp) -> Option<&'a ScalarOpSummaryRow> {
        summary.ops.iter().find(|row| &row.op == op)
    }
}
