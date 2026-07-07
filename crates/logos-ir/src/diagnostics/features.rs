use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::convert_file;
use crate::ir::{Feature, LogosIrFile};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureSummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub features: Vec<FeatureSummaryRow>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureSummaryRow {
    pub feature: Feature,
    pub files: usize,
    pub queries: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ScanFailure {
    pub path: String,
    pub error: String,
}

pub fn summarize_features(root: impl AsRef<Path>) -> FeatureSummary {
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

    summarize_converted(
        paths.len(),
        converted.iter().map(|(path, ir)| (path.as_path(), ir)),
        failures,
    )
}

pub fn calcite_ir_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    visit(root, &mut out);
    out.sort();
    out
}

fn summarize_converted<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = (&'a Path, &'a LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> FeatureSummary {
    let mut file_counts = BTreeMap::<Feature, usize>::new();
    let mut query_counts = BTreeMap::<Feature, usize>::new();
    let mut total_queries = 0usize;

    for (_, ir) in files {
        let mut file_features = BTreeSet::new();
        for query in &ir.queries {
            total_queries += 1;
            let query_features: BTreeSet<_> = query.features.iter().copied().collect();
            for feature in &query_features {
                *query_counts.entry(*feature).or_default() += 1;
            }
            file_features.extend(query_features);
        }
        for feature in file_features {
            *file_counts.entry(feature).or_default() += 1;
        }
    }

    let all_features: BTreeSet<_> = file_counts
        .keys()
        .chain(query_counts.keys())
        .copied()
        .collect();
    let features = all_features
        .into_iter()
        .map(|feature| FeatureSummaryRow {
            feature,
            files: file_counts.get(&feature).copied().unwrap_or_default(),
            queries: query_counts.get(&feature).copied().unwrap_or_default(),
        })
        .collect();

    FeatureSummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        features,
        failures,
    }
}

fn visit(path: &Path, out: &mut Vec<PathBuf>) {
    let Ok(metadata) = std::fs::metadata(path) else {
        return;
    };
    if metadata.is_file() {
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            return;
        };
        if name == "before.calcite-ir.json" || name == "after.calcite-ir.json" {
            out.push(path.to_path_buf());
        }
        return;
    }
    if metadata.is_dir() {
        let Ok(entries) = std::fs::read_dir(path) else {
            return;
        };
        for entry in entries.flatten() {
            visit(&entry.path(), out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Query, RelExpr, Schema};

    #[test]
    fn summarizes_file_and_query_feature_counts() {
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![
                query(vec![Feature::TableScan, Feature::Projection]),
                query(vec![Feature::TableScan, Feature::Selection]),
            ],
        };
        let summary = summarize_converted(
            1,
            [(Path::new("case/before.calcite-ir.json"), &ir)].into_iter(),
            Vec::new(),
        );

        assert_eq!(summary.scanned_files, 1);
        assert_eq!(summary.failed_files, 0);
        assert_eq!(summary.total_queries, 2);
        assert_eq!(
            row(&summary, Feature::TableScan),
            Some(&FeatureSummaryRow {
                feature: Feature::TableScan,
                files: 1,
                queries: 2,
            })
        );
        assert_eq!(
            row(&summary, Feature::Projection),
            Some(&FeatureSummaryRow {
                feature: Feature::Projection,
                files: 1,
                queries: 1,
            })
        );
    }

    fn query(features: Vec<Feature>) -> Query {
        Query {
            source_sql: None,
            rel: RelExpr::Values {
                tuples: crate::ir::ValuesTuples::UnavailableFromCalcite,
                output: Vec::new(),
            },
            output: Vec::new(),
            features,
            calcite_rel_text: None,
            calcite_rel_plan: None,
        }
    }

    fn row(summary: &FeatureSummary, feature: Feature) -> Option<&FeatureSummaryRow> {
        summary.features.iter().find(|row| row.feature == feature)
    }
}
