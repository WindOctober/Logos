use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::Serialize;

use crate::convert_file;
use crate::diagnostics::features::{ScanFailure, calcite_ir_files};
use crate::diagnostics::rel_audit::{RelStructuralMarker, query_rel_structural_markers};
use crate::ir::{Feature, LogosIrFile, Query};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SupportSummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub formal_unsupported_queries: usize,
    pub support_blockers: Vec<SupportFeatureRow>,
    pub structural_gaps: Vec<SupportMarkerRow>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SupportFeatureRow {
    pub feature: Feature,
    pub files: usize,
    pub queries: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub example: Option<SupportExample>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SupportMarkerRow {
    pub marker: RelStructuralMarker,
    pub files: usize,
    pub queries: usize,
    pub occurrences: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub example: Option<SupportExample>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SupportExample {
    pub path: String,
    pub query_index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SupportConsistencySummary {
    pub scanned_files: usize,
    pub failed_files: usize,
    pub total_queries: usize,
    pub formal_unsupported_queries: usize,
    pub support_blocker_queries: usize,
    pub structural_gap_queries: usize,
    pub unsupported_without_blocker: Vec<SupportConsistencyIssue>,
    pub blocker_without_formal_unsupported: Vec<SupportConsistencyIssue>,
    pub structural_gap_without_formal_unsupported: Vec<SupportConsistencyIssue>,
    pub failures: Vec<ScanFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SupportConsistencyIssue {
    pub path: String,
    pub query_index: usize,
    pub features: Vec<Feature>,
    pub support_blockers: Vec<Feature>,
    pub structural_gaps: Vec<RelStructuralMarker>,
}

pub fn summarize_support(root: impl AsRef<Path>) -> SupportSummary {
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

    summarize_converted_support(paths.len(), converted.iter(), failures)
}

pub fn summarize_support_consistency(root: impl AsRef<Path>) -> SupportConsistencySummary {
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

    summarize_converted_support_consistency(paths.len(), converted.iter(), failures)
}

fn summarize_converted_support<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = &'a (String, LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> SupportSummary {
    let mut total_queries = 0usize;
    let mut formal_unsupported_queries = 0usize;

    let mut feature_file_counts = BTreeMap::<Feature, usize>::new();
    let mut feature_query_counts = BTreeMap::<Feature, usize>::new();
    let mut feature_examples = BTreeMap::<Feature, SupportExample>::new();

    let mut marker_file_counts = BTreeMap::<RelStructuralMarker, usize>::new();
    let mut marker_query_counts = BTreeMap::<RelStructuralMarker, usize>::new();
    let mut marker_occurrence_counts = BTreeMap::<RelStructuralMarker, usize>::new();
    let mut marker_examples = BTreeMap::<RelStructuralMarker, SupportExample>::new();

    for (path, ir) in files {
        let mut file_features = BTreeSet::new();
        let mut file_markers = BTreeSet::new();

        for (query_index, query) in ir.queries.iter().enumerate() {
            total_queries += 1;
            let query_features: BTreeSet<_> = query.features.iter().copied().collect();
            if query_features.contains(&Feature::FormalSqlUnsupported) {
                formal_unsupported_queries += 1;
            }

            for feature in query_features
                .iter()
                .copied()
                .filter(|feature| is_support_blocker_feature(*feature))
            {
                *feature_query_counts.entry(feature).or_default() += 1;
                file_features.insert(feature);
                feature_examples
                    .entry(feature)
                    .or_insert_with(|| SupportExample {
                        path: path.clone(),
                        query_index,
                    });
            }

            let query_markers = query_rel_structural_markers(query);
            let query_marker_set: BTreeSet<_> = query_markers
                .iter()
                .copied()
                .filter(|marker| is_structural_gap_marker(*marker))
                .collect();
            for marker in &query_marker_set {
                *marker_query_counts.entry(*marker).or_default() += 1;
                file_markers.insert(*marker);
                marker_examples
                    .entry(*marker)
                    .or_insert_with(|| SupportExample {
                        path: path.clone(),
                        query_index,
                    });
            }
            for marker in query_markers
                .into_iter()
                .filter(|marker| is_structural_gap_marker(*marker))
            {
                *marker_occurrence_counts.entry(marker).or_default() += 1;
            }
        }

        for feature in file_features {
            *feature_file_counts.entry(feature).or_default() += 1;
        }
        for marker in file_markers {
            *marker_file_counts.entry(marker).or_default() += 1;
        }
    }

    let support_blockers = feature_file_counts
        .keys()
        .chain(feature_query_counts.keys())
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|feature| SupportFeatureRow {
            feature,
            files: feature_file_counts
                .get(&feature)
                .copied()
                .unwrap_or_default(),
            queries: feature_query_counts
                .get(&feature)
                .copied()
                .unwrap_or_default(),
            example: feature_examples.get(&feature).cloned(),
        })
        .collect();

    let structural_gaps = marker_file_counts
        .keys()
        .chain(marker_query_counts.keys())
        .chain(marker_occurrence_counts.keys())
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|marker| SupportMarkerRow {
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

    SupportSummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        formal_unsupported_queries,
        support_blockers,
        structural_gaps,
        failures,
    }
}

fn summarize_converted_support_consistency<'a>(
    scanned_files: usize,
    files: impl Iterator<Item = &'a (String, LogosIrFile)>,
    failures: Vec<ScanFailure>,
) -> SupportConsistencySummary {
    let mut total_queries = 0usize;
    let mut formal_unsupported_queries = 0usize;
    let mut support_blocker_queries = 0usize;
    let mut structural_gap_queries = 0usize;
    let mut unsupported_without_blocker = Vec::new();
    let mut blocker_without_formal_unsupported = Vec::new();
    let mut structural_gap_without_formal_unsupported = Vec::new();

    for (path, ir) in files {
        for (query_index, query) in ir.queries.iter().enumerate() {
            total_queries += 1;
            let snapshot = support_consistency_snapshot(path, query_index, query);
            let formal_unsupported = snapshot.features.contains(&Feature::FormalSqlUnsupported);
            let has_support_blocker = !snapshot.support_blockers.is_empty();
            let has_structural_gap = !snapshot.structural_gaps.is_empty();

            if formal_unsupported {
                formal_unsupported_queries += 1;
            }
            if has_support_blocker {
                support_blocker_queries += 1;
            }
            if has_structural_gap {
                structural_gap_queries += 1;
            }

            if formal_unsupported && !has_support_blocker && !has_structural_gap {
                unsupported_without_blocker.push(snapshot.clone());
            }
            if has_support_blocker && !formal_unsupported {
                blocker_without_formal_unsupported.push(snapshot.clone());
            }
            if has_structural_gap && !formal_unsupported {
                structural_gap_without_formal_unsupported.push(snapshot);
            }
        }
    }

    SupportConsistencySummary {
        scanned_files,
        failed_files: failures.len(),
        total_queries,
        formal_unsupported_queries,
        support_blocker_queries,
        structural_gap_queries,
        unsupported_without_blocker,
        blocker_without_formal_unsupported,
        structural_gap_without_formal_unsupported,
        failures,
    }
}

fn support_consistency_snapshot(
    path: &str,
    query_index: usize,
    query: &Query,
) -> SupportConsistencyIssue {
    let features = query.features.clone();
    let support_blockers = features
        .iter()
        .copied()
        .filter(|feature| is_support_blocker_feature(*feature))
        .collect();
    let structural_gaps = query_rel_structural_markers(query)
        .into_iter()
        .filter(|marker| is_structural_gap_marker(*marker))
        .collect();
    SupportConsistencyIssue {
        path: path.to_owned(),
        query_index,
        features,
        support_blockers,
        structural_gaps,
    }
}

fn is_support_blocker_feature(feature: Feature) -> bool {
    matches!(
        feature,
        Feature::OuterJoin
            | Feature::SemiJoin
            | Feature::AntiJoin
            | Feature::Aggregation
            | Feature::DistinctAggregate
            | Feature::FilteredAggregate
            | Feature::Union
            | Feature::Intersect
            | Feature::Except
            | Feature::SetDistinct
            | Feature::AdvancedAggregateFunction
            | Feature::GroupingFunction
            | Feature::GroupingSets
            | Feature::Rollup
            | Feature::Cube
            | Feature::WindowFunction
            | Feature::OpaqueScalar
            | Feature::SubqueryPredicate
            | Feature::CorrelatedPredicate
            | Feature::AnySqlType
            | Feature::FormalSqlOrderSensitive
            | Feature::Values
    )
}

fn is_structural_gap_marker(marker: RelStructuralMarker) -> bool {
    matches!(
        marker,
        RelStructuralMarker::SortNullDirectionMissing
            | RelStructuralMarker::ScalarEmbeddedRelShapeUnknown
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::scalar::calcite_scalar;
    use crate::ir::{
        Column, Query, RelExpr, ScalarAst, ScalarClass, ScalarExpr, Schema, SortDirection, SortKey,
        SqlType, TextRelAttr, TextRelNode, TextRelNodeKind, TextRelShape, ValuesTuples,
    };

    #[test]
    fn summarizes_support_blockers_and_structural_gaps() {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Values {
                tuples: ValuesTuples::Rows {
                    rows: vec![vec![calcite_scalar("ROW_NUMBER() OVER ()")]],
                },
                output: vec![Column {
                    name: "v".to_owned(),
                    ty: SqlType::Integer,
                    nullable: true,
                    precision: None,
                }],
            },
            output: Vec::new(),
            features: vec![
                Feature::Values,
                Feature::WindowFunction,
                Feature::FormalSqlUnsupported,
            ],
            calcite_rel_text: None,
            calcite_rel_plan: None,
        };
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert_eq!(summary.formal_unsupported_queries, 1);
        assert_eq!(feature_row(&summary, Feature::Values).unwrap().queries, 1);
        assert_eq!(
            feature_row(&summary, Feature::WindowFunction)
                .unwrap()
                .queries,
            1
        );
        assert!(summary.structural_gaps.is_empty());
    }

    #[test]
    fn parsed_embedded_rel_text_is_not_a_structural_gap() {
        let query = query_with_scalar(ScalarAst::RelText {
            raw: "LogicalTableScan(table=[[t]])".to_owned(),
            plan: TextRelNode {
                rel_type: "LogicalTableScan".to_owned(),
                kind: TextRelNodeKind::TableScan,
                shape: TextRelShape::TableScan {
                    table: vec!["t".to_owned()],
                },
                attrs: vec![TextRelAttr {
                    name: "table".to_owned(),
                    value: "[[t]]".to_owned(),
                }],
                inputs: Vec::new(),
                raw_line: "LogicalTableScan(table=[[t]])".to_owned(),
            },
        });
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert!(marker_row(&summary, RelStructuralMarker::ScalarEmbeddedRelText).is_none());
        assert!(marker_row(&summary, RelStructuralMarker::ScalarEmbeddedRelShapeUnknown).is_none());
    }

    #[test]
    fn unknown_embedded_rel_text_shape_is_a_structural_gap() {
        let query = query_with_scalar(ScalarAst::RelText {
            raw: "LogicalUnknown(...)".to_owned(),
            plan: TextRelNode {
                rel_type: "LogicalUnknown".to_owned(),
                kind: TextRelNodeKind::Other {
                    rel_type: "LogicalUnknown".to_owned(),
                },
                shape: TextRelShape::Other,
                attrs: Vec::new(),
                inputs: Vec::new(),
                raw_line: "LogicalUnknown(...)".to_owned(),
            },
        });
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert_eq!(
            marker_row(&summary, RelStructuralMarker::ScalarEmbeddedRelShapeUnknown)
                .unwrap()
                .occurrences,
            1
        );
    }

    #[test]
    fn order_sensitive_sort_is_a_support_blocker_not_a_structural_gap() {
        let column = Column {
            name: "v".to_owned(),
            ty: SqlType::Integer,
            nullable: true,
            precision: None,
        };
        let query = Query {
            source_sql: None,
            rel: RelExpr::Sort {
                input: Box::new(RelExpr::Values {
                    tuples: ValuesTuples::Rows { rows: Vec::new() },
                    output: vec![column.clone()],
                }),
                collation: vec![SortKey {
                    field_index: 0,
                    direction: SortDirection::Ascending,
                    null_direction: Some(crate::ir::SortNullDirection::Last),
                }],
                fetch: Some(ScalarExpr {
                    raw: "10".to_owned(),
                    class: ScalarClass::Literal,
                    parsed: ScalarAst::Literal {
                        raw: "10".to_owned(),
                    },
                }),
                offset: None,
                output: vec![column],
            },
            output: Vec::new(),
            features: vec![
                Feature::Sort,
                Feature::Limit,
                Feature::FormalSqlOrderSensitive,
                Feature::FormalSqlUnsupported,
            ],
            calcite_rel_text: None,
            calcite_rel_plan: None,
        };
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert_eq!(
            feature_row(&summary, Feature::FormalSqlOrderSensitive)
                .unwrap()
                .queries,
            1
        );
        assert!(marker_row(&summary, RelStructuralMarker::SortOrderSensitive).is_none());
        assert!(marker_row(&summary, RelStructuralMarker::SortNullDirectionMissing).is_none());
    }

    #[test]
    fn consistency_reports_formal_unsupported_without_specific_blocker() {
        let query = query_with_features(vec![Feature::FormalSqlUnsupported]);
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support_consistency(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert_eq!(summary.unsupported_without_blocker.len(), 1);
        assert!(summary.blocker_without_formal_unsupported.is_empty());
        assert!(summary.structural_gap_without_formal_unsupported.is_empty());
    }

    #[test]
    fn consistency_reports_support_blocker_without_formal_unsupported() {
        let query = query_with_features(vec![Feature::Values]);
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support_consistency(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert!(summary.unsupported_without_blocker.is_empty());
        assert_eq!(summary.blocker_without_formal_unsupported.len(), 1);
        assert!(summary.structural_gap_without_formal_unsupported.is_empty());
    }

    #[test]
    fn consistency_reports_structural_gap_without_formal_unsupported() {
        let column = Column {
            name: "v".to_owned(),
            ty: SqlType::Integer,
            nullable: true,
            precision: None,
        };
        let query = Query {
            source_sql: None,
            rel: RelExpr::Sort {
                input: Box::new(RelExpr::Values {
                    tuples: ValuesTuples::Rows { rows: Vec::new() },
                    output: vec![column.clone()],
                }),
                collation: vec![SortKey {
                    field_index: 0,
                    direction: SortDirection::Ascending,
                    null_direction: None,
                }],
                fetch: None,
                offset: None,
                output: vec![column],
            },
            output: Vec::new(),
            features: Vec::new(),
            calcite_rel_text: None,
            calcite_rel_plan: None,
        };
        let ir = LogosIrFile {
            schema: Schema { tables: Vec::new() },
            queries: vec![query],
        };

        let summary = summarize_converted_support_consistency(
            1,
            [("case/before.calcite-ir.json".to_owned(), ir)].iter(),
            Vec::new(),
        );

        assert!(summary.unsupported_without_blocker.is_empty());
        assert!(summary.blocker_without_formal_unsupported.is_empty());
        assert_eq!(summary.structural_gap_without_formal_unsupported.len(), 1);
    }

    fn query_with_scalar(ast: ScalarAst) -> Query {
        Query {
            source_sql: None,
            rel: RelExpr::Values {
                tuples: ValuesTuples::Rows {
                    rows: vec![vec![ScalarExpr {
                        raw: "subquery".to_owned(),
                        class: ScalarClass::Call,
                        parsed: ast,
                    }]],
                },
                output: vec![Column {
                    name: "v".to_owned(),
                    ty: SqlType::Integer,
                    nullable: true,
                    precision: None,
                }],
            },
            output: Vec::new(),
            features: vec![Feature::SubqueryPredicate, Feature::FormalSqlUnsupported],
            calcite_rel_text: None,
            calcite_rel_plan: None,
        }
    }

    fn query_with_features(features: Vec<Feature>) -> Query {
        Query {
            source_sql: None,
            rel: RelExpr::Values {
                tuples: ValuesTuples::Rows { rows: Vec::new() },
                output: vec![Column {
                    name: "v".to_owned(),
                    ty: SqlType::Integer,
                    nullable: true,
                    precision: None,
                }],
            },
            output: Vec::new(),
            features,
            calcite_rel_text: None,
            calcite_rel_plan: None,
        }
    }

    fn feature_row(summary: &SupportSummary, feature: Feature) -> Option<&SupportFeatureRow> {
        summary
            .support_blockers
            .iter()
            .find(|row| row.feature == feature)
    }

    fn marker_row(
        summary: &SupportSummary,
        marker: RelStructuralMarker,
    ) -> Option<&SupportMarkerRow> {
        summary
            .structural_gaps
            .iter()
            .find(|row| row.marker == marker)
    }
}
