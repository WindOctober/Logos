use std::collections::BTreeSet;

use logos_ir::ir::Feature;

use super::syntax::FeatureCoverage;

pub fn feature_coverage(features: &[Feature]) -> FeatureCoverage {
    let mut structurally_supported = BTreeSet::new();
    let mut requires_audit = BTreeSet::new();
    for feature in features {
        let name = feature_name(*feature).to_owned();
        if is_supported_feature(*feature) {
            structurally_supported.insert(name.clone());
        } else {
            requires_audit.insert(name.clone());
        }
        if requires_semantic_audit(*feature) {
            requires_audit.insert(name);
        }
    }
    FeatureCoverage {
        structurally_supported: structurally_supported.into_iter().collect(),
        requires_audit: requires_audit.into_iter().collect(),
    }
}

fn requires_semantic_audit(feature: Feature) -> bool {
    matches!(
        feature,
        Feature::OuterJoin | Feature::SemiJoin | Feature::AntiJoin
    )
}

fn is_supported_feature(feature: Feature) -> bool {
    matches!(
        feature,
        Feature::TableScan
            | Feature::Projection
            | Feature::Selection
            | Feature::InnerJoin
            | Feature::OuterJoin
            | Feature::SemiJoin
            | Feature::AntiJoin
            | Feature::Aggregation
            | Feature::BasicAggregateFunction
            | Feature::Union
            | Feature::Intersect
            | Feature::Except
    )
}

fn feature_name(feature: Feature) -> &'static str {
    match feature {
        Feature::TableScan => "table_scan",
        Feature::Projection => "projection",
        Feature::Selection => "selection",
        Feature::InnerJoin => "inner_join",
        Feature::OuterJoin => "outer_join",
        Feature::SemiJoin => "semi_join",
        Feature::AntiJoin => "anti_join",
        Feature::Aggregation => "aggregation",
        Feature::AggregateGroupingSetsUnavailable => "aggregate_grouping_sets_unavailable",
        Feature::DistinctAggregate => "distinct_aggregate",
        Feature::FilteredAggregate => "filtered_aggregate",
        Feature::Union => "union",
        Feature::Intersect => "intersect",
        Feature::Except => "except",
        Feature::SetDistinct => "set_distinct",
        Feature::Sort => "sort",
        Feature::Limit => "limit",
        Feature::Offset => "offset",
        Feature::Values => "values",
        Feature::ValuesTuplesUnavailable => "values_tuples_unavailable",
        Feature::OpaqueScalar => "opaque_scalar",
        Feature::SubqueryPredicate => "subquery_predicate",
        Feature::CorrelatedPredicate => "correlated_predicate",
        Feature::BasicAggregateFunction => "basic_aggregate_function",
        Feature::AdvancedAggregateFunction => "advanced_aggregate_function",
        Feature::GroupingFunction => "grouping_function",
        Feature::GroupingSets => "grouping_sets",
        Feature::Rollup => "rollup",
        Feature::Cube => "cube",
        Feature::WindowFunction => "window_function",
        Feature::AnySqlType => "any_sql_type",
        Feature::NullSqlType => "null_sql_type",
        Feature::FormalSqlOrderSensitive => "formal_sql_order_sensitive",
        Feature::FormalSqlUnsupported => "formal_sql_unsupported",
    }
}
