use crate::calcite::sort_semantics::calcite_text_sort_null_direction;
use crate::ir::{RelExpr, ScalarExpr, TextRelNode, TextRelNodeKind, TextRelShape, ValuesTuples};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RelTextHydrationStats {
    pub values_nodes: usize,
    pub hydrated_values_nodes: usize,
    pub already_available_values_nodes: usize,
    pub unavailable_values_nodes: usize,
    pub aggregate_nodes: usize,
    pub hydrated_aggregate_grouping_sets: usize,
    pub already_available_aggregate_grouping_sets: usize,
    pub unavailable_aggregate_grouping_sets: usize,
    pub sort_nodes: usize,
    pub hydrated_sort_null_directions: usize,
    pub unavailable_sort_null_directions: usize,
}

pub fn hydrate_rel_from_text_plan(rel: &mut RelExpr, plan: &TextRelNode) -> RelTextHydrationStats {
    let mut stats = RelTextHydrationStats::default();
    hydrate_rel_from_text_plan_inner(rel, plan, &mut stats);
    stats
}

pub fn hydrate_values_from_text_plan(
    rel: &mut RelExpr,
    plan: &TextRelNode,
) -> RelTextHydrationStats {
    hydrate_rel_from_text_plan(rel, plan)
}

pub fn rel_contains_unavailable_values(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::TableScan { .. } => false,
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::Aggregate { input, .. }
        | RelExpr::Sort { input, .. } => rel_contains_unavailable_values(input),
        RelExpr::Join { left, right, .. } => {
            rel_contains_unavailable_values(left) || rel_contains_unavailable_values(right)
        }
        RelExpr::Set { inputs, .. } => inputs.iter().any(rel_contains_unavailable_values),
        RelExpr::Values { tuples, .. } => matches!(tuples, ValuesTuples::UnavailableFromCalcite),
    }
}

pub fn rel_contains_unavailable_aggregate_grouping_sets(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => false,
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::Sort { input, .. } => rel_contains_unavailable_aggregate_grouping_sets(input),
        RelExpr::Aggregate {
            input,
            grouping_sets,
            ..
        } => grouping_sets.is_none() || rel_contains_unavailable_aggregate_grouping_sets(input),
        RelExpr::Join { left, right, .. } => {
            rel_contains_unavailable_aggregate_grouping_sets(left)
                || rel_contains_unavailable_aggregate_grouping_sets(right)
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .any(rel_contains_unavailable_aggregate_grouping_sets),
    }
}

fn hydrate_rel_from_text_plan_inner(
    rel: &mut RelExpr,
    plan: &TextRelNode,
    stats: &mut RelTextHydrationStats,
) {
    if !text_node_matches_rel(rel, plan) {
        return;
    }

    match rel {
        RelExpr::TableScan { .. } => {}
        RelExpr::Project { input, .. } | RelExpr::Filter { input, .. } => {
            if let Some(plan_input) = plan.inputs.first() {
                hydrate_rel_from_text_plan_inner(input, plan_input, stats);
            }
        }
        RelExpr::Sort {
            input, collation, ..
        } => {
            stats.sort_nodes += 1;
            if let TextRelShape::Sort { sort_keys, .. } = &plan.shape {
                for (key, text_key) in collation.iter_mut().zip(sort_keys) {
                    if key.null_direction.is_none() {
                        if let Some(direction) = calcite_text_sort_null_direction(
                            text_key.direction.as_deref(),
                            key.direction,
                        ) {
                            key.null_direction = Some(direction);
                            stats.hydrated_sort_null_directions += 1;
                        } else {
                            stats.unavailable_sort_null_directions += 1;
                        }
                    }
                }
            } else {
                stats.unavailable_sort_null_directions += collation
                    .iter()
                    .filter(|key| key.null_direction.is_none())
                    .count();
            }
            if let Some(plan_input) = plan.inputs.first() {
                hydrate_rel_from_text_plan_inner(input, plan_input, stats);
            }
        }
        RelExpr::Aggregate {
            input,
            group_keys,
            grouping_sets,
            ..
        } => {
            stats.aggregate_nodes += 1;
            match grouping_sets {
                Some(_) => stats.already_available_aggregate_grouping_sets += 1,
                None => {
                    if let TextRelShape::Aggregate {
                        group_keys: text_group_keys,
                        grouping_sets: text_grouping_sets,
                        ..
                    } = &plan.shape
                    {
                        let hydrated = text_grouping_sets.clone().or_else(|| {
                            text_group_keys.as_ref().and_then(|text_group_keys| {
                                if text_group_keys == group_keys {
                                    Some(vec![group_keys.clone()])
                                } else {
                                    None
                                }
                            })
                        });
                        if let Some(hydrated) = hydrated {
                            *grouping_sets = Some(hydrated);
                            stats.hydrated_aggregate_grouping_sets += 1;
                        } else {
                            stats.unavailable_aggregate_grouping_sets += 1;
                        }
                    } else {
                        stats.unavailable_aggregate_grouping_sets += 1;
                    }
                }
            }
            if let Some(plan_input) = plan.inputs.first() {
                hydrate_rel_from_text_plan_inner(input, plan_input, stats);
            }
        }
        RelExpr::Join { left, right, .. } => {
            if let Some(plan_left) = plan.inputs.first() {
                hydrate_rel_from_text_plan_inner(left, plan_left, stats);
            }
            if let Some(plan_right) = plan.inputs.get(1) {
                hydrate_rel_from_text_plan_inner(right, plan_right, stats);
            }
        }
        RelExpr::Set { inputs, .. } => {
            for (input, plan_input) in inputs.iter_mut().zip(&plan.inputs) {
                hydrate_rel_from_text_plan_inner(input, plan_input, stats);
            }
        }
        RelExpr::Values { tuples, .. } => {
            stats.values_nodes += 1;
            match tuples {
                ValuesTuples::Rows { .. } => stats.already_available_values_nodes += 1,
                ValuesTuples::UnavailableFromCalcite => {
                    if let TextRelShape::Values {
                        tuples: Some(text_rows),
                    } = &plan.shape
                    {
                        *tuples = ValuesTuples::Rows {
                            rows: clone_text_rows(text_rows),
                        };
                        stats.hydrated_values_nodes += 1;
                    } else {
                        stats.unavailable_values_nodes += 1;
                    }
                }
            }
        }
    }
}

fn text_node_matches_rel(rel: &RelExpr, plan: &TextRelNode) -> bool {
    matches!(
        (rel, &plan.kind),
        (RelExpr::TableScan { .. }, TextRelNodeKind::TableScan)
            | (RelExpr::Project { .. }, TextRelNodeKind::Project)
            | (RelExpr::Filter { .. }, TextRelNodeKind::Filter)
            | (RelExpr::Join { .. }, TextRelNodeKind::Join)
            | (RelExpr::Aggregate { .. }, TextRelNodeKind::Aggregate)
            | (RelExpr::Sort { .. }, TextRelNodeKind::Sort)
            | (RelExpr::Set { .. }, TextRelNodeKind::Union)
            | (RelExpr::Set { .. }, TextRelNodeKind::Intersect)
            | (RelExpr::Set { .. }, TextRelNodeKind::Minus)
            | (RelExpr::Values { .. }, TextRelNodeKind::Values)
    )
}

fn clone_text_rows(rows: &[Vec<Box<ScalarExpr>>]) -> Vec<Vec<ScalarExpr>> {
    rows.iter()
        .map(|row| row.iter().map(|expr| expr.as_ref().clone()).collect())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::text_plan::parse_calcite_text_plan;
    use crate::ir::{AggregateCall, Column, SortDirection, SortKey, SortNullDirection, SqlType};

    fn column(name: &str) -> Column {
        Column {
            name: name.to_owned(),
            ty: SqlType::Integer,
            nullable: false,
        }
    }

    #[test]
    fn hydrates_values_rows_from_text_plan() {
        let mut rel = RelExpr::Values {
            tuples: ValuesTuples::UnavailableFromCalcite,
            output: vec![column("EXPR$0")],
        };
        let plan = parse_calcite_text_plan("LogicalValues(tuples=[[{ 1 }, { +(2, 3) }]])")
            .expect("valid text plan");

        let stats = hydrate_values_from_text_plan(&mut rel, &plan);

        assert_eq!(stats.values_nodes, 1);
        assert_eq!(stats.hydrated_values_nodes, 1);
        assert!(!rel_contains_unavailable_values(&rel));
        let RelExpr::Values {
            tuples: ValuesTuples::Rows { rows },
            ..
        } = rel
        else {
            panic!("expected hydrated values");
        };
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0][0].raw, "1");
        assert_eq!(rows[1][0].raw, "+(2, 3)");
    }

    #[test]
    fn leaves_values_unavailable_without_text_tuples() {
        let mut rel = RelExpr::Values {
            tuples: ValuesTuples::UnavailableFromCalcite,
            output: vec![column("EXPR$0")],
        };
        let plan = parse_calcite_text_plan("LogicalValues").expect("valid text plan");

        let stats = hydrate_values_from_text_plan(&mut rel, &plan);

        assert_eq!(stats.values_nodes, 1);
        assert_eq!(stats.hydrated_values_nodes, 0);
        assert_eq!(stats.unavailable_values_nodes, 1);
        assert!(rel_contains_unavailable_values(&rel));
    }

    #[test]
    fn does_not_hydrate_when_text_plan_kind_is_mismatched() {
        let mut rel = RelExpr::Values {
            tuples: ValuesTuples::UnavailableFromCalcite,
            output: vec![column("EXPR$0")],
        };
        let plan = parse_calcite_text_plan("LogicalProject(EXPR$0=[1])").expect("valid text plan");

        let stats = hydrate_values_from_text_plan(&mut rel, &plan);

        assert_eq!(stats.values_nodes, 0);
        assert_eq!(stats.hydrated_values_nodes, 0);
        assert!(rel_contains_unavailable_values(&rel));
    }

    #[test]
    fn hydrates_ordinary_aggregate_grouping_set_from_group_attr() {
        let mut rel = RelExpr::Aggregate {
            input: Box::new(RelExpr::Values {
                tuples: ValuesTuples::Rows { rows: Vec::new() },
                output: vec![column("a")],
            }),
            group_keys: vec![0],
            grouping_sets: None,
            agg_calls: vec![AggregateCall {
                raw: "COUNT()".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                args: Vec::new(),
                filter: None,
            }],
            output: vec![column("c")],
        };
        let plan = parse_calcite_text_plan(
            "LogicalAggregate(group=[{0}], agg#0=[COUNT()])\n  LogicalValues(tuples=[[]])",
        )
        .expect("valid text plan");

        let stats = hydrate_rel_from_text_plan(&mut rel, &plan);

        assert_eq!(stats.aggregate_nodes, 1);
        assert_eq!(stats.hydrated_aggregate_grouping_sets, 1);
        assert!(!rel_contains_unavailable_aggregate_grouping_sets(&rel));
        let RelExpr::Aggregate { grouping_sets, .. } = rel else {
            panic!("expected aggregate");
        };
        assert_eq!(grouping_sets, Some(vec![vec![0]]));
    }

    #[test]
    fn hydrates_sort_null_direction_from_text_plan() {
        let mut rel = RelExpr::Sort {
            input: Box::new(RelExpr::Values {
                tuples: ValuesTuples::Rows { rows: Vec::new() },
                output: vec![column("a")],
            }),
            collation: vec![SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: None,
            }],
            fetch: None,
            offset: None,
            output: vec![column("a")],
        };
        let plan = parse_calcite_text_plan(
            "LogicalSort(sort0=[$0], dir0=[ASC-nulls-first])\n  LogicalValues(tuples=[[]])",
        )
        .expect("valid text plan");

        let stats = hydrate_rel_from_text_plan(&mut rel, &plan);

        assert_eq!(stats.sort_nodes, 1);
        assert_eq!(stats.hydrated_sort_null_directions, 1);
        let RelExpr::Sort { collation, .. } = rel else {
            panic!("expected sort");
        };
        assert_eq!(collation[0].null_direction, Some(SortNullDirection::First));
    }

    #[test]
    fn hydrates_default_sort_null_direction_from_calcite_short_direction() {
        let mut rel = RelExpr::Sort {
            input: Box::new(RelExpr::Values {
                tuples: ValuesTuples::Rows { rows: Vec::new() },
                output: vec![column("a")],
            }),
            collation: vec![SortKey {
                field_index: 0,
                direction: SortDirection::Ascending,
                null_direction: None,
            }],
            fetch: None,
            offset: None,
            output: vec![column("a")],
        };
        let plan = parse_calcite_text_plan(
            "LogicalSort(sort0=[$0], dir0=[ASC])\n  LogicalValues(tuples=[[]])",
        )
        .expect("valid text plan");

        let stats = hydrate_rel_from_text_plan(&mut rel, &plan);

        assert_eq!(stats.sort_nodes, 1);
        assert_eq!(stats.hydrated_sort_null_directions, 1);
        let RelExpr::Sort { collation, .. } = rel else {
            panic!("expected sort");
        };
        assert_eq!(collation[0].null_direction, Some(SortNullDirection::Last));
    }
}
