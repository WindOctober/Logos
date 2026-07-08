use super::scalar::{
    aggregate_function_is_supported, aggregate_function_name, annotate_literal_term,
    formal_attribute_constructor,
};
use super::*;
use logos_ir::ir::{
    AggregateCall, JoinType, RelExpr, ScalarAst, ScalarExpr, SetOp, SortDirection,
    SortNullDirection, ValuesTuples,
};

impl LoweringContext {
    pub(super) fn lower_list_rel(&mut self, path: &str, rel: &RelExpr) -> Option<FormalListQuery> {
        match rel {
            RelExpr::Sort {
                input,
                collation,
                fetch,
                offset,
                output,
            } => {
                let input_output = input.output();
                if output.len() != input_output.len() {
                    self.error(
                        path,
                        "sort_output_shape_changed",
                        "FormalSQL list lowering expects Sort to preserve its input row arity.",
                    );
                    return None;
                }
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                let mut list_query = FormalListQuery::Bag {
                    input: Box::new(input_query),
                };
                if !collation.is_empty() {
                    let keys = self.lower_sort_keys(path, collation, input_output)?;
                    list_query = FormalListQuery::OrderBy {
                        keys,
                        input: Box::new(list_query),
                    };
                }
                if let Some(offset) = offset {
                    let count = self.lower_row_count(&format!("{path}.offset"), offset)?;
                    list_query = FormalListQuery::Offset {
                        count,
                        input: Box::new(list_query),
                    };
                }
                if let Some(fetch) = fetch {
                    let count = self.lower_row_count(&format!("{path}.fetch"), fetch)?;
                    list_query = FormalListQuery::Fetch {
                        count,
                        input: Box::new(list_query),
                    };
                }
                Some(list_query)
            }
            _ => self.lower_rel(path, rel).map(|query| FormalListQuery::Bag {
                input: Box::new(query),
            }),
        }
    }

    pub(super) fn lower_rel(&mut self, path: &str, rel: &RelExpr) -> Option<FormalQuery> {
        match rel {
            RelExpr::TableScan { table, .. } => Some(FormalQuery::Table {
                relation: table.join("."),
            }),
            RelExpr::Project {
                input,
                exprs,
                output,
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                let input_scope = Scope::from_columns(input.output());
                let select = self.lower_project_select(path, exprs, output, &input_scope)?;
                Some(FormalQuery::Projection {
                    select,
                    input: Box::new(input_query),
                })
            }
            RelExpr::Filter {
                input, predicate, ..
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                let input_scope = Scope::from_columns(input.output());
                let predicate = self.lower_formula(
                    &format!("{path}.predicate"),
                    &predicate.parsed,
                    &input_scope,
                )?;
                Some(FormalQuery::Selection {
                    predicate,
                    input: Box::new(input_query),
                })
            }
            RelExpr::Aggregate {
                input,
                group_keys,
                grouping_sets,
                agg_calls,
                output,
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                let Some(grouping_sets) = grouping_sets else {
                    self.error(
                        path,
                        "grouping_sets_unavailable",
                        "Calcite did not expose grouping-set information; Q_Gamma lowering is not safe.",
                    );
                    return None;
                };
                if grouping_sets.len() != 1 || grouping_sets[0] != *group_keys {
                    self.error(
                        path,
                        "grouping_sets_not_supported",
                        "FormalSQL Q_Gamma has one Group_By list and no grouping sets/rollup/cube encoding.",
                    );
                    return None;
                }
                let input_scope = Scope::from_columns(input.output());
                let group_by = self.lower_group_keys(path, group_keys, &input_scope)?;
                let select =
                    self.lower_aggregate_select(path, group_keys, agg_calls, output, &input_scope)?;
                Some(FormalQuery::Group {
                    select,
                    group_by,
                    having: FormalFormula::True,
                    input: Box::new(input_query),
                })
            }
            RelExpr::Set {
                op,
                all,
                inputs,
                output: _,
            } => self.lower_set(path, *op, *all, inputs),
            RelExpr::Sort { input, fetch, .. } => {
                if let Some(fetch) = fetch {
                    let count = self.lower_row_count(&format!("{path}.fetch"), fetch)?;
                    if count == 0 {
                        let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                        return Some(FormalQuery::Selection {
                            predicate: FormalFormula::False,
                            input: Box::new(input_query),
                        });
                    }
                }
                self.error(
                    path,
                    "sort_limit_offset_not_supported",
                    "FormalSQL bag queries cannot directly encode non-empty ORDER BY, LIMIT, or OFFSET; use list-query lowering.",
                );
                None
            }
            RelExpr::Join {
                left,
                right,
                join_type,
                condition,
                output,
            } => self.lower_join(path, left, right, *join_type, &condition.parsed, output),
            RelExpr::Values { tuples, .. } => {
                match tuples {
                    ValuesTuples::Rows { rows } if rows.is_empty() => {
                        self.error(
                            path,
                            "empty_values_not_encoded",
                            "FormalSQL has Q_Empty_Tuple, but Logos Values with an explicit schema needs a separate encoding before it is safe to lower.",
                        );
                    }
                    ValuesTuples::Rows { .. } => self.error(
                        path,
                        "values_rows_not_supported",
                        "FormalSQL's core query algebra does not provide a VALUES rows constructor.",
                    ),
                    ValuesTuples::UnavailableFromCalcite => self.error(
                        path,
                        "values_tuples_unavailable",
                        "Calcite did not expose VALUES tuples, so the query cannot be lowered soundly.",
                    ),
                }
                None
            }
        }
    }

    fn lower_sort_keys(
        &mut self,
        path: &str,
        collation: &[logos_ir::ir::SortKey],
        output: &[Column],
    ) -> Option<Vec<FormalSortKey>> {
        let mut keys = Vec::with_capacity(collation.len());
        for (index, key) in collation.iter().enumerate() {
            let Some(column) = output.get(key.field_index) else {
                self.error(
                    &format!("{path}.collation[{index}]"),
                    "sort_key_index_out_of_bounds",
                    "Sort key field index is outside the Sort output schema.",
                );
                return None;
            };
            let direction = match key.direction {
                SortDirection::Ascending | SortDirection::StrictlyAscending => {
                    FormalSortDirection::Asc
                }
                SortDirection::Descending | SortDirection::StrictlyDescending => {
                    FormalSortDirection::Desc
                }
                SortDirection::Clustered => {
                    self.error(
                        &format!("{path}.collation[{index}]"),
                        "clustered_sort_not_supported",
                        "FormalSQL list semantics supports ASC/DESC ordering, not Calcite clustered collation.",
                    );
                    return None;
                }
            };
            let Some(null_direction) = key
                .null_direction
                .or_else(|| key.direction.default_null_direction())
            else {
                self.error(
                    &format!("{path}.collation[{index}]"),
                    "sort_null_direction_missing",
                    "FormalSQL list ordering requires explicit NULLS FIRST/LAST semantics.",
                );
                return None;
            };
            let null_direction = match null_direction {
                SortNullDirection::First => FormalNullDirection::First,
                SortNullDirection::Last => FormalNullDirection::Last,
            };
            keys.push(FormalSortKey {
                attribute_name: column.name.clone(),
                attribute_constructor: formal_attribute_constructor(query_attribute_type(column)),
                direction,
                null_direction,
            });
        }
        Some(keys)
    }

    fn lower_row_count(&mut self, path: &str, expr: &ScalarExpr) -> Option<u64> {
        match unsigned_integer_literal_ast(&expr.parsed) {
            Some(value) => Some(value),
            None => {
                self.error(
                    path,
                    "row_count_not_supported",
                    "FormalSQL list lowering currently supports only non-negative integer literal LIMIT/OFFSET counts.",
                );
                None
            }
        }
    }

    fn lower_set(
        &mut self,
        path: &str,
        op: SetOp,
        all: bool,
        inputs: &[RelExpr],
    ) -> Option<FormalQuery> {
        if inputs.len() < 2 {
            self.error(
                path,
                "set_arity_not_supported",
                "FormalSQL Q_Set is binary.",
            );
            return None;
        }
        if !all {
            self.error(
                path,
                "set_distinct_semantics_not_supported",
                "FormalSQL bag set operators model bag multiplicities; SQL DISTINCT set operations need an explicit duplicate-elimination encoding.",
            );
            return None;
        }
        let formal_op = match op {
            SetOp::Union => FormalSetOp::Union,
            SetOp::Intersect => FormalSetOp::Inter,
            SetOp::Except => FormalSetOp::Diff,
        };
        let mut iter = inputs.iter().enumerate();
        let (_, first) = iter.next()?;
        let mut acc = self.lower_rel(&format!("{path}.inputs[0]"), first)?;
        for (index, input) in iter {
            let right = self.lower_rel(&format!("{path}.inputs[{index}]"), input)?;
            acc = FormalQuery::Set {
                op: formal_op,
                left: Box::new(acc),
                right: Box::new(right),
            };
        }
        Some(acc)
    }

    fn lower_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        join_type: JoinType,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQuery> {
        match join_type {
            JoinType::Inner => self.lower_inner_join(path, left, right, condition, output),
            JoinType::Left | JoinType::Right | JoinType::Full => {
                self.lower_outer_join(path, left, right, join_type, condition, output)
            }
            JoinType::Semi | JoinType::Anti => {
                self.lower_existence_join(path, left, right, join_type, condition, output)
            }
        }
    }

    fn lower_inner_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQuery> {
        let left_len = left.output().len();
        if output.len() != left_len + right.output().len() {
            self.error(
                path,
                "join_output_arity_mismatch",
                "Calcite inner join output is expected to contain left columns followed by right columns.",
            );
            return None;
        }
        let (left_output, right_output) = output.split_at(left_len);
        if !is_true_literal(condition) {
            let scope = Scope::from_columns(output);
            let predicate = self.lower_formula(&format!("{path}.condition"), condition, &scope)?;
            let cross_join = self.lower_cross_join(path, left, left_output, right, right_output)?;
            return Some(FormalQuery::Selection {
                predicate,
                input: Box::new(cross_join),
            });
        }
        self.lower_cross_join(path, left, left_output, right, right_output)
    }

    fn lower_outer_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        join_type: JoinType,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQuery> {
        let left_len = left.output().len();
        if output.len() != left_len + right.output().len() {
            self.error(
                path,
                "join_output_arity_mismatch",
                "Calcite outer join output is expected to contain left columns followed by right columns.",
            );
            return None;
        }
        let (left_output, right_output) = output.split_at(left_len);
        if !disjoint_columns(left_output, right_output) {
            self.error(
                path,
                "outer_join_column_overlap",
                "FormalSQL outer join lowering requires unique output attributes before null padding is sound.",
            );
            return None;
        }
        let left = self.lower_join_input(&format!("{path}.left"), left, left_output)?;
        let right = self.lower_join_input(&format!("{path}.right"), right, right_output)?;
        let scope = Scope::from_columns(output);
        let predicate = self.lower_formula(&format!("{path}.condition"), condition, &scope)?;
        let inner = self.theta_join(left.clone(), right.clone(), predicate.clone());
        match join_type {
            JoinType::Left => {
                let unmatched_left =
                    self.anti_join_desugared(left, right, predicate, left_output, right_output);
                let padded_left = FormalQuery::Projection {
                    select: self.outer_join_padding_select(
                        path,
                        left_output,
                        right_output,
                        true,
                    )?,
                    input: Box::new(unmatched_left),
                };
                Some(self.union_all(inner, padded_left))
            }
            JoinType::Right => {
                let unmatched_right =
                    self.anti_join_desugared(right, left, predicate, right_output, left_output);
                let padded_right = FormalQuery::Projection {
                    select: self.outer_join_padding_select(
                        path,
                        left_output,
                        right_output,
                        false,
                    )?,
                    input: Box::new(unmatched_right),
                };
                Some(self.union_all(inner, padded_right))
            }
            JoinType::Full => {
                let unmatched_left = self.anti_join_desugared(
                    left.clone(),
                    right.clone(),
                    predicate.clone(),
                    left_output,
                    right_output,
                );
                let padded_left = FormalQuery::Projection {
                    select: self.outer_join_padding_select(
                        path,
                        left_output,
                        right_output,
                        true,
                    )?,
                    input: Box::new(unmatched_left),
                };
                let unmatched_right =
                    self.anti_join_desugared(right, left, predicate, right_output, left_output);
                let padded_right = FormalQuery::Projection {
                    select: self.outer_join_padding_select(
                        path,
                        left_output,
                        right_output,
                        false,
                    )?,
                    input: Box::new(unmatched_right),
                };
                Some(self.union_all(self.union_all(inner, padded_left), padded_right))
            }
            _ => unreachable!("outer join lowering called with non-outer join type"),
        }
    }

    fn lower_existence_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        join_type: JoinType,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQuery> {
        if output.len() != left.output().len() {
            self.error(
                path,
                "existence_join_output_arity_mismatch",
                "Calcite semi/anti join output is expected to contain only left columns.",
            );
            return None;
        }
        if !disjoint_columns(output, right.output()) {
            self.error(
                path,
                "existence_join_column_overlap",
                "FormalSQL semi/anti join lowering evaluates the predicate over left and right scopes and requires unique attributes.",
            );
            return None;
        }
        let right_output = right.output().to_vec();
        let left = self.lower_join_input(&format!("{path}.left"), left, output)?;
        let right = self.lower_rel(&format!("{path}.right"), right)?;
        let mut predicate_scope_columns = output.to_vec();
        predicate_scope_columns.extend_from_slice(&right_output);
        let scope = Scope::from_columns(&predicate_scope_columns);
        let predicate = self.lower_formula(&format!("{path}.condition"), condition, &scope)?;
        match join_type {
            JoinType::Semi => Some(self.semi_join_desugared(left, right, predicate)),
            JoinType::Anti => {
                Some(self.anti_join_desugared(left, right, predicate, output, &right_output))
            }
            _ => unreachable!("existence join lowering called with non-existence join type"),
        }
    }

    fn theta_join(
        &self,
        left: FormalQuery,
        right: FormalQuery,
        predicate: FormalFormula,
    ) -> FormalQuery {
        let cross_join = FormalQuery::CrossJoin {
            left: Box::new(left),
            right: Box::new(right),
        };
        if matches!(predicate, FormalFormula::True) {
            cross_join
        } else {
            FormalQuery::Selection {
                predicate,
                input: Box::new(cross_join),
            }
        }
    }

    fn semi_join_desugared(
        &self,
        left: FormalQuery,
        right: FormalQuery,
        predicate: FormalFormula,
    ) -> FormalQuery {
        FormalQuery::Selection {
            predicate: FormalFormula::Exists {
                query: Box::new(FormalQuery::Selection {
                    predicate,
                    input: Box::new(right),
                }),
            },
            input: Box::new(left),
        }
    }

    fn anti_join_desugared(
        &self,
        left: FormalQuery,
        right: FormalQuery,
        predicate: FormalFormula,
        _left_output: &[Column],
        _right_output: &[Column],
    ) -> FormalQuery {
        FormalQuery::Selection {
            predicate: FormalFormula::Not {
                formula: Box::new(FormalFormula::Exists {
                    query: Box::new(FormalQuery::Selection {
                        predicate,
                        input: Box::new(right),
                    }),
                }),
            },
            input: Box::new(left),
        }
    }

    fn union_all(&self, left: FormalQuery, right: FormalQuery) -> FormalQuery {
        FormalQuery::Set {
            op: FormalSetOp::UnionMax,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn outer_join_padding_select(
        &mut self,
        path: &str,
        left_output: &[Column],
        right_output: &[Column],
        keep_left: bool,
    ) -> Option<Vec<FormalSelectItem>> {
        let mut select = Vec::with_capacity(left_output.len() + right_output.len());
        for (index, column) in left_output.iter().enumerate() {
            select.push(if keep_left {
                self.identity_select_item(&format!("{path}.leftOutput[{index}]"), column)?
            } else {
                self.null_select_item(&format!("{path}.leftOutput[{index}]"), column)?
            });
        }
        for (index, column) in right_output.iter().enumerate() {
            select.push(if keep_left {
                self.null_select_item(&format!("{path}.rightOutput[{index}]"), column)?
            } else {
                self.identity_select_item(&format!("{path}.rightOutput[{index}]"), column)?
            });
        }
        Some(select)
    }

    fn identity_select_item(&mut self, path: &str, column: &Column) -> Option<FormalSelectItem> {
        let attr_ty = query_attribute_type(column);
        Some(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: column.name.clone(),
                    constructor: formal_attribute_constructor(attr_ty),
                },
            },
            alias: column.name.clone(),
            alias_constructor: self.lower_query_attribute_constructor(path, column)?,
        })
    }

    fn null_select_item(&mut self, path: &str, column: &Column) -> Option<FormalSelectItem> {
        Some(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "NULL".to_owned(),
                    ty: Some(query_attribute_type(column)),
                },
            },
            alias: column.name.clone(),
            alias_constructor: self.lower_query_attribute_constructor(path, column)?,
        })
    }

    fn lower_cross_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        left_output: &[Column],
        right: &RelExpr,
        right_output: &[Column],
    ) -> Option<FormalQuery> {
        if !disjoint_columns(left_output, right_output) {
            self.error(
                path,
                "cross_join_column_overlap",
                "Calcite join output still contains overlapping names; FormalSQL tuples are keyed by attribute sets and need unique attributes.",
            );
            return None;
        }
        let left = self.lower_join_input(&format!("{path}.left"), left, left_output)?;
        let right = self.lower_join_input(&format!("{path}.right"), right, right_output)?;
        Some(FormalQuery::CrossJoin {
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    fn lower_join_input(
        &mut self,
        path: &str,
        rel: &RelExpr,
        join_output: &[Column],
    ) -> Option<FormalQuery> {
        let input_output = rel.output();
        if input_output.len() != join_output.len() {
            self.error(
                path,
                "join_input_output_arity_mismatch",
                "Calcite join output slice does not match child output arity.",
            );
            return None;
        }
        let input = self.lower_rel(path, rel)?;
        if input_output
            .iter()
            .zip(join_output)
            .all(|(input_column, output_column)| {
                input_column.name == output_column.name
                    && input_column.ty == output_column.ty
                    && input_column.precision == output_column.precision
            })
        {
            return Some(input);
        }
        let select = self.lower_join_rename_select(path, input_output, join_output)?;
        Some(FormalQuery::Projection {
            select,
            input: Box::new(input),
        })
    }

    fn lower_join_rename_select(
        &mut self,
        path: &str,
        input_output: &[Column],
        join_output: &[Column],
    ) -> Option<Vec<FormalSelectItem>> {
        if !has_unique_column_names(join_output) {
            self.error(
                path,
                "duplicate_join_alias",
                "FormalSQL projection requires distinct aliases when aligning Calcite join output names.",
            );
            return None;
        }
        input_output
            .iter()
            .zip(join_output)
            .enumerate()
            .map(|(index, (input_column, output_column))| {
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: input_column.name.clone(),
                            constructor: formal_attribute_constructor(query_attribute_type(
                                input_column,
                            )),
                        },
                    },
                    alias: output_column.name.clone(),
                    alias_constructor: self.lower_query_attribute_constructor(
                        &format!("{path}.output[{index}]"),
                        output_column,
                    )?,
                })
            })
            .collect()
    }

    fn lower_project_select(
        &mut self,
        path: &str,
        exprs: &[logos_ir::ir::ScalarExpr],
        output: &[Column],
        scope: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        if !has_unique_column_names(output) {
            self.error(
                path,
                "duplicate_projection_alias",
                "FormalSQL projection requires distinct output attributes for well-formed select lists.",
            );
            return None;
        }
        if exprs.len() != output.len() {
            self.error(
                path,
                "project_arity_mismatch",
                "Project expression count does not match output column count.",
            );
            return None;
        }
        exprs
            .iter()
            .zip(output)
            .enumerate()
            .map(|(index, (expr, column))| {
                let lowered = self.lower_aggregate_term(
                    &format!("{path}.exprs[{index}]"),
                    &expr.parsed,
                    scope,
                )?;
                let lowered = annotate_literal_term(lowered, query_attribute_type(column));
                Some(FormalSelectItem {
                    expr: lowered,
                    alias: column.name.clone(),
                    alias_constructor: self.lower_query_attribute_constructor(
                        &format!("{path}.output[{index}]"),
                        column,
                    )?,
                })
            })
            .collect()
    }

    fn lower_group_keys(
        &mut self,
        path: &str,
        group_keys: &[usize],
        scope: &Scope,
    ) -> Option<Vec<FormalAggregateTerm>> {
        group_keys
            .iter()
            .enumerate()
            .map(|(index, key)| {
                let attr = scope.attribute(*key).or_else(|| {
                    self.error(
                        &format!("{path}.groupKeys[{index}]"),
                        "input_ref_out_of_range",
                        "Aggregate group key does not reference an input column.",
                    );
                    None
                })?;
                Some(FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attr.name,
                        constructor: attr.constructor,
                    },
                })
            })
            .collect()
    }

    fn lower_aggregate_select(
        &mut self,
        path: &str,
        group_keys: &[usize],
        agg_calls: &[AggregateCall],
        output: &[Column],
        scope: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        if !has_unique_column_names(output) {
            self.error(
                path,
                "duplicate_aggregate_alias",
                "FormalSQL Q_Gamma select list requires distinct output attributes.",
            );
            return None;
        }
        if output.len() != group_keys.len() + agg_calls.len() {
            self.error(
                path,
                "aggregate_output_arity_mismatch",
                "Aggregate output is expected to contain group keys followed by aggregate calls.",
            );
            return None;
        }
        let mut select = Vec::new();
        for (index, key) in group_keys.iter().enumerate() {
            let attr = scope.attribute(*key).or_else(|| {
                self.error(
                    &format!("{path}.groupKeys[{index}]"),
                    "input_ref_out_of_range",
                    "Aggregate group key does not reference an input column.",
                );
                None
            })?;
            select.push(FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attr.name,
                        constructor: attr.constructor,
                    },
                },
                alias: output[index].name.clone(),
                alias_constructor: self.lower_query_attribute_constructor(
                    &format!("{path}.output[{index}]"),
                    &output[index],
                )?,
            });
        }
        for (index, call) in agg_calls.iter().enumerate() {
            let output_index = group_keys.len() + index;
            select.push(FormalSelectItem {
                expr: self.lower_aggregate_call(path, index, call, scope)?,
                alias: output[output_index].name.clone(),
                alias_constructor: self.lower_query_attribute_constructor(
                    &format!("{path}.output[{output_index}]"),
                    &output[output_index],
                )?,
            });
        }
        Some(select)
    }

    fn lower_aggregate_call(
        &mut self,
        path: &str,
        index: usize,
        call: &AggregateCall,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        let call_path = format!("{path}.aggCalls[{index}]");
        if call.distinct {
            self.error(
                &call_path,
                "distinct_aggregate_not_supported",
                "FormalSQL A_agg has no DISTINCT aggregate flag.",
            );
            return None;
        }
        if call.filter.is_some() {
            self.error(
                &call_path,
                "filtered_aggregate_not_supported",
                "FormalSQL A_agg has no FILTER clause.",
            );
            return None;
        }
        if !call.modifiers.is_empty() {
            self.error(
                &call_path,
                "aggregate_modifier_not_supported",
                "FormalSQL aggregate lowering does not support approximate aggregates, IGNORE NULLS, DISTINCT keys, or aggregate-local ORDER BY.",
            );
            return None;
        }
        if call.args.is_empty() && call.function.eq_ignore_ascii_case("COUNT") {
            self.warning(
                &call_path,
                "count_star_argument_encoded",
                "Calcite COUNT(*) has no scalar argument; this lowering uses a constant argument and relies on the Rocq aggregate interpretation to treat it as COUNT(*).",
            );
            return Some(FormalAggregateTerm::Aggregate {
                function: aggregate_function_name(&call.function),
                arg: FormalFunctionTerm::Constant {
                    raw: "1".to_owned(),
                    ty: Some(FormalAttributeType::Z),
                },
            });
        }
        if call.args.len() != 1 {
            self.error(
                &call_path,
                "aggregate_argument_arity_not_supported",
                "FormalSQL A_agg expects one function term argument in this lowering.",
            );
            return None;
        }
        if !aggregate_function_is_supported(&call.function) {
            self.warning(
                &call_path,
                "aggregate_interpretation_required",
                "Lowered SQL aggregate requires a matching FormalSQL Tuple.aggregate interpretation in Rocq.",
            );
        }
        Some(FormalAggregateTerm::Aggregate {
            function: aggregate_function_name(&call.function),
            arg: self.lower_function_term(
                &format!("{call_path}.arg"),
                &call.args[0].parsed,
                scope,
            )?,
        })
    }
}

fn unsigned_integer_literal_ast(ast: &ScalarAst) -> Option<u64> {
    match ast {
        ScalarAst::Literal { raw } => parse_unsigned_integer_literal(raw),
        ScalarAst::TypeAnnotation { expr, .. } => unsigned_integer_literal_ast(expr),
        _ => None,
    }
}

fn parse_unsigned_integer_literal(raw: &str) -> Option<u64> {
    let value = raw.trim();
    if value.is_empty() || value.starts_with('-') {
        return None;
    }
    let value = value.strip_prefix('+').unwrap_or(value);
    if value.chars().all(|ch| ch.is_ascii_digit()) {
        value.parse().ok()
    } else {
        None
    }
}
