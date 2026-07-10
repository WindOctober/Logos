use super::scalar::{
    aggregate_function_is_supported, aggregate_function_name_for_type, annotate_literal_term,
};
use super::*;
use logos_ir::ir::{
    AggregateCall, JoinType, RelExpr, ScalarAst, ScalarExpr, SetOp, SortDirection,
    SortNullDirection, SqlType, ValuesTuples,
};

#[derive(Debug, Clone)]
struct FormalValuesColumn {
    name: String,
    ty: FormalAttributeType,
}

#[derive(Debug, Clone)]
struct ValuesCell {
    raw: String,
    ty: Option<FormalAttributeType>,
}

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
                let mut list_query = self.lower_list_rel(&format!("{path}.input"), input)?;
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
            _ => self.lower_rel(path, rel).map(query_to_list_query),
        }
    }

    pub(super) fn lower_rel(&mut self, path: &str, rel: &RelExpr) -> Option<FormalQuery> {
        match rel {
            RelExpr::TableScan { table, output } => {
                self.lower_scope(&format!("{path}.output"), output)?;
                Some(FormalQuery::Table {
                    relation: table.join("."),
                })
            }
            RelExpr::Project {
                input,
                exprs,
                correlations,
                output,
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                if matches!(input_query, FormalQuery::Empty { .. }) {
                    return self.empty_query_from_output(&format!("{path}.output"), output);
                }
                let (input_query, input_output, correlations) = self.prepare_correlated_input(
                    &format!("{path}.correlations"),
                    input_query,
                    input.output(),
                    correlations,
                )?;
                let input_scope = self.lower_scope(&format!("{path}.inputScope"), &input_output)?;
                let select = self.with_correlation_scopes(&correlations, |context| {
                    context.lower_project_select(path, exprs, output, &input_scope)
                })?;
                Some(FormalQuery::Projection {
                    select,
                    input: Box::new(input_query),
                })
            }
            RelExpr::Filter {
                input,
                predicate,
                correlations,
                output,
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                if matches!(input_query, FormalQuery::Empty { .. }) {
                    return self.empty_query_from_output(&format!("{path}.output"), output);
                }
                let (predicate_input, predicate_output, correlations) = self
                    .prepare_correlated_input(
                        &format!("{path}.correlations"),
                        input_query,
                        input.output(),
                        correlations,
                    )?;
                let input_scope =
                    self.lower_scope(&format!("{path}.predicateScope"), &predicate_output)?;
                let predicate = self.with_correlation_scopes(&correlations, |context| {
                    context.lower_formula(
                        &format!("{path}.predicate"),
                        &predicate.parsed,
                        &input_scope,
                    )
                })?;
                let selection = FormalQuery::Selection {
                    predicate,
                    input: Box::new(predicate_input),
                };
                if correlations.is_empty() {
                    Some(selection)
                } else {
                    Some(FormalQuery::Projection {
                        select: self.lower_join_rename_select(
                            &format!("{path}.output"),
                            &predicate_output,
                            input.output(),
                        )?,
                        input: Box::new(selection),
                    })
                }
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
                let input_scope =
                    self.lower_scope(&format!("{path}.inputScope"), input.output())?;
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
                output,
            } => self.lower_set(path, *op, *all, inputs, output),
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
                correlations,
                output,
            } => self.with_correlations(correlations, |context| {
                context.lower_join(path, left, right, *join_type, &condition.parsed, output)
            }),
            RelExpr::Values { tuples, output } => match tuples {
                ValuesTuples::Rows { rows } => self.lower_values_query(path, rows, output),
                ValuesTuples::UnavailableFromCalcite => {
                    self.error(
                        path,
                        "values_tuples_unavailable",
                        "Calcite did not expose VALUES tuples, so the query cannot be lowered soundly.",
                    );
                    None
                }
            },
        }
    }

    fn lower_values_query(
        &mut self,
        path: &str,
        rows: &[Vec<ScalarExpr>],
        output: &[Column],
    ) -> Option<FormalQuery> {
        self.ensure_values_output_schema(path, output)?;
        let cells = self.lower_values_cells(path, rows, output)?;
        let columns = self.lower_values_columns(path, output, &cells)?;
        let rows = self.type_values_rows(path, &cells, &columns)?;
        if cells.is_empty() {
            return Some(FormalQuery::Empty {
                columns: columns
                    .iter()
                    .map(|column| FormalAttribute {
                        name: column.name.clone(),
                        ty: column.ty,
                    })
                    .collect(),
            });
        }

        let mut queries = rows
            .iter()
            .enumerate()
            .map(|(index, row)| {
                self.values_singleton_query(&format!("{path}.rows[{index}]"), row, &columns)
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter();
        let first = queries.next()?;
        Some(queries.fold(first, |left, right| FormalQuery::Set {
            op: FormalSetOp::Union,
            left: Box::new(left),
            right: Box::new(right),
        }))
    }

    fn empty_query_from_output(&mut self, path: &str, output: &[Column]) -> Option<FormalQuery> {
        if !has_unique_column_names(output) {
            self.error(
                path,
                "duplicate_empty_alias",
                "FormalSQL empty relation output requires distinct aliases.",
            );
            return None;
        }
        let columns = output
            .iter()
            .enumerate()
            .map(|(index, column)| {
                Some(FormalAttribute {
                    name: column.name.clone(),
                    ty: self.empty_output_attribute_type(&format!("{path}[{index}]"), column)?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQuery::Empty { columns })
    }

    fn empty_output_attribute_type(
        &mut self,
        path: &str,
        column: &Column,
    ) -> Option<FormalAttributeType> {
        match column.ty {
            SqlType::Null => Some(self.unresolved_null_fallback_type(path)),
            _ => self.lower_attribute_type(path, column, AttributeTypeContext::QueryOutput),
        }
    }

    fn values_singleton_query(
        &mut self,
        path: &str,
        row: &[FormalValueLiteral],
        columns: &[FormalValuesColumn],
    ) -> Option<FormalQuery> {
        if row.len() != columns.len() {
            self.error(
                path,
                "values_row_arity_mismatch",
                "VALUES row arity does not match the output schema.",
            );
            return None;
        }
        let select = row
            .iter()
            .zip(columns.iter())
            .map(|(literal, column)| {
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Constant {
                            raw: literal.raw.clone(),
                            ty: Some(literal.ty),
                        },
                    },
                    alias: column.name.clone(),
                    alias_ty: column.ty,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQuery::Projection {
            select,
            input: Box::new(FormalQuery::EmptyTuple),
        })
    }

    fn lower_values_cells(
        &mut self,
        path: &str,
        rows: &[Vec<ScalarExpr>],
        output: &[Column],
    ) -> Option<Vec<Vec<ValuesCell>>> {
        rows.iter()
            .enumerate()
            .map(|(row_index, row)| {
                if row.len() != output.len() {
                    self.error(
                        &format!("{path}.rows[{row_index}]"),
                        "values_row_arity_mismatch",
                        "VALUES row arity does not match the output schema.",
                    );
                    return None;
                }
                row.iter()
                    .enumerate()
                    .map(|(column_index, expr)| {
                        self.lower_values_cell(
                            &format!("{path}.rows[{row_index}][{column_index}]"),
                            expr,
                        )
                    })
                    .collect()
            })
            .collect()
    }

    fn lower_values_cell(&mut self, path: &str, expr: &ScalarExpr) -> Option<ValuesCell> {
        let scope = Scope {
            attributes: Vec::new(),
        };
        let ast = &expr.parsed;
        let term = self.lower_function_term(path, ast, &scope)?;
        match term {
            FormalFunctionTerm::Constant {
                raw,
                ty: constant_ty,
            } => Some(ValuesCell {
                raw,
                ty: constant_ty,
            }),
            _ => {
                self.error(
                    path,
                    "values_expression_not_supported",
                    "VALUES lowering currently supports literal cells only.",
                );
                None
            }
        }
    }

    fn lower_values_columns(
        &mut self,
        path: &str,
        output: &[Column],
        rows: &[Vec<ValuesCell>],
    ) -> Option<Vec<FormalValuesColumn>> {
        output
            .iter()
            .enumerate()
            .map(|(index, column)| {
                let column_path = format!("{path}.output[{index}]");
                let ty = match self.values_output_type(&column_path, column)? {
                    Some(ty) => ty,
                    None => self.infer_values_column_type(&column_path, index, rows)?,
                };
                Some(FormalValuesColumn {
                    name: column.name.clone(),
                    ty,
                })
            })
            .collect()
    }

    fn values_output_type(
        &mut self,
        path: &str,
        column: &Column,
    ) -> Option<Option<FormalAttributeType>> {
        match &column.ty {
            SqlType::Any | SqlType::Null => Some(None),
            _ => self
                .lower_attribute_type(path, column, AttributeTypeContext::QueryInput)
                .map(Some),
        }
    }

    fn infer_values_column_type(
        &mut self,
        path: &str,
        column_index: usize,
        rows: &[Vec<ValuesCell>],
    ) -> Option<FormalAttributeType> {
        let mut inferred = None;
        for row in rows {
            let Some(cell) = row.get(column_index) else {
                self.error(
                    path,
                    "values_row_arity_mismatch",
                    "VALUES row arity does not match the output schema.",
                );
                return None;
            };
            let Some(cell_ty) = cell.ty else {
                continue;
            };
            match inferred {
                Some(existing) if !attribute_types_compatible_for_values(existing, cell_ty) => {
                    self.error(
                        path,
                        "values_column_type_conflict",
                        "VALUES column has no concrete output type and contains literals with incompatible inferred types.",
                    );
                    return None;
                }
                Some(_) => {}
                None => inferred = Some(cell_ty),
            }
        }
        inferred.or_else(|| {
            self.warning(
                path,
                "values_null_type_defaulted_to_integer",
                "VALUES NULL column has no concrete output type and no non-NULL typed literal from which FormalSQL can infer one. Logos defaults it to INTEGER as a fallback; this is sound only when the unresolved NULL is semantically unobservable, e.g. inside an empty relation.",
            );
            Some(FormalAttributeType::Z)
        })
    }

    fn type_values_rows(
        &mut self,
        path: &str,
        rows: &[Vec<ValuesCell>],
        columns: &[FormalValuesColumn],
    ) -> Option<Vec<Vec<FormalValueLiteral>>> {
        rows.iter()
            .enumerate()
            .map(|(row_index, row)| {
                if row.len() != columns.len() {
                    self.error(
                        &format!("{path}.rows[{row_index}]"),
                        "values_row_arity_mismatch",
                        "VALUES row arity does not match the output schema.",
                    );
                    return None;
                }
                row.iter()
                    .zip(columns.iter())
                    .enumerate()
                    .map(|(column_index, (cell, column))| {
                        if let Some(cell_ty) = cell.ty
                            && !attribute_types_compatible_for_values(cell_ty, column.ty)
                        {
                            self.error(
                                &format!("{path}.rows[{row_index}][{column_index}]"),
                                "values_literal_type_mismatch",
                                "VALUES literal type does not match the output column type.",
                            );
                            return None;
                        }
                        self.validate_literal_for_output_type(
                            &format!("{path}.rows[{row_index}][{column_index}]"),
                            &cell.raw,
                            column.ty,
                        )?;
                        Some(FormalValueLiteral {
                            raw: cell.raw.clone(),
                            ty: column.ty,
                        })
                    })
                    .collect()
            })
            .collect()
    }

    fn ensure_values_output_schema(&mut self, path: &str, output: &[Column]) -> Option<()> {
        if !has_unique_column_names(output) {
            self.error(
                path,
                "duplicate_values_alias",
                "FormalSQL tuple labels are finite sets; VALUES output column names must be unique.",
            );
            return None;
        }
        Some(())
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
                attribute_ty: self.lower_attribute_type(
                    &format!("{path}.collation[{index}].field"),
                    column,
                    AttributeTypeContext::QueryInput,
                )?,
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
        output: &[Column],
    ) -> Option<FormalQuery> {
        if inputs.len() < 2 {
            self.error(
                path,
                "set_arity_not_supported",
                "FormalSQL Q_Set is binary.",
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
        // SQL EXCEPT DISTINCT is delta(left) - delta(right), not
        // delta(left - right): {x,x} EXCEPT {x} must be empty.
        if !all && matches!(op, SetOp::Except) {
            acc = self.distinct_query(&format!("{path}.inputs[0].distinct"), acc, output)?;
        }
        for (index, input) in iter {
            let mut right = self.lower_rel(&format!("{path}.inputs[{index}]"), input)?;
            if !all && matches!(op, SetOp::Except) {
                right = self.distinct_query(
                    &format!("{path}.inputs[{index}].distinct"),
                    right,
                    output,
                )?;
            }
            acc = FormalQuery::Set {
                op: formal_op,
                left: Box::new(acc),
                right: Box::new(right),
            };
        }
        if !all && !matches!(op, SetOp::Except) {
            acc = self.distinct_query(&format!("{path}.distinct"), acc, output)?;
        }
        Some(acc)
    }

    fn distinct_query(
        &mut self,
        path: &str,
        input: FormalQuery,
        output: &[Column],
    ) -> Option<FormalQuery> {
        if !has_unique_column_names(output) {
            self.error(
                path,
                "set_distinct_duplicate_output_name",
                "FormalSQL duplicate elimination needs unique output attributes.",
            );
            return None;
        }

        let scope = self.lower_scope(&format!("{path}.scope"), output)?;
        let group_by = (0..output.len())
            .map(|index| {
                let attr = scope.attribute(index)?;
                Some(FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attr.name,
                        ty: attr.formal_ty,
                    },
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let select = output
            .iter()
            .enumerate()
            .map(|(index, column)| {
                self.identity_select_item(&format!("{path}.select[{index}]"), column)
            })
            .collect::<Option<Vec<_>>>()?;

        Some(FormalQuery::Group {
            select,
            group_by,
            having: FormalFormula::True,
            input: Box::new(input),
        })
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
            let scope = self.lower_scope(&format!("{path}.conditionScope"), output)?;
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
        let scope = self.lower_scope(&format!("{path}.conditionScope"), output)?;
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
        let scope =
            self.lower_scope(&format!("{path}.conditionScope"), &predicate_scope_columns)?;
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
            op: FormalSetOp::Union,
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
        let attr_ty = self.lower_attribute_type(path, column, AttributeTypeContext::QueryOutput)?;
        Some(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: column.name.clone(),
                    ty: attr_ty,
                },
            },
            alias: column.name.clone(),
            alias_ty: attr_ty,
        })
    }

    fn null_select_item(&mut self, path: &str, column: &Column) -> Option<FormalSelectItem> {
        let attr_ty = self.lower_attribute_type(path, column, AttributeTypeContext::QueryOutput)?;
        Some(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "NULL".to_owned(),
                    ty: Some(attr_ty),
                },
            },
            alias: column.name.clone(),
            alias_ty: attr_ty,
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
        self.lower_scope(&format!("{path}.inputOutput"), input_output)?;
        self.lower_scope(&format!("{path}.joinOutput"), join_output)?;
        let input = self.lower_rel(path, rel)?;
        if input_output
            .iter()
            .zip(join_output)
            .all(|(input_column, output_column)| {
                input_column.name == output_column.name && input_column.ty == output_column.ty
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

    fn prepare_correlated_input(
        &mut self,
        path: &str,
        input: FormalQuery,
        input_output: &[Column],
        correlations: &[logos_ir::ir::CorrelationBinding],
    ) -> Option<(FormalQuery, Vec<Column>, Vec<CorrelationScope>)> {
        if correlations.is_empty() {
            return Some((input, input_output.to_vec(), Vec::new()));
        }
        if correlations
            .iter()
            .any(|binding| binding.output.len() != input_output.len())
        {
            self.error(
                path,
                "correlation_binding_arity_mismatch",
                "Calcite correlation row type does not match the relational input it is expected to bind.",
            );
            return None;
        }
        let renamed = input_output
            .iter()
            .enumerate()
            .map(|(index, column)| Column {
                name: format!(
                    "__logos_cor_{}_{}",
                    sanitize_correlation_name(&correlations[0].correlation),
                    index
                ),
                ty: column.ty.clone(),
                nullable: column.nullable,
            })
            .collect::<Vec<_>>();
        if !has_unique_column_names(&renamed)
            || renamed.iter().any(|fresh| {
                input_output.iter().any(|column| column.name == fresh.name)
                    || self.correlations.iter().any(|scope| {
                        scope
                            .scope
                            .attributes
                            .iter()
                            .any(|attribute| attribute.name == fresh.name)
                    })
            })
        {
            self.error(
                path,
                "correlation_fresh_name_collision",
                "Generated correlation-safe attribute name collides with an existing attribute.",
            );
            return None;
        }
        let select = self.lower_join_rename_select(path, input_output, &renamed)?;
        let renamed_input = FormalQuery::Projection {
            select,
            input: Box::new(input),
        };
        let renamed_correlations = correlations
            .iter()
            .enumerate()
            .map(|(index, binding)| {
                Some(CorrelationScope {
                    correlation: binding.correlation.clone(),
                    scope: self
                        .lower_scope(&format!("{path}.correlations[{index}].renamed"), &renamed)?,
                    field_names: binding
                        .output
                        .iter()
                        .map(|column| column.name.clone())
                        .collect(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some((renamed_input, renamed, renamed_correlations))
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
                            ty: self.lower_attribute_type(
                                &format!("{path}.input[{index}]"),
                                input_column,
                                AttributeTypeContext::QueryInput,
                            )?,
                        },
                    },
                    alias: output_column.name.clone(),
                    alias_ty: self.lower_attribute_type(
                        &format!("{path}.output[{index}]"),
                        output_column,
                        AttributeTypeContext::QueryOutput,
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
                let output_ty = self.lower_attribute_type(
                    &format!("{path}.output[{index}]"),
                    column,
                    AttributeTypeContext::QueryOutput,
                )?;
                if matches!(output_ty, FormalAttributeType::Decimal { .. })
                    && aggregate_term_contains_bare_decimal_division(&lowered)
                {
                    self.error(
                        &format!("{path}.exprs[{index}]"),
                        "decimal_division_output_typmod_not_supported",
                        "Bare PostgreSQL NUMERIC division returns an unconstrained numeric value; projecting it into a fixed DECIMAL(p,s) output requires an explicit CAST.",
                    );
                    return None;
                }
                if let FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant { raw, ty: None },
                } = &lowered
                {
                    if matches!(
                        output_ty,
                        FormalAttributeType::Float | FormalAttributeType::Double
                    ) && !raw.eq_ignore_ascii_case("null")
                        && super::emit::float_literal_bits_for_type(raw, Some(&output_ty)).is_none()
                    {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "float_literal_not_supported",
                            "FormalSQL lowering supports FLOAT/DOUBLE literals only for finite SQL numeric literals that fit the target floating-point type.",
                        );
                        return None;
                    }
                    if matches!(output_ty, FormalAttributeType::Decimal { .. })
                        && !raw.eq_ignore_ascii_case("null")
                        && super::emit::decimal_literal_for_type(raw, Some(&output_ty)).is_none()
                    {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "decimal_literal_not_supported",
                            "FormalSQL DECIMAL lowering supports fixed-scale decimal literals only when coercion to the output DECIMAL(p,s) succeeds without precision overflow.",
                        );
                        return None;
                    }
                    if !raw.eq_ignore_ascii_case("null") {
                        self.validate_literal_for_output_type(
                            &format!("{path}.exprs[{index}]"),
                            raw,
                            output_ty,
                        )?;
                    }
                }
                if let Some(expr_ty) = self.direct_function_type(
                    &format!("{path}.exprs[{index}].type"),
                    &expr.parsed,
                    scope,
                )
                {
                    if floating_output_type_mismatch(&expr_ty, &output_ty) {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "floating_output_type_not_supported",
                            "Projected FLOAT/DOUBLE expression type differs from the output column type; implicit floating casts are not modeled yet.",
                        );
                        return None;
                    }
                    if decimal_typmod_mismatch(&expr_ty, &output_ty) {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "decimal_output_typmod_not_supported",
                            "Projected DECIMAL expression typmod differs from the output column typmod; explicit rounding/cast semantics are not modeled yet.",
                        );
                        return None;
                    }
                }
                let lowered = annotate_literal_term(lowered, output_ty);
                Some(FormalSelectItem {
                    expr: lowered,
                    alias: column.name.clone(),
                    alias_ty: output_ty,
                })
            })
            .collect()
    }

    fn validate_literal_for_output_type(
        &mut self,
        path: &str,
        raw: &str,
        output_ty: FormalAttributeType,
    ) -> Option<()> {
        if raw.eq_ignore_ascii_case("null") {
            return Some(());
        }
        match output_ty {
            FormalAttributeType::Date if !super::emit::date_literal_conforms_to_day(raw) => {
                self.error(
                    path,
                    "date_literal_not_supported",
                    "FormalSQL DATE lowering requires a valid canonical date literal or encoded day value.",
                );
                None
            }
            FormalAttributeType::Time if !super::emit::time_literal_conforms_to_day(raw) => {
                self.error(
                    path,
                    "time_literal_not_supported",
                    "FormalSQL TIME lowering requires a valid time-of-day literal or encoded microsecond value.",
                );
                None
            }
            FormalAttributeType::Timestamp { precision }
                if !super::emit::timestamp_literal_conforms_to_precision(
                    raw,
                    timestamp_precision(precision),
                ) =>
            {
                self.error(
                    path,
                    "timestamp_literal_not_supported",
                    "FormalSQL TIMESTAMP lowering requires a valid timestamp literal within the target precision.",
                );
                None
            }
            _ => Some(()),
        }
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
                        ty: attr.formal_ty,
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
            let output_ty = self.lower_attribute_type(
                &format!("{path}.output[{index}]"),
                &output[index],
                AttributeTypeContext::QueryOutput,
            )?;
            if floating_output_type_mismatch(&attr.formal_ty, &output_ty) {
                self.error(
                    &format!("{path}.groupKeys[{index}]"),
                    "floating_output_type_not_supported",
                    "Aggregate group key FLOAT/DOUBLE type differs from the output column type; implicit floating casts are not modeled yet.",
                );
                return None;
            }
            if decimal_typmod_mismatch(&attr.formal_ty, &output_ty) {
                self.error(
                    &format!("{path}.groupKeys[{index}]"),
                    "decimal_output_typmod_not_supported",
                    "Aggregate group key DECIMAL typmod differs from the output column typmod; explicit rounding/cast semantics are not modeled yet.",
                );
                return None;
            }
            select.push(FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attr.name,
                        ty: attr.formal_ty,
                    },
                },
                alias: output[index].name.clone(),
                alias_ty: output_ty,
            });
        }
        for (index, call) in agg_calls.iter().enumerate() {
            let output_index = group_keys.len() + index;
            let output_ty = self.lower_attribute_type(
                &format!("{path}.output[{output_index}]"),
                &output[output_index],
                AttributeTypeContext::QueryOutput,
            )?;
            select.push(FormalSelectItem {
                expr: self.lower_aggregate_call(path, index, call, scope, &output_ty)?,
                alias: output[output_index].name.clone(),
                alias_ty: output_ty,
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
        output_ty: &FormalAttributeType,
    ) -> Option<FormalAggregateTerm> {
        let call_path = format!("{path}.aggCalls[{index}]");
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
            if call.distinct {
                self.error(
                    &call_path,
                    "count_star_distinct_not_supported",
                    "COUNT(DISTINCT *) is not a modeled aggregate form.",
                );
                return None;
            }
            if output_ty != &FormalAttributeType::Z {
                self.error(
                    &call_path,
                    "aggregate_output_type_not_supported",
                    "COUNT(*) returns an integer count in the current FormalSQL model.",
                );
                return None;
            }
            return Some(FormalAggregateTerm::CountStar);
        }
        if call.args.len() != 1 {
            self.error(
                &call_path,
                "aggregate_argument_arity_not_supported",
                "FormalSQL A_agg expects one function term argument in this lowering.",
            );
            return None;
        }
        if !call.distinct && aggregate_name_uses_reserved_logos_namespace(&call.function) {
            self.error(
                &call_path,
                "reserved_aggregate_symbol_not_supported",
                "Aggregate names in the __logos_distinct_aggregate_ namespace are reserved for internal DISTINCT aggregate lowering.",
            );
            return None;
        }
        if !aggregate_function_is_supported(&call.function) {
            if call.distinct {
                self.error(
                    &call_path,
                    "distinct_aggregate_function_not_supported",
                    "DISTINCT aggregate lowering is currently limited to COUNT, SUM, MAX, MIN, and AVG because only these aggregate interpretations are modeled in FormalSQL.",
                );
                return None;
            }
            self.warning(
                &call_path,
                "aggregate_interpretation_required",
                "Lowered SQL aggregate requires a matching FormalSQL Tuple.aggregate interpretation in Rocq.",
            );
        }
        let arg_path = format!("{call_path}.arg");
        let arg_ty = self
            .direct_function_type(&arg_path, &call.args[0].parsed, scope)
            .or_else(|| self.infer_function_type(&arg_path, &call.args[0].parsed, scope));
        if call.function.eq_ignore_ascii_case("COUNT") {
            if output_ty != &FormalAttributeType::Z {
                self.error(
                    &call_path,
                    "aggregate_output_type_not_supported",
                    "COUNT(expr) returns an integer count in the current FormalSQL model.",
                );
                return None;
            }
        } else if aggregate_result_follows_argument_type(&call.function) {
            if let Some(arg_ty) = arg_ty.as_ref() {
                if floating_output_type_mismatch(arg_ty, output_ty) {
                    self.error(
                        &call_path,
                        "floating_aggregate_output_type_not_supported",
                        "FLOAT/DOUBLE aggregate output type must match the modeled aggregate argument/result type; implicit floating aggregate casts are not modeled yet.",
                    );
                    return None;
                }
            } else if matches!(
                output_ty,
                FormalAttributeType::Float | FormalAttributeType::Double
            ) {
                self.error(
                    &call_path,
                    "floating_aggregate_argument_type_not_supported",
                    "FLOAT/DOUBLE aggregate lowering requires an argument with a known modeled floating type.",
                );
                return None;
            }
        }
        if call.function.eq_ignore_ascii_case("AVG") || call.function.eq_ignore_ascii_case("SUM") {
            if matches!(arg_ty, Some(FormalAttributeType::Decimal { .. })) {
                self.error(
                    &call_path,
                    "decimal_aggregate_unconstrained_numeric_not_supported",
                    "PostgreSQL SUM/AVG(NUMERIC) returns unconstrained NUMERIC; FormalSQL currently models only fixed-scale DECIMAL aggregate results.",
                );
                return None;
            }
        }
        if matches!(call.function.to_ascii_lowercase().as_str(), "max" | "min")
            && matches!(arg_ty, Some(FormalAttributeType::Decimal { .. }))
            && arg_ty.as_ref() != Some(output_ty)
        {
            self.error(
                &call_path,
                "decimal_output_typmod_not_supported",
                "Decimal MIN/MAX returns a value with the input DECIMAL typmod; output typmod coercion is not modeled yet.",
            );
            return None;
        }
        let function =
            aggregate_function_name_for_type(&call.function, arg_ty.as_ref()).or_else(|| {
                self.error(
                    &call_path,
                    "decimal_aggregate_not_supported",
                    "This DECIMAL aggregate is outside the currently modeled FormalSQL Decimal subset.",
                );
                None
            })?;
        let arg = self.lower_function_term(&arg_path, &call.args[0].parsed, scope)?;
        if call.distinct {
            Some(FormalAggregateTerm::DistinctAggregate { function, arg })
        } else {
            Some(FormalAggregateTerm::Aggregate { function, arg })
        }
    }
}

fn decimal_typmod_mismatch(expr_ty: &FormalAttributeType, output_ty: &FormalAttributeType) -> bool {
    match (expr_ty, output_ty) {
        (
            FormalAttributeType::Decimal {
                precision: Some(expr_precision),
                scale: Some(expr_scale),
            },
            FormalAttributeType::Decimal {
                precision: Some(output_precision),
                scale: Some(output_scale),
            },
        ) => expr_precision != output_precision || expr_scale != output_scale,
        _ => false,
    }
}

fn floating_output_type_mismatch(
    expr_ty: &FormalAttributeType,
    output_ty: &FormalAttributeType,
) -> bool {
    (matches!(
        expr_ty,
        FormalAttributeType::Float | FormalAttributeType::Double
    ) || matches!(
        output_ty,
        FormalAttributeType::Float | FormalAttributeType::Double
    )) && expr_ty != output_ty
}

fn attribute_types_compatible_for_values(
    literal_ty: FormalAttributeType,
    output_ty: FormalAttributeType,
) -> bool {
    match (literal_ty, output_ty) {
        (
            FormalAttributeType::Timestamp {
                precision: literal_precision,
            },
            FormalAttributeType::Timestamp {
                precision: output_precision,
            },
        )
        | (
            FormalAttributeType::Timestamptz {
                precision: literal_precision,
            },
            FormalAttributeType::Timestamptz {
                precision: output_precision,
            },
        ) => timestamp_precision(literal_precision) == timestamp_precision(output_precision),
        _ => literal_ty == output_ty,
    }
}

pub(super) fn query_to_list_query(query: FormalQuery) -> FormalListQuery {
    match query {
        FormalQuery::Empty { columns } => FormalListQuery::Empty { columns },
        query => FormalListQuery::Bag {
            input: Box::new(query),
        },
    }
}

fn aggregate_result_follows_argument_type(function: &str) -> bool {
    matches!(
        function.to_ascii_lowercase().as_str(),
        "sum" | "max" | "min" | "avg"
    )
}

fn aggregate_name_uses_reserved_logos_namespace(function: &str) -> bool {
    function
        .to_ascii_lowercase()
        .starts_with("__logos_distinct_aggregate_")
}

fn aggregate_term_contains_bare_decimal_division(term: &FormalAggregateTerm) -> bool {
    match term {
        FormalAggregateTerm::Expr { term } => function_term_contains_bare_decimal_division(term),
        FormalAggregateTerm::Aggregate { arg, .. }
        | FormalAggregateTerm::DistinctAggregate { arg, .. } => {
            function_term_contains_bare_decimal_division(arg)
        }
        FormalAggregateTerm::CountStar => false,
        FormalAggregateTerm::Function { symbol, args } => {
            symbol == "divide_decimal"
                || args
                    .iter()
                    .any(aggregate_term_contains_bare_decimal_division)
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            branches.iter().any(|branch| {
                aggregate_term_contains_bare_decimal_division(&branch.when)
                    || aggregate_term_contains_bare_decimal_division(&branch.then_expr)
            }) || aggregate_term_contains_bare_decimal_division(else_expr)
        }
    }
}

fn function_term_contains_bare_decimal_division(term: &FormalFunctionTerm) -> bool {
    match term {
        FormalFunctionTerm::Function { symbol, args } => {
            symbol == "divide_decimal"
                || args
                    .iter()
                    .any(function_term_contains_bare_decimal_division)
        }
        FormalFunctionTerm::Cast { arg, .. } => function_term_contains_bare_decimal_division(arg),
        FormalFunctionTerm::Constant { .. } | FormalFunctionTerm::Attribute { .. } => false,
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
