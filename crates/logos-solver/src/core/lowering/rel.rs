use super::scalar::{
    aggregate_function_for_type, aggregate_function_is_supported, annotate_function_literal_term,
    annotate_literal_term, is_exact_numeric_type, rel_expr_may_raise_runtime,
    scalar_ast_may_raise_runtime_for_input, string_typmod_codes, top_level_string_case_mapping,
    z_constant_function,
};
use super::*;
use crate::core::syntax::FormalRowMapAdapter;
use logos_ir::calcite::ty::{SqlTypeAnnotation, classify_type_annotation};
use logos_ir::ir::{
    AggregateCall, JoinType, RelExpr, ScalarAst, ScalarExpr, ScalarOp, SetOp, SortDirection,
    SortNullDirection, SourceGroupingProvenance, SqlStringType, SqlType, WindowAst, WindowFrameAst,
    WindowFrameBoundAst, WindowFrameUnits,
};
use std::collections::BTreeSet;

#[derive(Debug, Clone)]
struct FormalValuesColumn {
    name: String,
    ty: FormalAttributeType,
}

#[derive(Debug, Clone)]
struct ValuesCell {
    raw: String,
    ty: Option<FormalAttributeType>,
    source_ty: Option<FormalAttributeType>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SetInputLiteralProvenance {
    Known,
    UnknownNull,
    UnknownString,
}

struct BinarySetScopeInputs<'a> {
    left: &'a Scope,
    right: &'a Scope,
    left_literal_provenance: &'a [SetInputLiteralProvenance],
    right_literal_provenance: &'a [SetInputLiteralProvenance],
    reported_output: &'a [Column],
    case_mapping_text_positions: &'a [usize],
}

#[derive(Clone, Copy)]
struct GroupingSetPlan<'a> {
    group_keys: &'a [usize],
    grouping_sets: &'a [Vec<usize>],
    agg_calls: &'a [AggregateCall],
    output: &'a [Column],
    scope: &'a Scope,
}

#[derive(Clone, Copy)]
struct GroupingSelectContext<'a> {
    group_keys: &'a [usize],
    grouping_set: &'a [usize],
    output: &'a Column,
    output_ty: FormalAttributeType,
    scope: &'a Scope,
}

impl SetInputLiteralProvenance {
    fn is_unknown(self) -> bool {
        !matches!(self, Self::Known)
    }
}

fn aggregate_source_grouping(agg_calls: &[AggregateCall]) -> Option<&SourceGroupingProvenance> {
    let source = agg_calls.first()?.modifiers.source_grouping.as_ref()?;
    agg_calls
        .iter()
        .all(|call| call.modifiers.source_grouping.as_ref() == Some(source))
        .then_some(source)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpecialAggregateKind {
    AnyValue,
    SingleValue,
}

fn special_aggregate_kind(function: &str) -> Option<SpecialAggregateKind> {
    if function.eq_ignore_ascii_case("ANY_VALUE") {
        Some(SpecialAggregateKind::AnyValue)
    } else if function.eq_ignore_ascii_case("SINGLE_VALUE") {
        Some(SpecialAggregateKind::SingleValue)
    } else {
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SupportedCountWindowShape {
    /// `COUNT(*) OVER (PARTITION BY k ORDER BY k RANGE BETWEEN UNBOUNDED
    /// PRECEDING AND CURRENT ROW)`.  Every row in one partition is a peer,
    /// because the ordering expression is the partition expression itself.
    PartitionPeerComplete { key_index: usize },
    /// `COUNT(arg) OVER (RANGE BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED
    /// FOLLOWING)` with no partitioning or ordering.
    GlobalFull { arg_index: usize },
}

fn merge_set_scope_provenance(mut left: Scope, right: Scope) -> Option<Scope> {
    if left.attributes.len() != right.attributes.len() {
        return None;
    }
    for (left_attribute, right_attribute) in left.attributes.iter_mut().zip(right.attributes.iter())
    {
        if left_attribute.formal_ty != right_attribute.formal_ty {
            return None;
        }
        if left_attribute.numeric_dscale != right_attribute.numeric_dscale {
            left_attribute.numeric_dscale = None;
        }
    }
    Some(left)
}

fn preserve_populated_set_scope(populated: Scope, empty: Scope) -> Option<Scope> {
    (populated.attributes.len() == empty.attributes.len()
        && populated
            .attributes
            .iter()
            .zip(&empty.attributes)
            .all(|(left, right)| left.formal_ty == right.formal_ty))
    .then_some(populated)
}

fn query_expr_is_typed_empty(query: &FormalQueryExpr) -> bool {
    matches!(query, FormalQueryExpr::Empty { .. })
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IntegralStddevAvgRatioPlan {
    stddev_output_index: usize,
    avg_output_index: usize,
    ratio_project_index: usize,
    input_index_map: Vec<usize>,
}

impl LoweringContext {
    pub(super) fn lower_query_expr(
        &mut self,
        path: &str,
        rel: &RelExpr,
    ) -> Option<FormalQueryExpr> {
        let lowered = self.lower_query_expr_with_streaming(path, rel, false);
        if lowered.is_none() && !self.has_errors() {
            self.error(
                path,
                "query_expression_lowering_incomplete_without_diagnostic",
                "Query-expression lowering returned no declarative FormalSQL expression without recording a specific rejection. This internal completeness failure is conservatively blocked.",
            );
        }
        lowered
    }

    /// Lower a source-attested guarded integral STDDEV/AVG ratio without
    /// fabricating a static dscale for AVG(int4) or STDDEV_SAMP(int4).
    /// PostgreSQL selects both scales from aggregate values at runtime. A
    /// hidden compositional aggregate term computes the guarded scalar ratio
    /// while the ordinary STDDEV and AVG outputs remain independently observable.
    fn lower_integral_stddev_avg_ratio_body(
        &mut self,
        path: &str,
        rel: &RelExpr,
        plan: IntegralStddevAvgRatioPlan,
    ) -> Option<FormalQueryExpr> {
        self.validate_all_table_scans_against_schema(&format!("{path}.integralRatioScans"), rel)?;
        let RelExpr::Project {
            input: aggregate_filter,
            exprs,
            output,
            ..
        } = rel
        else {
            unreachable!("integral ratio body shape checked")
        };
        let RelExpr::Filter {
            input: aggregate,
            predicate,
            ..
        } = aggregate_filter.as_ref()
        else {
            unreachable!("integral ratio aggregate filter shape checked")
        };

        let Some((aggregate, input_index_map)) = integral_ratio_aggregate_input(aggregate) else {
            self.error(
                path,
                "integral_stddev_avg_ratio_permutation_drift",
                "The guarded ratio input no longer has the exact direct Aggregate or source-bound one-to-one Project permutation validated by the compositional lowering plan.",
            );
            return None;
        };
        if input_index_map != plan.input_index_map {
            self.error(
                path,
                "integral_stddev_avg_ratio_permutation_drift",
                "The guarded ratio input Project permutation changed after structural validation.",
            );
            return None;
        }

        let mut grouped =
            self.lower_query_expr_with_streaming(&format!("{path}.input.input"), aggregate, true)?;
        let FormalQueryExpr::ScalarGroup { select, .. } = &mut grouped else {
            self.error(
                path,
                "integral_stddev_avg_ratio_lineage_group_drift",
                "The one-set integral STDDEV/AVG Aggregate did not lower to one compositional Group.",
            );
            return None;
        };
        let (stddev_value, avg_value, ratio_arg) = {
            let stddev_item = select.get(plan.stddev_output_index)?;
            let avg_item = select.get(plan.avg_output_index)?;
            let FormalScalarExpr::Leaf {
                term:
                    FormalAggregateTerm::Aggregate {
                        function: stddev_function,
                        quantifier: stddev_quantifier,
                        arg: stddev_arg,
                    },
                ..
            } = &stddev_item.expr
            else {
                self.error(
                    path,
                    "integral_stddev_avg_ratio_lineage_statistic_drift",
                    "The guarded ratio input is no longer a direct STDDEV_SAMP(INTEGER) aggregate.",
                );
                return None;
            };
            let FormalScalarExpr::Leaf {
                term:
                    FormalAggregateTerm::Aggregate {
                        function: avg_function,
                        quantifier: avg_quantifier,
                        arg: avg_arg,
                    },
                ..
            } = &avg_item.expr
            else {
                self.error(
                    path,
                    "integral_stddev_avg_ratio_lineage_average_drift",
                    "The guarded ratio divisor is no longer a direct AVG(INTEGER) aggregate.",
                );
                return None;
            };
            if *stddev_function != FormalAggregateFunction::StddevSampleInt32
                || *stddev_quantifier != FormalAggregateQuantifier::All
                || *avg_function != FormalAggregateFunction::AverageInt32Numeric
                || *avg_quantifier != FormalAggregateQuantifier::All
                || stddev_arg != avg_arg
            {
                self.error(
                    path,
                    "integral_stddev_avg_ratio_lineage_drift",
                    "The guarded ratio no longer contains PostgreSQL STDDEV_SAMP and AVG over the same INTEGER input.",
                );
                return None;
            }
            (
                match &stddev_item.expr {
                    FormalScalarExpr::Leaf { term, .. } => term.clone(),
                    _ => unreachable!("aggregate leaf shape checked"),
                },
                match &avg_item.expr {
                    FormalScalarExpr::Leaf { term, .. } => term.clone(),
                    _ => unreachable!("aggregate leaf shape checked"),
                },
                stddev_arg.clone(),
            )
        };
        let stddev_scale = FormalAggregateTerm::Aggregate {
            function: FormalAggregateFunction::NumericDisplayScale(
                FormalNumericAggregate::StddevSampleInt32,
            ),
            quantifier: FormalAggregateQuantifier::All,
            arg: ratio_arg.clone(),
        };
        let avg_scale = FormalAggregateTerm::Aggregate {
            function: FormalAggregateFunction::NumericDisplayScale(
                FormalNumericAggregate::AverageInt32,
            ),
            quantifier: FormalAggregateQuantifier::All,
            arg: ratio_arg,
        };
        let numeric_zero = FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: "0".to_owned(),
                ty: Some(FormalAttributeType::Numeric),
            },
        };
        let numeric_null = FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: "NULL".to_owned(),
                ty: Some(FormalAttributeType::Numeric),
            },
        };
        let ratio = FormalAggregateTerm::Case {
            branches: vec![FormalCaseBranch {
                when: FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::PredicateValue(FormalPredicate::Eq),
                    args: vec![avg_value.clone(), numeric_zero],
                },
                then_expr: numeric_null,
            }],
            else_expr: Box::new(FormalAggregateTerm::ScalarCall {
                operator: ScalarOperator::Divide(ScalarNumericKind::Numeric),
                args: vec![stddev_value, stddev_scale, avg_value, avg_scale],
            }),
        };
        let mut used_names = select
            .iter()
            .map(|item| item.alias.clone())
            .chain(output.iter().map(|column| column.name.clone()))
            .collect::<BTreeSet<_>>();
        let ratio_alias =
            fresh_internal_attribute_name("__logos_integral_stddev_avg_ratio", &mut used_names);
        let ratio_index = select.len();
        select.push(FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                result_ty: FormalAttributeType::Numeric,
                term: ratio,
            },
            alias: ratio_alias,
            alias_ty: FormalAttributeType::Numeric,
            numeric_dscale: None,
        });

        let aggregate_scope =
            self.scope_from_query_expr(&format!("{path}.input.scope"), &grouped)?;
        let remapped_predicate = remap_scalar_input_refs(&predicate.parsed, &plan.input_index_map)?;
        let ratio_predicate = rewrite_integral_stddev_avg_ratio_filter(
            &remapped_predicate,
            plan.stddev_output_index,
            plan.avg_output_index,
            ratio_index,
        )?;
        let lowered_predicate = self.lower_native_scalar_boolean_expr(
            &format!("{path}.input.predicate"),
            &ratio_predicate,
            &aggregate_scope,
        )?;
        let filtered = FormalQueryExpr::ScalarSelection {
            predicate: lowered_predicate,
            input: Box::new(grouped),
        };

        let mut rewritten_exprs = exprs.clone();
        for expr in &mut rewritten_exprs {
            expr.parsed = remap_scalar_input_refs(&expr.parsed, &plan.input_index_map)?;
        }
        rewritten_exprs[plan.ratio_project_index].parsed = rewrite_integral_stddev_avg_ratio_case(
            &rewritten_exprs[plan.ratio_project_index].parsed,
            plan.stddev_output_index,
            plan.avg_output_index,
            ratio_index,
        )?;
        let mut corrected_output = output.to_vec();
        let ratio_output = &mut corrected_output[plan.ratio_project_index];
        if ratio_output.ty
            != (SqlType::Decimal {
                precision: None,
                scale: None,
            })
        {
            if !matches!(
                ratio_output.ty,
                SqlType::Integer
                    | SqlType::BigInt
                    | SqlType::Float
                    | SqlType::Double
                    | SqlType::Decimal { .. }
            ) {
                self.error(
                    &format!("{path}.output[{}]", plan.ratio_project_index),
                    "integral_stddev_avg_ratio_output_type_drift",
                    "The exact guarded STDDEV_SAMP(INTEGER)/AVG(INTEGER) ratio has PostgreSQL NUMERIC type, but Calcite reported a non-numeric output family that cannot be a stale carrier.",
                );
                return None;
            }
            self.warning(
                &format!("{path}.output[{}]", plan.ratio_project_index),
                "calcite_integral_stddev_avg_ratio_type_overridden",
                "The exact source-bound guarded STDDEV_SAMP(INTEGER)/AVG(INTEGER) expression has PostgreSQL unconstrained NUMERIC type; FormalSQL ignores Calcite's stale numeric carrier type.",
            );
            ratio_output.ty = SqlType::Decimal {
                precision: None,
                scale: None,
            };
        }
        let select =
            self.lower_project_select(path, &rewritten_exprs, &corrected_output, &aggregate_scope)?;
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(filtered),
        })
    }

    fn lower_numeric_exp_avg_projection(
        &mut self,
        path: &str,
        input: &RelExpr,
        exprs: &[ScalarExpr],
        correlations: &[logos_ir::ir::CorrelationBinding],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if !correlations.is_empty() {
            self.error(
                path,
                "numeric_exp_correlation_not_supported",
                "Declarative EXP(AVG(integer)) lowering requires an uncorrelated aggregate projection.",
            );
            return None;
        }
        if exprs.len() != output.len() || !has_unique_column_names(output) {
            self.error(
                path,
                "numeric_exp_projection_shape_not_supported",
                "Declarative EXP(AVG(integer)) lowering requires one output per expression and distinct SQL-visible aliases.",
            );
            return None;
        }
        let exp_indexes = exprs
            .iter()
            .enumerate()
            .filter_map(|(index, expr)| {
                matches!(
                    expr.parsed,
                    ScalarAst::Call {
                        op: ScalarOp::Exp,
                        ..
                    }
                )
                .then_some(index)
            })
            .collect::<Vec<_>>();
        let [exp_index] = exp_indexes.as_slice() else {
            self.error(
                path,
                "numeric_exp_projection_shape_not_supported",
                "The currently modeled declarative row adapter requires exactly one top-level EXP expression in its Project.",
            );
            return None;
        };
        let exp_index = *exp_index;
        let ScalarAst::Call {
            op: ScalarOp::Exp,
            args: exp_args,
            ..
        } = &exprs[exp_index].parsed
        else {
            unreachable!("top-level EXP index was collected above")
        };
        let [
            ScalarAst::InputRef {
                index: avg_output_index,
            },
        ] = exp_args.as_slice()
        else {
            self.error(
                &format!("{path}.exprs[{exp_index}]"),
                "numeric_exp_projection_shape_not_supported",
                "The modeled NUMERIC EXP must consume one direct AVG aggregate output.",
            );
            return None;
        };
        let avg_output_index = *avg_output_index;

        let RelExpr::Aggregate {
            input: aggregate_input,
            group_keys,
            grouping_sets,
            agg_calls,
            output: aggregate_output,
        } = input
        else {
            self.error(
                path,
                "numeric_exp_input_not_aggregate",
                "The modeled NUMERIC EXP projection must remain immediately above its AVG Aggregate.",
            );
            return None;
        };
        if aggregate_output.len() != group_keys.len() + agg_calls.len()
            || !matches!(grouping_sets.as_slice(), [set] if set == group_keys)
        {
            self.error(
                path,
                "numeric_exp_grouping_shape_not_supported",
                "The modeled EXP(AVG(integer)) fragment requires one ordinary grouping set and the standard group-key/aggregate output layout.",
            );
            return None;
        }
        let Some(avg_call_index) = avg_output_index.checked_sub(group_keys.len()) else {
            self.error(
                path,
                "numeric_exp_argument_not_avg",
                "EXP references a grouping key instead of an AVG aggregate output.",
            );
            return None;
        };
        let Some(avg_call) = agg_calls.get(avg_call_index) else {
            self.error(
                path,
                "numeric_exp_argument_not_avg",
                "EXP references an output position outside the Aggregate's AVG calls.",
            );
            return None;
        };
        if !attested_numeric_exp_avg_int32(&exprs[exp_index], avg_call, aggregate_input.output()) {
            self.error(
                &format!("{path}.exprs[{exp_index}]"),
                "numeric_exp_source_not_attested",
                "Exact NUMERIC EXP lowering requires source-bound EXP(AVG(direct_integer_column)) with no DISTINCT, FILTER, aggregate modifier, source CAST, or generated expression drift.",
            );
            return None;
        }
        if !matches!(
            output[exp_index].ty,
            SqlType::Double | SqlType::Decimal { .. }
        ) || exprs
            .iter()
            .enumerate()
            .any(|(index, expr)| index != exp_index && direct_input_ref(&expr.parsed).is_none())
        {
            self.error(
                path,
                "numeric_exp_projection_shape_not_supported",
                "Besides its one source-attested EXP(AVG(integer)), the supported projection may contain only direct aggregate-output references.",
            );
            return None;
        }

        let mut grouped =
            self.lower_query_expr_with_streaming(&format!("{path}.input"), input, true)?;
        let mut used_names = output
            .iter()
            .map(|column| column.name.clone())
            .collect::<BTreeSet<_>>();
        let avg_arg = {
            let FormalQueryExpr::ScalarGroup {
                select,
                having: FormalScalarExpr::True,
                ..
            } = &grouped
            else {
                self.error(
                    path,
                    "numeric_exp_group_lowering_not_supported",
                    "The ordinary AVG Aggregate did not lower to one declarative Group.",
                );
                return None;
            };
            used_names.extend(select.iter().map(|item| item.alias.clone()));
            let Some(FormalScalarSelectItem {
                expr:
                    FormalScalarExpr::Leaf {
                        term:
                            FormalAggregateTerm::Aggregate {
                                function,
                                quantifier,
                                arg,
                            },
                        ..
                    },
                ..
            }) = select.get(avg_output_index)
            else {
                self.error(
                    path,
                    "numeric_exp_avg_lowering_drift",
                    "The source-attested AVG output did not lower to one ordinary aggregate term.",
                );
                return None;
            };
            if *function != FormalAggregateFunction::AverageInt32Numeric
                || *quantifier != FormalAggregateQuantifier::All
            {
                self.error(
                    path,
                    "numeric_exp_avg_lowering_drift",
                    "The source-attested AVG(integer) output no longer uses PostgreSQL's NUMERIC average semantics.",
                );
                return None;
            }
            arg.clone()
        };
        let avg_value_name =
            fresh_internal_attribute_name("__logos_numeric_exp_avg_value", &mut used_names);
        let avg_dscale_name =
            fresh_internal_attribute_name("__logos_numeric_exp_avg_dscale", &mut used_names);
        let exp_dscale_name =
            fresh_internal_attribute_name("__logos_numeric_exp_result_dscale", &mut used_names);
        let avg_dscale_index = {
            let FormalQueryExpr::ScalarGroup { select, .. } = &mut grouped else {
                unreachable!("group shape checked above")
            };
            let index = select.len();
            select.push(FormalScalarSelectItem {
                expr: FormalScalarExpr::Leaf {
                    result_ty: FormalAttributeType::Z,
                    term: FormalAggregateTerm::Aggregate {
                        function: FormalAggregateFunction::NumericDisplayScale(
                            FormalNumericAggregate::AverageInt32,
                        ),
                        quantifier: FormalAggregateQuantifier::All,
                        arg: avg_arg,
                    },
                },
                alias: avg_dscale_name.clone(),
                alias_ty: FormalAttributeType::Z,
                numeric_dscale: None,
            });
            index
        };
        let grouped_scope =
            self.scope_from_query_expr(&format!("{path}.groupedScope"), &grouped)?;
        let avg_attribute = grouped_scope.attribute(avg_output_index)?;
        let avg_dscale_attribute = grouped_scope.attribute(avg_dscale_index)?;
        if avg_attribute.formal_ty != FormalAttributeType::Numeric
            || avg_dscale_attribute.formal_ty != FormalAttributeType::Z
        {
            self.error(
                path,
                "numeric_exp_avg_lowering_drift",
                "The paired AVG value/display-scale aggregates do not expose NUMERIC and mathematical-integer attributes.",
            );
            return None;
        }

        let mut staged_select = Vec::with_capacity(exprs.len() + 1);
        let mut passthrough = Vec::with_capacity(exprs.len().saturating_sub(1));
        let mut final_positions = vec![0; exprs.len()];
        for (index, (expr, column)) in exprs.iter().zip(output).enumerate() {
            if index == exp_index {
                continue;
            }
            let source_index = direct_input_ref(&expr.parsed)?;
            let source = grouped_scope.attribute(source_index)?.clone();
            let reported_type = self.lower_attribute_type(
                &format!("{path}.output[{index}]"),
                column,
                AttributeTypeContext::QueryOutput,
            )?;
            if reported_type != source.formal_ty
                && !(source.formal_ty == FormalAttributeType::Numeric
                    && calcite_stale_numeric_copy_type(reported_type))
            {
                self.error(
                    &format!("{path}.output[{index}]"),
                    "numeric_exp_passthrough_type_mismatch",
                    "A non-EXP projection output disagrees with the independently lowered aggregate attribute type.",
                );
                return None;
            }
            if reported_type != source.formal_ty {
                self.warning(
                    &format!("{path}.output[{index}]"),
                    "calcite_project_input_type_overridden",
                    "A direct relational input reference preserves its independently lowered PostgreSQL NUMERIC type; Calcite's copied result metadata is not a cast.",
                );
            }
            final_positions[index] = passthrough.len();
            passthrough.push(FormalAttribute {
                name: column.name.clone(),
                ty: source.formal_ty,
            });
            staged_select.push(FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: source.name,
                        ty: source.formal_ty,
                    },
                },
                alias: column.name.clone(),
                alias_ty: source.formal_ty,
                numeric_dscale: source.numeric_dscale.clone(),
            });
        }
        staged_select.push(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: avg_attribute.name,
                    ty: avg_attribute.formal_ty,
                },
            },
            alias: avg_value_name.clone(),
            alias_ty: FormalAttributeType::Numeric,
            numeric_dscale: avg_attribute.numeric_dscale,
        });
        staged_select.push(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: avg_dscale_attribute.name,
                    ty: avg_dscale_attribute.formal_ty,
                },
            },
            alias: avg_dscale_name.clone(),
            alias_ty: FormalAttributeType::Z,
            numeric_dscale: None,
        });
        let staged = FormalQueryExpr::Projection {
            select: staged_select,
            input: Box::new(grouped),
        };
        let output_numeric = FormalAttribute {
            name: output[exp_index].name.clone(),
            ty: FormalAttributeType::Numeric,
        };
        let adapter = FormalRowMapAdapter::NumericExp {
            passthrough: passthrough.clone(),
            avg_value: FormalAttribute {
                name: avg_value_name,
                ty: FormalAttributeType::Numeric,
            },
            avg_dscale: FormalAttribute {
                name: avg_dscale_name,
                ty: FormalAttributeType::Z,
            },
            output_numeric: output_numeric.clone(),
            output_dscale: FormalAttribute {
                name: exp_dscale_name.clone(),
                ty: FormalAttributeType::Z,
            },
        };
        let mapped = FormalQueryExpr::RowMap {
            adapter,
            input: Box::new(staged),
        };
        let mapped_scope = self.scope_from_query_expr(&format!("{path}.rowMapScope"), &mapped)?;
        final_positions[exp_index] = passthrough.len();
        self.warning(
            &format!("{path}.output[{exp_index}]"),
            "calcite_numeric_exp_type_overridden",
            "PostgreSQL EXP(AVG(integer)) returns unconstrained NUMERIC; FormalSQL ignores Calcite's DOUBLE/fixed-DECIMAL result metadata and preserves the exact value/display-scale operation.",
        );
        let mut select = final_positions
            .into_iter()
            .enumerate()
            .map(|(index, position)| {
                let attribute = mapped_scope.attribute(position)?.clone();
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: attribute.name,
                            ty: attribute.formal_ty,
                        },
                    },
                    alias: output[index].name.clone(),
                    alias_ty: attribute.formal_ty,
                    numeric_dscale: attribute.numeric_dscale.clone(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let dscale_attribute = mapped_scope.attribute(passthrough.len() + 1)?;
        if dscale_attribute.name != exp_dscale_name
            || dscale_attribute.formal_ty != FormalAttributeType::Z
        {
            self.error(
                path,
                "numeric_exp_dscale_output_drift",
                "The NUMERIC EXP row adapter did not retain its hidden runtime display-scale attribute.",
            );
            return None;
        }
        select.push(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: dscale_attribute.name.clone(),
                    ty: dscale_attribute.formal_ty,
                },
            },
            alias: dscale_attribute.name,
            alias_ty: FormalAttributeType::Z,
            numeric_dscale: None,
        });
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(mapped),
        })
    }

    fn lower_query_expr_with_streaming(
        &mut self,
        path: &str,
        rel: &RelExpr,
        force_streaming: bool,
    ) -> Option<FormalQueryExpr> {
        if let Some(plan) = integral_stddev_avg_ratio_body_plan(rel) {
            return self.lower_integral_stddev_avg_ratio_body(path, rel, plan);
        }
        if !force_streaming && !rel_requires_explicit_query_expr(rel) {
            return self.lower_rel(path, rel);
        }

        match rel {
            RelExpr::Sort {
                input,
                collation,
                fetch,
                offset,
                output,
            } => {
                // LIMIT/FETCH does not suppress evaluation of OFFSET itself.
                // Validate every row-count operand before any FETCH 0
                // simplification or child lowering can return early.
                let (offset_count, fetch_count) =
                    self.lower_sort_row_counts(path, offset.as_deref(), fetch.as_ref())?;
                let input_output = input.output();
                if output.len() != input_output.len() {
                    self.error(
                        path,
                        "sort_output_shape_changed",
                        "Query-expression lowering expects Sort to preserve its input row arity.",
                    );
                    return None;
                }
                if output
                    .iter()
                    .zip(input_output)
                    .any(|(sort_column, input_column)| {
                        sort_column.name != input_column.name || sort_column.ty != input_column.ty
                    })
                {
                    self.error(
                        path,
                        "sort_output_shape_changed",
                        "Query-expression Sort lowering requires every output position to preserve its input label and SQL type.",
                    );
                    return None;
                }
                let mut query_expr = self.lower_query_expr(&format!("{path}.input"), input)?;
                if !collation.is_empty() {
                    let input_scope =
                        self.scope_from_query_expr(&format!("{path}.inputScope"), &query_expr)?;
                    let keys = self.lower_sort_keys(path, collation, &input_scope)?;
                    query_expr = FormalQueryExpr::OrderBy {
                        keys,
                        input: Box::new(query_expr),
                    };
                }
                if let Some(count) = offset_count {
                    query_expr = FormalQueryExpr::Offset {
                        count,
                        input: Box::new(query_expr),
                    };
                }
                if let Some(count) = fetch_count {
                    query_expr = FormalQueryExpr::Fetch {
                        count,
                        input: Box::new(query_expr),
                    };
                }
                Some(query_expr)
            }
            RelExpr::Project {
                input,
                exprs,
                correlations,
                output,
            } => {
                // The NumericExp row adapter is an aggregate-specific
                // PostgreSQL typing repair.  An ordinary EXP call must stay
                // on the generic scalar path and be rejected until FormalSQL
                // has semantics for its resolved SQL type; merely seeing an
                // EXP syntax node is not authority to reinterpret it as
                // EXP(AVG(int4)).
                if project_has_top_level_numeric_exp(exprs)
                    && matches!(input.as_ref(), RelExpr::Aggregate { .. })
                {
                    return self.lower_numeric_exp_avg_projection(
                        path,
                        input,
                        exprs,
                        correlations,
                        output,
                    );
                }
                let contains_window = exprs
                    .iter()
                    .any(|expr| scalar_ast_contains_window(&expr.parsed));
                let input_query = if force_streaming {
                    self.lower_query_expr_with_streaming(&format!("{path}.input"), input, true)?
                } else {
                    self.lower_query_expr(&format!("{path}.input"), input)?
                };
                let input_is_empty = query_expr_is_typed_empty(&input_query);
                if contains_window && project_has_top_level_rank_window(exprs) {
                    if !correlations.is_empty() {
                        self.error(
                            path,
                            "rank_window_correlation_not_supported",
                            "Declarative RANK lowering requires an uncorrelated Project.",
                        );
                        return None;
                    }
                    return self.lower_declarative_rank_window_projection(
                        path,
                        input,
                        input_query,
                        exprs,
                        output,
                    );
                }
                if contains_window {
                    if !correlations.is_empty() {
                        self.error(
                            path,
                            "window_correlation_not_supported",
                            "The supported COUNT window rewrites require an uncorrelated direct table input.",
                        );
                        return None;
                    }
                    if project_has_supported_cumulative_rows_windows(exprs) {
                        return self.lower_declarative_cumulative_window_projection(
                            path,
                            input,
                            input_query,
                            exprs,
                            output,
                        );
                    }
                    return self.lower_supported_count_window_projection(
                        path,
                        input_query,
                        exprs,
                        output,
                    );
                }
                let scalar_roots = exprs
                    .iter()
                    .map(|expression| &expression.parsed)
                    .collect::<Vec<_>>();
                let isolate_subquery_owner = scalar_roots
                    .iter()
                    .any(|scalar| scalar_ast_contains_rel_subquery(scalar));
                if correlations.is_empty() && !isolate_subquery_owner {
                    let input_scope =
                        self.scope_from_query_expr(&format!("{path}.inputScope"), &input_query)?;
                    let select = self.lower_native_project_select_with_input(
                        path,
                        input,
                        exprs,
                        output,
                        &input_scope,
                        true,
                    )?;
                    if input_is_empty {
                        return self
                            .empty_query_expr_from_output(&format!("{path}.output"), output);
                    }
                    return Some(FormalQueryExpr::ScalarProjection {
                        select,
                        input: Box::new(input_query),
                    });
                }
                let (input_query, input_scope, correlations, _) = self
                    .prepare_correlated_query_expr_input(
                        &format!("{path}.correlations"),
                        input_query,
                        correlations,
                        &scalar_roots,
                    )?;
                let select = self.with_correlation_scopes(&correlations, |context| {
                    context.lower_native_project_select_with_input(
                        path,
                        input,
                        exprs,
                        output,
                        &input_scope,
                        true,
                    )
                })?;
                if input_is_empty {
                    return self.empty_query_expr_from_output(&format!("{path}.output"), output);
                }
                Some(FormalQueryExpr::ScalarProjection {
                    select,
                    input: Box::new(input_query),
                })
            }
            RelExpr::NativeHaving {
                input,
                predicate,
                correlations,
                output,
            } => self.lower_query_expr_native_having(path, input, predicate, correlations, output),
            RelExpr::Filter {
                input,
                predicate,
                correlations,
                output,
            } => {
                let input_query = self.lower_query_expr(&format!("{path}.input"), input)?;
                let input_is_empty = query_expr_is_typed_empty(&input_query);
                let isolate_subquery_owner = scalar_ast_contains_rel_subquery(&predicate.parsed);
                if correlations.is_empty() && !isolate_subquery_owner {
                    let input_scope = self
                        .scope_from_query_expr(&format!("{path}.predicateScope"), &input_query)?;
                    let predicate_ast = rewrite_source_disproved_numeric_coercions(
                        &predicate.parsed,
                        predicate.source.as_ref(),
                        &input_scope,
                    );
                    if predicate_ast != predicate.parsed {
                        self.warning(
                            &format!("{path}.predicate"),
                            "calcite_predicate_numeric_coercion_overridden",
                            "The source predicate has no explicit CAST, while Calcite inserted a coercion based on stale result metadata. FormalSQL derives the comparison coercion from the independently lowered PostgreSQL input types.",
                        );
                    }
                    let predicate = self.lower_native_scalar_boolean_expr(
                        &format!("{path}.predicate"),
                        &predicate_ast,
                        &input_scope,
                    )?;
                    if input_is_empty {
                        return self
                            .empty_query_expr_from_output(&format!("{path}.output"), output);
                    }
                    return Some(FormalQueryExpr::ScalarSelection {
                        predicate,
                        input: Box::new(input_query),
                    });
                }
                let (predicate_input, predicate_scope, correlations, isolated) = self
                    .prepare_correlated_query_expr_input(
                        &format!("{path}.correlations"),
                        input_query,
                        correlations,
                        &[&predicate.parsed],
                    )?;
                let predicate_ast = rewrite_source_disproved_numeric_coercions(
                    &predicate.parsed,
                    predicate.source.as_ref(),
                    &predicate_scope,
                );
                if predicate_ast != predicate.parsed {
                    self.warning(
                        &format!("{path}.predicate"),
                        "calcite_predicate_numeric_coercion_overridden",
                        "The source predicate has no explicit CAST, while Calcite inserted a coercion based on stale result metadata. FormalSQL derives the comparison coercion from the independently lowered PostgreSQL input types.",
                    );
                }
                let predicate = self.with_correlation_scopes(&correlations, |context| {
                    context.lower_native_scalar_boolean_expr(
                        &format!("{path}.predicate"),
                        &predicate_ast,
                        &predicate_scope,
                    )
                })?;
                if input_is_empty {
                    return self.empty_query_expr_from_output(&format!("{path}.output"), output);
                }
                let selection = FormalQueryExpr::ScalarSelection {
                    predicate,
                    input: Box::new(predicate_input),
                };
                if !isolated {
                    Some(selection)
                } else {
                    let output_scope = self.scope_restored_to_visible_names(
                        &format!("{path}.output"),
                        &predicate_scope,
                    )?;
                    Some(FormalQueryExpr::Projection {
                        select: self.lower_scope_rename_select(
                            &format!("{path}.output"),
                            &predicate_scope,
                            &output_scope,
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
                let special = self.validate_special_aggregate_shape(
                    path,
                    input,
                    group_keys,
                    grouping_sets,
                    agg_calls,
                    output,
                )?;
                let input_query = self.lower_query_expr(&format!("{path}.input"), input)?;
                let input_scope =
                    self.scope_from_query_expr(&format!("{path}.inputScope"), &input_query)?;
                if let Some((SpecialAggregateKind::AnyValue, argument_index)) = special {
                    return self.lower_any_value_int32_query_expr(
                        path,
                        input_query,
                        &input_scope,
                        argument_index,
                        output,
                    );
                }
                let (input_query, input_scope, agg_calls) = self
                    .lower_filtered_aggregate_input_expr(
                        path,
                        input_query,
                        input_scope,
                        agg_calls,
                    )?;
                self.lower_query_expr_grouping_sets(
                    path,
                    input_query,
                    GroupingSetPlan {
                        group_keys,
                        grouping_sets,
                        agg_calls: &agg_calls,
                        output,
                        scope: &input_scope,
                    },
                )
            }
            RelExpr::Distinct { input, output } => {
                let input_query = self.lower_query_expr(&format!("{path}.input"), input)?;
                self.require_distinct_output_matches_input(
                    &format!("{path}.output"),
                    &input_query,
                    output,
                )?;
                Some(FormalQueryExpr::Distinct {
                    input: Box::new(input_query),
                })
            }
            RelExpr::Set {
                op,
                all,
                inputs,
                output,
            } => self.lower_query_expr_set(path, *op, *all, inputs, output),
            RelExpr::Join {
                left,
                right,
                join_type,
                condition,
                correlations,
                output,
            } => {
                if !correlations.is_empty() && scalar_ast_contains_rel_subquery(&condition.parsed) {
                    self.error(
                        &format!("{path}.condition"),
                        "correlated_join_subquery_scope_barrier_not_supported",
                        "A correlated join condition containing a relational subquery requires rebinding Calcite's correlation row to split capture-avoiding join scopes; the current join barrier supports uncorrelated nested subqueries only.",
                    );
                    return None;
                }
                self.with_correlations(correlations, |context| {
                    context.lower_query_expr_join(path, left, right, *join_type, condition, output)
                })
            }
            RelExpr::TableScan { .. } | RelExpr::Values { .. } => self.lower_rel(path, rel),
        }
    }

    pub(super) fn lower_rel(&mut self, path: &str, rel: &RelExpr) -> Option<FormalQueryExpr> {
        match rel {
            RelExpr::TableScan { table, output } => {
                let relation = table.join(".");
                let scope = if self.has_authoritative_schema() {
                    self.authoritative_table_scan_scope(path, &relation, output)?
                } else {
                    self.lower_scope(&format!("{path}.output"), output)?
                };
                let columns = scope
                    .attributes
                    .into_iter()
                    .map(|attribute| FormalAttribute {
                        name: attribute.name,
                        ty: attribute.formal_ty,
                    })
                    .collect();
                Some(FormalQueryExpr::Table { relation, columns })
            }
            RelExpr::Project {
                input,
                exprs,
                correlations,
                output,
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                let input_is_empty = matches!(input_query, FormalQueryExpr::Empty { .. });
                let scalar_roots = exprs
                    .iter()
                    .map(|expression| &expression.parsed)
                    .collect::<Vec<_>>();
                let isolate_subquery_owner = scalar_roots
                    .iter()
                    .any(|scalar| scalar_ast_contains_rel_subquery(scalar));
                if correlations.is_empty() && !isolate_subquery_owner {
                    let input_scope =
                        self.scope_from_lowered_query(&format!("{path}.inputScope"), &input_query)?;
                    let select = self.lower_native_project_select_with_input(
                        path,
                        input,
                        exprs,
                        output,
                        &input_scope,
                        false,
                    )?;
                    if input_is_empty {
                        return self.empty_query_from_output(&format!("{path}.output"), output);
                    }
                    return Some(FormalQueryExpr::ScalarProjection {
                        select,
                        input: Box::new(input_query),
                    });
                }
                let (input_query, input_scope, correlations, _) = self.prepare_correlated_input(
                    &format!("{path}.correlations"),
                    input_query,
                    correlations,
                    &scalar_roots,
                )?;
                let select = self.with_correlation_scopes(&correlations, |context| {
                    context.lower_native_project_select_with_input(
                        path,
                        input,
                        exprs,
                        output,
                        &input_scope,
                        false,
                    )
                })?;
                if input_is_empty {
                    return self.empty_query_from_output(&format!("{path}.output"), output);
                }
                Some(FormalQueryExpr::ScalarProjection {
                    select,
                    input: Box::new(input_query),
                })
            }
            RelExpr::NativeHaving { .. } => {
                self.error(
                    path,
                    "native_having_requires_query_expr",
                    "Native SQL HAVING requires the logical Group query-expression semantics.",
                );
                None
            }
            RelExpr::Filter {
                input,
                predicate,
                correlations,
                output,
            } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                let input_is_empty = matches!(input_query, FormalQueryExpr::Empty { .. });
                let isolate_subquery_owner = scalar_ast_contains_rel_subquery(&predicate.parsed);
                if correlations.is_empty() && !isolate_subquery_owner {
                    let input_scope = self.scope_from_lowered_query(
                        &format!("{path}.predicateScope"),
                        &input_query,
                    )?;
                    let predicate = self.lower_native_scalar_boolean_expr(
                        &format!("{path}.predicate"),
                        &predicate.parsed,
                        &input_scope,
                    )?;
                    if input_is_empty {
                        return self.empty_query_from_output(&format!("{path}.output"), output);
                    }
                    return Some(FormalQueryExpr::ScalarSelection {
                        predicate,
                        input: Box::new(input_query),
                    });
                }
                let (predicate_input, predicate_scope, correlations, isolated) = self
                    .prepare_correlated_input(
                        &format!("{path}.correlations"),
                        input_query,
                        correlations,
                        &[&predicate.parsed],
                    )?;
                let predicate = self.with_correlation_scopes(&correlations, |context| {
                    context.lower_native_scalar_boolean_expr(
                        &format!("{path}.predicate"),
                        &predicate.parsed,
                        &predicate_scope,
                    )
                })?;
                if input_is_empty {
                    return self.empty_query_from_output(&format!("{path}.output"), output);
                }
                let selection = FormalQueryExpr::ScalarSelection {
                    predicate,
                    input: Box::new(predicate_input),
                };
                if !isolated {
                    Some(selection)
                } else {
                    let output_scope = self.scope_restored_to_visible_names(
                        &format!("{path}.output"),
                        &predicate_scope,
                    )?;
                    Some(FormalQueryExpr::Projection {
                        select: self.lower_scope_rename_select(
                            &format!("{path}.output"),
                            &predicate_scope,
                            &output_scope,
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
                let input_scope =
                    self.scope_from_lowered_query(&format!("{path}.inputScope"), &input_query)?;
                let (input_query, input_scope, agg_calls) =
                    self.lower_filtered_aggregate_input(path, input_query, input_scope, agg_calls)?;
                self.lower_grouping_sets(
                    path,
                    input_query,
                    GroupingSetPlan {
                        group_keys,
                        grouping_sets,
                        agg_calls: &agg_calls,
                        output,
                        scope: &input_scope,
                    },
                )
            }
            RelExpr::Distinct { input, output } => {
                let input_query = self.lower_rel(&format!("{path}.input"), input)?;
                self.require_distinct_output_matches_input(
                    &format!("{path}.output"),
                    &input_query,
                    output,
                )?;
                Some(FormalQueryExpr::Distinct {
                    input: Box::new(input_query),
                })
            }
            RelExpr::Set {
                op,
                all,
                inputs,
                output,
            } => self.lower_set(path, *op, *all, inputs, output),
            RelExpr::Sort {
                input,
                collation,
                fetch,
                offset,
                ..
            } => {
                self.lower_sort_row_counts(path, offset.as_deref(), fetch.as_ref())?;
                if collation.is_empty() && fetch.is_none() && offset.is_none() {
                    return self.lower_rel(&format!("{path}.input"), input);
                }
                self.error(
                    path,
                    "query_order_behavior_analysis_mismatch",
                    "Internal order-behavior analysis routed an order-sensitive Sort through the order-insensitive relational path.",
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
                ..
            } => {
                if !correlations.is_empty() && scalar_ast_contains_rel_subquery(&condition.parsed) {
                    self.error(
                        &format!("{path}.condition"),
                        "correlated_join_subquery_scope_barrier_not_supported",
                        "A correlated join condition containing a relational subquery requires rebinding Calcite's correlation row to split capture-avoiding join scopes; the current join barrier supports uncorrelated nested subqueries only.",
                    );
                    return None;
                }
                self.with_correlations(correlations, |context| {
                    context.lower_join(path, left, right, *join_type, &condition.parsed, output)
                })
            }
            RelExpr::Values { rows, output } => self.lower_values_query(path, rows, output),
        }
    }

    fn lower_query_expr_native_having(
        &mut self,
        path: &str,
        input: &RelExpr,
        predicate: &ScalarExpr,
        correlations: &[logos_ir::ir::CorrelationBinding],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        let RelExpr::Aggregate {
            group_keys,
            grouping_sets,
            ..
        } = input
        else {
            self.error(
                path,
                "native_having_input_not_aggregate",
                "A source-attested native HAVING must remain immediately over its Aggregate.",
            );
            return None;
        };
        if !correlations.is_empty() {
            self.error(
                path,
                "correlated_native_having_not_supported",
                "Correlated native HAVING requires a group-environment correlation binding that is not represented by the current logical Group formula interface.",
            );
            return None;
        }
        if scalar_ast_contains_rel_subquery(&predicate.parsed) {
            self.error(
                &format!("{path}.predicate"),
                "having_subquery_scope_barrier_not_supported",
                "A native HAVING formula containing a relational subquery requires one capture-avoiding environment shared by aggregate terms and every generated nested-query binding. That complete transport is not modeled, so this path is conservatively unsupported.",
            );
            return None;
        }
        if output != input.output() {
            self.error(
                &format!("{path}.output"),
                "native_having_output_shape_changed",
                "A native HAVING Filter must preserve every Aggregate output position, name, and SQL type.",
            );
            return None;
        }
        let ordinary_group =
            matches!(grouping_sets.as_slice(), [set] if set.as_slice() == group_keys.as_slice());
        if !ordinary_group {
            self.error(
                &format!("{path}.predicate"),
                "grouping_sets_having_scalar_phase_not_supported",
                "Native GROUPING SETS shares one child exactly, but its compatibility grouping-set records do not yet carry a pre-target scalar HAVING expression. Lowering this HAVING outside the grouping operator would evaluate rejected target expressions too early, so the boundary is fail-closed.",
            );
            return None;
        }

        let grouped =
            self.lower_query_expr_with_streaming(&format!("{path}.input"), input, true)?;
        let aggregate_scope =
            self.scope_from_query_expr(&format!("{path}.predicateScope"), &grouped)?;
        let predicate_ast = predicate.parsed.clone();
        let predicate = self.lower_formula_expr(
            &format!("{path}.predicate"),
            &predicate_ast,
            &aggregate_scope,
        )?;

        install_query_expr_having(grouped, &predicate).or_else(|| {
            self.error(
                path,
                "native_having_group_installation_not_supported",
                "Declarative native HAVING expected one ScalarGroup and required every predicate output reference to resolve to its group-key or aggregate scalar leaf.",
            );
            None
        })
    }

    pub(super) fn scope_from_lowered_query(
        &mut self,
        path: &str,
        query: &FormalQueryExpr,
    ) -> Option<Scope> {
        self.scope_from_query_expr(path, query)
    }

    fn scope_from_signature_and_dscales(
        &mut self,
        path: &str,
        signature: Vec<FormalAttribute>,
        dscales: Vec<Option<NumericDscaleProvenance>>,
    ) -> Option<Scope> {
        if signature.len() != dscales.len() {
            self.error(
                path,
                "formal_query_output_provenance_arity_mismatch",
                "Numeric display-scale provenance does not align with the authoritative ordered query output signature.",
            );
            return None;
        }
        let scope = Scope {
            attributes: signature
                .into_iter()
                .zip(dscales)
                .map(|(attribute, numeric_dscale)| ScopeAttribute {
                    visible_name: attribute.name.clone(),
                    name: attribute.name,
                    formal_ty: attribute.ty,
                    numeric_dscale,
                })
                .collect(),
        };
        self.validate_scope_numeric_dscale_references(path, &scope)?;
        Some(scope)
    }

    /// Reconcile every base scan in the complete typed query tree with the
    /// authoritative schema before a root-level analysis-error result is
    /// allowed to discard ordinary relational lowering.  Scalar subqueries
    /// are included: an unreachable or erroring outer expression cannot make
    /// a forged nested table identity part of the attested statement.
    pub(super) fn validate_all_table_scans_against_schema(
        &mut self,
        path: &str,
        rel: &RelExpr,
    ) -> Option<()> {
        if !self.has_authoritative_schema() {
            self.error(
                path,
                "analysis_error_authoritative_schema_required",
                "A root-level PostgreSQL analysis-error shortcut requires an authoritative schema for every table scan in the complete typed query tree.",
            );
            return None;
        }
        self.validate_rel_table_scans_against_schema(path, rel)
    }

    fn validate_rel_table_scans_against_schema(&mut self, path: &str, rel: &RelExpr) -> Option<()> {
        match rel {
            RelExpr::TableScan { table, output } => {
                let relation = table.join(".");
                self.authoritative_table_scan_scope(path, &relation, output)?;
            }
            RelExpr::Project { input, exprs, .. } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.input"), input)?;
                for (index, expr) in exprs.iter().enumerate() {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.exprs[{index}]"),
                        &expr.parsed,
                    )?;
                }
            }
            RelExpr::Filter {
                input, predicate, ..
            }
            | RelExpr::NativeHaving {
                input, predicate, ..
            } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.input"), input)?;
                self.validate_scalar_table_scans_against_schema(
                    &format!("{path}.predicate"),
                    &predicate.parsed,
                )?;
            }
            RelExpr::Join {
                left,
                right,
                condition,
                ..
            } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.left"), left)?;
                self.validate_rel_table_scans_against_schema(&format!("{path}.right"), right)?;
                self.validate_scalar_table_scans_against_schema(
                    &format!("{path}.condition"),
                    &condition.parsed,
                )?;
            }
            RelExpr::Aggregate {
                input, agg_calls, ..
            } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.input"), input)?;
                for (call_index, call) in agg_calls.iter().enumerate() {
                    for (arg_index, arg) in call.args.iter().enumerate() {
                        self.validate_scalar_table_scans_against_schema(
                            &format!("{path}.aggCalls[{call_index}].args[{arg_index}]"),
                            &arg.parsed,
                        )?;
                    }
                    if let Some(filter) = &call.filter {
                        self.validate_scalar_table_scans_against_schema(
                            &format!("{path}.aggCalls[{call_index}].filter"),
                            &filter.parsed,
                        )?;
                    }
                }
            }
            RelExpr::Distinct { input, .. } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.input"), input)?;
            }
            RelExpr::Sort {
                input,
                fetch,
                offset,
                ..
            } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.input"), input)?;
                if let Some(fetch) = fetch {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.fetch"),
                        &fetch.parsed,
                    )?;
                }
                if let Some(offset) = offset {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.offset"),
                        &offset.parsed,
                    )?;
                }
            }
            RelExpr::Set { inputs, .. } => {
                for (index, input) in inputs.iter().enumerate() {
                    self.validate_rel_table_scans_against_schema(
                        &format!("{path}.inputs[{index}]"),
                        input,
                    )?;
                }
            }
            RelExpr::Values { rows, .. } => {
                for (row_index, row) in rows.iter().enumerate() {
                    for (column_index, value) in row.iter().enumerate() {
                        self.validate_scalar_table_scans_against_schema(
                            &format!("{path}.rows[{row_index}][{column_index}]"),
                            &value.parsed,
                        )?;
                    }
                }
            }
        }
        Some(())
    }

    fn validate_scalar_table_scans_against_schema(
        &mut self,
        path: &str,
        ast: &ScalarAst,
    ) -> Option<()> {
        match ast {
            ScalarAst::Call { args, .. } => {
                for (index, arg) in args.iter().enumerate() {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.args[{index}]"),
                        arg,
                    )?;
                }
            }
            ScalarAst::TypeAnnotation { expr, .. } => {
                self.validate_scalar_table_scans_against_schema(&format!("{path}.expr"), expr)?;
            }
            ScalarAst::Window { parsed } => {
                for (index, arg) in parsed.args.iter().enumerate() {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.args[{index}]"),
                        arg,
                    )?;
                }
                for (index, partition) in parsed.partition_by.iter().enumerate() {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.partitionBy[{index}]"),
                        partition,
                    )?;
                }
                for (index, order) in parsed.order_by.iter().enumerate() {
                    self.validate_scalar_table_scans_against_schema(
                        &format!("{path}.orderBy[{index}]"),
                        &order.expr,
                    )?;
                }
                if let Some(frame) = &parsed.frame {
                    for (index, offset) in frame.offset_exprs().enumerate() {
                        self.validate_scalar_table_scans_against_schema(
                            &format!("{path}.frame.offsets[{index}]"),
                            offset,
                        )?;
                    }
                }
            }
            ScalarAst::RelSubquery { rel } => {
                self.validate_rel_table_scans_against_schema(&format!("{path}.rel"), rel)?;
            }
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. } => {}
        }
        Some(())
    }

    fn authoritative_table_scan_scope(
        &mut self,
        path: &str,
        relation: &str,
        reported_output: &[Column],
    ) -> Option<Scope> {
        let authoritative_columns = self.authoritative_table_columns(path, relation)?;
        if authoritative_columns.len() != reported_output.len() {
            self.error(
                &format!("{path}.output"),
                "table_scan_schema_arity_mismatch",
                &format!(
                    "Calcite reported {} columns for table {relation:?}, but the authoritative schema declares {}. A table scan cannot change row arity without an explicit relational operator.",
                    reported_output.len(),
                    authoritative_columns.len()
                ),
            );
            return None;
        }

        let mut attributes = Vec::with_capacity(authoritative_columns.len());
        for (index, (authoritative, reported)) in authoritative_columns
            .iter()
            .zip(reported_output)
            .enumerate()
        {
            let attribute_path = format!("{path}.output[{index}]");
            if authoritative.name != reported.name {
                self.error(
                    &attribute_path,
                    "table_scan_schema_name_mismatch",
                    &format!(
                        "Calcite reported table-scan column name {:?}, but authoritative table {relation:?} has {:?} at this position. A scan-level rename is not semantically modeled.",
                        reported.name, authoritative.name
                    ),
                );
                return None;
            }
            let authoritative_ty = self.lower_attribute_type(
                &format!("{attribute_path}.schema"),
                authoritative,
                AttributeTypeContext::Schema,
            )?;
            let reported_ty = self.lower_attribute_type(
                &format!("{attribute_path}.reported"),
                reported,
                AttributeTypeContext::QueryInput,
            )?;
            if authoritative_ty != reported_ty {
                self.error(
                    &attribute_path,
                    "table_scan_schema_type_mismatch",
                    &format!(
                        "Calcite reported table-scan type {:?}, but authoritative table {relation:?} has {:?} at this position. Base types and PostgreSQL typmods must agree at a scan boundary.",
                        reported.ty, authoritative.ty
                    ),
                );
                return None;
            }
            attributes.push(ScopeAttribute {
                name: authoritative.name.clone(),
                visible_name: authoritative.name.clone(),
                formal_ty: authoritative_ty,
                numeric_dscale: numeric_dscale_for_type(authoritative_ty),
            });
        }

        if authoritative_columns.iter().any(|column| {
            matches!(
                column.ty,
                SqlType::Decimal {
                    precision: None,
                    scale: None
                }
            )
        }) {
            self.error(
                path,
                "numeric_table_special_values_not_supported",
                "PostgreSQL unconstrained NUMERIC table columns may contain infinities and per-value display scales that are not represented by the current FormalSQL numeric carrier. Fixed DECIMAL(p,s) columns, including NaN, are modeled separately.",
            );
            return None;
        }

        Some(Scope { attributes })
    }

    fn authoritative_table_columns(&mut self, path: &str, relation: &str) -> Option<Vec<Column>> {
        let matches = self
            .schema
            .as_ref()
            .expect("authoritative table lookup requires a schema")
            .tables
            .iter()
            .filter(|table| table.name == relation)
            .map(|table| table.columns.clone())
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [columns] => Some(columns.clone()),
            [] => {
                self.error(
                    path,
                    "table_scan_relation_not_in_schema",
                    &format!(
                        "Calcite table scan references relation {relation:?}, which is absent from the authoritative generated schema."
                    ),
                );
                None
            }
            _ => {
                self.error(
                    path,
                    "table_scan_relation_ambiguous_in_schema",
                    &format!(
                        "Authoritative schema contains multiple relations named {relation:?}; a table scan cannot be resolved soundly."
                    ),
                );
                None
            }
        }
    }

    pub(super) fn scope_from_query_expr(
        &mut self,
        path: &str,
        query: &FormalQueryExpr,
    ) -> Option<Scope> {
        let signature = query_expr_output_signature(query).or_else(|| {
            self.error(
                path,
                "formal_query_expr_output_signature_inconsistent",
                "FormalSQL query-expression syntax does not carry one consistent ordered typed output signature.",
            );
            None
        })?;
        let dscales = self.query_expr_output_dscales(path, query)?;
        self.scope_from_signature_and_dscales(path, signature, dscales)
    }

    fn query_expr_output_dscales(
        &mut self,
        path: &str,
        query: &FormalQueryExpr,
    ) -> Option<Vec<Option<NumericDscaleProvenance>>> {
        match query {
            FormalQueryExpr::Empty { columns } | FormalQueryExpr::Table { columns, .. } => Some(
                columns
                    .iter()
                    .map(|column| numeric_dscale_for_type(column.ty))
                    .collect(),
            ),
            FormalQueryExpr::EmptyTuple => Some(Vec::new()),
            FormalQueryExpr::Projection { select, .. } | FormalQueryExpr::Group { select, .. } => {
                Some(
                    select
                        .iter()
                        .map(|item| item.numeric_dscale.clone())
                        .collect(),
                )
            }
            FormalQueryExpr::ScalarProjection { select, .. }
            | FormalQueryExpr::ScalarGroup { select, .. } => Some(
                select
                    .iter()
                    .map(|item| item.numeric_dscale.clone())
                    .collect(),
            ),
            FormalQueryExpr::RowMap { adapter, input } => {
                self.row_map_output_dscales(path, adapter, input)
            }
            FormalQueryExpr::GroupingSets { grouping_sets, .. } => {
                let select = grouping_sets.first().map(|set| &set.select).or_else(|| {
                    self.error(
                        path,
                        "formal_grouping_sets_empty",
                        "Native FormalSQL grouping sets require at least one grouping set.",
                    );
                    None
                })?;
                // Every runtime NUMERIC display scale must remain in the same
                // row as its value. In particular, a grouping-set key cannot
                // retain a reference to an input-only hidden scale attribute:
                // grouping by that attribute would split numerically equal
                // values, while dropping it would make later arithmetic NULL.
                Some(
                    select
                        .iter()
                        .map(|item| item.numeric_dscale.clone())
                        .collect(),
                )
            }
            FormalQueryExpr::Rank {
                rank_attribute,
                input,
                ..
            } => {
                let scope = self.scope_from_query_expr(path, input)?;
                if scope
                    .attributes
                    .iter()
                    .any(|attribute| attribute.name == rank_attribute.name)
                {
                    self.error(
                        path,
                        "formal_rank_attribute_collision",
                        "The native RANK attribute must be fresh relative to its staged input scope.",
                    );
                    return None;
                }
                let mut dscales = scope
                    .attributes
                    .into_iter()
                    .map(|attribute| attribute.numeric_dscale)
                    .collect::<Vec<_>>();
                dscales.push(numeric_dscale_for_type(rank_attribute.ty));
                Some(dscales)
            }
            FormalQueryExpr::Window { items, input, .. } => {
                let scope = self.scope_from_query_expr(path, input)?;
                let mut output_names = scope
                    .attributes
                    .iter()
                    .map(|attribute| attribute.name.clone())
                    .collect::<Vec<_>>();
                for item in items {
                    if output_names.iter().any(|name| name == &item.output.name) {
                        self.error(
                            path,
                            "formal_window_attribute_collision",
                            "Every native window output attribute must be fresh relative to its staged input and the preceding window items.",
                        );
                        return None;
                    }
                    output_names.push(item.output.name.clone());
                }
                Some(
                    scope
                        .attributes
                        .into_iter()
                        .map(|attribute| attribute.numeric_dscale)
                        .chain(items.iter().map(|item| item.numeric_dscale.clone()))
                        .collect(),
                )
            }
            FormalQueryExpr::Join {
                join_kind,
                matched_select,
                left_select,
                ..
            } => {
                let select = match join_kind {
                    FormalQueryJoinKind::Semi | FormalQueryJoinKind::Anti => left_select,
                    _ => matched_select,
                };
                Some(
                    select
                        .iter()
                        .map(|item| item.numeric_dscale.clone())
                        .collect(),
                )
            }
            FormalQueryExpr::Selection { input, .. }
            | FormalQueryExpr::ScalarSelection { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => {
                let scope = self.scope_from_query_expr(path, input)?;
                Some(
                    scope
                        .attributes
                        .into_iter()
                        .map(|attribute| attribute.numeric_dscale)
                        .collect(),
                )
            }
            FormalQueryExpr::Set { left, right, .. }
                if query_expr_is_typed_empty(right.as_ref()) =>
            {
                // A typed empty set operand contributes no values. Its
                // value-free NUMERIC metadata cannot invalidate display-scale
                // provenance from the populated operand.
                let populated = self.scope_from_query_expr(path, left)?;
                let empty = self.scope_from_query_expr(path, right)?;
                let scope = preserve_populated_set_scope(populated, empty).or_else(|| {
                    self.error(
                        path,
                        "typed_empty_set_scope_mismatch",
                        "A typed empty set branch does not have the same arity and FormalSQL value types as its populated branch.",
                    );
                    None
                })?;
                Some(
                    scope
                        .attributes
                        .into_iter()
                        .map(|attribute| attribute.numeric_dscale)
                        .collect(),
                )
            }
            FormalQueryExpr::Set { left, right, .. }
                if query_expr_is_typed_empty(left.as_ref()) =>
            {
                let populated = self.scope_from_query_expr(path, right)?;
                let empty = self.scope_from_query_expr(path, left)?;
                let scope = preserve_populated_set_scope(populated, empty).or_else(|| {
                    self.error(
                        path,
                        "typed_empty_set_scope_mismatch",
                        "A typed empty set branch does not have the same arity and FormalSQL value types as its populated branch.",
                    );
                    None
                })?;
                Some(
                    scope
                        .attributes
                        .into_iter()
                        .map(|attribute| attribute.numeric_dscale)
                        .collect(),
                )
            }
            FormalQueryExpr::Set { left, right, .. } => {
                let left_scope = self.scope_from_query_expr(path, left)?;
                let right_scope = self.scope_from_query_expr(path, right)?;
                let scope = merge_set_scope_provenance(left_scope, right_scope).or_else(|| {
                    self.error(
                        path,
                        "set_scope_mismatch",
                        "Set-operation branches do not have the same arity and FormalSQL value types after positional coercion.",
                    );
                    None
                })?;
                Some(
                    scope
                        .attributes
                        .into_iter()
                        .map(|attribute| attribute.numeric_dscale)
                        .collect(),
                )
            }
            FormalQueryExpr::CrossJoin { left, right } => {
                let left_scope = self.scope_from_query_expr(path, left)?;
                let right_scope = self.scope_from_query_expr(path, right)?;
                Some(
                    left_scope
                        .attributes
                        .into_iter()
                        .chain(right_scope.attributes)
                        .map(|attribute| attribute.numeric_dscale)
                        .collect(),
                )
            }
            FormalQueryExpr::Error { columns, .. } => Some(
                columns
                    .iter()
                    .map(|column| numeric_dscale_for_type(column.ty))
                    .collect(),
            ),
        }
    }

    fn row_map_output_dscales(
        &mut self,
        path: &str,
        adapter: &FormalRowMapAdapter,
        input: &FormalQueryExpr,
    ) -> Option<Vec<Option<NumericDscaleProvenance>>> {
        let input_scope = self.scope_from_query_expr(&format!("{path}.rowMapInput"), input)?;
        let output_attributes = adapter.output_attributes();
        if !output_attributes
            .iter()
            .enumerate()
            .all(|(index, attribute)| {
                output_attributes
                    .iter()
                    .skip(index + 1)
                    .all(|other| other.name != attribute.name)
            })
        {
            self.error(
                path,
                "row_map_output_collision",
                "A declarative row adapter must produce attributes with distinct names.",
            );
            return None;
        }
        match adapter {
            FormalRowMapAdapter::NumericExp {
                passthrough,
                avg_value,
                avg_dscale,
                output_numeric,
                output_dscale,
            } => {
                if avg_value.ty != FormalAttributeType::Numeric
                    || avg_dscale.ty != FormalAttributeType::Z
                    || output_numeric.ty != FormalAttributeType::Numeric
                    || output_dscale.ty != FormalAttributeType::Z
                {
                    self.error(
                        path,
                        "numeric_exp_row_map_type_mismatch",
                        "The NUMERIC EXP row adapter requires NUMERIC value attributes and mathematical-integer display-scale attributes.",
                    );
                    return None;
                }
                let attributes = passthrough
                    .iter()
                    .enumerate()
                    .map(|(index, attribute)| {
                        self.resolve_row_map_input_attribute(
                            &format!("{path}.passthrough[{index}]"),
                            &input_scope,
                            attribute,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                self.resolve_row_map_input_attribute(
                    &format!("{path}.avgValue"),
                    &input_scope,
                    avg_value,
                )?;
                self.resolve_row_map_input_attribute(
                    &format!("{path}.avgDscale"),
                    &input_scope,
                    avg_dscale,
                )?;
                let mut dscales = attributes
                    .into_iter()
                    .map(|attribute| attribute.numeric_dscale)
                    .collect::<Vec<_>>();
                dscales.push(Some(NumericDscaleProvenance::Attribute(
                    output_dscale.name.clone(),
                )));
                dscales.push(numeric_dscale_for_type(output_dscale.ty));
                Some(dscales)
            }
        }
    }

    fn resolve_row_map_input_attribute(
        &mut self,
        path: &str,
        input_scope: &Scope,
        binding: &FormalAttribute,
    ) -> Option<ScopeAttribute> {
        let matches = input_scope
            .attributes
            .iter()
            .filter(|attribute| attribute.name == binding.name)
            .collect::<Vec<_>>();
        let [attribute] = matches.as_slice() else {
            self.error(
                path,
                "row_map_input_binding_not_unique",
                "A declarative row-adapter input attribute must resolve to exactly one input position by name.",
            );
            return None;
        };
        if attribute.formal_ty != binding.ty {
            self.error(
                path,
                "row_map_input_binding_type_mismatch",
                "A declarative row-adapter input attribute disagrees with the resolved input position's FormalSQL type.",
            );
            return None;
        }
        Some((**attribute).clone())
    }

    fn lower_values_query(
        &mut self,
        path: &str,
        rows: &[Vec<ScalarExpr>],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        self.ensure_values_output_schema(path, output)?;
        let cells = self.lower_values_cells(path, rows, output)?;
        let columns = self.lower_values_columns(path, output, &cells)?;
        let rows = self.type_values_rows(path, &cells, &columns)?;
        if cells.is_empty() {
            return Some(FormalQueryExpr::Empty {
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
        Some(queries.fold(first, |left, right| FormalQueryExpr::Set {
            op: FormalSetOp::Union,
            left: Box::new(left),
            right: Box::new(right),
        }))
    }

    fn empty_query_from_output(
        &mut self,
        path: &str,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
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
        Some(FormalQueryExpr::Empty { columns })
    }

    fn empty_query_expr_from_output(
        &mut self,
        path: &str,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        let query = self.empty_query_from_output(path, output)?;
        Some(query)
    }

    fn empty_output_attribute_type(
        &mut self,
        path: &str,
        column: &Column,
    ) -> Option<FormalAttributeType> {
        match column.ty {
            SqlType::Null => Some(self.unresolved_null_postgres_type(path)),
            _ => self.lower_attribute_type(path, column, AttributeTypeContext::QueryOutput),
        }
    }

    fn values_singleton_query(
        &mut self,
        path: &str,
        row: &[FormalValueLiteral],
        columns: &[FormalValuesColumn],
    ) -> Option<FormalQueryExpr> {
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
                let constant = FormalFunctionTerm::Constant {
                    raw: literal.raw.clone(),
                    ty: Some(literal.source_ty.unwrap_or(literal.ty)),
                };
                let term = match literal.source_ty {
                    Some(FormalAttributeType::Int32)
                        if literal.ty == FormalAttributeType::Numeric =>
                    {
                        FormalFunctionTerm::ScalarCall {
                            operator: ScalarOperator::Cast(ScalarCast::ToNumeric(
                                ScalarNumericSource::Int32,
                            )),
                            args: vec![constant],
                        }
                    }
                    Some(FormalAttributeType::Int64)
                        if literal.ty == FormalAttributeType::Numeric =>
                    {
                        FormalFunctionTerm::ScalarCall {
                            operator: ScalarOperator::Cast(ScalarCast::ToNumeric(
                                ScalarNumericSource::Int64,
                            )),
                            args: vec![constant],
                        }
                    }
                    Some(source_ty)
                        if source_ty != literal.ty
                            && matches!(source_ty, FormalAttributeType::String { .. })
                            && set_string_common_type_target(literal.ty) =>
                    {
                        string_implicit_coercion_term(constant, literal.ty)?
                    }
                    Some(source_ty) if source_ty != literal.ty => {
                        self.error(
                            path,
                            "values_literal_coercion_not_supported",
                            "VALUES supports only exact integral-to-NUMERIC and modeled string common-type coercions.",
                        );
                        return None;
                    }
                    _ => constant,
                };
                let numeric_dscale = match literal.source_ty {
                    Some(FormalAttributeType::Int32 | FormalAttributeType::Int64)
                        if literal.ty == FormalAttributeType::Numeric =>
                    {
                        Some(NumericDscaleProvenance::Exact(0))
                    }
                    _ if literal.ty == FormalAttributeType::Numeric => {
                        super::emit::parse_decimal_literal(&literal.raw)
                            .map(|(_, scale)| NumericDscaleProvenance::Exact(scale))
                    }
                    _ => numeric_dscale_for_type(column.ty),
                };
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr { term },
                    alias: column.name.clone(),
                    alias_ty: column.ty,
                    numeric_dscale,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(FormalQueryExpr::EmptyTuple),
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
                source_ty: None,
            }),
            FormalFunctionTerm::ScalarCall {
                operator:
                    ScalarOperator::Cast(ScalarCast::ToNumeric(
                        source @ (ScalarNumericSource::Int32 | ScalarNumericSource::Int64),
                    )),
                args,
            } =>
            {
                let [FormalFunctionTerm::Constant {
                    raw,
                    ty: Some(source_ty),
                }] = args.as_slice()
                else {
                    self.error(
                        path,
                        "values_integral_numeric_cast_not_supported",
                        "A VALUES integral-to-NUMERIC coercion must contain one exact typed constant.",
                    );
                    return None;
                };
                let expected_source = match source {
                    ScalarNumericSource::Int32 => FormalAttributeType::Int32,
                    ScalarNumericSource::Int64 => FormalAttributeType::Int64,
                    _ => unreachable!("VALUES cast pattern accepts only integral sources"),
                };
                if *source_ty != expected_source {
                    self.error(
                        path,
                        "values_integral_numeric_cast_not_supported",
                        "A VALUES integral-to-NUMERIC coercion function does not match its exact constant type.",
                    );
                    return None;
                }
                Some(ValuesCell {
                    raw: raw.clone(),
                    ty: Some(FormalAttributeType::Numeric),
                    source_ty: Some(expected_source),
                })
            }
            FormalFunctionTerm::ScalarCall {
                operator: ScalarOperator::Cast(ScalarCast::StringExplicit),
                args,
            } =>
            {
                lower_values_string_cast_cell(args).or_else(|| {
                    self.error(
                        path,
                        "values_string_cast_not_supported",
                        "VALUES supports an explicit string cast only when its operand is a literal and its target typmod is structured.",
                    );
                    None
                })
            }
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
        inferred.or_else(|| Some(self.unresolved_null_postgres_type(path)))
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
                        let inferred_source_ty = match cell.ty {
                            Some(cell_ty)
                                if !attribute_types_compatible_for_values(cell_ty, column.ty) =>
                            {
                                if matches!(cell_ty, FormalAttributeType::String { .. })
                                    && set_string_common_type_target(column.ty)
                                {
                                    Some(cell_ty)
                                } else {
                                    self.error(
                                        &format!("{path}.rows[{row_index}][{column_index}]"),
                                        "values_literal_type_mismatch",
                                        "VALUES literal type does not match the output column type.",
                                    );
                                    return None;
                                }
                            }
                            _ => None,
                        };
                        let source_ty = match cell.source_ty {
                            Some(source_ty)
                                if matches!(
                                    source_ty,
                                    FormalAttributeType::Int32 | FormalAttributeType::Int64
                                ) && cell.ty == Some(FormalAttributeType::Numeric)
                                    && column.ty == FormalAttributeType::Numeric =>
                            {
                                Some(source_ty)
                            }
                            Some(_) => {
                                self.error(
                                    &format!("{path}.rows[{row_index}][{column_index}]"),
                                    "values_literal_coercion_not_supported",
                                    "VALUES cell source typing supports only an exact integral-to-NUMERIC coercion.",
                                );
                                return None;
                            }
                            None => inferred_source_ty,
                        };
                        self.validate_literal_for_output_type(
                            &format!("{path}.rows[{row_index}][{column_index}]"),
                            &cell.raw,
                            column.ty,
                        )?;
                        Some(FormalValueLiteral {
                            raw: cell.raw.clone(),
                            ty: column.ty,
                            source_ty,
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
        scope: &Scope,
    ) -> Option<Vec<FormalSortKey>> {
        let mut keys = Vec::with_capacity(collation.len());
        for (index, key) in collation.iter().enumerate() {
            let Some(attribute) = scope.attribute(key.field_index) else {
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
                        "Exact query observation semantics supports ASC/DESC ordering, not Calcite clustered collation.",
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
                    "Query-expression ordering requires explicit NULLS FIRST/LAST semantics.",
                );
                return None;
            };
            let null_direction = match null_direction {
                SortNullDirection::First => FormalNullDirection::First,
                SortNullDirection::Last => FormalNullDirection::Last,
            };
            let attribute_ty = attribute.formal_ty;
            if matches!(attribute_ty, FormalAttributeType::String { .. })
                && !self
                    .config
                    .sql_environment
                    .has_postgres_utf8_c_text_semantics()
            {
                self.error(
                    &format!("{path}.collation[{index}].field"),
                    "string_collation_sort_not_supported",
                    "PostgreSQL string ORDER BY is lowered only for an explicitly attested UTF8 database with libc provider, default collation C, and character classification C.",
                );
                return None;
            }
            keys.push(FormalSortKey {
                attribute_name: attribute.name,
                attribute_ty,
                direction,
                null_direction,
            });
        }
        Some(keys)
    }

    fn lower_row_count(&mut self, path: &str, expr: &ScalarExpr) -> Option<u64> {
        match unsigned_integer_literal_ast(&expr.parsed) {
            Some(value) if value <= i64::MAX as u64 => Some(value),
            Some(_) => {
                self.error(
                    path,
                    "row_count_out_of_bigint_range",
                    "PostgreSQL LIMIT/OFFSET integer literals must fit the signed BIGINT range.",
                );
                None
            }
            None => {
                self.error(
                    path,
                    "row_count_not_supported",
                    "Query-expression lowering currently supports only non-negative integer literal LIMIT/OFFSET counts.",
                );
                None
            }
        }
    }

    fn lower_sort_row_counts(
        &mut self,
        path: &str,
        offset: Option<&ScalarExpr>,
        fetch: Option<&ScalarExpr>,
    ) -> Option<(Option<u64>, Option<u64>)> {
        let offset_count =
            offset.and_then(|expr| self.lower_row_count(&format!("{path}.offset"), expr));
        let fetch_count =
            fetch.and_then(|expr| self.lower_row_count(&format!("{path}.fetch"), expr));
        if (offset.is_some() && offset_count.is_none())
            || (fetch.is_some() && fetch_count.is_none())
        {
            None
        } else {
            Some((offset_count, fetch_count))
        }
    }

    fn lower_set(
        &mut self,
        path: &str,
        op: SetOp,
        all: bool,
        inputs: &[RelExpr],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if inputs.len() < 2 {
            self.error(
                path,
                "set_arity_not_supported",
                "The FormalSQL set-expression constructor is binary.",
            );
            return None;
        }
        let formal_op = match op {
            SetOp::Union => FormalSetOp::Union,
            SetOp::Intersect => FormalSetOp::Inter,
            SetOp::Except => FormalSetOp::Diff,
        };
        let case_mapping_text_positions = set_case_mapping_text_positions(inputs, output.len());
        let mut iter = inputs.iter().enumerate();
        let (_, first) = iter.next()?;
        let mut acc = self.lower_rel(&format!("{path}.inputs[0]"), first)?;
        let mut acc_scope =
            self.scope_from_lowered_query(&format!("{path}.inputs[0].actualScope"), &acc)?;
        let mut acc_literal_provenance = self
            .set_input_literal_provenance(&format!("{path}.inputs[0].literalProvenance"), first)?;
        for (index, input) in iter {
            let mut right = self.lower_rel(&format!("{path}.inputs[{index}]"), input)?;
            let right_scope = self
                .scope_from_lowered_query(&format!("{path}.inputs[{index}].actualScope"), &right)?;
            let right_literal_provenance = self.set_input_literal_provenance(
                &format!("{path}.inputs[{index}].literalProvenance"),
                input,
            )?;
            let common_scope = self.resolve_binary_set_scope(
                &format!("{path}.inputs[{index}].commonType"),
                BinarySetScopeInputs {
                    left: &acc_scope,
                    right: &right_scope,
                    left_literal_provenance: &acc_literal_provenance,
                    right_literal_provenance: &right_literal_provenance,
                    reported_output: output,
                    case_mapping_text_positions: &case_mapping_text_positions,
                },
            )?;
            acc = self.align_set_input(
                &format!("{path}.inputs[0..{index}].positionAlignment"),
                acc,
                &acc_scope,
                &acc_literal_provenance,
                &common_scope,
            )?;
            right = self.align_set_input(
                &format!("{path}.inputs[{index}].positionAlignment"),
                right,
                &right_scope,
                &right_literal_provenance,
                &common_scope,
            )?;
            // SQL EXCEPT DISTINCT is delta(left) - delta(right), not
            // delta(left - right): {x,x} EXCEPT {x} must be empty.
            if !all && matches!(op, SetOp::Except) {
                acc = Self::distinct_query(acc, &common_scope);
                right = Self::distinct_query(right, &common_scope);
            }
            acc = FormalQueryExpr::Set {
                op: formal_op,
                left: Box::new(acc),
                right: Box::new(right),
            };
            acc_scope = common_scope;
            acc_literal_provenance =
                vec![SetInputLiteralProvenance::Known; acc_scope.attributes.len()];
        }
        if !all && !matches!(op, SetOp::Except) {
            acc = Self::distinct_query(acc, &acc_scope);
        }
        Some(acc)
    }

    fn lower_query_expr_set(
        &mut self,
        path: &str,
        op: SetOp,
        all: bool,
        inputs: &[RelExpr],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if inputs.len() < 2 {
            self.error(
                path,
                "set_arity_not_supported",
                "Query-expression set operations are binary.",
            );
            return None;
        }
        let formal_op = match op {
            SetOp::Union => FormalSetOp::Union,
            SetOp::Intersect => FormalSetOp::Inter,
            SetOp::Except => FormalSetOp::Diff,
        };
        let case_mapping_text_positions = set_case_mapping_text_positions(inputs, output.len());
        let mut iter = inputs.iter().enumerate();
        let (_, first) = iter.next()?;
        let mut acc = self.lower_query_expr(&format!("{path}.inputs[0]"), first)?;
        let mut acc_scope =
            self.scope_from_query_expr(&format!("{path}.inputs[0].actualScope"), &acc)?;
        let mut acc_literal_provenance = self
            .set_input_literal_provenance(&format!("{path}.inputs[0].literalProvenance"), first)?;
        for (index, input) in iter {
            let mut right = self.lower_query_expr(&format!("{path}.inputs[{index}]"), input)?;
            let right_scope =
                self.scope_from_query_expr(&format!("{path}.inputs[{index}].actualScope"), &right)?;
            let right_literal_provenance = self.set_input_literal_provenance(
                &format!("{path}.inputs[{index}].literalProvenance"),
                input,
            )?;
            let common_scope = self.resolve_binary_set_scope(
                &format!("{path}.inputs[{index}].commonType"),
                BinarySetScopeInputs {
                    left: &acc_scope,
                    right: &right_scope,
                    left_literal_provenance: &acc_literal_provenance,
                    right_literal_provenance: &right_literal_provenance,
                    reported_output: output,
                    case_mapping_text_positions: &case_mapping_text_positions,
                },
            )?;
            acc = self.align_query_expr_set_input(
                &format!("{path}.inputs[0..{index}].positionAlignment"),
                acc,
                &acc_scope,
                &acc_literal_provenance,
                &common_scope,
            )?;
            right = self.align_query_expr_set_input(
                &format!("{path}.inputs[{index}].positionAlignment"),
                right,
                &right_scope,
                &right_literal_provenance,
                &common_scope,
            )?;
            if !all && matches!(op, SetOp::Except) {
                acc = Self::distinct_query_expr(acc);
                right = Self::distinct_query_expr(right);
            }
            acc = FormalQueryExpr::Set {
                op: formal_op,
                left: Box::new(acc),
                right: Box::new(right),
            };
            acc_scope = common_scope;
            acc_literal_provenance =
                vec![SetInputLiteralProvenance::Known; acc_scope.attributes.len()];
        }
        if !all && !matches!(op, SetOp::Except) {
            acc = Self::distinct_query_expr(acc);
        }
        Some(acc)
    }

    fn resolve_binary_set_scope(
        &mut self,
        path: &str,
        inputs: BinarySetScopeInputs<'_>,
    ) -> Option<Scope> {
        let BinarySetScopeInputs {
            left,
            right,
            left_literal_provenance,
            right_literal_provenance,
            reported_output,
            case_mapping_text_positions,
        } = inputs;
        if left.attributes.len() != right.attributes.len()
            || left.attributes.len() != reported_output.len()
            || left.attributes.len() != left_literal_provenance.len()
            || right.attributes.len() != right_literal_provenance.len()
        {
            self.error(
                path,
                "set_input_arity_mismatch",
                "SQL set-operation inputs and the reported output must have the same positional arity.",
            );
            return None;
        }
        if !has_unique_column_names(reported_output) {
            self.error(
                path,
                "set_output_duplicate_name_not_supported",
                "FormalSQL needs unique canonical labels when aligning set-operation columns by position.",
            );
            return None;
        }

        let attributes = left
            .attributes
            .iter()
            .zip(&right.attributes)
            .zip(reported_output)
            .enumerate()
            .map(|(index, ((left_attribute, right_attribute), reported_column))| {
                let Some(formal_ty) = postgres_binary_set_common_type(
                    left_attribute.formal_ty,
                    right_attribute.formal_ty,
                    left_literal_provenance[index].is_unknown(),
                    right_literal_provenance[index].is_unknown(),
                ) else {
                    self.error(
                        &format!("{path}.output[{index}]"),
                        "set_input_type_override_not_supported",
                        "The independently lowered set inputs have different PostgreSQL types, and this exact common-type/coercion pair is not modeled. Calcite output metadata is not used to relabel either child.",
                    );
                    return None;
                };
                let reported_ty = self.lower_attribute_type(
                    &format!("{path}.reportedOutput[{index}]"),
                    reported_column,
                    AttributeTypeContext::QueryOutput,
                )?;
                if formal_ty != reported_ty {
                    let (code, message) = if formal_ty == FormalAttributeType::Numeric {
                        (
                            "calcite_set_numeric_type_overridden",
                            "Every independently lowered input at this set position has PostgreSQL unconstrained NUMERIC type; FormalSQL propagates that common type instead of Calcite's stale fixed-DECIMAL metadata.",
                        )
                    } else if formal_ty
                        == (FormalAttributeType::String {
                            typmod: SqlStringType::Text,
                        })
                        && case_mapping_text_positions.contains(&index)
                    {
                        (
                            "calcite_set_string_case_mapping_type_overridden",
                            "Every set-operation input at this position is PostgreSQL UPPER/LOWER, whose common result type is text; FormalSQL ignores Calcite's stale constrained-character metadata.",
                        )
                    } else {
                        (
                            "calcite_set_output_type_overridden",
                            "The independently lowered set inputs establish a PostgreSQL common type that differs from Calcite's reported output metadata; FormalSQL preserves the child-derived type and applies only modeled positional coercions.",
                        )
                    };
                    self.warning(&format!("{path}.output[{index}]"), code, message);
                }
                Some(ScopeAttribute {
                    name: reported_column.name.clone(),
                    visible_name: reported_column.name.clone(),
                    formal_ty,
                    numeric_dscale: match (
                        left_literal_provenance[index].is_unknown(),
                        right_literal_provenance[index].is_unknown(),
                    ) {
                        (true, false) => right_attribute.numeric_dscale.clone(),
                        (false, true) => left_attribute.numeric_dscale.clone(),
                        (false, false)
                            if left_attribute.numeric_dscale
                                == right_attribute.numeric_dscale =>
                        {
                            left_attribute.numeric_dscale.clone()
                        }
                        _ => None,
                    },
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Scope { attributes })
    }

    fn set_input_literal_provenance(
        &mut self,
        path: &str,
        input: &RelExpr,
    ) -> Option<Vec<SetInputLiteralProvenance>> {
        source_set_literal_provenance(input).or_else(|| {
            self.error(
                path,
                "set_unknown_literal_provenance_required",
                "A set input contains a top-level bare NULL or string literal whose independently parsed source node is missing or ambiguous. Calcite's contextual type cannot distinguish PostgreSQL unknown from an explicit cast, so the set is rejected rather than trusting that metadata.",
            );
            None
        })
    }

    fn align_query_expr_set_input(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        input_scope: &Scope,
        input_literal_provenance: &[SetInputLiteralProvenance],
        set_scope: &Scope,
    ) -> Option<FormalQueryExpr> {
        if input_scope.attributes.len() != set_scope.attributes.len()
            || input_scope.attributes.len() != input_literal_provenance.len()
        {
            self.error(
                path,
                "set_input_arity_mismatch",
                "SQL set-operation inputs must have the same positional arity as the set output.",
            );
            return None;
        }
        let select = set_scope
            .attributes
            .iter()
            .enumerate()
            .map(|(index, output_attribute)| {
                let input_attribute = input_scope.attribute(index)?;
                let numeric_dscale = if input_literal_provenance[index].is_unknown() {
                    output_attribute.numeric_dscale.clone()
                } else {
                    input_attribute.numeric_dscale.clone()
                };
                Some(FormalSelectItem {
                    expr: self.align_set_input_expression(
                        &format!("{path}.output[{index}]"),
                        input_attribute,
                        input_literal_provenance[index],
                        output_attribute.formal_ty,
                    )?,
                    alias: output_attribute.name.clone(),
                    alias_ty: output_attribute.formal_ty,
                    numeric_dscale,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(input),
        })
    }

    fn require_distinct_output_matches_input(
        &mut self,
        path: &str,
        input: &FormalQueryExpr,
        output: &[Column],
    ) -> Option<()> {
        let input_scope = self.scope_from_query_expr(&format!("{path}.input"), input)?;
        let output_scope = self.lower_scope(&format!("{path}.reported"), output)?;
        if input_scope.attributes.len() != output_scope.attributes.len()
            || input_scope
                .attributes
                .iter()
                .zip(&output_scope.attributes)
                .any(|(input, output)| {
                    input.visible_name != output.visible_name || input.formal_ty != output.formal_ty
                })
        {
            self.error(
                path,
                "distinct_output_type_override_not_supported",
                "SELECT DISTINCT must preserve every input output name and PostgreSQL type; duplicate elimination cannot rename or coerce a column.",
            );
            return None;
        }
        Some(())
    }

    fn distinct_query_expr(input: FormalQueryExpr) -> FormalQueryExpr {
        FormalQueryExpr::Distinct {
            input: Box::new(input),
        }
    }

    fn align_set_input(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        input_scope: &Scope,
        input_literal_provenance: &[SetInputLiteralProvenance],
        set_scope: &Scope,
    ) -> Option<FormalQueryExpr> {
        if input_scope.attributes.len() != set_scope.attributes.len()
            || input_scope.attributes.len() != input_literal_provenance.len()
        {
            self.error(
                path,
                "set_input_arity_mismatch",
                "SQL set-operation inputs must have the same positional arity as the set output.",
            );
            return None;
        }
        let select = set_scope
            .attributes
            .iter()
            .enumerate()
            .map(|(index, output_attribute)| {
                let input_attribute = input_scope.attribute(index)?;
                let numeric_dscale = if input_literal_provenance[index].is_unknown() {
                    output_attribute.numeric_dscale.clone()
                } else {
                    input_attribute.numeric_dscale.clone()
                };
                Some(FormalSelectItem {
                    expr: self.align_set_input_expression(
                        &format!("{path}.output[{index}]"),
                        input_attribute,
                        input_literal_provenance[index],
                        output_attribute.formal_ty,
                    )?,
                    alias: output_attribute.name.clone(),
                    alias_ty: output_attribute.formal_ty,
                    numeric_dscale,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(input),
        })
    }

    fn align_set_input_expression(
        &mut self,
        path: &str,
        input: ScopeAttribute,
        input_literal_provenance: SetInputLiteralProvenance,
        output_ty: FormalAttributeType,
    ) -> Option<FormalAggregateTerm> {
        if matches!(
            input_literal_provenance,
            SetInputLiteralProvenance::UnknownNull
        ) {
            return Some(FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "NULL".to_owned(),
                    ty: Some(output_ty),
                },
            });
        }
        let attribute = FormalFunctionTerm::Attribute {
            name: input.name,
            ty: input.formal_ty,
        };
        if matches!(
            input_literal_provenance,
            SetInputLiteralProvenance::UnknownString
        ) && !matches!(output_ty, FormalAttributeType::String { .. })
        {
            self.error(
                path,
                "set_unknown_string_target_not_supported",
                "PostgreSQL can coerce an unknown string literal to the selected non-string set type during parse analysis, but that type's input conversion and possible error are not modeled here.",
            );
            return None;
        }
        if input.formal_ty == output_ty {
            return Some(FormalAggregateTerm::Expr { term: attribute });
        }

        if matches!(input.formal_ty, FormalAttributeType::String { .. })
            && set_string_common_type_target(output_ty)
        {
            return Some(FormalAggregateTerm::Expr {
                term: string_implicit_coercion_term(attribute, output_ty)?,
            });
        }

        if matches!(input.formal_ty, FormalAttributeType::Decimal { .. })
            && output_ty == FormalAttributeType::Numeric
        {
            return Some(FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::ScalarCall {
                    operator: ScalarOperator::Cast(ScalarCast::ToNumeric(
                        ScalarNumericSource::Numeric,
                    )),
                    args: vec![attribute],
                },
            });
        }

        self.error(
            path,
            "set_input_positional_type_mismatch",
            "Set-operation input and output types differ after lowering, and no modeled PostgreSQL implicit common-type coercion applies.",
        );
        None
    }

    fn distinct_query(input: FormalQueryExpr, output_scope: &Scope) -> FormalQueryExpr {
        let group_by = output_scope
            .attributes
            .iter()
            .map(|attribute| FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: attribute.name.clone(),
                    ty: attribute.formal_ty,
                },
            })
            .collect();
        let select = output_scope
            .attributes
            .iter()
            .map(|attribute| FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attribute.name.clone(),
                        ty: attribute.formal_ty,
                    },
                },
                alias: attribute.name.clone(),
                alias_ty: attribute.formal_ty,
                numeric_dscale: attribute.numeric_dscale.clone(),
            })
            .collect();

        FormalQueryExpr::Group {
            select,
            group_by,
            having: FormalFormulaExpr::True,
            input: Box::new(input),
        }
    }

    fn lower_query_expr_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        join_type: JoinType,
        condition: &ScalarExpr,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        match join_type {
            JoinType::Inner => {
                self.lower_query_expr_inner_join(path, left, right, &condition.parsed, output)
            }
            JoinType::Left | JoinType::Right | JoinType::Full => self.lower_query_expr_outer_join(
                path,
                left,
                right,
                join_type,
                &condition.parsed,
                output,
            ),
            JoinType::Semi | JoinType::Anti => self.lower_query_expr_existence_join(
                path,
                left,
                right,
                join_type,
                &condition.parsed,
                output,
            ),
        }
    }

    fn lower_query_expr_inner_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
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
        let cross_join =
            self.lower_query_expr_cross_join(path, left, left_output, right, right_output)?;
        if !is_true_literal(condition) {
            let scope =
                self.scope_from_query_expr(&format!("{path}.conditionScope"), &cross_join)?;
            let isolate = scalar_ast_contains_rel_subquery(condition);
            let (predicate_input, predicate_scope) = if isolate {
                self.isolate_query_scope_for_subquery_owner(
                    &format!("{path}.conditionBarrier"),
                    cross_join,
                    &scope,
                    &[condition],
                )?
            } else {
                (cross_join, scope)
            };
            let predicate = self.lower_native_scalar_boolean_expr(
                &format!("{path}.condition"),
                condition,
                &predicate_scope,
            )?;
            let selection = FormalQueryExpr::ScalarSelection {
                predicate,
                input: Box::new(predicate_input),
            };
            if !isolate {
                return Some(selection);
            }
            let output_scope = self.scope_restored_to_visible_names(
                &format!("{path}.conditionOutput"),
                &predicate_scope,
            )?;
            return Some(FormalQueryExpr::Projection {
                select: self.lower_scope_rename_select(
                    &format!("{path}.conditionOutput"),
                    &predicate_scope,
                    &output_scope,
                )?,
                input: Box::new(selection),
            });
        }
        Some(cross_join)
    }

    fn lower_query_expr_outer_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        join_type: JoinType,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if scalar_ast_contains_rel_subquery(condition) {
            self.error(
                &format!("{path}.condition"),
                "outer_join_subquery_scope_barrier_not_supported",
                "An outer-join condition containing a relational subquery requires capture-avoiding renaming of both child rows together with matched and null-padded output transport; this path is conservatively unsupported until that complete transport is modeled.",
            );
            return None;
        }
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
        let left = self.lower_query_expr_join_input(&format!("{path}.left"), left, left_output)?;
        let right =
            self.lower_query_expr_join_input(&format!("{path}.right"), right, right_output)?;
        // Derive the join scope from the already-lowered children.  Logical
        // joins do not re-coerce values, and Calcite can retain stale fixed
        // DECIMAL metadata for a typmodless PostgreSQL NUMERIC child.  The
        // derived scope also carries exact display-scale provenance through
        // matched and null-padded outer-join rows.
        let left_scope = self.scope_from_query_expr(&format!("{path}.leftScope"), &left)?;
        let right_scope = self.scope_from_query_expr(&format!("{path}.rightScope"), &right)?;
        if left_scope.attributes.len() != left_output.len()
            || right_scope.attributes.len() != right_output.len()
        {
            self.error(
                path,
                "outer_join_auxiliary_dscale_not_supported",
                "Outer joins over runtime-scale NUMERIC auxiliaries require null-padding the value/scale pair together and are conservatively unsupported.",
            );
            return None;
        }
        let mut scope = left_scope.clone();
        scope.attributes.extend(right_scope.attributes.clone());
        if !has_unique_scope_names(&scope) {
            self.error(
                path,
                "outer_join_column_overlap",
                "FormalSQL outer join lowering requires disjoint lowered child attributes.",
            );
            return None;
        }
        let predicate = self.lower_formula_expr(&format!("{path}.condition"), condition, &scope)?;
        let join_kind = match join_type {
            JoinType::Left => FormalQueryJoinKind::Left,
            JoinType::Right => FormalQueryJoinKind::Right,
            JoinType::Full => FormalQueryJoinKind::Full,
            _ => unreachable!("query-expression outer join called with non-outer join type"),
        };
        Some(FormalQueryExpr::Join {
            join_kind,
            predicate,
            matched_select: self.lower_scope_rename_select(
                &format!("{path}.matchedOutput"),
                &scope,
                &scope,
            )?,
            left_select: self.outer_join_padding_scope_select(&left_scope, &right_scope, true),
            right_select: self.outer_join_padding_scope_select(&left_scope, &right_scope, false),
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    fn lower_query_expr_existence_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        join_type: JoinType,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if scalar_ast_contains_rel_subquery(condition) {
            self.error(
                &format!("{path}.condition"),
                "existence_join_subquery_scope_barrier_not_supported",
                "A semi/anti-join condition containing a relational subquery requires capture-avoiding renaming of both child rows and output transport; this path is conservatively unsupported until that complete transport is modeled.",
            );
            return None;
        }
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
        let left = self.lower_query_expr_join_input(&format!("{path}.left"), left, output)?;
        let right =
            self.lower_query_expr_join_input(&format!("{path}.right"), right, &right_output)?;
        let left_scope = self.scope_from_query_expr(&format!("{path}.leftScope"), &left)?;
        let right_scope = self.scope_from_query_expr(&format!("{path}.rightScope"), &right)?;
        if left_scope.attributes.len() != output.len()
            || right_scope.attributes.len() != right_output.len()
        {
            self.error(
                path,
                "existence_join_auxiliary_dscale_not_supported",
                "SEMI/ANTI joins over runtime-scale NUMERIC auxiliaries are conservatively unsupported until value/scale liveness is represented across the existence boundary.",
            );
            return None;
        }
        let mut scope = left_scope.clone();
        scope.attributes.extend(right_scope.attributes.clone());
        if !has_unique_scope_names(&scope) {
            self.error(
                path,
                "existence_join_column_overlap",
                "FormalSQL semi/anti join lowering requires disjoint lowered child attributes.",
            );
            return None;
        }
        let predicate = self.lower_formula_expr(&format!("{path}.condition"), condition, &scope)?;
        let join_kind = match join_type {
            JoinType::Semi => FormalQueryJoinKind::Semi,
            JoinType::Anti => FormalQueryJoinKind::Anti,
            _ => unreachable!("query-expression existence join called with other join type"),
        };
        let output_select = self.lower_scope_rename_select(
            &format!("{path}.existenceOutput"),
            &left_scope,
            &left_scope,
        )?;
        Some(FormalQueryExpr::Join {
            join_kind,
            predicate,
            matched_select: output_select.clone(),
            left_select: output_select,
            // This select is unreachable for SEMI/ANTI, but keeping it empty
            // makes that fact visible in emitted syntax.
            right_select: Vec::new(),
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    fn lower_query_expr_cross_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        left_output: &[Column],
        right: &RelExpr,
        right_output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if !disjoint_columns(left_output, right_output) {
            self.error(
                path,
                "cross_join_column_overlap",
                "Calcite join output still contains overlapping names; FormalSQL tuples are keyed by attribute sets and need unique attributes.",
            );
            return None;
        }
        let left = self.lower_query_expr_join_input(&format!("{path}.left"), left, left_output)?;
        let right =
            self.lower_query_expr_join_input(&format!("{path}.right"), right, right_output)?;
        let left_scope = self.scope_from_query_expr(&format!("{path}.leftScope"), &left)?;
        let right_scope = self.scope_from_query_expr(&format!("{path}.rightScope"), &right)?;
        let mut combined_scope = left_scope.clone();
        combined_scope
            .attributes
            .extend(right_scope.attributes.clone());
        if !has_unique_scope_names(&combined_scope) {
            self.error(
                path,
                "cross_join_column_overlap",
                "FormalSQL cross join lowering requires disjoint SQL-visible and hidden auxiliary attributes.",
            );
            return None;
        }
        let joined = FormalQueryExpr::CrossJoin {
            left: Box::new(left),
            right: Box::new(right),
        };
        if left_scope.attributes.len() == left_output.len()
            && right_scope.attributes.len() == right_output.len()
        {
            return Some(joined);
        }
        // Each child keeps its hidden display-scale attributes after its
        // visible prefix. Reorder the combined scope so every raw Calcite
        // input index still addresses left-visible ++ right-visible, while
        // all non-SQL auxiliaries remain in a trailing suffix.
        let ordered = left_scope.attributes[..left_output.len()]
            .iter()
            .chain(&right_scope.attributes[..right_output.len()])
            .chain(&left_scope.attributes[left_output.len()..])
            .chain(&right_scope.attributes[right_output.len()..]);
        let select = ordered
            .map(|attribute| FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attribute.name.clone(),
                        ty: attribute.formal_ty,
                    },
                },
                alias: attribute.name.clone(),
                alias_ty: attribute.formal_ty,
                numeric_dscale: attribute.numeric_dscale.clone(),
            })
            .collect();
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(joined),
        })
    }

    fn lower_query_expr_join_input(
        &mut self,
        path: &str,
        rel: &RelExpr,
        join_output: &[Column],
    ) -> Option<FormalQueryExpr> {
        let input_output = rel.output();
        if input_output.len() != join_output.len() {
            self.error(
                path,
                "join_input_output_arity_mismatch",
                "Calcite join output slice does not match child output arity.",
            );
            return None;
        }
        let input = self.lower_query_expr(path, rel)?;
        let input_scope = self.scope_from_query_expr(&format!("{path}.inputOutput"), &input)?;
        if !scope_has_well_formed_auxiliary_dscales(&input_scope, input_output.len()) {
            self.error(
                path,
                "join_input_auxiliary_dscale_shape_not_supported",
                "A query-expression join input may carry only uniquely named hidden Z attributes referenced as runtime NUMERIC display scales by its SQL-visible prefix.",
            );
            return None;
        }
        let mut select = input_scope
            .attributes
            .iter()
            .take(input_output.len())
            .zip(join_output)
            .enumerate()
            .map(|(index, (source, target))| {
                let mut target_ty = self.lower_attribute_type(
                    &format!("{path}.joinOutput[{index}]"),
                    target,
                    AttributeTypeContext::QueryOutput,
                )?;
                if source.formal_ty == FormalAttributeType::Numeric
                    && calcite_stale_numeric_copy_type(target_ty)
                {
                    // A logical join does not coerce its child columns.  Any
                    // source-visible cast must already occur in the lowered
                    // child expression, so the independently derived child
                    // type is authoritative here. Calcite can reattach either
                    // the aggregate argument's integral type or a stale fixed
                    // typmod while copying a NUMERIC expression through a
                    // join row type.
                    self.warning(
                        &format!("{path}.joinOutput[{index}]"),
                        "calcite_join_numeric_type_overridden",
                        "A logical PostgreSQL join preserves the independently lowered unconstrained NUMERIC child type; Calcite's copied integral or fixed-DECIMAL row metadata is not a cast.",
                    );
                    target_ty = FormalAttributeType::Numeric;
                }
                if source.formal_ty != target_ty {
                    self.error(
                        &format!("{path}.joinOutput[{index}]"),
                        "join_output_type_not_supported",
                        "Join output coercion differs from the lowered child type and is not an explicit SQL cast.",
                    );
                    return None;
                }
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: source.name.clone(),
                            ty: source.formal_ty,
                        },
                    },
                    alias: target.name.clone(),
                    alias_ty: target_ty,
                    numeric_dscale: source.numeric_dscale.clone(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        select.extend(
            input_scope
                .attributes
                .iter()
                .skip(input_output.len())
                .map(|attribute| FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: attribute.name.clone(),
                            ty: attribute.formal_ty,
                        },
                    },
                    alias: attribute.name.clone(),
                    alias_ty: attribute.formal_ty,
                    numeric_dscale: attribute.numeric_dscale.clone(),
                }),
        );
        Some(FormalQueryExpr::Projection {
            select,
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
    ) -> Option<FormalQueryExpr> {
        match join_type {
            JoinType::Inner => self.lower_inner_join(path, left, right, condition, output),
            JoinType::Left | JoinType::Right | JoinType::Full => {
                self.lower_query_expr_outer_join(path, left, right, join_type, condition, output)
            }
            JoinType::Semi | JoinType::Anti => self
                .lower_query_expr_existence_join(path, left, right, join_type, condition, output),
        }
    }

    fn lower_inner_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        right: &RelExpr,
        condition: &ScalarAst,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
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
        let cross_join = self.lower_cross_join(path, left, left_output, right, right_output)?;
        if !is_true_literal(condition) {
            let scope =
                self.scope_from_lowered_query(&format!("{path}.conditionScope"), &cross_join)?;
            let isolate = scalar_ast_contains_rel_subquery(condition);
            let (predicate_input, predicate_scope) = if isolate {
                self.isolate_query_scope_for_subquery_owner(
                    &format!("{path}.conditionBarrier"),
                    cross_join,
                    &scope,
                    &[condition],
                )?
            } else {
                (cross_join, scope)
            };
            let predicate = self.lower_native_scalar_boolean_expr(
                &format!("{path}.condition"),
                condition,
                &predicate_scope,
            )?;
            let selection = FormalQueryExpr::ScalarSelection {
                predicate,
                input: Box::new(predicate_input),
            };
            if !isolate {
                return Some(selection);
            }
            let output_scope = self.scope_restored_to_visible_names(
                &format!("{path}.conditionOutput"),
                &predicate_scope,
            )?;
            return Some(FormalQueryExpr::Projection {
                select: self.lower_scope_rename_select(
                    &format!("{path}.conditionOutput"),
                    &predicate_scope,
                    &output_scope,
                )?,
                input: Box::new(selection),
            });
        }
        Some(cross_join)
    }

    fn outer_join_padding_scope_select(
        &self,
        left: &Scope,
        right: &Scope,
        keep_left: bool,
    ) -> Vec<FormalSelectItem> {
        left.attributes
            .iter()
            .map(|attribute| (attribute, keep_left))
            .chain(
                right
                    .attributes
                    .iter()
                    .map(|attribute| (attribute, !keep_left)),
            )
            .map(|(attribute, keep)| FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: if keep {
                        FormalFunctionTerm::Attribute {
                            name: attribute.name.clone(),
                            ty: attribute.formal_ty,
                        }
                    } else {
                        FormalFunctionTerm::Constant {
                            raw: "NULL".to_owned(),
                            ty: Some(attribute.formal_ty),
                        }
                    },
                },
                alias: attribute.name.clone(),
                alias_ty: attribute.formal_ty,
                // A NULL-only arm contributes no conflicting value scale; the
                // join output's possible non-NULL values retain the child's
                // exact provenance.
                numeric_dscale: attribute.numeric_dscale.clone(),
            })
            .collect()
    }

    fn lower_cross_join(
        &mut self,
        path: &str,
        left: &RelExpr,
        left_output: &[Column],
        right: &RelExpr,
        right_output: &[Column],
    ) -> Option<FormalQueryExpr> {
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
        Some(FormalQueryExpr::CrossJoin {
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    fn lower_join_input(
        &mut self,
        path: &str,
        rel: &RelExpr,
        join_output: &[Column],
    ) -> Option<FormalQueryExpr> {
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
        let input_scope = self.scope_from_lowered_query(&format!("{path}.inputOutput"), &input)?;
        let select = input_scope
            .attributes
            .iter()
            .zip(join_output)
            .enumerate()
            .map(|(index, (source, target))| {
                let mut target_ty = self.lower_attribute_type(
                    &format!("{path}.joinOutput[{index}]"),
                    target,
                    AttributeTypeContext::QueryOutput,
                )?;
                if source.formal_ty == FormalAttributeType::Numeric
                    && calcite_stale_numeric_copy_type(target_ty)
                {
                    self.warning(
                        &format!("{path}.joinOutput[{index}]"),
                        "calcite_join_numeric_type_overridden",
                        "A logical PostgreSQL join preserves the independently lowered unconstrained NUMERIC child type; Calcite's copied integral or fixed-DECIMAL row metadata is not a cast.",
                    );
                    target_ty = FormalAttributeType::Numeric;
                }
                if source.formal_ty != target_ty {
                    self.error(
                        &format!("{path}.joinOutput[{index}]"),
                        "join_output_type_not_supported",
                        "Join output coercion differs from the lowered child type and is not an explicit SQL cast.",
                    );
                    return None;
                }
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: source.name.clone(),
                            ty: source.formal_ty,
                        },
                    },
                    alias: target.name.clone(),
                    alias_ty: target_ty,
                    numeric_dscale: source.numeric_dscale.clone(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(input),
        })
    }

    fn prepare_correlated_input(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        correlations: &[logos_ir::ir::CorrelationBinding],
        scalar_roots: &[&ScalarAst],
    ) -> Option<(FormalQueryExpr, Scope, Vec<CorrelationScope>, bool)> {
        let input_scope = self.scope_from_lowered_query(&format!("{path}.inputScope"), &input)?;
        let isolate_subquery_owner = scalar_roots
            .iter()
            .any(|scalar| scalar_ast_contains_rel_subquery(scalar));
        if correlations.is_empty() && !isolate_subquery_owner {
            return Some((input, input_scope, Vec::new(), false));
        }
        if correlations
            .iter()
            .any(|binding| binding.output.len() != input_scope.attributes.len())
        {
            self.error(
                path,
                "correlation_binding_arity_mismatch",
                "Calcite correlation row type does not match the relational input it is expected to bind.",
            );
            return None;
        }
        let renamed_names = self.allocate_bound_scope_names(
            &input_scope,
            scalar_roots,
            correlations
                .first()
                .map(|binding| binding.correlation.as_str()),
        );
        let renamed_scope = self.rename_scope_attributes(path, &input_scope, renamed_names)?;
        if !has_unique_scope_names(&renamed_scope)
            || renamed_scope.attributes.iter().any(|fresh| {
                input_scope
                    .attributes
                    .iter()
                    .any(|attribute| attribute.name == fresh.name)
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
        let select = self.lower_scope_rename_select(path, &input_scope, &renamed_scope)?;
        let renamed_input = FormalQueryExpr::Projection {
            select,
            input: Box::new(input),
        };
        let renamed_correlations = correlations
            .iter()
            .map(|binding| {
                Some(CorrelationScope {
                    correlation: binding.correlation.clone(),
                    scope: renamed_scope.clone(),
                    field_names: binding
                        .output
                        .iter()
                        .map(|column| column.name.clone())
                        .collect(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some((renamed_input, renamed_scope, renamed_correlations, true))
    }

    fn prepare_correlated_query_expr_input(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        correlations: &[logos_ir::ir::CorrelationBinding],
        scalar_roots: &[&ScalarAst],
    ) -> Option<(FormalQueryExpr, Scope, Vec<CorrelationScope>, bool)> {
        let input_scope = self.scope_from_query_expr(&format!("{path}.inputScope"), &input)?;
        let isolate_subquery_owner = scalar_roots
            .iter()
            .any(|scalar| scalar_ast_contains_rel_subquery(scalar));
        if correlations.is_empty() && !isolate_subquery_owner {
            return Some((input, input_scope, Vec::new(), false));
        }
        if correlations
            .iter()
            .any(|binding| binding.output.len() != input_scope.attributes.len())
        {
            self.error(
                path,
                "correlation_binding_arity_mismatch",
                "Calcite correlation row type does not match the relational input it is expected to bind.",
            );
            return None;
        }
        let renamed_names = self.allocate_bound_scope_names(
            &input_scope,
            scalar_roots,
            correlations
                .first()
                .map(|binding| binding.correlation.as_str()),
        );
        let renamed_scope = self.rename_scope_attributes(path, &input_scope, renamed_names)?;
        if !has_unique_scope_names(&renamed_scope)
            || renamed_scope.attributes.iter().any(|fresh| {
                input_scope
                    .attributes
                    .iter()
                    .any(|attribute| attribute.name == fresh.name)
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
        let select = self.lower_scope_rename_select(path, &input_scope, &renamed_scope)?;
        let renamed_input = FormalQueryExpr::Projection {
            select,
            input: Box::new(input),
        };
        let renamed_correlations = correlations
            .iter()
            .map(|binding| {
                Some(CorrelationScope {
                    correlation: binding.correlation.clone(),
                    scope: renamed_scope.clone(),
                    field_names: binding
                        .output
                        .iter()
                        .map(|column| column.name.clone())
                        .collect(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some((renamed_input, renamed_scope, renamed_correlations, true))
    }

    /// Allocate a deterministic set of FormalSQL-only names for the current
    /// evaluation slice.  Calcite's InputRef ordinals are local to their
    /// owning relational input; the barrier prevents the nominal FormalSQL
    /// environment from accidentally capturing an equally named attribute in
    /// a nested subquery (or vice versa).
    pub(super) fn allocate_scope_barrier_names(
        &mut self,
        input: &Scope,
        scalar_roots: &[&ScalarAst],
    ) -> Vec<String> {
        self.allocate_bound_scope_names(input, scalar_roots, None)
    }

    /// Reserve one globally fresh FormalSQL binding row.  Correlated owners
    /// retain the readable legacy prefix when it is genuinely fresh; if a
    /// user/nested scope already contains that spelling, the same generic
    /// allocator used for uncorrelated subquery barriers takes over.
    fn allocate_bound_scope_names(
        &mut self,
        input: &Scope,
        scalar_roots: &[&ScalarAst],
        correlation: Option<&str>,
    ) -> Vec<String> {
        let mut unavailable = self.scope_barrier_names.clone();
        unavailable.extend(
            input
                .attributes
                .iter()
                .map(|attribute| attribute.name.clone()),
        );
        for correlation in &self.correlations {
            unavailable.extend(
                correlation
                    .scope
                    .attributes
                    .iter()
                    .map(|attribute| attribute.name.clone()),
            );
        }
        for scalar in scalar_roots {
            collect_nested_rel_attribute_names(scalar, &mut unavailable);
        }

        if let Some(correlation) = correlation {
            let prefix = sanitize_correlation_name(correlation);
            let preferred = (0..input.attributes.len())
                .map(|index| format!("__logos_cor_{prefix}_{index}"))
                .collect::<Vec<_>>();
            if preferred.iter().all(|name| !unavailable.contains(name)) {
                self.scope_barrier_names.extend(preferred.iter().cloned());
                return preferred;
            }
        }

        loop {
            let generation = self.next_scope_barrier;
            self.next_scope_barrier = self.next_scope_barrier.saturating_add(1);
            let names = (0..input.attributes.len())
                .map(|index| format!("__logos_scope_{generation}_{index}"))
                .collect::<Vec<_>>();
            if names.iter().any(|name| unavailable.contains(name)) {
                continue;
            }
            self.scope_barrier_names.extend(names.iter().cloned());
            return names;
        }
    }

    fn isolate_query_scope_for_subquery_owner(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        input_scope: &Scope,
        scalar_roots: &[&ScalarAst],
    ) -> Option<(FormalQueryExpr, Scope)> {
        let names = self.allocate_scope_barrier_names(input_scope, scalar_roots);
        let isolated_scope = self.rename_scope_attributes(path, input_scope, names)?;
        let select = self.lower_scope_rename_select(path, input_scope, &isolated_scope)?;
        Some((
            FormalQueryExpr::Projection {
                select,
                input: Box::new(input),
            },
            isolated_scope,
        ))
    }

    fn scope_restored_to_visible_names(
        &mut self,
        path: &str,
        isolated_scope: &Scope,
    ) -> Option<Scope> {
        let names = isolated_scope
            .attributes
            .iter()
            .map(|attribute| attribute.visible_name.clone())
            .collect();
        let mut restored = self.rename_scope_attributes(path, isolated_scope, names)?;
        for attribute in &mut restored.attributes {
            attribute.visible_name = attribute.name.clone();
        }
        Some(restored)
    }

    /// Rename a complete row while rebinding every same-row dynamic NUMERIC
    /// display-scale reference to the corresponding output attribute.
    pub(super) fn rename_scope_attributes(
        &mut self,
        path: &str,
        input: &Scope,
        output_names: Vec<String>,
    ) -> Option<Scope> {
        if input.attributes.len() != output_names.len() {
            self.error(
                path,
                "scope_rename_arity_mismatch",
                "Formal query scope renaming requires identical input and output arity.",
            );
            return None;
        }
        if !has_unique_scope_names(input)
            || output_names.iter().enumerate().any(|(index, name)| {
                output_names
                    .iter()
                    .skip(index + 1)
                    .any(|other| other == name)
            })
        {
            self.error(
                path,
                "scope_rename_name_collision",
                "Formal query scope renaming requires unique input and output attribute names.",
            );
            return None;
        }

        let mut attributes = Vec::with_capacity(input.attributes.len());
        for (index, (attribute, output_name)) in
            input.attributes.iter().zip(&output_names).enumerate()
        {
            let numeric_dscale = match &attribute.numeric_dscale {
                Some(NumericDscaleProvenance::Attribute(source_name)) => {
                    let mut matches = input
                        .attributes
                        .iter()
                        .enumerate()
                        .filter(|(_, candidate)| candidate.name == *source_name);
                    let Some((scale_index, scale_attribute)) = matches.next() else {
                        self.error(
                            &format!("{path}[{index}]"),
                            "numeric_dscale_scope_rename_source_invalid",
                            "A renamed NUMERIC value references a display-scale attribute that is absent from its input row.",
                        );
                        return None;
                    };
                    if matches.next().is_some()
                        || scale_attribute.formal_ty != FormalAttributeType::Z
                    {
                        self.error(
                            &format!("{path}[{index}]"),
                            "numeric_dscale_scope_rename_source_invalid",
                            "A renamed NUMERIC display scale must resolve to one unique mathematical-integer input attribute.",
                        );
                        return None;
                    }
                    Some(NumericDscaleProvenance::Attribute(
                        output_names[scale_index].clone(),
                    ))
                }
                provenance => provenance.clone(),
            };
            attributes.push(ScopeAttribute {
                name: output_name.clone(),
                visible_name: attribute.visible_name.clone(),
                formal_ty: attribute.formal_ty,
                numeric_dscale,
            });
        }
        let scope = Scope { attributes };
        self.validate_scope_numeric_dscale_references(path, &scope)?;
        Some(scope)
    }

    pub(super) fn lower_scope_rename_select(
        &mut self,
        path: &str,
        input: &Scope,
        output: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        if input.attributes.len() != output.attributes.len() {
            self.error(
                path,
                "scope_rename_arity_mismatch",
                "Formal query scope renaming requires identical input and output arity.",
            );
            return None;
        }
        let expected_output = self.rename_scope_attributes(
            &format!("{path}.scope"),
            input,
            output
                .attributes
                .iter()
                .map(|attribute| attribute.name.clone())
                .collect(),
        )?;
        input
            .attributes
            .iter()
            .zip(output.attributes.iter().zip(&expected_output.attributes))
            .enumerate()
            .map(|(index, (source, (target, expected_target)))| {
                if source.formal_ty != target.formal_ty {
                    self.error(
                        &format!("{path}[{index}]"),
                        "scope_rename_type_mismatch",
                        "A lowered scope rename cannot change the formal attribute type.",
                    );
                    return None;
                }
                if target.numeric_dscale != expected_target.numeric_dscale {
                    self.error(
                        &format!("{path}[{index}]"),
                        "scope_rename_numeric_dscale_mismatch",
                        "A lowered scope rename must rebind dynamic NUMERIC display-scale provenance to the corresponding output attribute.",
                    );
                    return None;
                }
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: source.name.clone(),
                            ty: source.formal_ty,
                        },
                    },
                    alias: target.name.clone(),
                    alias_ty: target.formal_ty,
                    numeric_dscale: expected_target.numeric_dscale.clone(),
                })
            })
            .collect()
    }

    /// Lower a structured PostgreSQL RANK window into the logical FormalSQL
    /// rank reset. Partition/order expressions and ordinary target
    /// expressions are staged once before ranking. This transformation is
    /// derived from the declarative window specification and never from a
    /// physical WindowAgg, Sort, or frozen benchmark plan.
    fn lower_declarative_rank_window_projection(
        &mut self,
        path: &str,
        input: &RelExpr,
        input_query: FormalQueryExpr,
        exprs: &[ScalarExpr],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if exprs.len() != output.len() {
            self.error(
                path,
                "rank_projection_arity_mismatch",
                "A declarative RANK Project expression and output arities must match.",
            );
            return None;
        }
        if !has_unique_column_names(output) {
            self.error(
                path,
                "rank_projection_duplicate_alias",
                "A declarative RANK projection requires unique output aliases for FormalSQL tuple labels.",
            );
            return None;
        }
        let window_indexes = exprs
            .iter()
            .enumerate()
            .filter_map(|(index, expr)| {
                matches!(expr.parsed, ScalarAst::Window { .. }).then_some(index)
            })
            .collect::<Vec<_>>();
        let [window_index] = window_indexes.as_slice() else {
            self.error(
                path,
                "rank_window_count_not_supported",
                "A declarative RANK projection must contain exactly one top-level window expression.",
            );
            return None;
        };
        let ScalarAst::Window { parsed } = &exprs[*window_index].parsed else {
            unreachable!("window index was collected from a top-level window expression")
        };
        if !parsed.function.eq_ignore_ascii_case("RANK")
            || !parsed.args.is_empty()
            || parsed.partition_by.is_empty()
            || parsed.order_by.len() != 1
            || parsed.distinct
            || parsed.ignore_nulls
            || parsed.exclude.as_deref() != Some("EXCLUDE_NO_OTHER")
            || !matches!(
                parsed.frame.as_ref(),
                Some(WindowFrameAst {
                    units: WindowFrameUnits::Range,
                    start: WindowFrameBoundAst::UnboundedPreceding,
                    end: Some(WindowFrameBoundAst::CurrentRow),
                })
            )
        {
            self.error(
                &format!("{path}.exprs[{window_index}]"),
                "rank_window_shape_not_supported",
                "Declarative RANK currently requires RANK() over at least one partition expression and exactly one ordered key with Calcite's complete PostgreSQL default RANGE frame provenance.",
            );
            return None;
        }
        if exprs.iter().enumerate().any(|(index, expr)| {
            index != *window_index
                && (scalar_ast_contains_window(&expr.parsed)
                    || scalar_ast_contains_rel_subquery(&expr.parsed)
                    || scalar_ast_may_raise_runtime_for_input(&expr.parsed, input))
        }) || parsed.partition_by.iter().any(|expr| {
            scalar_ast_contains_window(expr)
                || scalar_ast_contains_rel_subquery(expr)
                || scalar_ast_may_raise_runtime_for_input(expr, input)
        }) || parsed.order_by.iter().any(|key| {
            scalar_ast_contains_window(&key.expr)
                || scalar_ast_contains_rel_subquery(&key.expr)
                || scalar_ast_may_raise_runtime_for_input(&key.expr, input)
        }) {
            self.error(
                path,
                "rank_window_expression_runtime_not_supported",
                "Declarative RANK may stage only total, uncorrelated partition, ordering, and ordinary target expressions before the logical rank reset.",
            );
            return None;
        }

        let rank_output_ty = self.lower_attribute_type(
            &format!("{path}.output[{window_index}]"),
            &output[*window_index],
            AttributeTypeContext::QueryOutput,
        )?;
        if rank_output_ty != FormalAttributeType::Int64 || output[*window_index].nullable {
            self.error(
                &format!("{path}.output[{window_index}]"),
                "rank_output_type_not_supported",
                "PostgreSQL RANK must have a non-null BIGINT output attribute.",
            );
            return None;
        }
        let input_scope =
            self.scope_from_query_expr(&format!("{path}.rankInputScope"), &input_query)?;
        let ordinary_exprs = exprs
            .iter()
            .enumerate()
            .filter(|(index, _)| index != window_index)
            .map(|(_, expr)| expr.clone())
            .collect::<Vec<_>>();
        let ordinary_output = output
            .iter()
            .enumerate()
            .filter(|(index, _)| index != window_index)
            .map(|(_, column)| column.clone())
            .collect::<Vec<_>>();
        let mut key_projection =
            self.lower_project_select(path, &ordinary_exprs, &ordinary_output, &input_scope)?;
        let mut used_names = input_scope
            .attributes
            .iter()
            .map(|attribute| attribute.name.clone())
            .chain(output.iter().map(|column| column.name.clone()))
            .collect::<BTreeSet<_>>();

        let mut partition_keys = Vec::with_capacity(parsed.partition_by.len());
        for (index, expr) in parsed.partition_by.iter().enumerate() {
            let alias = fresh_internal_attribute_name(
                &format!("__logos_rank_partition_{index}"),
                &mut used_names,
            );
            let (select, key) = self.lower_declarative_window_key_projection(
                &format!("{path}.exprs[{window_index}].partitionBy[{index}]"),
                expr,
                &input_scope,
                alias,
                FormalSortDirection::Asc,
                FormalNullDirection::First,
            )?;
            key_projection.push(select);
            partition_keys.push(key);
        }
        let mut order_keys = Vec::with_capacity(parsed.order_by.len());
        for (index, key) in parsed.order_by.iter().enumerate() {
            let direction = match key.direction.unwrap_or(SortDirection::Ascending) {
                SortDirection::Ascending | SortDirection::StrictlyAscending => {
                    FormalSortDirection::Asc
                }
                SortDirection::Descending | SortDirection::StrictlyDescending => {
                    FormalSortDirection::Desc
                }
                SortDirection::Clustered => {
                    self.error(
                        &format!("{path}.exprs[{window_index}].orderBy[{index}]"),
                        "rank_clustered_order_not_supported",
                        "PostgreSQL RANK requires an ASC/DESC window ordering, not Calcite clustered collation.",
                    );
                    return None;
                }
            };
            let null_direction = key
                .null_direction
                .or_else(|| {
                    key.direction
                        .unwrap_or(SortDirection::Ascending)
                        .default_null_direction()
                })
                .map(|null_direction| match null_direction {
                    SortNullDirection::First => FormalNullDirection::First,
                    SortNullDirection::Last => FormalNullDirection::Last,
                })?;
            let alias = fresh_internal_attribute_name(
                &format!("__logos_rank_order_{index}"),
                &mut used_names,
            );
            let (select, formal_key) = self.lower_declarative_window_key_projection(
                &format!("{path}.exprs[{window_index}].orderBy[{index}]"),
                &key.expr,
                &input_scope,
                alias,
                direction,
                null_direction,
            )?;
            key_projection.push(select);
            order_keys.push(formal_key);
        }

        let rank_attribute = FormalAttribute {
            name: output[*window_index].name.clone(),
            ty: FormalAttributeType::Int64,
        };
        let mut ranked_scope = Scope {
            attributes: key_projection
                .iter()
                .map(|item| ScopeAttribute {
                    name: item.alias.clone(),
                    visible_name: item.alias.clone(),
                    formal_ty: item.alias_ty,
                    numeric_dscale: item.numeric_dscale.clone(),
                })
                .collect(),
        };
        ranked_scope.attributes.push(ScopeAttribute {
            name: rank_attribute.name.clone(),
            visible_name: rank_attribute.name.clone(),
            formal_ty: rank_attribute.ty,
            numeric_dscale: numeric_dscale_for_type(rank_attribute.ty),
        });
        let ranked = FormalQueryExpr::Rank {
            partition_keys,
            order_keys,
            rank_attribute,
            input: Box::new(FormalQueryExpr::Projection {
                select: key_projection,
                input: Box::new(input_query),
            }),
        };
        let final_select = output
            .iter()
            .enumerate()
            .map(|(index, column)| {
                let Some(source) = ranked_scope
                    .attributes
                    .iter()
                    .find(|attribute| attribute.visible_name == column.name)
                else {
                    self.error(
                        &format!("{path}.output[{index}]"),
                        "rank_output_binding_missing",
                        "The declarative RANK projection output did not bind to its staged ordinary expression or rank attribute.",
                    );
                    return None;
                };
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: source.name.clone(),
                            ty: source.formal_ty,
                        },
                    },
                    alias: column.name.clone(),
                    alias_ty: source.formal_ty,
                    numeric_dscale: source.numeric_dscale.clone(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQueryExpr::Projection {
            select: final_select,
            input: Box::new(ranked),
        })
    }

    fn lower_declarative_window_key_projection(
        &mut self,
        path: &str,
        expr: &ScalarAst,
        scope: &Scope,
        alias: String,
        direction: FormalSortDirection,
        null_direction: FormalNullDirection,
    ) -> Option<(FormalSelectItem, FormalSortKey)> {
        let Some(ty) = self.direct_function_type(&format!("{path}.type"), expr, scope) else {
            self.error(
                path,
                "rank_key_type_not_supported",
                "A declarative window key must have an independently modeled scalar result type.",
            );
            return None;
        };
        if matches!(ty, FormalAttributeType::String { .. })
            && !self
                .config
                .sql_environment
                .has_postgres_utf8_c_text_semantics()
        {
            self.error(
                path,
                "rank_string_collation_not_supported",
                "PostgreSQL string partitioning and window ordering are lowered only for an explicitly attested UTF8/libc C collation and C character classification.",
            );
            return None;
        }
        let term = annotate_literal_term(self.lower_aggregate_term(path, expr, scope)?, ty);
        let numeric_dscale = self.infer_numeric_dscale(expr, scope);
        let select = FormalSelectItem {
            expr: term,
            alias: alias.clone(),
            alias_ty: ty,
            numeric_dscale,
        };
        let key = FormalSortKey {
            attribute_name: alias,
            attribute_ty: ty,
            direction,
            null_direction,
        };
        Some((select, key))
    }

    /// Lower declarative cumulative ROWS windows without reconstructing a
    /// physical WindowAgg plan.  Every partition/order expression is staged
    /// once, one FormalSQL Window node chooses a legal ordering (including
    /// every peer permutation), and all window items consume the same
    /// partition prefixes.  Ordinary target expressions are staged only
    /// when total, so moving them across the window boundary cannot change a
    /// language-level runtime outcome.
    fn lower_declarative_cumulative_window_projection(
        &mut self,
        path: &str,
        input: &RelExpr,
        input_query: FormalQueryExpr,
        exprs: &[ScalarExpr],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        if exprs.len() != output.len() {
            self.error(
                path,
                "window_projection_arity_mismatch",
                "A declarative window Project must preserve expression/output arity.",
            );
            return None;
        }
        if !has_unique_column_names(output) {
            self.error(
                path,
                "window_projection_duplicate_alias",
                "Declarative window outputs require unique aliases in the FormalSQL tuple model.",
            );
            return None;
        }

        let mut window_indexes = Vec::new();
        let mut shared_spec: Option<&WindowAst> = None;
        for (index, expr) in exprs.iter().enumerate() {
            match &expr.parsed {
                ScalarAst::Window { parsed } if supported_cumulative_rows_window(parsed) => {
                    if let Some(first) = shared_spec {
                        if first.partition_by != parsed.partition_by
                            || first.order_by != parsed.order_by
                        {
                            self.error(
                                path,
                                "mixed_window_specifications_not_supported",
                                "Window expressions in one Project must share one partition/order specification so their peer-sensitive results are evaluated against the same legal ordering.",
                            );
                            return None;
                        }
                    } else {
                        shared_spec = Some(parsed);
                    }
                    window_indexes.push(index);
                }
                ScalarAst::Window { .. } => {
                    self.error(
                        &format!("{path}.exprs[{index}]"),
                        "window_shape_not_supported",
                        "Declarative native windows currently require structured ROW_NUMBER(), SUM(expr), or MAX(expr) with ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW and EXCLUDE NO OTHERS.",
                    );
                    return None;
                }
                ast if scalar_ast_contains_window(ast) => {
                    self.error(
                        &format!("{path}.exprs[{index}]"),
                        "nested_window_expression_not_supported",
                        "A supported cumulative window must be a complete SELECT expression; nested window expressions remain conservatively rejected.",
                    );
                    return None;
                }
                ast if scalar_ast_contains_rel_subquery(ast)
                    || scalar_ast_may_raise_runtime_for_input(ast, input) =>
                {
                    self.error(
                        &format!("{path}.exprs[{index}]"),
                        "window_ordinary_expression_runtime_not_supported",
                        "An ordinary expression sharing a window Project may be staged before the window only when it is total and contains no relational subquery.",
                    );
                    return None;
                }
                _ => {}
            }
        }
        let spec = shared_spec.expect("the cumulative window classifier requires a window");

        let input_scope =
            self.scope_from_query_expr(&format!("{path}.windowInputScope"), &input_query)?;
        let mut used_names = input_scope
            .attributes
            .iter()
            .map(|attribute| attribute.name.clone())
            .chain(output.iter().map(|column| column.name.clone()))
            .collect::<BTreeSet<_>>();
        let row_scope = self.rename_scope_attributes(
            &format!("{path}.windowInputScopeRename"),
            &input_scope,
            input_scope
                .attributes
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    fresh_internal_attribute_name(
                        &format!("__logos_window_input_{index}"),
                        &mut used_names,
                    )
                })
                .collect(),
        )?;
        let renamed_input = FormalQueryExpr::Projection {
            select: self.lower_scope_rename_select(
                &format!("{path}.windowInputRename"),
                &input_scope,
                &row_scope,
            )?,
            input: Box::new(input_query),
        };

        // Retain the renamed raw attributes for aggregate arguments, then
        // stage every total ordinary target and every ordering key once.
        let mut stage_select = self.lower_scope_rename_select(
            &format!("{path}.windowInputIdentity"),
            &row_scope,
            &row_scope,
        )?;
        let ordinary_exprs = exprs
            .iter()
            .enumerate()
            .filter(|(index, _)| !window_indexes.contains(index))
            .map(|(_, expr)| expr.clone())
            .collect::<Vec<_>>();
        let ordinary_output = output
            .iter()
            .enumerate()
            .filter(|(index, _)| !window_indexes.contains(index))
            .map(|(_, column)| column.clone())
            .collect::<Vec<_>>();
        stage_select.extend(self.lower_project_select(
            &format!("{path}.windowOrdinary"),
            &ordinary_exprs,
            &ordinary_output,
            &row_scope,
        )?);

        let mut partition_keys = Vec::with_capacity(spec.partition_by.len());
        for (index, expr) in spec.partition_by.iter().enumerate() {
            let alias = fresh_internal_attribute_name(
                &format!("__logos_window_partition_{index}"),
                &mut used_names,
            );
            let (select, key) = self.lower_declarative_window_key_projection(
                &format!("{path}.window.partitionBy[{index}]"),
                expr,
                &row_scope,
                alias,
                FormalSortDirection::Asc,
                FormalNullDirection::First,
            )?;
            stage_select.push(select);
            partition_keys.push(key);
        }
        let mut order_keys = Vec::with_capacity(spec.order_by.len());
        for (index, key) in spec.order_by.iter().enumerate() {
            let direction = match key.direction.unwrap_or(SortDirection::Ascending) {
                SortDirection::Ascending | SortDirection::StrictlyAscending => {
                    FormalSortDirection::Asc
                }
                SortDirection::Descending | SortDirection::StrictlyDescending => {
                    FormalSortDirection::Desc
                }
                SortDirection::Clustered => {
                    self.error(
                        &format!("{path}.window.orderBy[{index}]"),
                        "window_clustered_order_not_supported",
                        "A declarative SQL window requires ASC/DESC ordering, not Calcite clustered collation.",
                    );
                    return None;
                }
            };
            let null_direction = key
                .null_direction
                .or_else(|| {
                    key.direction
                        .unwrap_or(SortDirection::Ascending)
                        .default_null_direction()
                })
                .map(|nulls| match nulls {
                    SortNullDirection::First => FormalNullDirection::First,
                    SortNullDirection::Last => FormalNullDirection::Last,
                })?;
            let alias = fresh_internal_attribute_name(
                &format!("__logos_window_order_{index}"),
                &mut used_names,
            );
            let (select, key) = self.lower_declarative_window_key_projection(
                &format!("{path}.window.orderBy[{index}]"),
                &key.expr,
                &row_scope,
                alias,
                direction,
                null_direction,
            )?;
            stage_select.push(select);
            order_keys.push(key);
        }

        let staged_scope = Scope {
            attributes: stage_select
                .iter()
                .map(|item| ScopeAttribute {
                    name: item.alias.clone(),
                    visible_name: item.alias.clone(),
                    formal_ty: item.alias_ty,
                    numeric_dscale: item.numeric_dscale.clone(),
                })
                .collect(),
        };
        let mut items = Vec::with_capacity(window_indexes.len());
        for (item_index, output_index) in window_indexes.iter().copied().enumerate() {
            let ScalarAst::Window { parsed } = &exprs[output_index].parsed else {
                unreachable!("window indexes were collected from top-level windows")
            };
            let calcite_output_ty = self.lower_attribute_type(
                &format!("{path}.output[{output_index}]"),
                &output[output_index],
                AttributeTypeContext::QueryOutput,
            )?;
            let (function, output_ty, numeric_dscale) = if parsed
                .function
                .eq_ignore_ascii_case("ROW_NUMBER")
            {
                if calcite_output_ty != FormalAttributeType::Int64 || output[output_index].nullable
                {
                    self.error(
                        &format!("{path}.output[{output_index}]"),
                        "row_number_output_type_not_supported",
                        "PostgreSQL ROW_NUMBER returns a non-NULL BIGINT.",
                    );
                    return None;
                }
                (
                    FormalWindowFunction::RowNumber,
                    FormalAttributeType::Int64,
                    Some(NumericDscaleProvenance::Exact(0)),
                )
            } else {
                let call = AggregateCall {
                    raw: exprs[output_index].raw.clone(),
                    function: parsed.function.clone(),
                    distinct: parsed.distinct,
                    modifiers: Default::default(),
                    args: parsed
                        .args
                        .iter()
                        .map(|arg| ScalarExpr {
                            raw: format!("window argument {item_index}"),
                            parsed: arg.clone(),
                            source: None,
                        })
                        .collect(),
                    filter: None,
                };
                let postgres_output_ty = self.postgres_aggregate_output_type(
                    &format!("{path}.exprs[{output_index}]"),
                    &call,
                    &row_scope,
                    calcite_output_ty,
                )?;
                if postgres_output_ty != calcite_output_ty {
                    if !self.calcite_aggregate_type_override_is_known(
                        &call,
                        &row_scope,
                        postgres_output_ty,
                    ) {
                        self.error(
                                &format!("{path}.output[{output_index}]"),
                                "window_aggregate_output_type_mismatch",
                                "Calcite's window result type does not match the modeled PostgreSQL aggregate result type.",
                            );
                        return None;
                    }
                    self.warning(
                            &format!("{path}.output[{output_index}]"),
                            "calcite_window_aggregate_type_overridden",
                            &format!(
                                "Calcite reported {calcite_output_ty:?}, but PostgreSQL window-aggregate semantics require {postgres_output_ty:?}; FormalSQL uses the PostgreSQL result type."
                            ),
                        );
                }
                let numeric_dscale = self.aggregate_numeric_dscale(&call, &row_scope);
                let term = self.lower_aggregate_call(
                    &format!("{path}.windowItems"),
                    item_index,
                    &call,
                    &row_scope,
                    &postgres_output_ty,
                )?;
                (
                    FormalWindowFunction::Aggregate { term },
                    postgres_output_ty,
                    numeric_dscale,
                )
            };
            items.push(FormalWindowItem {
                output: FormalAttribute {
                    name: output[output_index].name.clone(),
                    ty: output_ty,
                },
                function,
                numeric_dscale,
            });
        }

        let mut window_scope = staged_scope.clone();
        window_scope
            .attributes
            .extend(items.iter().map(|item| ScopeAttribute {
                name: item.output.name.clone(),
                visible_name: item.output.name.clone(),
                formal_ty: item.output.ty,
                numeric_dscale: item.numeric_dscale.clone(),
            }));
        let windowed = FormalQueryExpr::Window {
            partition_keys,
            order_keys,
            items,
            input: Box::new(FormalQueryExpr::Projection {
                select: stage_select,
                input: Box::new(renamed_input),
            }),
        };
        let final_select = output
            .iter()
            .enumerate()
            .map(|(index, column)| {
                let source = window_scope
                    .attributes
                    .iter()
                    .find(|attribute| attribute.visible_name == column.name)
                    .or_else(|| {
                        self.error(
                            &format!("{path}.output[{index}]"),
                            "window_output_binding_missing",
                            "A declarative window output did not bind to its staged ordinary expression or window item.",
                        );
                        None
                    })?;
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: source.name.clone(),
                            ty: source.formal_ty,
                        },
                    },
                    alias: column.name.clone(),
                    alias_ty: source.formal_ty,
                    numeric_dscale: source.numeric_dscale.clone(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalQueryExpr::Projection {
            select: final_select,
            input: Box::new(windowed),
        })
    }

    /// Lowers the two COUNT window forms exercised by the frozen Calcite
    /// corpus.  Both are full-partition counts represented by one native
    /// shared-child window observation:
    ///
    /// * `PARTITION BY k ORDER BY k RANGE ... CURRENT ROW` has one peer group
    ///   per partition, hence its frame is the complete partition.
    /// * an unpartitioned `RANGE ... UNBOUNDED FOLLOWING` frame is the complete
    ///   input for every row.
    ///
    /// PostgreSQL puts all NULL partition keys in the same partition.  The
    /// FormalSQL window evaluator already uses its SQL ordering comparison for
    /// this partition equality, so no grouped copy or null-safe attachment
    /// join is needed.  In particular, the child below occurs exactly once.
    fn lower_supported_count_window_projection(
        &mut self,
        path: &str,
        input_query: FormalQueryExpr,
        exprs: &[ScalarExpr],
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        let mut shape = None;
        for (index, expr) in exprs.iter().enumerate() {
            match &expr.parsed {
                ScalarAst::Window { .. } => {
                    let Some(candidate) = classify_supported_count_window(&expr.parsed) else {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "window_shape_not_supported",
                            "Only structured PostgreSQL COUNT(*) over a peer-complete partition RANGE frame and COUNT(input-column) over a global fully-unbounded RANGE frame are modeled.",
                        );
                        return None;
                    };
                    if shape.is_some_and(|first| first != candidate) {
                        self.error(
                            path,
                            "mixed_window_shapes_not_supported",
                            "One projection may repeat one supported COUNT window, but cannot combine distinct window specifications in one native full-partition window.",
                        );
                        return None;
                    }
                    shape = Some(candidate);
                }
                ast if scalar_ast_contains_window(ast) => {
                    self.error(
                        &format!("{path}.exprs[{index}]"),
                        "nested_window_expression_not_supported",
                        "A supported COUNT window must be a complete SELECT expression; arithmetic, casts, CASE, and other expressions around a window remain conservatively rejected.",
                    );
                    return None;
                }
                _ => {}
            }
        }
        let shape =
            shape.expect("window lowering is called only for a project containing a window");

        let input_scope =
            self.scope_from_query_expr(&format!("{path}.windowInputScope"), &input_query)?;
        let referenced_index = match shape {
            SupportedCountWindowShape::PartitionPeerComplete { key_index } => key_index,
            SupportedCountWindowShape::GlobalFull { arg_index } => arg_index,
        };
        if input_scope.attribute(referenced_index).is_none() {
            self.error(
                path,
                "window_input_ref_out_of_range",
                "The supported COUNT window references a column outside its direct table input.",
            );
            return None;
        }

        let mut used_names = input_scope
            .attributes
            .iter()
            .map(|attribute| attribute.name.clone())
            .chain(output.iter().map(|column| column.name.clone()))
            .collect::<BTreeSet<_>>();
        let (partition_keys, order_keys) = match shape {
            SupportedCountWindowShape::PartitionPeerComplete { key_index } => {
                let key = input_scope
                    .attribute(key_index)
                    .expect("the supported partition key index was checked above");
                (
                    vec![FormalSortKey {
                        attribute_name: key.name.clone(),
                        attribute_ty: key.formal_ty,
                        direction: FormalSortDirection::Asc,
                        null_direction: FormalNullDirection::First,
                    }],
                    vec![FormalSortKey {
                        attribute_name: key.name,
                        attribute_ty: key.formal_ty,
                        direction: FormalSortDirection::Asc,
                        null_direction: FormalNullDirection::Last,
                    }],
                )
            }
            SupportedCountWindowShape::GlobalFull { .. } => (Vec::new(), Vec::new()),
        };

        let mut items = Vec::new();
        let mut attached_scope = input_scope.clone();
        let mut window_bindings = Vec::new();
        for (output_index, expr) in exprs.iter().enumerate() {
            if !matches!(expr.parsed, ScalarAst::Window { .. }) {
                continue;
            }
            let output_ty = self.lower_attribute_type(
                &format!("{path}.output[{output_index}]"),
                &output[output_index],
                AttributeTypeContext::QueryOutput,
            )?;
            if output_ty != FormalAttributeType::Int64 {
                self.error(
                    &format!("{path}.output[{output_index}]"),
                    "count_window_output_type_not_supported",
                    "PostgreSQL COUNT window expressions must have BIGINT output type.",
                );
                return None;
            }
            let term = match shape {
                SupportedCountWindowShape::PartitionPeerComplete { .. } => {
                    FormalAggregateTerm::CountStar
                }
                SupportedCountWindowShape::GlobalFull { arg_index } => {
                    let argument = input_scope
                        .attribute(arg_index)
                        .expect("the supported COUNT argument index was checked above");
                    FormalAggregateTerm::Aggregate {
                        function: FormalAggregateFunction::Count,
                        quantifier: FormalAggregateQuantifier::All,
                        arg: FormalFunctionTerm::Attribute {
                            name: argument.name,
                            ty: argument.formal_ty,
                        },
                    }
                }
            };
            let internal_name = fresh_internal_attribute_name(
                &format!("__logos_window_count_{output_index}"),
                &mut used_names,
            );
            let count_attribute = ScopeAttribute {
                name: internal_name.clone(),
                visible_name: internal_name.clone(),
                formal_ty: FormalAttributeType::Int64,
                numeric_dscale: numeric_dscale_for_type(FormalAttributeType::Int64),
            };
            let attached_index = attached_scope.attributes.len();
            attached_scope.attributes.push(count_attribute.clone());
            window_bindings.push((output_index, attached_index));
            items.push(FormalWindowItem {
                output: FormalAttribute {
                    name: internal_name,
                    ty: FormalAttributeType::Int64,
                },
                function: FormalWindowFunction::FullPartitionAggregate { term },
                numeric_dscale: count_attribute.numeric_dscale,
            });
        }
        let attached = FormalQueryExpr::Window {
            partition_keys,
            order_keys,
            items,
            input: Box::new(input_query),
        };

        let mut rewritten_exprs = exprs.to_vec();
        for (output_index, attached_index) in window_bindings {
            rewritten_exprs[output_index].raw = format!("${attached_index}");
            rewritten_exprs[output_index].parsed = ScalarAst::InputRef {
                index: attached_index,
            };
        }
        let select = self.lower_project_select(path, &rewritten_exprs, output, &attached_scope)?;
        Some(FormalQueryExpr::Projection {
            select,
            input: Box::new(attached),
        })
    }

    pub(super) fn lower_project_select(
        &mut self,
        path: &str,
        exprs: &[logos_ir::ir::ScalarExpr],
        output: &[Column],
        scope: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        self.lower_project_select_with_input(path, exprs, output, scope, None)
    }

    fn scalar_select_from_legacy(select: Vec<FormalSelectItem>) -> Vec<FormalScalarSelectItem> {
        select
            .into_iter()
            .map(|item| FormalScalarSelectItem {
                expr: FormalScalarExpr::Leaf {
                    result_ty: item.alias_ty,
                    term: item.expr,
                },
                alias: item.alias,
                alias_ty: item.alias_ty,
                numeric_dscale: item.numeric_dscale,
            })
            .collect()
    }

    /// Lower an ordinary SQL SELECT list through the one native scalar AST.
    /// Mature query-free scalar and aggregate terms remain value leaves;
    /// query-valued expressions are lowered directly and therefore evaluate
    /// each nested query exactly once per containing scalar evaluation.
    fn lower_native_project_select_with_input(
        &mut self,
        path: &str,
        input: &RelExpr,
        exprs: &[logos_ir::ir::ScalarExpr],
        output: &[Column],
        scope: &Scope,
        preserve_runtime_numeric_dscale: bool,
    ) -> Option<Vec<FormalScalarSelectItem>> {
        let contains_subquery = exprs
            .iter()
            .any(|expr| scalar_ast_contains_rel_subquery(&expr.parsed));
        if !contains_subquery {
            let legacy = if preserve_runtime_numeric_dscale {
                self.lower_query_projection_select(path, input, exprs, output, scope)?
            } else {
                self.lower_project_select_with_input(path, exprs, output, scope, Some(input))?
            };
            return Some(Self::scalar_select_from_legacy(legacy));
        }
        if !has_unique_column_names(output) {
            self.error(
                path,
                "duplicate_projection_alias",
                "FormalSQL scalar projection requires distinct output attributes.",
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

        let mut select = Vec::with_capacity(exprs.len());
        for (index, (expr, column)) in exprs.iter().zip(output).enumerate() {
            let item_path = format!("{path}.exprs[{index}]");
            if scalar_ast_contains_rel_subquery(&expr.parsed) {
                let output_ty = self.lower_attribute_type(
                    &format!("{path}.output[{index}]"),
                    column,
                    AttributeTypeContext::QueryOutput,
                )?;
                let lowered = self.lower_native_scalar_value_expr(
                    &item_path,
                    &expr.parsed,
                    scope,
                    output_ty,
                )?;
                if lowered.value_type() != Some(output_ty) {
                    self.error(
                        &item_path,
                        "native_scalar_projection_kind_mismatch",
                        "Every SELECT item must lower to a typed SQL value; Boolean search conditions must cross the nullable BOOLEAN value bridge.",
                    );
                    return None;
                }
                select.push(FormalScalarSelectItem {
                    expr: lowered,
                    alias: column.name.clone(),
                    alias_ty: output_ty,
                    numeric_dscale: numeric_dscale_for_type(output_ty)
                        .or_else(|| self.infer_numeric_dscale(&expr.parsed, scope)),
                });
            } else {
                let singleton_expr = std::slice::from_ref(expr);
                let singleton_output = std::slice::from_ref(column);
                let mut legacy = self.lower_project_select_with_input(
                    &format!("{item_path}.leaf"),
                    singleton_expr,
                    singleton_output,
                    scope,
                    Some(input),
                )?;
                let item = legacy.pop().expect("singleton projection lowering");
                select.push(FormalScalarSelectItem {
                    expr: FormalScalarExpr::Leaf {
                        result_ty: item.alias_ty,
                        term: item.expr,
                    },
                    alias: item.alias,
                    alias_ty: item.alias_ty,
                    numeric_dscale: item.numeric_dscale,
                });
            }
        }

        if preserve_runtime_numeric_dscale {
            self.attach_native_projection_numeric_dscales(path, scope, &mut select)?;
        }
        Some(select)
    }

    fn attach_native_projection_numeric_dscales(
        &mut self,
        path: &str,
        input_scope: &Scope,
        select: &mut Vec<FormalScalarSelectItem>,
    ) -> Option<()> {
        let referenced = select
            .iter()
            .filter_map(|item| match &item.numeric_dscale {
                Some(NumericDscaleProvenance::Attribute(name)) => Some(name.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut used_names = select
            .iter()
            .map(|item| item.alias.clone())
            .collect::<BTreeSet<_>>();
        for source_name in referenced {
            let mut matches = input_scope
                .attributes
                .iter()
                .filter(|attribute| attribute.name == source_name);
            let Some(source) = matches.next().cloned() else {
                self.error(
                    path,
                    "numeric_dscale_projection_source_missing",
                    "A projected NUMERIC value references a runtime display-scale attribute that is absent from its input row.",
                );
                return None;
            };
            if matches.next().is_some() || source.formal_ty != FormalAttributeType::Z {
                self.error(
                    path,
                    "numeric_dscale_projection_source_invalid",
                    "A projected runtime NUMERIC display scale must resolve to one unique mathematical-integer input attribute.",
                );
                return None;
            }
            let output_name = fresh_internal_attribute_name(&source_name, &mut used_names);
            for item in &mut *select {
                if item.numeric_dscale
                    == Some(NumericDscaleProvenance::Attribute(source_name.clone()))
                {
                    item.numeric_dscale =
                        Some(NumericDscaleProvenance::Attribute(output_name.clone()));
                }
            }
            select.push(FormalScalarSelectItem {
                expr: FormalScalarExpr::Leaf {
                    result_ty: FormalAttributeType::Z,
                    term: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: source.name,
                            ty: source.formal_ty,
                        },
                    },
                },
                alias: output_name,
                alias_ty: FormalAttributeType::Z,
                numeric_dscale: source.numeric_dscale,
            });
        }
        Some(())
    }

    fn lower_project_select_with_input(
        &mut self,
        path: &str,
        exprs: &[logos_ir::ir::ScalarExpr],
        output: &[Column],
        scope: &Scope,
        input: Option<&RelExpr>,
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
                let (corrected_coalesce, corrected_coalesce_origin) =
                    match postgres_numeric_coalesce_override(expr, column, scope, input) {
                        NumericCoalesceOverride::NotApplicable => (None, None),
                        NumericCoalesceOverride::Rewritten { ast, origin } => {
                            (Some(ast), Some(origin))
                        }
                        NumericCoalesceOverride::Drift => {
                            self.error(
                                &format!("{path}.exprs[{index}]"),
                                "numeric_coalesce_source_provenance_drift",
                                "A source-provenanced COALESCE over an unconstrained NUMERIC value had a Calcite CASE/cast tree, positional source identity, or enclosing arithmetic shape that did not support removing the stale DECIMAL typmod. The repair is fail-closed.",
                            );
                            return None;
                        }
                    };
                let expr_ast = corrected_coalesce.as_deref().unwrap_or(&expr.parsed);
                let lowered = self.lower_aggregate_term(
                    &format!("{path}.exprs[{index}]"),
                    expr_ast,
                    scope,
                )?;
                let mut output_ty = self.lower_attribute_type(
                    &format!("{path}.output[{index}]"),
                    column,
                    AttributeTypeContext::QueryOutput,
                )?;
                let expr_ty = self.direct_function_type(
                    &format!("{path}.exprs[{index}].type"),
                    expr_ast,
                    scope,
                );
                if let Some(origin) = corrected_coalesce_origin {
                    match origin {
                        NumericCoalesceOverrideOrigin::BigintSum
                            if output_ty != FormalAttributeType::Numeric =>
                        {
                            output_ty = FormalAttributeType::Numeric;
                            self.warning(
                                &format!("{path}.output[{index}]"),
                                "calcite_coalesce_numeric_type_overridden",
                                "Calcite inserted a BIGINT CASE/CAST around COALESCE(SUM(BIGINT), 0), but PostgreSQL resolves SUM(BIGINT) and the common COALESCE type as NUMERIC; FormalSQL removes the stale cast and preserves NUMERIC.",
                            );
                        }
                        NumericCoalesceOverrideOrigin::DecimalSum => {
                            output_ty = FormalAttributeType::Numeric;
                            self.warning(
                                &format!("{path}.output[{index}]"),
                                "calcite_coalesce_numeric_type_overridden",
                                "The source SQL has COALESCE over an unconstrained PostgreSQL NUMERIC value and no typmod cast, but Calcite synthesized DECIMAL(19,2) CASE casts. FormalSQL removes only those source-disproved casts and preserves NUMERIC.",
                            );
                        }
                        NumericCoalesceOverrideOrigin::BigintSum => {}
                    }
                }
                if matches!(&expr.parsed, ScalarAst::InputRef { .. })
                    && matches!(expr_ty, Some(FormalAttributeType::Numeric))
                    && calcite_stale_numeric_copy_type(output_ty)
                {
                    output_ty = FormalAttributeType::Numeric;
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_project_input_type_overridden",
                        "Calcite retained copied integral, floating, or fixed-DECIMAL output metadata for a direct reference to a child whose PostgreSQL result type is NUMERIC; a relational input reference cannot cast its value, so FormalSQL preserves the child NUMERIC type.",
                    );
                }
                if matches!(&expr.parsed, ScalarAst::InputRef { .. })
                    && expr_ty
                        == Some(FormalAttributeType::String {
                            typmod: SqlStringType::Text,
                        })
                    && matches!(&output_ty, FormalAttributeType::String { .. })
                    && output_ty != expr_ty.expect("input text type checked")
                {
                    output_ty = FormalAttributeType::String {
                        typmod: SqlStringType::Text,
                    };
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_project_input_string_type_overridden",
                        "Calcite retained VARCHAR output metadata for a direct reference to a PostgreSQL text-valued child; a relational input reference performs no cast, so FormalSQL preserves text.",
                    );
                }
                if matches!(
                    (&expr.parsed, expr_ty, output_ty),
                    (
                        ScalarAst::Call {
                            op: ScalarOp::StringConcat,
                            ..
                        },
                        Some(FormalAttributeType::String {
                            typmod: SqlStringType::Text,
                        }),
                        FormalAttributeType::String { .. }
                    )
                ) && expr_ty != Some(output_ty)
                {
                    output_ty = expr_ty.expect("concat result type matched");
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_string_concat_type_overridden",
                        "Calcite reported a constrained character width for a PostgreSQL || expression; PostgreSQL string concatenation returns text, so the formal projection preserves text.",
                    );
                }
                if matches!(
                    (&expr.parsed, expr_ty, output_ty),
                    (
                        ScalarAst::Call {
                            op: ScalarOp::Substring,
                            ..
                        },
                        Some(FormalAttributeType::String {
                            typmod: SqlStringType::Text,
                        }),
                        FormalAttributeType::String { .. }
                    )
                ) && expr_ty != Some(output_ty)
                {
                    output_ty = expr_ty.expect("substring result type matched");
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_substring_type_overridden",
                        "PostgreSQL substring over character strings returns text; FormalSQL ignores Calcite's stale constrained character result metadata.",
                    );
                }
                if top_level_string_case_mapping(&expr.parsed).is_some()
                    && expr_ty
                        == Some(FormalAttributeType::String {
                            typmod: SqlStringType::Text,
                        })
                    && output_ty != expr_ty.expect("case mapping type checked")
                {
                    output_ty = FormalAttributeType::String {
                        typmod: SqlStringType::Text,
                    };
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_string_case_mapping_type_overridden",
                        "PostgreSQL UPPER/LOWER return text; FormalSQL ignores Calcite's stale constrained character result metadata.",
                    );
                }
                if matches!(
                    (&expr.parsed, expr_ty),
                    (
                        ScalarAst::Call {
                            op: ScalarOp::Extract,
                            ..
                        },
                        Some(FormalAttributeType::Numeric)
                    )
                ) && output_ty != FormalAttributeType::Numeric
                {
                    output_ty = FormalAttributeType::Numeric;
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_extract_type_overridden",
                        "PostgreSQL EXTRACT returns unconstrained NUMERIC; FormalSQL ignores Calcite's stale integral or fixed-DECIMAL result metadata.",
                    );
                }
                if matches!(expr_ty, Some(FormalAttributeType::Numeric))
                    && matches!(output_ty, FormalAttributeType::Decimal { .. })
                {
                    output_ty = FormalAttributeType::Numeric;
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_numeric_type_overridden",
                        "Calcite reported a fixed DECIMAL typmod for an expression whose PostgreSQL result is unconstrained NUMERIC; FormalSQL preserves NUMERIC. Only an explicit typmod CAST can impose DECIMAL(p,s).",
                    );
                }
                if matches!(output_ty, FormalAttributeType::Decimal { .. })
                    && aggregate_term_contains_bare_decimal_division(&lowered)
                {
                    output_ty = FormalAttributeType::Numeric;
                    self.warning(
                        &format!("{path}.output[{index}]"),
                        "calcite_numeric_type_overridden",
                        "Calcite reported a fixed DECIMAL result for PostgreSQL NUMERIC division; the formal output remains unconstrained NUMERIC and its modeled runtime failures stay explicit.",
                    );
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
                if let Some(expr_ty) = expr_ty {
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
                    if matches!(expr_ty, FormalAttributeType::Numeric)
                        && matches!(output_ty, FormalAttributeType::Decimal { .. })
                    {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "numeric_output_typmod_requires_cast",
                            "Projecting unconstrained NUMERIC into DECIMAL(p,s) requires an explicit CAST so rounding and overflow are modeled.",
                        );
                        return None;
                    }
                    if integer_output_type_mismatch(&expr_ty, &output_ty) {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "integer_output_type_not_supported",
                            "Projected INTEGER/BIGINT expression type differs from the output column type; implicit integer widening/narrowing casts must be explicit.",
                        );
                        return None;
                    }
                    if string_output_typmod_mismatch(&expr_ty, &output_ty) {
                        self.error(
                            &format!("{path}.exprs[{index}]"),
                            "string_output_typmod_requires_cast",
                            "Projected string expression typmod differs from the output typmod; PostgreSQL CHAR/VARCHAR coercion must be represented by an explicit CAST.",
                        );
                        return None;
                    }
                }
                let lowered = annotate_literal_term(lowered, output_ty);
                Some(FormalSelectItem {
                    expr: lowered,
                    alias: column.name.clone(),
                    alias_ty: output_ty,
                    // A fixed DECIMAL result typmod determines the display
                    // scale even when a nullable CASE arm is the untyped NULL
                    // literal and therefore carries no value provenance of
                    // its own.  For typmodless NUMERIC, retain the stricter
                    // expression-derived analysis.
                    numeric_dscale: numeric_dscale_for_type(output_ty)
                        .or_else(|| self.infer_numeric_dscale(expr_ast, scope)),
                })
            })
            .collect()
    }

    /// Preserve each runtime-selected NUMERIC display scale that remains live
    /// after a relational Project. The SQL-visible items stay in their Calcite
    /// order; referenced scale attributes are copied into a hidden suffix and
    /// provenance is rebound to those output aliases. A true query boundary
    /// removes this suffix in `close_query_root_output`.
    fn lower_query_projection_select(
        &mut self,
        path: &str,
        input: &RelExpr,
        exprs: &[logos_ir::ir::ScalarExpr],
        output: &[Column],
        input_scope: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        let mut select =
            self.lower_project_select_with_input(path, exprs, output, input_scope, Some(input))?;
        let referenced = select
            .iter()
            .filter_map(|item| match &item.numeric_dscale {
                Some(NumericDscaleProvenance::Attribute(name)) => Some(name.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut used_names = select
            .iter()
            .map(|item| item.alias.clone())
            .collect::<BTreeSet<_>>();

        for source_name in referenced {
            let mut matches = input_scope
                .attributes
                .iter()
                .filter(|attribute| attribute.name == source_name);
            let Some(source) = matches.next().cloned() else {
                self.error(
                    path,
                    "numeric_dscale_projection_source_missing",
                    "A projected NUMERIC value references a runtime display-scale attribute that is absent from its input row.",
                );
                return None;
            };
            if matches.next().is_some() || source.formal_ty != FormalAttributeType::Z {
                self.error(
                    path,
                    "numeric_dscale_projection_source_invalid",
                    "A projected runtime NUMERIC display scale must resolve to one unique mathematical-integer input attribute.",
                );
                return None;
            }

            let output_name = fresh_internal_attribute_name(&source_name, &mut used_names);
            for item in &mut select {
                if item.numeric_dscale
                    == Some(NumericDscaleProvenance::Attribute(source_name.clone()))
                {
                    item.numeric_dscale =
                        Some(NumericDscaleProvenance::Attribute(output_name.clone()));
                }
            }
            select.push(FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: source.name,
                        ty: source.formal_ty,
                    },
                },
                alias: output_name,
                alias_ty: FormalAttributeType::Z,
                numeric_dscale: source.numeric_dscale,
            });
        }
        Some(select)
    }

    fn validate_scope_numeric_dscale_references(
        &mut self,
        path: &str,
        scope: &Scope,
    ) -> Option<()> {
        for attribute in &scope.attributes {
            let Some(NumericDscaleProvenance::Attribute(scale_name)) =
                attribute.numeric_dscale.as_ref()
            else {
                continue;
            };
            let matching_scales = scope
                .attributes
                .iter()
                .filter(|candidate| {
                    candidate.name == *scale_name && candidate.formal_ty == FormalAttributeType::Z
                })
                .count();
            if attribute.formal_ty != FormalAttributeType::Numeric || matching_scales != 1 {
                self.error(
                    path,
                    "numeric_dscale_scope_reference_invalid",
                    "Every dynamic NUMERIC display-scale provenance must resolve to one unique mathematical-integer attribute in the same logical row.",
                );
                return None;
            }
        }
        Some(())
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
            FormalAttributeType::Int32 if raw.trim().parse::<i32>().is_err() => {
                self.error(
                    path,
                    "integer_literal_out_of_range",
                    "VALUES INTEGER literal is outside the modeled int32 range.",
                );
                None
            }
            FormalAttributeType::Int64 if raw.trim().parse::<i64>().is_err() => {
                self.error(
                    path,
                    "bigint_literal_out_of_range",
                    "VALUES BIGINT literal is outside the modeled int64 range.",
                );
                None
            }
            FormalAttributeType::Numeric
                if !super::emit::numeric_literal_fits_postgres_runtime(raw) =>
            {
                self.error(
                    path,
                    "numeric_literal_not_supported",
                    "FormalSQL NUMERIC lowering accepts finite decimal literals only within PostgreSQL's 131072 integer-digit and 16383 fractional-digit runtime limits; NaN and infinities are rejected.",
                );
                None
            }
            FormalAttributeType::Decimal { .. }
                if super::emit::decimal_literal_for_type(raw, Some(&output_ty)).is_none() =>
            {
                self.error(
                    path,
                    "decimal_literal_not_supported",
                    "FormalSQL DECIMAL lowering accepts finite literals that fit the declared precision and scale.",
                );
                None
            }
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

    fn validate_grouping_set(
        &mut self,
        path: &str,
        group_keys: &[usize],
        grouping_set: &[usize],
    ) -> Option<()> {
        for (index, key) in grouping_set.iter().enumerate() {
            if !group_keys.contains(key) {
                self.error(
                    &format!("{path}[{index}]"),
                    "grouping_set_key_not_in_group_keys",
                    "A Calcite grouping set contains a key outside the aggregate's complete group-key list.",
                );
                return None;
            }
            if grouping_set[..index].contains(key) {
                self.error(
                    &format!("{path}[{index}]"),
                    "duplicate_grouping_set_key",
                    "A single Calcite grouping set contains a duplicate key; the bit-set representation is expected to contain each key once.",
                );
                return None;
            }
        }
        Some(())
    }

    /// Admit only the benchmark-required, fully typed global forms of
    /// ANY_VALUE and SINGLE_VALUE.  Their semantics are sufficiently unusual
    /// that letting the generic aggregate paths accept DISTINCT, FILTER,
    /// grouped, expression-valued, or mixed-select-list variants would be an
    /// unsound accidental extension.
    fn validate_special_aggregate_shape(
        &mut self,
        path: &str,
        input: &RelExpr,
        group_keys: &[usize],
        grouping_sets: &[Vec<usize>],
        agg_calls: &[AggregateCall],
        output: &[Column],
    ) -> Option<Option<(SpecialAggregateKind, usize)>> {
        let special_count = agg_calls
            .iter()
            .filter(|call| special_aggregate_kind(&call.function).is_some())
            .count();
        if special_count == 0 {
            return Some(None);
        }
        if special_count != 1 || agg_calls.len() != 1 || output.len() != 1 {
            self.error(
                path,
                "special_aggregate_select_shape_not_supported",
                "ANY_VALUE/SINGLE_VALUE lowering supports exactly one aggregate call and one output column.",
            );
            return None;
        }
        if !group_keys.is_empty()
            || !matches!(grouping_sets, [grouping_set] if grouping_set.is_empty())
        {
            self.error(
                path,
                "special_aggregate_grouping_shape_not_supported",
                "ANY_VALUE/SINGLE_VALUE lowering is restricted to one ordinary global grouping set.",
            );
            return None;
        }
        let call = &agg_calls[0];
        let kind = special_aggregate_kind(&call.function)
            .expect("the sole call was counted as a special aggregate");
        if call.distinct || call.filter.is_some() || call.modifiers.has_semantic_modifiers() {
            self.error(
                &format!("{path}.aggCalls[0]"),
                "special_aggregate_modifier_not_supported",
                "ANY_VALUE/SINGLE_VALUE lowering rejects DISTINCT, FILTER, approximate, IGNORE NULLS, DISTINCT-key, and aggregate-local ORDER BY variants.",
            );
            return None;
        }
        let [argument] = call.args.as_slice() else {
            self.error(
                &format!("{path}.aggCalls[0]"),
                "special_aggregate_argument_arity_not_supported",
                "ANY_VALUE/SINGLE_VALUE lowering requires exactly one argument.",
            );
            return None;
        };
        let ScalarAst::InputRef {
            index: argument_index,
        } = &argument.parsed
        else {
            self.error(
                &format!("{path}.aggCalls[0].arg"),
                "special_aggregate_argument_shape_not_supported",
                "ANY_VALUE/SINGLE_VALUE lowering requires one direct input-column reference; expression arguments are conservatively rejected.",
            );
            return None;
        };
        let argument_index = *argument_index;
        if argument_index >= input.output().len() {
            self.error(
                &format!("{path}.aggCalls[0].arg"),
                "input_ref_out_of_range",
                "ANY_VALUE/SINGLE_VALUE argument does not reference an input column.",
            );
            return None;
        }
        Some(Some((kind, argument_index)))
    }

    /// PostgreSQL documents ANY_VALUE as choosing an arbitrary non-NULL input
    /// value.  A fixed MIN/first representative would under-approximate that
    /// observable choice.  Instead, filter NULLs, left-join a one-row seed to
    /// obtain the empty/all-NULL fallback, use the join's bag reset to expose
    /// every candidate permutation, and FETCH one row.  Thus every and only
    /// legal PostgreSQL result is represented.
    fn lower_any_value_int32_query_expr(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        input_scope: &Scope,
        argument_index: usize,
        output: &[Column],
    ) -> Option<FormalQueryExpr> {
        let argument = input_scope.attribute(argument_index).or_else(|| {
            self.error(
                &format!("{path}.aggCalls[0].arg"),
                "input_ref_out_of_range",
                "ANY_VALUE argument does not reference a lowered input column.",
            );
            None
        })?;
        if argument.formal_ty != FormalAttributeType::Int32 {
            self.error(
                &format!("{path}.aggCalls[0].arg"),
                "any_value_argument_type_not_supported",
                "Exact ANY_VALUE lowering currently supports PostgreSQL INTEGER input only.",
            );
            return None;
        }
        let output_ty = self.lower_attribute_type(
            &format!("{path}.output[0]"),
            &output[0],
            AttributeTypeContext::QueryOutput,
        )?;
        if output_ty != FormalAttributeType::Int32 {
            self.error(
                &format!("{path}.output[0]"),
                "any_value_output_type_not_supported",
                "PostgreSQL ANY_VALUE(INTEGER) returns INTEGER; Calcite's output type must agree.",
            );
            return None;
        }

        let predicate_ast = ScalarAst::Call {
            operator: "IS NOT NULL".to_owned(),
            op: ScalarOp::IsNotNull,
            args: vec![ScalarAst::InputRef {
                index: argument_index,
            }],
        };
        let predicate = self.lower_native_scalar_boolean_expr(
            &format!("{path}.anyValue.nonNull"),
            &predicate_ast,
            input_scope,
        )?;
        let candidate_item = FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: argument.name.clone(),
                    ty: FormalAttributeType::Int32,
                },
            },
            alias: output[0].name.clone(),
            alias_ty: FormalAttributeType::Int32,
            numeric_dscale: argument.numeric_dscale.clone(),
        };
        let candidates = FormalQueryExpr::Projection {
            select: vec![candidate_item],
            input: Box::new(FormalQueryExpr::ScalarSelection {
                predicate,
                input: Box::new(input),
            }),
        };
        let result_item = FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: output[0].name.clone(),
                    ty: FormalAttributeType::Int32,
                },
            },
            alias: output[0].name.clone(),
            alias_ty: FormalAttributeType::Int32,
            numeric_dscale: argument.numeric_dscale.clone(),
        };
        let null_item = FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "NULL".to_owned(),
                    ty: Some(FormalAttributeType::Int32),
                },
            },
            alias: output[0].name.clone(),
            alias_ty: FormalAttributeType::Int32,
            numeric_dscale: argument.numeric_dscale.clone(),
        };
        let with_empty_fallback = FormalQueryExpr::Join {
            join_kind: FormalQueryJoinKind::Left,
            predicate: FormalFormulaExpr::True,
            matched_select: vec![result_item.clone()],
            left_select: vec![null_item],
            right_select: vec![result_item],
            left: Box::new(FormalQueryExpr::EmptyTuple),
            right: Box::new(candidates),
        };
        Some(FormalQueryExpr::Fetch {
            count: 1,
            input: Box::new(with_empty_fallback),
        })
    }

    fn lower_grouping_set_select(
        &mut self,
        path: &str,
        group_keys: &[usize],
        grouping_set: &[usize],
        agg_calls: &[AggregateCall],
        output: &[Column],
        scope: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        let mut select =
            self.lower_aggregate_select(path, group_keys, grouping_set, agg_calls, output, scope)?;
        for (output_index, key) in group_keys.iter().enumerate() {
            if !grouping_set.contains(key) {
                let output_ty = select[output_index].alias_ty;
                select[output_index].expr = FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        raw: "NULL".to_owned(),
                        ty: Some(output_ty),
                    },
                };
            }
        }
        Some(select)
    }

    /// PostgreSQL evaluates an aggregate FILTER before its argument and
    /// ignores the row when the filter is FALSE or NULL.  Every aggregate
    /// currently admitted by this lowering is NULL-ignoring, so a lazy
    /// searched CASE in an immediately preceding projection is exact:
    ///
    ///   agg(arg) FILTER (WHERE p) = agg(CASE WHEN p THEN arg ELSE NULL END)
    ///
    /// COUNT(*) uses a non-NULL integer sentinel in the selected branch.
    /// Keeping the CASE as a real FormalSQL term (rather than dropping the
    /// filter or eagerly evaluating `arg`) preserves PostgreSQL's lazy
    /// argument evaluation and runtime-error behavior. DISTINCT remains on the aggregate
    /// call and therefore sees exactly the selected non-NULL values.
    fn lower_filtered_aggregate_projection(
        &mut self,
        path: &str,
        scope: &Scope,
        agg_calls: &[AggregateCall],
    ) -> Option<(Vec<FormalSelectItem>, Scope, Vec<AggregateCall>)> {
        let mut select = scope
            .attributes
            .iter()
            .map(|attribute| FormalSelectItem {
                expr: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attribute.name.clone(),
                        ty: attribute.formal_ty,
                    },
                },
                alias: attribute.name.clone(),
                alias_ty: attribute.formal_ty,
                numeric_dscale: attribute.numeric_dscale.clone(),
            })
            .collect::<Vec<_>>();
        let mut projected_scope = scope.clone();
        let mut rewritten = agg_calls.to_vec();

        for (index, call) in agg_calls.iter().enumerate() {
            let Some(filter) = call.filter.as_ref() else {
                continue;
            };
            let call_path = format!("{path}.aggCalls[{index}]");
            let (argument, argument_ty, numeric_dscale) = match call.args.as_slice() {
                [] if call.function.eq_ignore_ascii_case("COUNT") && !call.distinct => (
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    FormalAttributeType::Int32,
                    Some(NumericDscaleProvenance::Exact(0)),
                ),
                [argument] => {
                    let argument_ty = self
                        .direct_function_type(
                            &format!("{call_path}.filteredArgType"),
                            &argument.parsed,
                            scope,
                        )
                        .or_else(|| {
                            self.infer_function_type(
                                &format!("{call_path}.filteredArgType"),
                                &argument.parsed,
                                scope,
                            )
                        })
                        .or_else(|| {
                            self.infer_numeric_operand_type(
                                &format!("{call_path}.filteredArgType"),
                                &argument.parsed,
                                scope,
                            )
                        })
                        .or_else(|| {
                            self.error(
                                &call_path,
                                "filtered_aggregate_argument_type_not_supported",
                                "Aggregate FILTER desugaring requires one argument with an exact modeled PostgreSQL type.",
                            );
                            None
                        })?;
                    (
                        argument.parsed.clone(),
                        argument_ty,
                        self.infer_numeric_dscale(&argument.parsed, scope),
                    )
                }
                _ => {
                    self.error(
                        &call_path,
                        "filtered_aggregate_argument_arity_not_supported",
                        "Aggregate FILTER desugaring supports COUNT(*) or one aggregate argument.",
                    );
                    return None;
                }
            };

            let case = ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    filter.parsed.clone(),
                    argument,
                    ScalarAst::Literal {
                        raw: "NULL".to_owned(),
                    },
                ],
            };
            let case_term =
                self.lower_aggregate_term(&format!("{call_path}.filteredCase"), &case, scope)?;
            let mut alias = format!("__logos_filtered_aggregate_{index}");
            let mut suffix = 0usize;
            while projected_scope
                .attributes
                .iter()
                .any(|attribute| attribute.name == alias)
            {
                suffix += 1;
                alias = format!("__logos_filtered_aggregate_{index}_{suffix}");
            }
            let projected_index = projected_scope.attributes.len();
            select.push(FormalSelectItem {
                expr: case_term,
                alias: alias.clone(),
                alias_ty: argument_ty,
                numeric_dscale: numeric_dscale.clone(),
            });
            projected_scope.attributes.push(ScopeAttribute {
                name: alias.clone(),
                visible_name: alias.clone(),
                formal_ty: argument_ty,
                numeric_dscale,
            });
            rewritten[index].filter = None;
            rewritten[index].args = vec![ScalarExpr {
                raw: alias,
                parsed: ScalarAst::InputRef {
                    index: projected_index,
                },
                source: None,
            }];
        }

        Some((select, projected_scope, rewritten))
    }

    fn lower_filtered_aggregate_input_expr(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        scope: Scope,
        agg_calls: &[AggregateCall],
    ) -> Option<(FormalQueryExpr, Scope, Vec<AggregateCall>)> {
        if !agg_calls.iter().any(|call| call.filter.is_some()) {
            return Some((input, scope, agg_calls.to_vec()));
        }
        let (select, scope, agg_calls) =
            self.lower_filtered_aggregate_projection(path, &scope, agg_calls)?;
        Some((
            FormalQueryExpr::Projection {
                select,
                input: Box::new(input),
            },
            scope,
            agg_calls,
        ))
    }

    fn lower_filtered_aggregate_input(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        scope: Scope,
        agg_calls: &[AggregateCall],
    ) -> Option<(FormalQueryExpr, Scope, Vec<AggregateCall>)> {
        if !agg_calls.iter().any(|call| call.filter.is_some()) {
            return Some((input, scope, agg_calls.to_vec()));
        }
        let (select, scope, agg_calls) =
            self.lower_filtered_aggregate_projection(path, &scope, agg_calls)?;
        Some((
            FormalQueryExpr::Projection {
                select,
                input: Box::new(input),
            },
            scope,
            agg_calls,
        ))
    }

    fn lower_query_expr_grouping_sets(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        plan: GroupingSetPlan<'_>,
    ) -> Option<FormalQueryExpr> {
        let GroupingSetPlan {
            group_keys,
            grouping_sets,
            agg_calls,
            output,
            scope,
        } = plan;
        if grouping_sets.is_empty() {
            self.error(
                path,
                "grouping_sets_empty",
                "Calcite exposed no grouping set for a grouping aggregate.",
            );
            return None;
        }
        if agg_calls
            .iter()
            .any(|call| call.function.eq_ignore_ascii_case("GROUPING"))
            && !aggregate_source_grouping(agg_calls).is_some_and(|source| {
                source.group_indexes == group_keys && source.grouping_sets == grouping_sets
            })
        {
            self.error(
                path,
                "grouping_source_sequence_not_attested",
                "GROUPING calls do not share exact query-block authority for this complete ordered grouping-set sequence.",
            );
            return None;
        }
        if let [grouping_set] = grouping_sets {
            let branch_path = format!("{path}.groupingSets[0]");
            self.validate_grouping_set(&branch_path, group_keys, grouping_set)?;
            let select = self.lower_grouping_set_select(
                &branch_path,
                group_keys,
                grouping_set,
                agg_calls,
                output,
                scope,
            )?;
            return Some(FormalQueryExpr::ScalarGroup {
                select: Self::scalar_select_from_legacy(select),
                group_by: self.lower_scalar_group_keys(&branch_path, grouping_set, scope)?,
                having: FormalScalarExpr::True,
                input: Box::new(input),
            });
        }
        // Every multi-branch grouping-set operator must consume the same
        // chosen child observation. QExpr_GroupingSets owns that child
        // natively, so no branch contains a cloned query expression.
        let mut lowered_sets = Vec::with_capacity(grouping_sets.len());
        for (index, grouping_set) in grouping_sets.iter().enumerate() {
            let branch_path = format!("{path}.groupingSets[{index}]");
            self.validate_grouping_set(&branch_path, group_keys, grouping_set)?;
            lowered_sets.push(FormalGroupingSet {
                select: self.lower_grouping_set_select(
                    &branch_path,
                    group_keys,
                    grouping_set,
                    agg_calls,
                    output,
                    scope,
                )?,
                group_by: self.lower_group_keys(&branch_path, grouping_set, scope)?,
            });
        }
        Some(FormalQueryExpr::GroupingSets {
            grouping_sets: lowered_sets,
            input: Box::new(input),
        })
    }

    fn lower_grouping_sets(
        &mut self,
        path: &str,
        input: FormalQueryExpr,
        plan: GroupingSetPlan<'_>,
    ) -> Option<FormalQueryExpr> {
        let GroupingSetPlan {
            group_keys,
            grouping_sets,
            agg_calls,
            output,
            scope,
        } = plan;
        if grouping_sets.is_empty() {
            self.error(
                path,
                "grouping_sets_empty",
                "Calcite exposed no grouping set for a grouping aggregate.",
            );
            return None;
        }
        if agg_calls
            .iter()
            .any(|call| call.function.eq_ignore_ascii_case("GROUPING"))
            && !aggregate_source_grouping(agg_calls).is_some_and(|source| {
                source.group_indexes == group_keys && source.grouping_sets == grouping_sets
            })
        {
            self.error(
                path,
                "grouping_source_sequence_not_attested",
                "GROUPING calls do not share exact query-block authority for this complete ordered grouping-set sequence.",
            );
            return None;
        }
        if let [grouping_set] = grouping_sets {
            let branch_path = format!("{path}.groupingSets[0]");
            self.validate_grouping_set(&branch_path, group_keys, grouping_set)?;
            let select = self.lower_grouping_set_select(
                &branch_path,
                group_keys,
                grouping_set,
                agg_calls,
                output,
                scope,
            )?;
            return Some(FormalQueryExpr::ScalarGroup {
                select: Self::scalar_select_from_legacy(select),
                group_by: self.lower_scalar_group_keys(&branch_path, grouping_set, scope)?,
                having: FormalScalarExpr::True,
                input: Box::new(input),
            });
        }
        // The exact grouping-set operator chooses the input once and passes
        // that one bag to every branch.  Do not clone even a currently
        // deterministic-looking child: later order-sensitive or relational
        // extensions must not silently turn this path into independent replay.
        let mut lowered_sets = Vec::with_capacity(grouping_sets.len());
        for (index, grouping_set) in grouping_sets.iter().enumerate() {
            let branch_path = format!("{path}.groupingSets[{index}]");
            self.validate_grouping_set(&branch_path, group_keys, grouping_set)?;
            lowered_sets.push(FormalGroupingSet {
                select: self.lower_grouping_set_select(
                    &branch_path,
                    group_keys,
                    grouping_set,
                    agg_calls,
                    output,
                    scope,
                )?,
                group_by: self.lower_group_keys(&branch_path, grouping_set, scope)?,
            });
        }
        Some(FormalQueryExpr::GroupingSets {
            grouping_sets: lowered_sets,
            input: Box::new(input),
        })
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

    fn lower_scalar_group_keys(
        &mut self,
        path: &str,
        group_keys: &[usize],
        scope: &Scope,
    ) -> Option<Vec<FormalScalarExpr>> {
        let terms = self.lower_group_keys(path, group_keys, scope)?;
        group_keys
            .iter()
            .zip(terms)
            .map(|(key, term)| {
                let result_ty = scope.attribute(*key)?.formal_ty;
                Some(FormalScalarExpr::Leaf { result_ty, term })
            })
            .collect()
    }

    fn lower_aggregate_select(
        &mut self,
        path: &str,
        group_keys: &[usize],
        grouping_set: &[usize],
        agg_calls: &[AggregateCall],
        output: &[Column],
        scope: &Scope,
    ) -> Option<Vec<FormalSelectItem>> {
        if !has_unique_column_names(output) {
            self.error(
                path,
                "duplicate_aggregate_alias",
                "FormalSQL grouped-expression select lists require distinct output attributes.",
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
            let calcite_output_ty = self.lower_attribute_type(
                &format!("{path}.output[{index}]"),
                &output[index],
                AttributeTypeContext::QueryOutput,
            )?;
            // A Calcite Aggregate group key is a direct reference into its
            // child Project.  It cannot introduce a cast: ordinary grouping
            // returns that value unchanged, and an omitted grouping-set key
            // is NULL of that same input type.  The lowered child scope is
            // therefore authoritative whenever Calcite repeats stale Rex
            // metadata (notably text-valued SUBSTRING and numeric EXTRACT).
            let output_ty = attr.formal_ty;
            if calcite_output_ty != output_ty {
                self.warning(
                    &format!("{path}.output[{index}]"),
                    "calcite_group_key_type_overridden",
                    &format!(
                        "Calcite reported {calcite_output_ty:?} for an Aggregate group-key output, but PostgreSQL preserves the authoritative child type {output_ty:?}; FormalSQL uses the child type."
                    ),
                );
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
                numeric_dscale: attr.numeric_dscale,
            });
        }
        for (index, call) in agg_calls.iter().enumerate() {
            let output_index = group_keys.len() + index;
            let calcite_output_ty = self.lower_attribute_type(
                &format!("{path}.output[{output_index}]"),
                &output[output_index],
                AttributeTypeContext::QueryOutput,
            )?;
            if call.function.eq_ignore_ascii_case("GROUPING") {
                select.push(self.lower_grouping_select_item(
                    &format!("{path}.aggCalls[{index}]"),
                    call,
                    GroupingSelectContext {
                        group_keys,
                        grouping_set,
                        output: &output[output_index],
                        output_ty: calcite_output_ty,
                        scope,
                    },
                )?);
                continue;
            }
            if let Some(key) = grouped_text_minmax_key(call, grouping_set) {
                let attr = scope.attribute(key).or_else(|| {
                    self.error(
                        &format!("{path}.aggCalls[{index}].arg"),
                        "input_ref_out_of_range",
                        "Grouped MIN/MAX argument does not reference an input column.",
                    );
                    None
                })?;
                if matches!(
                    attr.formal_ty,
                    FormalAttributeType::String {
                        typmod: logos_ir::ir::SqlStringType::Text
                    }
                ) {
                    let output_ty = attr.formal_ty;
                    if output_ty != calcite_output_ty {
                        self.warning(
                            &format!("{path}.output[{output_index}]"),
                            "calcite_aggregate_type_overridden",
                            &format!(
                                "Calcite reported {calcite_output_ty:?}, but PostgreSQL MIN/MAX over a grouped string key preserves the authoritative key type {output_ty:?}; FormalSQL uses the PostgreSQL result type."
                            ),
                        );
                    }
                    select.push(FormalSelectItem {
                        expr: FormalAggregateTerm::Expr {
                            term: FormalFunctionTerm::Attribute {
                                name: attr.name,
                                ty: output_ty,
                            },
                        },
                        alias: output[output_index].name.clone(),
                        alias_ty: output_ty,
                        numeric_dscale: attr.numeric_dscale,
                    });
                    continue;
                }
            }
            let output_ty = self.postgres_aggregate_output_type(
                &format!("{path}.aggCalls[{index}]"),
                call,
                scope,
                calcite_output_ty,
            )?;
            if output_ty != calcite_output_ty {
                if !self.calcite_aggregate_type_override_is_known(call, scope, output_ty) {
                    let (code, message) = if matches!(
                        (calcite_output_ty, output_ty),
                        (
                            FormalAttributeType::Float | FormalAttributeType::Double,
                            FormalAttributeType::Float | FormalAttributeType::Double
                        )
                    ) {
                        (
                            "floating_aggregate_output_type_not_supported",
                            "FLOAT/DOUBLE aggregate output type must match the PostgreSQL aggregate result type.",
                        )
                    } else if call.function.eq_ignore_ascii_case("SUM")
                        && matches!(output_ty, FormalAttributeType::Int64)
                    {
                        (
                            "integer_sum_output_type_not_supported",
                            "PostgreSQL SUM(INTEGER) returns BIGINT; other output coercions must be explicit.",
                        )
                    } else {
                        (
                            "aggregate_output_type_not_supported",
                            "Calcite aggregate output conflicts with the PostgreSQL result type.",
                        )
                    };
                    self.error(
                        &format!("{path}.output[{output_index}]"),
                        code,
                        &format!(
                            "{message} Calcite reported {calcite_output_ty:?}; PostgreSQL requires {output_ty:?}."
                        ),
                    );
                    return None;
                }
                self.warning(
                    &format!("{path}.output[{output_index}]"),
                    "calcite_aggregate_type_overridden",
                    &format!(
                        "Calcite reported {calcite_output_ty:?}, but PostgreSQL aggregate semantics require {output_ty:?}; FormalSQL uses the PostgreSQL result type."
                    ),
                );
            }
            select.push(FormalSelectItem {
                expr: self.lower_aggregate_call(path, index, call, scope, &output_ty)?,
                alias: output[output_index].name.clone(),
                alias_ty: output_ty,
                numeric_dscale: self.aggregate_numeric_dscale(call, scope),
            });
        }
        Some(select)
    }

    fn lower_grouping_select_item(
        &mut self,
        path: &str,
        call: &AggregateCall,
        context: GroupingSelectContext<'_>,
    ) -> Option<FormalSelectItem> {
        let GroupingSelectContext {
            group_keys,
            grouping_set,
            output,
            output_ty,
            scope,
        } = context;
        let Some(source_grouping) = call.modifiers.source_grouping.as_ref() else {
            self.error(
                path,
                "grouping_source_not_attested",
                "GROUPING lowering requires exact independently parsed query-block authority for the owning grouping-set sequence.",
            );
            return None;
        };
        if output_ty != FormalAttributeType::Int32
            || source_grouping.group_indexes != group_keys
            || !source_grouping
                .grouping_sets
                .iter()
                .any(|set| set.as_slice() == grouping_set)
            || call.distinct
            || call.filter.is_some()
            || call.modifiers.has_semantic_modifiers()
            || call.modifiers.source_distinct != Some(false)
            || call.args.is_empty()
            || call.args.len() > 31
        {
            self.error(
                path,
                "grouping_shape_not_supported",
                "PostgreSQL GROUPING requires INTEGER output, one to 31 unmodified source-bound grouping arguments, and the exact owning grouping-set sequence.",
            );
            return None;
        }
        let Some(source) = call.modifiers.source.as_ref() else {
            self.error(
                path,
                "grouping_call_source_not_attested",
                "GROUPING has no exact source-call provenance.",
            );
            return None;
        };
        if !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("OTHER_FUNCTION"))
            || !source
                .operator
                .as_deref()
                .is_some_and(|operator| operator.eq_ignore_ascii_case("GROUPING"))
            || !source_has_exact_binding(source)
            || source.operands.len() != call.args.len()
        {
            self.error(
                path,
                "grouping_call_source_not_attested",
                "GROUPING source operator and positional operands do not match the generated aggregate call.",
            );
            return None;
        }
        let mut mask = 0u32;
        for (position, (argument, source_argument)) in
            call.args.iter().zip(&source.operands).enumerate()
        {
            let ScalarAst::InputRef { index } = argument.parsed else {
                self.error(
                    &format!("{path}.args[{position}]"),
                    "grouping_argument_not_supported",
                    "GROUPING arguments must be direct references to source-attested grouping expressions.",
                );
                return None;
            };
            let Some(attribute) = scope.attribute(index) else {
                self.error(
                    &format!("{path}.args[{position}]"),
                    "input_ref_out_of_range",
                    "GROUPING argument is outside the aggregate input row.",
                );
                return None;
            };
            if !group_keys.contains(&index)
                || !source_argument.as_ref().is_some_and(|source| {
                    source_is_direct_identifier(source, &attribute.visible_name)
                })
            {
                self.error(
                    &format!("{path}.args[{position}]"),
                    "grouping_argument_source_not_attested",
                    "GROUPING argument does not match one authoritative grouping expression in the owning query block.",
                );
                return None;
            }
            mask = (mask << 1) | u32::from(!grouping_set.contains(&index));
        }
        let source_arguments = source.operands.iter().flatten().collect::<Vec<_>>();
        if source_arguments.len() != call.args.len()
            || !exact_source_function_operands_match(source, "GROUPING", &source_arguments, false)
        {
            self.error(
                path,
                "grouping_call_source_not_attested",
                "GROUPING exact source text does not match its positional source operands.",
            );
            return None;
        }
        Some(FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: mask.to_string(),
                    ty: Some(FormalAttributeType::Int32),
                },
            },
            alias: output.name.clone(),
            alias_ty: FormalAttributeType::Int32,
            numeric_dscale: Some(NumericDscaleProvenance::Exact(0)),
        })
    }

    fn aggregate_numeric_dscale(
        &mut self,
        call: &AggregateCall,
        scope: &Scope,
    ) -> Option<NumericDscaleProvenance> {
        let function = call.function.to_ascii_lowercase();
        if function == "count" {
            return Some(NumericDscaleProvenance::Exact(0));
        }
        if !matches!(function.as_str(), "sum" | "min" | "max") || call.args.len() != 1 {
            return None;
        }
        self.infer_numeric_dscale(&call.args[0].parsed, scope)
    }

    fn postgres_aggregate_output_type(
        &mut self,
        path: &str,
        call: &AggregateCall,
        scope: &Scope,
        fallback: FormalAttributeType,
    ) -> Option<FormalAttributeType> {
        let function = call.function.to_ascii_lowercase();
        if !aggregate_function_is_supported(&call.function) {
            return Some(fallback);
        }
        if function == "count" {
            return Some(FormalAttributeType::Int64);
        }
        let [arg] = call.args.as_slice() else {
            self.error(
                path,
                "aggregate_argument_arity_not_supported",
                "PostgreSQL aggregate result typing requires one argument for this function.",
            );
            return None;
        };
        let arg_ty = self
            .direct_function_type(&format!("{path}.argType"), &arg.parsed, scope)
            .or_else(|| self.infer_function_type(&format!("{path}.argType"), &arg.parsed, scope))
            .or_else(|| {
                self.infer_numeric_operand_type(&format!("{path}.argType"), &arg.parsed, scope)
            })?;
        if attested_postgres_stddev_samp_numeric_fixed(call, scope).is_some() {
            return Some(FormalAttributeType::Numeric);
        }
        if function == "max"
            && matches!(
                &arg_ty,
                FormalAttributeType::String {
                    typmod: SqlStringType::Text
                }
            )
        {
            if !self
                .config
                .sql_environment
                .has_postgres_utf8_c_text_semantics()
            {
                self.error(
                    path,
                    "string_collation_aggregate_not_supported",
                    "PostgreSQL MAX(text) depends on the locale environment; exact lowering requires --sql-default-collation C, --sql-character-classification C, --sql-locale-provider libc, and --sql-server-encoding UTF8.",
                );
                return None;
            }
            return Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            });
        }
        if matches!(
            function.as_str(),
            "var_pop" | "var_samp" | "variance" | "stddev_pop" | "stddev_samp" | "stddev"
        ) && matches!(
            arg_ty,
            FormalAttributeType::Float | FormalAttributeType::Double
        ) {
            self.error(
                path,
                "floating_statistic_semantics_not_supported",
                "PostgreSQL floating variance/stddev uses the Youngs-Cramer transition state, which is not yet modeled as a value aggregate.",
            );
            return None;
        }
        match (function.as_str(), arg_ty) {
            ("single_value", FormalAttributeType::Int32) => Some(FormalAttributeType::Int32),
            ("sum", FormalAttributeType::Int32) => Some(FormalAttributeType::Int64),
            ("sum", FormalAttributeType::Int64)
            | ("sum" | "avg", FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })
            | ("avg", FormalAttributeType::Int32 | FormalAttributeType::Int64) => {
                Some(FormalAttributeType::Numeric)
            }
            (
                "var_pop" | "var_samp" | "variance" | "stddev_pop" | "stddev_samp" | "stddev",
                FormalAttributeType::Int32 | FormalAttributeType::Int64,
            ) => Some(FormalAttributeType::Numeric),
            ("max" | "min", FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. }) => {
                Some(FormalAttributeType::Numeric)
            }
            (
                "bit_and" | "bit_or",
                ty @ (FormalAttributeType::Int32 | FormalAttributeType::Int64),
            ) => Some(ty),
            (
                "max" | "min",
                ty @ (FormalAttributeType::Z
                | FormalAttributeType::Int32
                | FormalAttributeType::Int64
                | FormalAttributeType::Float
                | FormalAttributeType::Double),
            ) => Some(ty),
            ("sum", ty @ (FormalAttributeType::Float | FormalAttributeType::Double)) => Some(ty),
            ("avg", FormalAttributeType::Float | FormalAttributeType::Double) => {
                Some(FormalAttributeType::Double)
            }
            ("sum" | "avg", FormalAttributeType::Z) => Some(FormalAttributeType::Z),
            ("single_value", _) => {
                self.error(
                    path,
                    "single_value_argument_type_not_supported",
                    "Exact SINGLE_VALUE lowering currently supports INTEGER input only.",
                );
                None
            }
            _ => {
                self.error(
                    path,
                    "aggregate_result_type_not_supported",
                    "The PostgreSQL result type of this aggregate/argument pair is not modeled.",
                );
                None
            }
        }
    }

    fn calcite_aggregate_type_override_is_known(
        &mut self,
        call: &AggregateCall,
        scope: &Scope,
        postgres_ty: FormalAttributeType,
    ) -> bool {
        let function = call.function.to_ascii_lowercase();
        if function == "avg" && postgres_ty == FormalAttributeType::Double {
            let [arg] = call.args.as_slice() else {
                return false;
            };
            let arg_ty = self
                .direct_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                .or_else(|| {
                    self.infer_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                });
            return matches!(
                arg_ty,
                Some(FormalAttributeType::Float | FormalAttributeType::Double)
            );
        }
        if matches!(function.as_str(), "bit_and" | "bit_or") {
            let [arg] = call.args.as_slice() else {
                return false;
            };
            let arg_ty = self
                .direct_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                .or_else(|| {
                    self.infer_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                })
                .or_else(|| {
                    self.infer_numeric_operand_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                });
            return matches!(
                arg_ty,
                Some(FormalAttributeType::Int32 | FormalAttributeType::Int64)
            ) && arg_ty == Some(postgres_ty);
        }
        if function == "max"
            && matches!(
                &postgres_ty,
                FormalAttributeType::String {
                    typmod: SqlStringType::Text
                }
            )
        {
            let [arg] = call.args.as_slice() else {
                return false;
            };
            let arg_ty = self
                .direct_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                .or_else(|| {
                    self.infer_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
                });
            return arg_ty == Some(postgres_ty);
        }
        if postgres_ty != FormalAttributeType::Numeric {
            return false;
        }
        if attested_postgres_stddev_samp_numeric_fixed(call, scope).is_some() {
            return true;
        }
        let [arg] = call.args.as_slice() else {
            return false;
        };
        let arg_ty = self
            .direct_function_type("aggregateTypeOverride.arg", &arg.parsed, scope)
            .or_else(|| self.infer_function_type("aggregateTypeOverride.arg", &arg.parsed, scope))
            .or_else(|| {
                self.infer_numeric_operand_type("aggregateTypeOverride.arg", &arg.parsed, scope)
            });
        match (function.as_str(), arg_ty) {
            ("avg", Some(ty)) => is_integral_aggregate_type(ty) || is_exact_numeric_type(ty),
            (
                "var_pop" | "var_samp" | "variance" | "stddev_pop" | "stddev_samp" | "stddev",
                Some(ty),
            ) => is_integral_aggregate_type(ty),
            ("sum", Some(FormalAttributeType::Int64)) => true,
            ("sum", Some(ty)) => is_exact_numeric_type(ty),
            ("min" | "max", Some(ty)) => is_exact_numeric_type(ty),
            _ => false,
        }
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
        debug_assert!(
            call.filter.is_none(),
            "filtered calls must be projected to lazy CASE arguments first"
        );
        if call.modifiers.has_semantic_modifiers() {
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
            if output_ty != &FormalAttributeType::Int64 {
                self.error(
                    &call_path,
                    "aggregate_output_type_not_supported",
                    "COUNT(*) returns BIGINT in the PostgreSQL/FormalSQL model.",
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
        if !aggregate_function_is_supported(&call.function) {
            let code = if call.distinct {
                "distinct_aggregate_function_not_supported"
            } else {
                "aggregate_function_not_supported"
            };
            self.error(
                &call_path,
                code,
                "FormalSQL aggregate lowering has no built-in Rocq value/runtime-error interpretation for this aggregate and argument family.",
            );
            return None;
        }
        let arg_path = format!("{call_path}.arg");
        let arg_ty = self
            .direct_function_type(&arg_path, &call.args[0].parsed, scope)
            .or_else(|| self.infer_function_type(&arg_path, &call.args[0].parsed, scope))
            .or_else(|| self.infer_numeric_operand_type(&arg_path, &call.args[0].parsed, scope));
        let numeric_fixed_stddev_samp = attested_postgres_stddev_samp_numeric_fixed(call, scope);
        if call.function.eq_ignore_ascii_case("STDDEV_SAMP")
            && matches!(arg_ty, Some(FormalAttributeType::Decimal { .. }))
        {
            if numeric_fixed_stddev_samp.is_none() {
                self.error(
                    &call_path,
                    "numeric_stddev_source_not_attested",
                    "Exact fixed-typmod DECIMAL STDDEV_SAMP lowering requires one direct source-AST identifier bound to the same typed aggregate input, with no DISTINCT, FILTER, cast, expression, or aggregate modifier.",
                );
                return None;
            }
            if output_ty != &FormalAttributeType::Numeric {
                self.error(
                    &call_path,
                    "numeric_statistic_output_type_not_supported",
                    "PostgreSQL STDDEV_SAMP(DECIMAL(p,s)) returns unconstrained NUMERIC.",
                );
                return None;
            }
        }
        if call.function.eq_ignore_ascii_case("MAX")
            && matches!(
                arg_ty.as_ref(),
                Some(FormalAttributeType::String {
                    typmod: SqlStringType::Text
                })
            )
        {
            if !self
                .config
                .sql_environment
                .has_postgres_utf8_c_text_semantics()
            {
                self.error(
                    &call_path,
                    "string_collation_aggregate_not_supported",
                    "PostgreSQL MAX(text) depends on the locale environment; exact lowering requires --sql-default-collation C, --sql-character-classification C, --sql-locale-provider libc, and --sql-server-encoding UTF8.",
                );
                return None;
            }
            if output_ty
                != &(FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                })
            {
                self.error(
                    &call_path,
                    "string_aggregate_output_type_not_supported",
                    "PostgreSQL MAX(text) returns text without an implicit result cast.",
                );
                return None;
            }
        }
        if call.function.eq_ignore_ascii_case("COUNT") {
            if output_ty != &FormalAttributeType::Int64 {
                self.error(
                    &call_path,
                    "aggregate_output_type_not_supported",
                    "COUNT(expr) returns BIGINT in the PostgreSQL/FormalSQL model.",
                );
                return None;
            }
        } else if call.function.eq_ignore_ascii_case("SUM")
            && matches!(arg_ty, Some(FormalAttributeType::Int32))
        {
            if output_ty != &FormalAttributeType::Int64 {
                self.error(
                    &call_path,
                    "integer_sum_output_type_not_supported",
                    "PostgreSQL SUM(INTEGER) returns BIGINT; other output coercions are not modeled.",
                );
                return None;
            }
        } else if call.function.eq_ignore_ascii_case("SUM")
            && matches!(arg_ty, Some(FormalAttributeType::Int64))
        {
            if output_ty != &FormalAttributeType::Numeric {
                self.error(
                    &call_path,
                    "bigint_sum_output_type_not_supported",
                    "PostgreSQL SUM(BIGINT) returns unconstrained NUMERIC.",
                );
                return None;
            }
        } else if call.function.eq_ignore_ascii_case("AVG")
            && arg_ty.is_some_and(is_integral_aggregate_type)
        {
            if output_ty != &FormalAttributeType::Numeric {
                self.error(
                    &call_path,
                    "integer_avg_output_type_not_supported",
                    "PostgreSQL AVG(INTEGER/BIGINT) returns unconstrained NUMERIC.",
                );
                return None;
            }
        } else if postgres_integral_statistic(&call.function)
            && arg_ty.is_some_and(is_integral_aggregate_type)
        {
            if matches!(arg_ty, Some(FormalAttributeType::Int64)) {
                self.error(
                    &call_path,
                    "bigint_statistic_not_supported",
                    "PostgreSQL BIGINT variance/stddev uses the general exact-NUMERIC transition state, not the signed-128 polynomial state used by INTEGER; that distinct transition and its runtime limits are not modeled yet.",
                );
                return None;
            }
            if output_ty != &FormalAttributeType::Numeric {
                self.error(
                    &call_path,
                    "integer_statistic_output_type_not_supported",
                    "PostgreSQL integral variance/stddev aggregates return unconstrained NUMERIC.",
                );
                return None;
            }
        } else if matches!(call.function.to_ascii_lowercase().as_str(), "max" | "min")
            && arg_ty.is_some_and(is_integral_aggregate_type)
        {
            if arg_ty.as_ref() != Some(output_ty) {
                self.error(
                    &call_path,
                    "integer_minmax_output_type_not_supported",
                    "PostgreSQL MIN/MAX over INTEGER/BIGINT returns the input integer type.",
                );
                return None;
            }
        } else if matches!(
            call.function.to_ascii_lowercase().as_str(),
            "bit_and" | "bit_or"
        ) {
            if !matches!(
                arg_ty,
                Some(FormalAttributeType::Int32 | FormalAttributeType::Int64)
            ) || arg_ty.as_ref() != Some(output_ty)
            {
                self.error(
                    &call_path,
                    "bitwise_aggregate_output_type_not_supported",
                    "PostgreSQL BIT_AND/BIT_OR over INTEGER/BIGINT returns the unchanged input integer type; SMALLINT, BIT strings, and implicit aggregate result casts are not modeled.",
                );
                return None;
            }
        } else if call.function.eq_ignore_ascii_case("SINGLE_VALUE") {
            if arg_ty != Some(FormalAttributeType::Int32)
                || output_ty != &FormalAttributeType::Int32
            {
                self.error(
                    &call_path,
                    "single_value_type_not_supported",
                    "Exact SINGLE_VALUE lowering requires matching INTEGER argument and result types.",
                );
                return None;
            }
        } else if call.function.eq_ignore_ascii_case("AVG")
            && matches!(
                arg_ty,
                Some(FormalAttributeType::Float | FormalAttributeType::Double)
            )
        {
            if output_ty != &FormalAttributeType::Double {
                self.error(
                    &call_path,
                    "floating_aggregate_output_type_not_supported",
                    "PostgreSQL AVG(REAL/DOUBLE PRECISION) returns DOUBLE PRECISION.",
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
        if (call.function.eq_ignore_ascii_case("AVG") || call.function.eq_ignore_ascii_case("SUM"))
            && arg_ty.is_some_and(is_exact_numeric_type)
            && output_ty != &FormalAttributeType::Numeric
        {
            self.error(
                &call_path,
                "numeric_aggregate_output_type_not_supported",
                "PostgreSQL SUM/AVG(NUMERIC) returns unconstrained NUMERIC.",
            );
            return None;
        }
        let numeric_avg_function = if call.function.eq_ignore_ascii_case("AVG") {
            match arg_ty.as_ref() {
                Some(FormalAttributeType::Decimal { precision, scale }) => {
                    Some(FormalAggregateFunction::AverageNumericFixed {
                        precision: *precision,
                        scale: *scale,
                    })
                }
                Some(FormalAttributeType::Numeric) => {
                    match self.infer_numeric_dscale(&call.args[0].parsed, scope) {
                        Some(
                            NumericDscaleProvenance::Exact(scale)
                            | NumericDscaleProvenance::Representative(scale),
                        ) => Some(FormalAggregateFunction::AverageNumericAtScale { scale }),
                        _ => None,
                    }
                }
                _ => None,
            }
        } else {
            None
        };
        if call.function.eq_ignore_ascii_case("AVG")
            && arg_ty.is_some_and(is_exact_numeric_type)
            && numeric_avg_function.is_none()
        {
            self.error(
                &call_path,
                "numeric_avg_typmod_not_supported",
                "Exact PostgreSQL NUMERIC AVG lowering requires either a fixed DECIMAL typmod or exact/representative display-scale provenance. Unconstrained NUMERIC without that provenance is rejected because its transition/finalization scale is not recoverable from numeric equality.",
            );
            return None;
        }
        let function = if let Some((precision, scale)) = numeric_fixed_stddev_samp {
            FormalAggregateFunction::StddevSampleNumericFixed { precision, scale }
        } else if let Some(function) = numeric_avg_function {
            function
        } else {
            aggregate_function_for_type(&call.function, arg_ty.as_ref()).or_else(|| {
                self.error(
                    &call_path,
                    "decimal_aggregate_not_supported",
                    "This DECIMAL aggregate is outside the currently modeled FormalSQL Decimal subset.",
                );
                None
            })?
        };
        let arg = self
            .lower_function_term(&arg_path, &call.args[0].parsed, scope)
            .map(|arg| {
                arg_ty
                    .map(|ty| annotate_function_literal_term(arg.clone(), ty))
                    .unwrap_or(arg)
            })?;
        Some(FormalAggregateTerm::Aggregate {
            function,
            quantifier: if call.distinct {
                FormalAggregateQuantifier::Distinct
            } else {
                FormalAggregateQuantifier::All
            },
            arg,
        })
    }
}

/// Recognize the declarative cumulative ROWS window shapes represented by the
/// current FormalSQL Window node. Unsupported functions, modifiers, and frame
/// boundaries remain conservatively rejected.
fn supported_cumulative_rows_window(window: &WindowAst) -> bool {
    let arity_supported = if window.function.eq_ignore_ascii_case("ROW_NUMBER") {
        window.args.is_empty()
    } else if window.function.eq_ignore_ascii_case("SUM")
        || window.function.eq_ignore_ascii_case("MAX")
    {
        window.args.len() == 1
    } else {
        false
    };
    arity_supported
        && !window.distinct
        && !window.ignore_nulls
        && window.exclude.as_deref() == Some("EXCLUDE_NO_OTHER")
        && matches!(
            window.frame.as_ref(),
            Some(WindowFrameAst {
                units: WindowFrameUnits::Rows,
                start: WindowFrameBoundAst::UnboundedPreceding,
                end: Some(WindowFrameBoundAst::CurrentRow),
            })
        )
}

fn project_has_top_level_numeric_exp(exprs: &[ScalarExpr]) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            expr.parsed,
            ScalarAst::Call {
                op: ScalarOp::Exp,
                ..
            }
        )
    })
}

fn project_has_top_level_rank_window(exprs: &[ScalarExpr]) -> bool {
    exprs.iter().any(|expr| {
        matches!(
            &expr.parsed,
            ScalarAst::Window { parsed }
                if parsed.function.eq_ignore_ascii_case("RANK")
        )
    })
}

fn project_has_supported_cumulative_rows_windows(exprs: &[ScalarExpr]) -> bool {
    let mut found = false;
    for expr in exprs {
        if let ScalarAst::Window { parsed } = &expr.parsed {
            if !supported_cumulative_rows_window(parsed) {
                return false;
            }
            found = true;
        } else if scalar_ast_contains_window(&expr.parsed) {
            return false;
        }
    }
    found
}

fn classify_supported_count_window(ast: &ScalarAst) -> Option<SupportedCountWindowShape> {
    let ScalarAst::Window { parsed } = ast else {
        return None;
    };
    if !parsed.function.eq_ignore_ascii_case("COUNT")
        || parsed.distinct
        || parsed.ignore_nulls
        || parsed.exclude.as_deref() != Some("EXCLUDE_NO_OTHER")
    {
        return None;
    }

    if matches!(
        parsed.frame.as_ref(),
        Some(WindowFrameAst {
            units: WindowFrameUnits::Range,
            start: WindowFrameBoundAst::UnboundedPreceding,
            end: Some(WindowFrameBoundAst::CurrentRow),
        })
    ) && parsed.args.is_empty()
    {
        let [ScalarAst::InputRef { index: key_index }] = parsed.partition_by.as_slice() else {
            return None;
        };
        let [order_key] = parsed.order_by.as_slice() else {
            return None;
        };
        let ScalarAst::InputRef { index: order_index } = &order_key.expr else {
            return None;
        };
        if order_index == key_index
            && order_key.direction == Some(SortDirection::Ascending)
            && order_key.null_direction == Some(SortNullDirection::Last)
        {
            return Some(SupportedCountWindowShape::PartitionPeerComplete {
                key_index: *key_index,
            });
        }
        return None;
    }

    if matches!(
        parsed.frame.as_ref(),
        Some(WindowFrameAst {
            units: WindowFrameUnits::Range,
            start: WindowFrameBoundAst::UnboundedPreceding,
            end: Some(WindowFrameBoundAst::UnboundedFollowing),
        })
    ) && parsed.partition_by.is_empty()
        && parsed.order_by.is_empty()
    {
        let [ScalarAst::InputRef { index: arg_index }] = parsed.args.as_slice() else {
            return None;
        };
        return Some(SupportedCountWindowShape::GlobalFull {
            arg_index: *arg_index,
        });
    }

    None
}

fn scalar_ast_contains_window(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::Window { .. } => true,
        ScalarAst::Call { args, .. } => args.iter().any(scalar_ast_contains_window),
        ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_contains_window(expr),
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::RelSubquery { .. } => false,
    }
}

fn scalar_ast_contains_rel_subquery(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::RelSubquery { .. } => true,
        ScalarAst::Call { args, .. } => args.iter().any(scalar_ast_contains_rel_subquery),
        ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_contains_rel_subquery(expr),
        ScalarAst::Window { parsed } => {
            parsed.args.iter().any(scalar_ast_contains_rel_subquery)
                || parsed
                    .partition_by
                    .iter()
                    .any(scalar_ast_contains_rel_subquery)
                || parsed
                    .order_by
                    .iter()
                    .any(|key| scalar_ast_contains_rel_subquery(&key.expr))
                || parsed.frame.as_ref().is_some_and(|frame| {
                    window_frame_bound_contains_rel_subquery(&frame.start)
                        || frame
                            .end
                            .as_ref()
                            .is_some_and(window_frame_bound_contains_rel_subquery)
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => false,
    }
}

fn collect_nested_rel_attribute_names(ast: &ScalarAst, names: &mut BTreeSet<String>) {
    match ast {
        ScalarAst::RelSubquery { rel } => collect_rel_attribute_names(rel, names),
        ScalarAst::Call { args, .. } => {
            for argument in args {
                collect_nested_rel_attribute_names(argument, names);
            }
        }
        ScalarAst::TypeAnnotation { expr, .. } => {
            collect_nested_rel_attribute_names(expr, names);
        }
        ScalarAst::Window { parsed } => {
            for argument in &parsed.args {
                collect_nested_rel_attribute_names(argument, names);
            }
            for partition in &parsed.partition_by {
                collect_nested_rel_attribute_names(partition, names);
            }
            for key in &parsed.order_by {
                collect_nested_rel_attribute_names(&key.expr, names);
            }
            if let Some(frame) = &parsed.frame {
                for offset in frame.offset_exprs() {
                    collect_nested_rel_attribute_names(offset, names);
                }
            }
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => {}
    }
}

fn collect_rel_attribute_names(rel: &RelExpr, names: &mut BTreeSet<String>) {
    names.extend(rel.output().iter().map(|column| column.name.clone()));
    match rel {
        RelExpr::TableScan { .. } => {}
        RelExpr::Project {
            input,
            exprs,
            correlations,
            ..
        } => {
            collect_rel_attribute_names(input, names);
            for expression in exprs {
                collect_nested_rel_attribute_names(&expression.parsed, names);
            }
            for binding in correlations {
                names.extend(binding.output.iter().map(|column| column.name.clone()));
            }
        }
        RelExpr::Filter {
            input,
            predicate,
            correlations,
            ..
        }
        | RelExpr::NativeHaving {
            input,
            predicate,
            correlations,
            ..
        } => {
            collect_rel_attribute_names(input, names);
            collect_nested_rel_attribute_names(&predicate.parsed, names);
            for binding in correlations {
                names.extend(binding.output.iter().map(|column| column.name.clone()));
            }
        }
        RelExpr::Join {
            left,
            right,
            condition,
            correlations,
            ..
        } => {
            collect_rel_attribute_names(left, names);
            collect_rel_attribute_names(right, names);
            collect_nested_rel_attribute_names(&condition.parsed, names);
            for binding in correlations {
                names.extend(binding.output.iter().map(|column| column.name.clone()));
            }
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            collect_rel_attribute_names(input, names);
            for call in agg_calls {
                for argument in &call.args {
                    collect_nested_rel_attribute_names(&argument.parsed, names);
                }
                if let Some(filter) = &call.filter {
                    collect_nested_rel_attribute_names(&filter.parsed, names);
                }
            }
        }
        RelExpr::Distinct { input, .. } => collect_rel_attribute_names(input, names),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            collect_rel_attribute_names(input, names);
            if let Some(fetch) = fetch {
                collect_nested_rel_attribute_names(&fetch.parsed, names);
            }
            if let Some(offset) = offset {
                collect_nested_rel_attribute_names(&offset.parsed, names);
            }
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_rel_attribute_names(input, names);
            }
        }
        RelExpr::Values { rows, .. } => {
            for row in rows {
                for expression in row {
                    collect_nested_rel_attribute_names(&expression.parsed, names);
                }
            }
        }
    }
}

fn window_frame_bound_contains_rel_subquery(bound: &WindowFrameBoundAst) -> bool {
    match bound {
        WindowFrameBoundAst::OffsetPreceding { expr, .. }
        | WindowFrameBoundAst::OffsetFollowing { expr, .. } => {
            scalar_ast_contains_rel_subquery(expr)
        }
        WindowFrameBoundAst::UnboundedPreceding
        | WindowFrameBoundAst::CurrentRow
        | WindowFrameBoundAst::UnboundedFollowing => false,
    }
}

fn fresh_internal_attribute_name(base: &str, used: &mut BTreeSet<String>) -> String {
    if used.insert(base.to_owned()) {
        return base.to_owned();
    }
    for suffix in 1_u64.. {
        let candidate = format!("{base}_{suffix}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("the finite set of used attribute names cannot exhaust all numeric suffixes")
}

fn select_output_term(
    select: &[FormalSelectItem],
    name: &str,
    ty: FormalAttributeType,
) -> Option<FormalAggregateTerm> {
    let mut matches = select
        .iter()
        .filter(|item| item.alias == name && item.alias_ty == ty);
    let term = matches.next()?.expr.clone();
    matches.next().is_none().then_some(term)
}

fn function_term_contains_attribute(term: &FormalFunctionTerm) -> bool {
    match term {
        FormalFunctionTerm::Constant { .. } => false,
        FormalFunctionTerm::Attribute { .. } => true,
        FormalFunctionTerm::ScalarCall { args, .. } => {
            args.iter().any(function_term_contains_attribute)
        }
    }
}

/// Replace references to Calcite Aggregate output slots by the exact Group
/// select terms that produce those slots. A direct output attribute may turn
/// into an aggregate term (for example COUNT(*)), so an attribute nested
/// inside a function-term-only context is rejected conservatively.
fn substitute_having_term(
    term: &FormalAggregateTerm,
    select: &[FormalSelectItem],
) -> Option<FormalAggregateTerm> {
    match term {
        FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Attribute { name, ty },
        } => select_output_term(select, name, *ty),
        FormalAggregateTerm::Expr { term } => (!function_term_contains_attribute(term))
            .then(|| FormalAggregateTerm::Expr { term: term.clone() }),
        FormalAggregateTerm::Aggregate {
            function,
            quantifier,
            arg,
        } => Some(FormalAggregateTerm::Aggregate {
            function: *function,
            quantifier: *quantifier,
            arg: arg.clone(),
        }),
        FormalAggregateTerm::CountStar => Some(FormalAggregateTerm::CountStar),
        FormalAggregateTerm::ScalarCall { operator, args } => {
            Some(FormalAggregateTerm::ScalarCall {
                operator: *operator,
                args: args
                    .iter()
                    .map(|arg| substitute_having_term(arg, select))
                    .collect::<Option<Vec<_>>>()?,
            })
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => Some(FormalAggregateTerm::Case {
            branches: branches
                .iter()
                .map(|branch| {
                    Some(FormalCaseBranch {
                        when: substitute_having_term(&branch.when, select)?,
                        then_expr: substitute_having_term(&branch.then_expr, select)?,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
            else_expr: Box::new(substitute_having_term(else_expr, select)?),
        }),
    }
}

fn substitute_having_select_item(
    item: &FormalSelectItem,
    select: &[FormalSelectItem],
) -> Option<FormalSelectItem> {
    Some(FormalSelectItem {
        expr: substitute_having_term(&item.expr, select)?,
        alias: item.alias.clone(),
        alias_ty: item.alias_ty,
        numeric_dscale: item.numeric_dscale.clone(),
    })
}

fn legacy_select_from_scalar_leaves(
    select: &[FormalScalarSelectItem],
) -> Option<Vec<FormalSelectItem>> {
    select
        .iter()
        .map(|item| {
            let FormalScalarExpr::Leaf { result_ty, term } = &item.expr else {
                return None;
            };
            (*result_ty == item.alias_ty).then(|| FormalSelectItem {
                expr: term.clone(),
                alias: item.alias.clone(),
                alias_ty: item.alias_ty,
                numeric_dscale: item.numeric_dscale.clone(),
            })
        })
        .collect()
}

fn substitute_having_scalar_expr(
    expression: &FormalScalarExpr,
    select: &[FormalSelectItem],
) -> Option<FormalScalarExpr> {
    Some(match expression {
        FormalScalarExpr::Leaf { result_ty, term } => FormalScalarExpr::Leaf {
            result_ty: *result_ty,
            term: substitute_having_term(term, select)?,
        },
        FormalScalarExpr::Call {
            result_ty,
            operator,
            args,
        } => FormalScalarExpr::Call {
            result_ty: *result_ty,
            operator: *operator,
            args: args
                .iter()
                .map(|arg| substitute_having_scalar_expr(arg, select))
                .collect::<Option<Vec<_>>>()?,
        },
        FormalScalarExpr::Case {
            result_ty,
            condition,
            then_expr,
            else_expr,
        } => FormalScalarExpr::Case {
            result_ty: *result_ty,
            condition: Box::new(substitute_having_scalar_expr(condition, select)?),
            then_expr: Box::new(substitute_having_scalar_expr(then_expr, select)?),
            else_expr: Box::new(substitute_having_scalar_expr(else_expr, select)?),
        },
        FormalScalarExpr::BooleanValue { expression } => FormalScalarExpr::BooleanValue {
            expression: Box::new(substitute_having_scalar_expr(expression, select)?),
        },
        FormalScalarExpr::ValueBoolean { expression } => FormalScalarExpr::ValueBoolean {
            expression: Box::new(substitute_having_scalar_expr(expression, select)?),
        },
        FormalScalarExpr::Predicate { predicate, args } => FormalScalarExpr::Predicate {
            predicate: *predicate,
            args: args
                .iter()
                .map(|arg| substitute_having_scalar_expr(arg, select))
                .collect::<Option<Vec<_>>>()?,
        },
        FormalScalarExpr::And { left, right } => FormalScalarExpr::And {
            left: Box::new(substitute_having_scalar_expr(left, select)?),
            right: Box::new(substitute_having_scalar_expr(right, select)?),
        },
        FormalScalarExpr::Or { left, right } => FormalScalarExpr::Or {
            left: Box::new(substitute_having_scalar_expr(left, select)?),
            right: Box::new(substitute_having_scalar_expr(right, select)?),
        },
        FormalScalarExpr::Not { expression } => FormalScalarExpr::Not {
            expression: Box::new(substitute_having_scalar_expr(expression, select)?),
        },
        FormalScalarExpr::True => FormalScalarExpr::True,
        FormalScalarExpr::QuantifiedComparison {
            quantifier,
            predicate,
            args,
            query,
        } => FormalScalarExpr::QuantifiedComparison {
            quantifier: *quantifier,
            predicate: *predicate,
            args: args
                .iter()
                .map(|arg| substitute_having_scalar_expr(arg, select))
                .collect::<Option<Vec<_>>>()?,
            query: query.clone(),
        },
        FormalScalarExpr::In { args, query } => FormalScalarExpr::In {
            args: args
                .iter()
                .map(|arg| substitute_having_scalar_expr(arg, select))
                .collect::<Option<Vec<_>>>()?,
            query: query.clone(),
        },
        FormalScalarExpr::Exists { query } => FormalScalarExpr::Exists {
            query: query.clone(),
        },
        FormalScalarExpr::Subquery { result_ty, query } => FormalScalarExpr::Subquery {
            result_ty: *result_ty,
            query: query.clone(),
        },
    })
}

fn substitute_having_formula_expr(
    formula: &FormalFormulaExpr,
    select: &[FormalSelectItem],
) -> Option<FormalFormulaExpr> {
    match formula {
        FormalFormulaExpr::True => Some(FormalFormulaExpr::True),
        FormalFormulaExpr::False => Some(FormalFormulaExpr::False),
        FormalFormulaExpr::Predicate { predicate, args } => Some(FormalFormulaExpr::Predicate {
            predicate: *predicate,
            args: args
                .iter()
                .map(|arg| substitute_having_term(arg, select))
                .collect::<Option<Vec<_>>>()?,
        }),
        FormalFormulaExpr::And { left, right } => Some(FormalFormulaExpr::And {
            left: Box::new(substitute_having_formula_expr(left, select)?),
            right: Box::new(substitute_having_formula_expr(right, select)?),
        }),
        FormalFormulaExpr::Or { left, right } => Some(FormalFormulaExpr::Or {
            left: Box::new(substitute_having_formula_expr(left, select)?),
            right: Box::new(substitute_having_formula_expr(right, select)?),
        }),
        FormalFormulaExpr::Not { formula } => Some(FormalFormulaExpr::Not {
            formula: Box::new(substitute_having_formula_expr(formula, select)?),
        }),
        FormalFormulaExpr::In {
            select: left_select,
            query,
        } => Some(FormalFormulaExpr::In {
            select: left_select
                .iter()
                .map(|item| substitute_having_select_item(item, select))
                .collect::<Option<Vec<_>>>()?,
            query: query.clone(),
        }),
        FormalFormulaExpr::QuantifiedComparison {
            predicate,
            args,
            query,
        } => Some(FormalFormulaExpr::QuantifiedComparison {
            predicate: *predicate,
            args: args
                .iter()
                .map(|arg| substitute_having_term(arg, select))
                .collect::<Option<Vec<_>>>()?,
            query: query.clone(),
        }),
        FormalFormulaExpr::Exists { query } => Some(FormalFormulaExpr::Exists {
            query: query.clone(),
        }),
        FormalFormulaExpr::Scalar { expression } => Some(FormalFormulaExpr::Scalar {
            expression: Box::new(substitute_having_scalar_expr(expression, select)?),
        }),
    }
}

fn install_query_expr_having(
    query: FormalQueryExpr,
    predicate: &FormalFormulaExpr,
) -> Option<FormalQueryExpr> {
    match query {
        FormalQueryExpr::ScalarGroup {
            select,
            group_by,
            having: FormalScalarExpr::True,
            input,
        } => {
            let FormalFormulaExpr::Scalar { expression } = predicate else {
                return None;
            };
            let legacy_select = legacy_select_from_scalar_leaves(&select)?;
            Some(FormalQueryExpr::ScalarGroup {
                having: substitute_having_scalar_expr(expression, &legacy_select)?,
                select,
                group_by,
                input,
            })
        }
        FormalQueryExpr::Group {
            select,
            group_by,
            having: FormalFormulaExpr::True,
            input,
        } => Some(FormalQueryExpr::Group {
            having: substitute_having_formula_expr(predicate, &select)?,
            select,
            group_by,
            input,
        }),
        _ => None,
    }
}

/// Under the deterministic default-collation contract, every TEXT value in a
/// group keyed by that exact input reference has the same logical payload.
/// PostgreSQL MIN/MAX ignore NULL, so the all-NULL group also yields the key's
/// NULL value.  This identity deliberately does not apply to absent grouping
/// keys, filtered/DISTINCT aggregates, expressions, or aggregate modifiers.
fn grouped_text_minmax_key(call: &AggregateCall, grouping_set: &[usize]) -> Option<usize> {
    if call.distinct
        || call.filter.is_some()
        || call.modifiers.has_semantic_modifiers()
        || !matches!(call.function.to_ascii_lowercase().as_str(), "min" | "max")
    {
        return None;
    }
    let [arg] = call.args.as_slice() else {
        return None;
    };
    let ScalarAst::InputRef { index } = &arg.parsed else {
        return None;
    };
    grouping_set.contains(index).then_some(*index)
}

enum NumericCoalesceOverrideOrigin {
    BigintSum,
    DecimalSum,
}

enum NumericCoalesceOverride {
    NotApplicable,
    Rewritten {
        ast: Box<ScalarAst>,
        origin: NumericCoalesceOverrideOrigin,
    },
    Drift,
}

/// PostgreSQL first types the exact bare token `0` as int4 and only then
/// applies the common-type coercion to unconstrained NUMERIC.  The Calcite
/// converter reconstructs this exact lexical int4 step before lowering: its
/// display scale is zero and can be observed by later NUMERIC arithmetic.
fn postgres_int4_to_numeric_zero(ast: &ScalarAst) -> bool {
    matches!(ast,
        ScalarAst::TypeAnnotation { expr, ty }
            if ty.eq_ignore_ascii_case("NUMERIC")
                && matches!(expr.as_ref(),
                    ScalarAst::Call {
                        operator,
                        op: ScalarOp::Cast,
                        args,
                    } if operator.eq_ignore_ascii_case("CAST")
                        && matches!(args.as_slice(), [
                            ScalarAst::TypeAnnotation { expr, ty }
                        ] if ty.eq_ignore_ascii_case("INTEGER")
                            && matches!(expr.as_ref(),
                                ScalarAst::Literal { raw } if raw == "0"))))
}

fn postgres_numeric_coalesce_override(
    expr: &ScalarExpr,
    output: &Column,
    scope: &Scope,
    input: Option<&RelExpr>,
) -> NumericCoalesceOverride {
    if let Some(source) = expr.source.as_ref()
        && let Some(ast) =
            postgres_bigint_sum_numeric_coalesce_override(&expr.parsed, source, scope)
    {
        return NumericCoalesceOverride::Rewritten {
            ast: Box::new(ast),
            origin: NumericCoalesceOverrideOrigin::BigintSum,
        };
    }

    let source_candidate = expr
        .source
        .as_ref()
        .is_some_and(postgres_decimal_sum_numeric_coalesce_source_candidate);
    let ast_candidate = postgres_decimal_sum_numeric_coalesce_ast_candidate(&expr.parsed, output);
    let typed_numeric_candidate =
        postgres_numeric_coalesce_generated_input_is_numeric(&expr.parsed, scope);
    if ast_candidate
        && expr.source.as_ref().is_some_and(|source| {
            postgres_explicit_decimal_case_source_matches(&expr.parsed, source, output, scope)
        })
    {
        return NumericCoalesceOverride::NotApplicable;
    }
    if !(ast_candidate || source_candidate && typed_numeric_candidate) {
        return NumericCoalesceOverride::NotApplicable;
    }
    let Some(source) = expr.source.as_ref() else {
        return NumericCoalesceOverride::Drift;
    };
    match rewrite_postgres_decimal_sum_numeric_coalesce_node(
        &expr.parsed,
        source,
        output,
        scope,
        input,
    ) {
        Some((ast, true)) => NumericCoalesceOverride::Rewritten {
            ast: Box::new(ast),
            origin: NumericCoalesceOverrideOrigin::DecimalSum,
        },
        _ => NumericCoalesceOverride::Drift,
    }
}

fn postgres_numeric_coalesce_generated_input_is_numeric(ast: &ScalarAst, scope: &Scope) -> bool {
    match ast {
        ScalarAst::Call {
            op: ScalarOp::Case,
            args,
            ..
        } => matches!(args.as_slice(), [
            ScalarAst::Call {
                op: ScalarOp::IsNotNull,
                args: condition_args,
                ..
            },
            _,
            _
        ] if matches!(condition_args.as_slice(), [ScalarAst::InputRef { index }]
            if scope.attribute(*index).is_some_and(|attribute|
                attribute.formal_ty == FormalAttributeType::Numeric))),
        ScalarAst::Call {
            op: ScalarOp::Minus,
            args,
            ..
        } => args
            .iter()
            .any(|arg| postgres_numeric_coalesce_generated_input_is_numeric(arg, scope)),
        _ => false,
    }
}

fn postgres_bigint_sum_numeric_coalesce_override(
    ast: &ScalarAst,
    source: &ScalarSourceProvenance,
    scope: &Scope,
) -> Option<ScalarAst> {
    let ScalarAst::Call {
        operator,
        op: ScalarOp::Case,
        args,
    } = ast
    else {
        return None;
    };
    let [condition, then_value, else_value] = args.as_slice() else {
        return None;
    };
    let ScalarAst::Call {
        op: ScalarOp::IsNotNull,
        args: condition_args,
        ..
    } = condition
    else {
        return None;
    };
    let [
        ScalarAst::InputRef {
            index: condition_index,
        },
    ] = condition_args.as_slice()
    else {
        return None;
    };
    let ScalarAst::TypeAnnotation {
        expr: then_cast,
        ty: then_ty,
    } = then_value
    else {
        return None;
    };
    let ScalarAst::Call {
        op: ScalarOp::Cast,
        args: then_args,
        ..
    } = then_cast.as_ref()
    else {
        return None;
    };
    let [ScalarAst::InputRef { index: then_index }] = then_args.as_slice() else {
        return None;
    };
    if !postgres_int4_to_numeric_zero(else_value) {
        return None;
    }
    if condition_index != then_index
        || !then_ty.eq_ignore_ascii_case("BIGINT")
        || scope.attribute(*then_index)?.formal_ty != FormalAttributeType::Numeric
    {
        return None;
    }
    let [
        Some(condition_source),
        Some(value_source),
        Some(zero_source),
    ] = source.operands.as_slice()
    else {
        return None;
    };
    let [Some(condition_leaf)] = condition_source.operands.as_slice() else {
        return None;
    };
    let [Some(value_leaf)] = value_source.operands.as_slice() else {
        return None;
    };
    if !source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("OTHER_FUNCTION"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|name| name.eq_ignore_ascii_case("coalesce"))
        || !source_has_exact_binding(source)
        || source.clause_ownership.is_some()
        || condition_source.clause_ownership.is_some()
        || value_source.clause_ownership.is_some()
        || zero_source.clause_ownership.is_some()
        || !condition_source
            .operator
            .as_deref()
            .is_some_and(|name| name.eq_ignore_ascii_case("sum"))
        || !exact_source_unary_function_has_direct_identifier(condition_source, "SUM")
        || !exact_source_function_operands_match(
            source,
            "COALESCE",
            &[condition_source, zero_source],
            false,
        )
        || !source_nodes_identical(condition_source, value_source)
        || !source_nodes_identical(condition_source, condition_leaf)
        || !source_nodes_identical(value_source, value_leaf)
        || !condition_leaf.operands.is_empty()
        || !value_leaf.operands.is_empty()
        || !zero_source.operands.is_empty()
        || !source_is_bare_integer_literal(zero_source, "0")
    {
        return None;
    }
    Some(ScalarAst::Call {
        operator: operator.clone(),
        op: ScalarOp::Case,
        args: vec![
            condition.clone(),
            ScalarAst::InputRef { index: *then_index },
            else_value.clone(),
        ],
    })
}

fn postgres_decimal_sum_numeric_coalesce_source_candidate(source: &ScalarSourceProvenance) -> bool {
    let is_coalesce = |node: &ScalarSourceProvenance| {
        source_has_exact_binding(node)
            && node
                .operator
                .as_deref()
                .is_some_and(|operator| operator.eq_ignore_ascii_case("coalesce"))
    };
    is_coalesce(source)
        || (source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("MINUS"))
            && source.operands.iter().flatten().any(is_coalesce))
}

fn postgres_decimal_sum_numeric_coalesce_ast_candidate(ast: &ScalarAst, output: &Column) -> bool {
    match ast {
        ScalarAst::Call {
            op: ScalarOp::Case,
            args,
            ..
        } => {
            let [
                ScalarAst::Call {
                    op: ScalarOp::IsNotNull,
                    args: condition_args,
                    ..
                },
                ScalarAst::TypeAnnotation {
                    expr: then_cast,
                    ty: then_ty,
                },
                else_value,
            ] = args.as_slice()
            else {
                return false;
            };
            matches!(condition_args.as_slice(), [ScalarAst::InputRef { .. }])
                && fixed_decimal_annotation_matches_output(then_ty, output)
                && matches!(then_cast.as_ref(),
                    ScalarAst::Call {
                        op: ScalarOp::Cast,
                        args,
                        ..
                    } if matches!(args.as_slice(), [ScalarAst::InputRef { .. }]))
                && postgres_int4_to_numeric_zero(else_value)
        }
        ScalarAst::Call {
            op: ScalarOp::Minus,
            args,
            ..
        } => args
            .iter()
            .any(|arg| postgres_decimal_sum_numeric_coalesce_ast_candidate(arg, output)),
        _ => false,
    }
}

fn fixed_decimal_annotation_matches_output(ty: &str, output: &Column) -> bool {
    let Some(SqlTypeAnnotation::Decimal {
        precision: Some(precision),
        scale: Some(scale),
    }) = classify_type_annotation(ty)
    else {
        return false;
    };
    output.ty
        == SqlType::Decimal {
            precision: Some(precision),
            scale: Some(scale),
        }
}

fn consume_attested_token(
    tokens: &[AttestedSqlToken],
    cursor: &mut usize,
    expected: &AttestedSqlToken,
) -> bool {
    if tokens.get(*cursor) != Some(expected) {
        return false;
    }
    *cursor += 1;
    true
}

fn consume_attested_identifier(
    tokens: &[AttestedSqlToken],
    cursor: &mut usize,
    expected: &str,
) -> bool {
    if !tokens
        .get(*cursor)
        .is_some_and(|token| token_is_identifier(token, expected))
    {
        return false;
    }
    *cursor += 1;
    true
}

fn consume_attested_direct_column(
    tokens: &[AttestedSqlToken],
    cursor: &mut usize,
    expected: &str,
) -> bool {
    let Some(end) = direct_column_at(tokens, *cursor, expected) else {
        return false;
    };
    *cursor = end;
    true
}

fn exact_attested_is_not_null(tokens: &[AttestedSqlToken], attribute_name: &str) -> bool {
    let mut cursor = 0;
    consume_attested_direct_column(tokens, &mut cursor, attribute_name)
        && consume_attested_identifier(tokens, &mut cursor, "is")
        && consume_attested_identifier(tokens, &mut cursor, "not")
        && consume_attested_identifier(tokens, &mut cursor, "null")
        && cursor == tokens.len()
}

fn exact_attested_decimal_cast(
    tokens: &[AttestedSqlToken],
    attribute_name: &str,
    precision: u32,
    scale: u32,
) -> bool {
    let mut cursor = 0;
    consume_attested_identifier(tokens, &mut cursor, "cast")
        && consume_attested_token(tokens, &mut cursor, &AttestedSqlToken::LeftParen)
        && consume_attested_direct_column(tokens, &mut cursor, attribute_name)
        && consume_attested_identifier(tokens, &mut cursor, "as")
        && consume_attested_identifier(tokens, &mut cursor, "decimal")
        && consume_attested_token(tokens, &mut cursor, &AttestedSqlToken::LeftParen)
        && consume_attested_token(
            tokens,
            &mut cursor,
            &AttestedSqlToken::Number(precision.to_string()),
        )
        && consume_attested_token(tokens, &mut cursor, &AttestedSqlToken::Comma)
        && consume_attested_token(
            tokens,
            &mut cursor,
            &AttestedSqlToken::Number(scale.to_string()),
        )
        && consume_attested_token(tokens, &mut cursor, &AttestedSqlToken::RightParen)
        && consume_attested_token(tokens, &mut cursor, &AttestedSqlToken::RightParen)
        && cursor == tokens.len()
}

fn exact_attested_explicit_decimal_case(
    tokens: &[AttestedSqlToken],
    attribute_name: &str,
    precision: u32,
    scale: u32,
) -> bool {
    let mut cursor = 0;
    consume_attested_identifier(tokens, &mut cursor, "case")
        && consume_attested_identifier(tokens, &mut cursor, "when")
        && consume_attested_direct_column(tokens, &mut cursor, attribute_name)
        && consume_attested_identifier(tokens, &mut cursor, "is")
        && consume_attested_identifier(tokens, &mut cursor, "not")
        && consume_attested_identifier(tokens, &mut cursor, "null")
        && consume_attested_identifier(tokens, &mut cursor, "then")
        && {
            let cast_start = cursor;
            let Some(cast_end) =
                tokens[cast_start..]
                    .iter()
                    .enumerate()
                    .find_map(|(index, token)| {
                        (matches!(token, AttestedSqlToken::RightParen)
                            && matches!(tokens.get(cast_start + index + 1), Some(next)
                            if token_is_identifier(next, "else")))
                        .then_some(cast_start + index + 1)
                    })
            else {
                return false;
            };
            if !exact_attested_decimal_cast(
                &tokens[cast_start..cast_end],
                attribute_name,
                precision,
                scale,
            ) {
                return false;
            }
            cursor = cast_end;
            true
        }
        && consume_attested_identifier(tokens, &mut cursor, "else")
        && consume_attested_token(
            tokens,
            &mut cursor,
            &AttestedSqlToken::Number("0".to_owned()),
        )
        && consume_attested_identifier(tokens, &mut cursor, "end")
        && cursor == tokens.len()
}

/// A source-written fixed-DECIMAL CASE can have the same Calcite scalar tree
/// as generated COALESCE lowering.  Keep it on the ordinary CASE path only
/// when every source operand and the complete token stream independently bind
/// the same input ordinal and exact DECIMAL typmod.
fn postgres_explicit_decimal_case_source_matches(
    ast: &ScalarAst,
    source: &ScalarSourceProvenance,
    output: &Column,
    scope: &Scope,
) -> bool {
    let ScalarAst::Call {
        operator,
        op: ScalarOp::Case,
        args,
    } = ast
    else {
        return false;
    };
    let [condition, then_value, else_value] = args.as_slice() else {
        return false;
    };
    let ScalarAst::Call {
        operator: condition_operator,
        op: ScalarOp::IsNotNull,
        args: condition_args,
    } = condition
    else {
        return false;
    };
    let [
        ScalarAst::InputRef {
            index: condition_index,
        },
    ] = condition_args.as_slice()
    else {
        return false;
    };
    let ScalarAst::TypeAnnotation {
        expr: then_cast,
        ty: then_ty,
    } = then_value
    else {
        return false;
    };
    let ScalarAst::Call {
        operator: cast_operator,
        op: ScalarOp::Cast,
        args: cast_args,
    } = then_cast.as_ref()
    else {
        return false;
    };
    let [ScalarAst::InputRef { index: then_index }] = cast_args.as_slice() else {
        return false;
    };
    let SqlType::Decimal {
        precision: Some(precision),
        scale: Some(scale),
    } = output.ty
    else {
        return false;
    };
    let Some(attribute) = scope.attribute(*then_index) else {
        return false;
    };
    let [Some(condition_source), Some(then_source), Some(zero_source)] = source.operands.as_slice()
    else {
        return false;
    };
    let [Some(condition_attribute)] = condition_source.operands.as_slice() else {
        return false;
    };
    let [Some(then_attribute)] = then_source.operands.as_slice() else {
        return false;
    };
    operator.eq_ignore_ascii_case("CASE")
        && condition_operator.eq_ignore_ascii_case("IS NOT NULL")
        && cast_operator.eq_ignore_ascii_case("CAST")
        && condition_index == then_index
        && fixed_decimal_annotation_matches_output(then_ty, output)
        && postgres_int4_to_numeric_zero(else_value)
        && source_has_exact_binding(source)
        && source.clause_ownership.is_none()
        && source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("CASE"))
        && source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("CASE"))
        && condition_source.clause_ownership.is_none()
        && condition_source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("IS_NOT_NULL"))
        && condition_source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("IS NOT NULL"))
        && then_source.clause_ownership.is_none()
        && then_source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("CAST"))
        && then_source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("CAST"))
        && zero_source.clause_ownership.is_none()
        && source_is_direct_identifier(condition_attribute, &attribute.visible_name)
        && source_is_direct_identifier(then_attribute, &attribute.visible_name)
        && source_is_bare_integer_literal(zero_source, "0")
        && exact_source_tokens(condition_source)
            .is_some_and(|tokens| exact_attested_is_not_null(&tokens, &attribute.visible_name))
        && exact_source_tokens(then_source).is_some_and(|tokens| {
            exact_attested_decimal_cast(&tokens, &attribute.visible_name, precision, scale)
        })
        && exact_source_tokens(source).is_some_and(|tokens| {
            exact_attested_explicit_decimal_case(&tokens, &attribute.visible_name, precision, scale)
        })
}

fn postgres_numeric_coalesce_source_parts(
    source: &ScalarSourceProvenance,
) -> Option<(
    &ScalarSourceProvenance,
    &ScalarSourceProvenance,
    &ScalarSourceProvenance,
)> {
    if !source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("OTHER_FUNCTION"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("coalesce"))
        || !source_has_exact_binding(source)
        || source.clause_ownership.is_some()
    {
        return None;
    }
    let [
        Some(condition_source),
        Some(value_source),
        Some(zero_source),
    ] = source.operands.as_slice()
    else {
        return None;
    };
    let [Some(condition_leaf)] = condition_source.operands.as_slice() else {
        return None;
    };
    let [Some(value_leaf)] = value_source.operands.as_slice() else {
        return None;
    };
    if condition_source.clause_ownership.is_some()
        || condition_leaf.clause_ownership.is_some()
        || value_source.clause_ownership.is_some()
        || value_leaf.clause_ownership.is_some()
        || zero_source.clause_ownership.is_some()
        || !source_nodes_identical(condition_source, value_source)
        || !source_nodes_identical(condition_source, condition_leaf)
        || !source_nodes_identical(value_source, value_leaf)
        || !condition_leaf.operands.is_empty()
        || !value_leaf.operands.is_empty()
        || !zero_source.operands.is_empty()
        || !source_is_bare_integer_literal(zero_source, "0")
    {
        return None;
    }
    Some((condition_source, value_source, zero_source))
}

fn postgres_numeric_coalesce_source_text_matches(
    source: &ScalarSourceProvenance,
    attribute_name: &str,
) -> bool {
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    if tokens.len() < 6
        || !token_is_identifier(&tokens[0], "coalesce")
        || !matches!(tokens[1], AttestedSqlToken::LeftParen)
    {
        return false;
    }
    let Some(identifier_end) = direct_column_at(&tokens, 2, attribute_name) else {
        return false;
    };
    matches!(tokens.get(identifier_end), Some(AttestedSqlToken::Comma))
        && matches!(
            tokens.get(identifier_end + 1),
            Some(AttestedSqlToken::Number(value)) if value == "0"
        )
        && matches!(
            tokens.get(identifier_end + 2),
            Some(AttestedSqlToken::RightParen)
        )
        && identifier_end + 3 == tokens.len()
}

fn exact_sum_source_for_aggregate_output(
    input: &RelExpr,
    output_index: usize,
) -> Option<&ScalarSourceProvenance> {
    let input = match input {
        RelExpr::NativeHaving {
            input,
            correlations,
            output,
            ..
        } if correlations.is_empty() && output == input.output() => input.as_ref(),
        input => input,
    };
    let RelExpr::Aggregate {
        group_keys,
        agg_calls,
        output,
        ..
    } = input
    else {
        return None;
    };
    if output.len() != group_keys.len() + agg_calls.len()
        || output.get(output_index)?.ty
            != (SqlType::Decimal {
                precision: None,
                scale: None,
            })
    {
        return None;
    }
    let call = agg_calls.get(output_index.checked_sub(group_keys.len())?)?;
    if !call.function.eq_ignore_ascii_case("SUM")
        || call.distinct
        || call.filter.is_some()
        || call.modifiers.has_semantic_modifiers()
        || call.modifiers.source_distinct != Some(false)
    {
        return None;
    }
    let source = call.modifiers.source.as_ref()?;
    exact_source_unary_function(source, "SUM")?;
    Some(source)
}

pub(super) fn exact_repeated_group_aggregate_definition(
    repeated: &ScalarSourceProvenance,
    aggregate: &ScalarSourceProvenance,
    grouping: &logos_ir::ir::SourceGroupingProvenance,
) -> bool {
    let Some(repeated_tokens) = exact_source_tokens(repeated) else {
        return false;
    };
    let Some(aggregate_tokens) = exact_source_tokens(aggregate) else {
        return false;
    };
    let Some(query_block) = parse_exact_source_span(&grouping.query_block_id) else {
        return false;
    };
    let Some(repeated_span) = repeated
        .node_id
        .as_deref()
        .and_then(parse_exact_source_span)
    else {
        return false;
    };
    let Some(aggregate_span) = aggregate
        .node_id
        .as_deref()
        .and_then(parse_exact_source_span)
    else {
        return false;
    };
    grouping.source_has_having
        && grouping.source_select_node_id == grouping.query_block_id
        && repeated.clause_ownership.is_none()
        && repeated
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("OTHER_FUNCTION"))
        && repeated
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("SUM"))
        && exact_source_unary_function(aggregate, "SUM").is_some()
        && repeated_tokens == aggregate_tokens
        && exact_source_span_contains(query_block, repeated_span)
        && exact_source_span_contains(query_block, aggregate_span)
}

fn postgres_numeric_coalesce_source_binds_input(
    source: &ScalarSourceProvenance,
    condition_source: &ScalarSourceProvenance,
    value_source: &ScalarSourceProvenance,
    zero_source: &ScalarSourceProvenance,
    attribute: &ScopeAttribute,
    input_index: usize,
    input: Option<&RelExpr>,
) -> bool {
    if !exact_source_function_operands_match(
        source,
        "COALESCE",
        &[condition_source, zero_source],
        false,
    ) {
        return false;
    }
    let direct_input = source_is_direct_identifier(condition_source, &attribute.visible_name)
        && source_is_direct_identifier(value_source, &attribute.visible_name)
        && postgres_numeric_coalesce_source_text_matches(source, &attribute.visible_name);
    let aggregate_input = input.is_some_and(|input| {
        let Some(sum_source) = exact_sum_source_for_aggregate_output(input, input_index) else {
            return false;
        };
        if exact_source_nodes_identical(condition_source, sum_source)
            && exact_source_nodes_identical(value_source, sum_source)
        {
            return true;
        }
        let RelExpr::Aggregate {
            group_keys,
            grouping_sets,
            agg_calls,
            ..
        } = input
        else {
            return false;
        };
        let Some(call_index) = input_index.checked_sub(group_keys.len()) else {
            return false;
        };
        let Some(grouping) = agg_calls
            .get(call_index)
            .and_then(|call| call.modifiers.source_grouping.as_ref())
        else {
            return false;
        };
        grouping.group_indexes == *group_keys
            && grouping.grouping_sets == *grouping_sets
            && exact_repeated_group_aggregate_definition(condition_source, sum_source, grouping)
            && exact_repeated_group_aggregate_definition(value_source, sum_source, grouping)
    });
    direct_input || aggregate_input
}

fn rewrite_postgres_decimal_sum_numeric_coalesce_case(
    ast: &ScalarAst,
    source: &ScalarSourceProvenance,
    output: &Column,
    scope: &Scope,
    input: Option<&RelExpr>,
) -> Option<ScalarAst> {
    let ScalarAst::Call {
        operator,
        op: ScalarOp::Case,
        args,
    } = ast
    else {
        return None;
    };
    let [condition, then_value, else_value] = args.as_slice() else {
        return None;
    };
    let ScalarAst::Call {
        operator: condition_operator,
        op: ScalarOp::IsNotNull,
        args: condition_args,
    } = condition
    else {
        return None;
    };
    let [
        ScalarAst::InputRef {
            index: condition_index,
        },
    ] = condition_args.as_slice()
    else {
        return None;
    };
    // The IR boundary may already have removed Calcite's independently
    // disproved DECIMAL carrier. Accept either representation, but close the
    // direct-NUMERIC form again against this complete CASE, source node, and
    // typed scope instead of trusting the earlier repair.
    let then_index = match then_value {
        ScalarAst::InputRef { index } => *index,
        ScalarAst::TypeAnnotation {
            expr: then_cast,
            ty: then_ty,
        } if fixed_decimal_annotation_matches_output(then_ty, output) => {
            let ScalarAst::Call {
                operator: cast_operator,
                op: ScalarOp::Cast,
                args: then_args,
            } = then_cast.as_ref()
            else {
                return None;
            };
            if !cast_operator.eq_ignore_ascii_case("CAST") {
                return None;
            }
            let [ScalarAst::InputRef { index }] = then_args.as_slice() else {
                return None;
            };
            *index
        }
        _ => return None,
    };
    let attribute = scope.attribute(then_index)?;
    let (condition_source, value_source, zero_source) =
        postgres_numeric_coalesce_source_parts(source)?;
    if !operator.eq_ignore_ascii_case("CASE")
        || !condition_operator.eq_ignore_ascii_case("IS NOT NULL")
        || *condition_index != then_index
        || !postgres_int4_to_numeric_zero(else_value)
        || attribute.formal_ty != FormalAttributeType::Numeric
        || !postgres_numeric_coalesce_source_binds_input(
            source,
            condition_source,
            value_source,
            zero_source,
            &attribute,
            then_index,
            input,
        )
    {
        return None;
    }
    Some(ScalarAst::Call {
        operator: operator.clone(),
        op: ScalarOp::Case,
        args: vec![
            condition.clone(),
            ScalarAst::InputRef { index: then_index },
            else_value.clone(),
        ],
    })
}

fn rewrite_postgres_numeric_input_ref(
    ast: &ScalarAst,
    source: &ScalarSourceProvenance,
    scope: &Scope,
) -> Option<ScalarAst> {
    let ScalarAst::InputRef { index } = ast else {
        return None;
    };
    let attribute = scope.attribute(*index)?;
    if attribute.formal_ty != FormalAttributeType::Numeric
        || source.clause_ownership.is_some()
        || !source.operands.is_empty()
        || !source_is_direct_identifier(source, &attribute.visible_name)
    {
        return None;
    }
    Some(ast.clone())
}

fn rewrite_postgres_decimal_sum_numeric_coalesce_node(
    ast: &ScalarAst,
    source: &ScalarSourceProvenance,
    output: &Column,
    scope: &Scope,
    input: Option<&RelExpr>,
) -> Option<(ScalarAst, bool)> {
    if let Some(rewritten) =
        rewrite_postgres_decimal_sum_numeric_coalesce_case(ast, source, output, scope, input)
    {
        return Some((rewritten, true));
    }
    if let Some(rewritten) = rewrite_postgres_numeric_input_ref(ast, source, scope) {
        return Some((rewritten, false));
    }
    let ScalarAst::Call {
        operator,
        op: ScalarOp::Minus,
        args,
    } = ast
    else {
        return None;
    };
    if !operator.eq_ignore_ascii_case("-")
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("MINUS"))
        || source
            .operator
            .as_deref()
            .is_none_or(|source_operator| source_operator != "-")
        || source.clause_ownership.is_some()
        || !exact_source_binary_operands_match(source, AttestedSqlToken::Minus)
    {
        return None;
    }
    let [left, right] = args.as_slice() else {
        return None;
    };
    let [Some(left_source), Some(right_source)] = source.operands.as_slice() else {
        return None;
    };
    let (left, left_changed) = rewrite_postgres_decimal_sum_numeric_coalesce_node(
        left,
        left_source,
        output,
        scope,
        input,
    )?;
    let (right, right_changed) = rewrite_postgres_decimal_sum_numeric_coalesce_node(
        right,
        right_source,
        output,
        scope,
        input,
    )?;
    Some((
        ScalarAst::Call {
            operator: operator.clone(),
            op: ScalarOp::Minus,
            args: vec![left, right],
        },
        left_changed || right_changed,
    ))
}

pub(super) fn rel_structural_max_rows(rel: &RelExpr) -> Option<u64> {
    match rel {
        RelExpr::Values { rows, .. } => u64::try_from(rows.len()).ok(),
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::NativeHaving { input, .. }
        | RelExpr::Distinct { input, .. }
        | RelExpr::Sort { input, .. } => rel_structural_max_rows(input),
        RelExpr::Aggregate {
            group_keys,
            grouping_sets,
            ..
        } if group_keys.is_empty()
            && matches!(grouping_sets.as_slice(), [set] if set.is_empty()) =>
        {
            Some(1)
        }
        RelExpr::TableScan { .. }
        | RelExpr::Join { .. }
        | RelExpr::Aggregate { .. }
        | RelExpr::Set { .. } => None,
    }
}

fn attested_numeric_exp_avg_int32(
    exp: &ScalarExpr,
    avg: &AggregateCall,
    aggregate_input: &[Column],
) -> bool {
    if !avg.function.eq_ignore_ascii_case("AVG")
        || avg.distinct
        || avg.filter.is_some()
        || avg.modifiers.has_semantic_modifiers()
        || avg.modifiers.source_distinct != Some(false)
    {
        return false;
    }
    let [argument] = avg.args.as_slice() else {
        return false;
    };
    let Some(argument_index) = direct_input_ref(&argument.parsed) else {
        return false;
    };
    let Some(argument_column) = aggregate_input.get(argument_index) else {
        return false;
    };
    if argument_column.ty != SqlType::Integer {
        return false;
    }
    let Some(avg_source) = avg.modifiers.source.as_ref() else {
        return false;
    };
    let Some(avg_argument_source) = exact_source_unary_function(avg_source, "AVG") else {
        return false;
    };
    if !exact_source_direct_identifier_chain(avg_argument_source, &argument_column.name) {
        return false;
    }
    let Some(exp_source) = exp.source.as_ref() else {
        return false;
    };
    let Some(exp_avg_source) = exact_source_unary_function(exp_source, "EXP") else {
        return false;
    };
    exact_source_nodes_identical(exp_avg_source, avg_source)
        && exact_source_direct_identifier_chain(avg_argument_source, &argument_column.name)
}

fn calcite_stale_numeric_copy_type(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Int32
            | FormalAttributeType::Int64
            | FormalAttributeType::Float
            | FormalAttributeType::Double
            | FormalAttributeType::Decimal { .. }
    )
}

fn integral_ratio_aggregate_input(input: &RelExpr) -> Option<(&RelExpr, Vec<usize>)> {
    if matches!(input, RelExpr::Aggregate { .. }) {
        return Some((input, (0..input.output().len()).collect()));
    }
    let RelExpr::Project {
        input: aggregate,
        exprs,
        correlations,
        output,
    } = input
    else {
        return None;
    };
    let RelExpr::Aggregate {
        group_keys,
        agg_calls,
        output: aggregate_output,
        ..
    } = aggregate.as_ref()
    else {
        return None;
    };
    if !correlations.is_empty()
        || exprs.len() != output.len()
        || output.len() != aggregate_output.len()
        || aggregate_output.len() != group_keys.len() + agg_calls.len()
    {
        return None;
    }
    let mapping = exprs
        .iter()
        .map(|expr| direct_input_ref(&expr.parsed))
        .collect::<Option<Vec<_>>>()?;
    let mut permutation = mapping.clone();
    permutation.sort_unstable();
    if permutation != (0..aggregate_output.len()).collect::<Vec<_>>() {
        return None;
    }
    for ((expr, projected), aggregate_index) in exprs.iter().zip(output).zip(&mapping) {
        let aggregate_column = aggregate_output.get(*aggregate_index)?;
        if projected.name != aggregate_column.name
            || projected.ty != aggregate_column.ty
            || projected.nullable != aggregate_column.nullable
        {
            return None;
        }
        let source = expr.source.as_ref()?;
        let source_matches = if *aggregate_index < group_keys.len() {
            source.clause_ownership.is_none()
                && source_is_direct_identifier(source, &aggregate_column.name)
        } else {
            let call = agg_calls.get(*aggregate_index - group_keys.len())?;
            call.modifiers
                .source
                .as_ref()
                .is_some_and(|aggregate_source| {
                    exact_source_nodes_identical(source, aggregate_source)
                })
        };
        if !source_matches || direct_input_ref(&expr.parsed) != Some(*aggregate_index) {
            return None;
        }
    }
    Some((aggregate.as_ref(), mapping))
}

fn remap_scalar_input_refs(ast: &ScalarAst, mapping: &[usize]) -> Option<ScalarAst> {
    match ast {
        ScalarAst::InputRef { index } => Some(ScalarAst::InputRef {
            index: *mapping.get(*index)?,
        }),
        ScalarAst::Call { operator, op, args } => Some(ScalarAst::Call {
            operator: operator.clone(),
            op: op.clone(),
            args: args
                .iter()
                .map(|arg| remap_scalar_input_refs(arg, mapping))
                .collect::<Option<Vec<_>>>()?,
        }),
        ScalarAst::TypeAnnotation { expr, ty } => Some(ScalarAst::TypeAnnotation {
            expr: Box::new(remap_scalar_input_refs(expr, mapping)?),
            ty: ty.clone(),
        }),
        ScalarAst::Literal { .. } | ScalarAst::Flag { .. } => Some(ast.clone()),
        ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Window { .. }
        | ScalarAst::RelSubquery { .. } => None,
    }
}

pub(super) fn exact_repeated_group_identifier_lineage(
    aggregate_source: &ScalarSourceProvenance,
    input_source: &ScalarSourceProvenance,
    grouping: &logos_ir::ir::SourceGroupingProvenance,
) -> bool {
    let Some(aggregate_tokens) = exact_source_tokens(aggregate_source) else {
        return false;
    };
    let Some(input_tokens) = exact_source_tokens(input_source) else {
        return false;
    };
    let [
        AttestedSqlToken::Identifier(_),
        AttestedSqlToken::Dot,
        AttestedSqlToken::Identifier(_),
    ] = aggregate_tokens.as_slice()
    else {
        return false;
    };
    let Some(query_block) = parse_exact_source_span(&grouping.query_block_id) else {
        return false;
    };
    let Some(aggregate_span) = aggregate_source
        .node_id
        .as_deref()
        .and_then(parse_exact_source_span)
    else {
        return false;
    };
    let Some(input_span) = input_source
        .node_id
        .as_deref()
        .and_then(parse_exact_source_span)
    else {
        return false;
    };
    grouping.source_select_node_id == grouping.query_block_id
        && aggregate_source.clause_ownership.is_none()
        && input_source.clause_ownership.is_none()
        && source_is_any_direct_identifier(aggregate_source)
        && source_is_any_direct_identifier(input_source)
        && aggregate_tokens == input_tokens
        && exact_source_span_contains(query_block, aggregate_span)
        && exact_source_span_contains(query_block, input_span)
}

fn integral_stddev_avg_ratio_body_plan(rel: &RelExpr) -> Option<IntegralStddevAvgRatioPlan> {
    let RelExpr::Project {
        input: aggregate_filter,
        exprs,
        correlations: project_correlations,
        output: project_output,
    } = rel
    else {
        return None;
    };
    let RelExpr::Filter {
        input: aggregate,
        predicate,
        correlations: filter_correlations,
        output: filter_output,
    } = aggregate_filter.as_ref()
    else {
        return None;
    };
    let filter_input = aggregate.as_ref();
    let (aggregate, input_index_map) = integral_ratio_aggregate_input(filter_input)?;
    let RelExpr::Aggregate {
        input,
        group_keys,
        grouping_sets,
        agg_calls,
        output: aggregate_output,
    } = aggregate
    else {
        return None;
    };
    if !project_correlations.is_empty()
        || !filter_correlations.is_empty()
        || exprs.len() != project_output.len()
        || filter_output != filter_input.output()
        || aggregate_output.len() != group_keys.len() + agg_calls.len()
        || !matches!(grouping_sets.as_slice(), [set] if set == group_keys)
        || rel_expr_may_raise_runtime(input)
    {
        return None;
    }

    let ratio_projects = exprs
        .iter()
        .enumerate()
        .filter_map(|(index, expr)| {
            integral_stddev_avg_ratio_case_refs(&expr.parsed, true).and_then(|(stddev, avg)| {
                Some((
                    index,
                    (*input_index_map.get(stddev)?, *input_index_map.get(avg)?),
                ))
            })
        })
        .collect::<Vec<_>>();
    let [(ratio_project_index, (stddev_output_index, avg_output_index))] =
        ratio_projects.as_slice()
    else {
        return None;
    };
    let (filter_stddev_index, filter_avg_index, _) =
        integral_stddev_avg_ratio_filter_parts(&predicate.parsed)?;
    if *input_index_map.get(filter_stddev_index)? != *stddev_output_index
        || *input_index_map.get(filter_avg_index)? != *avg_output_index
        || stddev_output_index == avg_output_index
    {
        return None;
    }

    // Apart from the one guarded ratio expression, this lowering is an exact
    // positional carrier for every Aggregate output. Accept any permutation,
    // but neither omission, duplication, nor an additional computed item.
    let mut passthrough = exprs
        .iter()
        .enumerate()
        .filter(|(index, _)| index != ratio_project_index)
        .map(|(_, expr)| {
            direct_input_ref(&expr.parsed).and_then(|index| input_index_map.get(index).copied())
        })
        .collect::<Option<Vec<_>>>()?;
    passthrough.sort_unstable();
    if passthrough != (0..aggregate_output.len()).collect::<Vec<_>>() {
        return None;
    }

    let stddev_call_index = stddev_output_index.checked_sub(group_keys.len())?;
    let avg_call_index = avg_output_index.checked_sub(group_keys.len())?;
    let stddev = agg_calls.get(stddev_call_index)?;
    let avg = agg_calls.get(avg_call_index)?;
    let exact_integral_call = |call: &AggregateCall, function: &str| -> Option<usize> {
        let [argument] = call.args.as_slice() else {
            return None;
        };
        let argument_index = direct_input_ref(&argument.parsed)?;
        let statistic_input = input.output().get(argument_index)?;
        (call.function.eq_ignore_ascii_case(function)
            && !call.distinct
            && !call.modifiers.has_semantic_modifiers()
            && call.modifiers.source_distinct == Some(false)
            && call.filter.is_none()
            && call.modifiers.source.as_ref().is_some_and(|source| {
                exact_source_unary_function(source, function).is_some_and(|argument| {
                    exact_source_direct_identifier_chain(argument, &statistic_input.name)
                        || aggregate_input_source(input, argument_index).is_some_and(
                            |input_source| {
                                source_is_any_direct_identifier(input_source)
                                    && (source_nodes_identical(argument, input_source)
                                        || call.modifiers.source_grouping.as_ref().is_some_and(
                                            |grouping| {
                                                exact_repeated_group_identifier_lineage(
                                                    argument,
                                                    input_source,
                                                    grouping,
                                                )
                                            },
                                        ))
                            },
                        )
                })
            }))
        .then_some(argument_index)
    };
    let stddev_argument = exact_integral_call(stddev, "STDDEV_SAMP")?;
    let avg_argument = exact_integral_call(avg, "AVG")?;
    if stddev_argument != avg_argument
        || input.output().get(stddev_argument)?.ty != SqlType::Integer
    {
        return None;
    }
    let stddev_output = aggregate_output.get(*stddev_output_index)?;
    let avg_output = aggregate_output.get(*avg_output_index)?;
    let stddev_source = stddev.modifiers.source.as_ref();
    let avg_source = avg.modifiers.source.as_ref();
    if !exact_integral_ratio_source_case(
        exprs[*ratio_project_index].source.as_ref(),
        &stddev_output.name,
        &avg_output.name,
        stddev_source,
        avg_source,
        true,
    ) || !exact_integral_ratio_source_filter(
        predicate.source.as_ref(),
        &stddev_output.name,
        &avg_output.name,
        stddev_source,
        avg_source,
    ) {
        return None;
    }
    Some(IntegralStddevAvgRatioPlan {
        stddev_output_index: *stddev_output_index,
        avg_output_index: *avg_output_index,
        ratio_project_index: *ratio_project_index,
        input_index_map,
    })
}

fn exact_integral_ratio_source_literal(
    source: &ScalarSourceProvenance,
    expected: AttestedSqlToken,
) -> bool {
    source_has_exact_binding(source)
        && source.clause_ownership.is_none()
        && source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("LITERAL"))
        && source.operator.is_none()
        && source.operands.is_empty()
        && source
            .text
            .as_deref()
            .and_then(tokenize_attested_sql)
            .is_some_and(|tokens| tokens.as_slice() == [expected])
}

fn exact_integral_ratio_condition_tokens(source: &ScalarSourceProvenance, avg_name: &str) -> bool {
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    let mut cursor = 0;
    consume_attested_direct_column(&tokens, &mut cursor, avg_name)
        && consume_attested_token(
            &tokens,
            &mut cursor,
            &AttestedSqlToken::Compare("=".to_owned()),
        )
        && consume_attested_token(
            &tokens,
            &mut cursor,
            &AttestedSqlToken::Number("0".to_owned()),
        )
        && cursor == tokens.len()
}

fn exact_integral_ratio_division_tokens(
    source: &ScalarSourceProvenance,
    stddev_name: &str,
    avg_name: &str,
) -> bool {
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    let mut cursor = 0;
    consume_attested_direct_column(&tokens, &mut cursor, stddev_name)
        && consume_attested_token(&tokens, &mut cursor, &AttestedSqlToken::Divide)
        && consume_attested_direct_column(&tokens, &mut cursor, avg_name)
        && cursor == tokens.len()
}

fn exact_integral_ratio_case_tokens(
    source: &ScalarSourceProvenance,
    stddev_name: &str,
    avg_name: &str,
    null_when_zero: bool,
    searched_case: bool,
) -> bool {
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    let mut cursor = 0;
    if !consume_attested_identifier(&tokens, &mut cursor, "case") {
        return false;
    }
    if searched_case {
        if !consume_attested_identifier(&tokens, &mut cursor, "when")
            || !consume_attested_direct_column(&tokens, &mut cursor, avg_name)
            || !consume_attested_token(
                &tokens,
                &mut cursor,
                &AttestedSqlToken::Compare("=".to_owned()),
            )
        {
            return false;
        }
    } else if !consume_attested_direct_column(&tokens, &mut cursor, avg_name)
        || !consume_attested_identifier(&tokens, &mut cursor, "when")
    {
        return false;
    }
    consume_attested_token(
        &tokens,
        &mut cursor,
        &AttestedSqlToken::Number("0".to_owned()),
    ) && consume_attested_identifier(&tokens, &mut cursor, "then")
        && consume_attested_token(
            &tokens,
            &mut cursor,
            &if null_when_zero {
                AttestedSqlToken::Identifier("null".to_owned())
            } else {
                AttestedSqlToken::Number("0".to_owned())
            },
        )
        && consume_attested_identifier(&tokens, &mut cursor, "else")
        && consume_attested_direct_column(&tokens, &mut cursor, stddev_name)
        && consume_attested_token(&tokens, &mut cursor, &AttestedSqlToken::Divide)
        && consume_attested_direct_column(&tokens, &mut cursor, avg_name)
        && consume_attested_identifier(&tokens, &mut cursor, "end")
        && cursor == tokens.len()
}

fn exact_integral_ratio_source_case(
    source: Option<&ScalarSourceProvenance>,
    stddev_name: &str,
    avg_name: &str,
    stddev_definition: Option<&ScalarSourceProvenance>,
    avg_definition: Option<&ScalarSourceProvenance>,
    null_when_zero: bool,
) -> bool {
    let Some(source) = source else {
        return false;
    };
    if !source_has_exact_binding(source)
        || source.clause_ownership.is_some()
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("CASE"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("CASE"))
    {
        return false;
    }
    let [Some(condition), Some(when_zero), Some(otherwise)] = source.operands.as_slice() else {
        return false;
    };
    let [Some(condition_avg), Some(condition_zero)] = condition.operands.as_slice() else {
        return false;
    };
    let [Some(ratio_stddev), Some(ratio_avg)] = otherwise.operands.as_slice() else {
        return false;
    };
    let simple_case = source.node_id == condition.node_id
        && source.text == condition.text
        && condition
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("EQUALS"))
        && condition.operator.as_deref() == Some("=");
    let zero_result = if null_when_zero {
        exact_integral_ratio_source_literal(
            when_zero,
            AttestedSqlToken::Identifier("null".to_owned()),
        )
    } else {
        exact_integral_ratio_source_literal(when_zero, AttestedSqlToken::Number("0".to_owned()))
    };
    let searched_case = !simple_case
        && source_has_exact_binding(condition)
        && condition.clause_ownership.is_none()
        && condition
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("EQUALS"))
        && condition.operator.as_deref() == Some("=")
        && exact_integral_ratio_condition_tokens(condition, avg_name);
    if !(simple_case || searched_case)
        || !exact_integral_ratio_statistic_reference(condition_avg, avg_name, avg_definition)
        || !exact_integral_ratio_source_literal(
            condition_zero,
            AttestedSqlToken::Number("0".to_owned()),
        )
        || !zero_result
        || !source_has_exact_binding(otherwise)
        || !otherwise
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("DIVIDE"))
        || otherwise.operator.as_deref() != Some("/")
        || otherwise.clause_ownership.is_some()
        || !exact_integral_ratio_statistic_reference(ratio_stddev, stddev_name, stddev_definition)
        || !exact_integral_ratio_statistic_reference(ratio_avg, avg_name, avg_definition)
        || !exact_integral_ratio_division_tokens(otherwise, stddev_name, avg_name)
    {
        return false;
    }
    exact_integral_ratio_case_tokens(source, stddev_name, avg_name, null_when_zero, searched_case)
}

fn exact_integral_ratio_source_filter(
    source: Option<&ScalarSourceProvenance>,
    stddev_name: &str,
    avg_name: &str,
    stddev_definition: Option<&ScalarSourceProvenance>,
    avg_definition: Option<&ScalarSourceProvenance>,
) -> bool {
    let Some(source) = source else {
        return false;
    };
    let [Some(case), Some(threshold)] = source.operands.as_slice() else {
        return false;
    };
    if !source_has_exact_binding(source)
        || source.clause_ownership.is_some()
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("GREATER_THAN"))
        || source.operator.as_deref() != Some(">")
        || !exact_integral_ratio_source_case(
            Some(case),
            stddev_name,
            avg_name,
            stddev_definition,
            avg_definition,
            false,
        )
        || !source_has_exact_binding(threshold)
        || threshold.clause_ownership.is_some()
    {
        return false;
    }
    let (Some(case_tokens), Some(threshold_tokens)) =
        (exact_source_tokens(case), exact_source_tokens(threshold))
    else {
        return false;
    };
    let mut expected = case_tokens;
    expected.push(AttestedSqlToken::Compare(">".to_owned()));
    expected.extend(threshold_tokens);
    exact_source_tokens(source).is_some_and(|tokens| tokens == expected)
}

/// A projected alias use is represented either by its direct source
/// identifier (the ordinary derived-table boundary) or by the exact aggregate
/// definition selected by the converter's independently validated projected
/// expansion. Accept the latter only by byte/span identity with the same
/// already source-validated Aggregate call; equal rendered SQL is not enough.
fn exact_integral_ratio_statistic_reference(
    source: &ScalarSourceProvenance,
    public_name: &str,
    definition: Option<&ScalarSourceProvenance>,
) -> bool {
    exact_source_direct_identifier_chain(source, public_name)
        || definition.is_some_and(|definition| exact_source_nodes_identical(source, definition))
}

/// Remove only fixed-NUMERIC coercions that are disproved by two independent
/// facts: the lowered input already has PostgreSQL's unconstrained NUMERIC
/// type, and the source parser binds the same scalar position to a direct
/// identifier rather than a CAST. This is a general logical type-recovery
/// rule and is independent of the containing query shape.
pub(super) fn rewrite_source_disproved_numeric_coercions(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
    scope: &Scope,
) -> ScalarAst {
    if let ScalarAst::TypeAnnotation { expr, ty } = ast
        && numeric_type_annotation(ty)
        && let ScalarAst::Call {
            op: ScalarOp::Cast,
            args,
            ..
        } = expr.as_ref()
        && let [argument] = args.as_slice()
        && let Some(index) = direct_input_ref(argument)
        && let Some(attribute) = scope.attribute(index)
        && attribute.formal_ty == FormalAttributeType::Numeric
        && source.is_some_and(|source| {
            source.clause_ownership.is_none()
                && source_is_direct_identifier_chain(source, &attribute.visible_name)
        })
    {
        return ScalarAst::InputRef { index };
    }

    match ast {
        ScalarAst::Call { operator, op, args } => {
            let source_operands = source
                .filter(|source| source.operands.len() == args.len())
                .map(|source| source.operands.as_slice());
            let mut rewritten_args = args
                .iter()
                .enumerate()
                .map(|(index, argument)| {
                    rewrite_source_disproved_numeric_coercions(
                        argument,
                        source_operands
                            .and_then(|operands| operands.get(index))
                            .and_then(Option::as_ref),
                        scope,
                    )
                })
                .collect::<Vec<_>>();
            if op.is_ordinary_comparison() && rewritten_args.len() == 2 && source_operands.is_some()
            {
                for index in 0..2 {
                    let other = 1 - index;
                    let Some(input_index) = floating_cast_direct_input(&rewritten_args[index])
                    else {
                        continue;
                    };
                    let Some(attribute) = scope.attribute(input_index) else {
                        continue;
                    };
                    let source_binds_direct_input = source_operands
                        .and_then(|operands| operands.get(index))
                        .and_then(Option::as_ref)
                        .is_some_and(|source| {
                            source.clause_ownership.is_none()
                                && source_is_direct_identifier_chain(
                                    source,
                                    &attribute.visible_name,
                                )
                        });
                    if !matches!(
                        attribute.formal_ty,
                        FormalAttributeType::Int32 | FormalAttributeType::Int64
                    ) || !source_binds_direct_input
                        || numeric_expression_kind(&rewritten_args[other], scope)
                            != NumericExpressionKind::Numeric
                    {
                        continue;
                    }
                    let ScalarAst::TypeAnnotation { expr, .. } = &rewritten_args[index] else {
                        unreachable!("floating_cast_direct_input requires a type annotation")
                    };
                    rewritten_args[index] = ScalarAst::TypeAnnotation {
                        expr: expr.clone(),
                        ty: "NUMERIC".to_owned(),
                    };
                }
            }
            ScalarAst::Call {
                operator: operator.clone(),
                op: op.clone(),
                args: rewritten_args,
            }
        }
        ScalarAst::TypeAnnotation { expr, ty } => ScalarAst::TypeAnnotation {
            expr: Box::new(rewrite_source_disproved_numeric_coercions(
                expr, source, scope,
            )),
            ty: ty.clone(),
        },
        _ => ast.clone(),
    }
}

fn numeric_type_annotation(ty: &str) -> bool {
    matches!(
        classify_type_annotation(ty),
        Some(SqlTypeAnnotation::Decimal { .. })
    )
}

fn floating_type_annotation(ty: &str) -> bool {
    let Some(annotation) = classify_type_annotation(ty) else {
        return false;
    };
    let compact = ty
        .chars()
        .filter(|ch| !ch.is_ascii_whitespace())
        .flat_map(char::to_uppercase)
        .collect::<String>();
    match annotation {
        SqlTypeAnnotation::Real => compact == "REAL",
        SqlTypeAnnotation::Float { .. } => compact == "FLOAT" || compact.starts_with("FLOAT("),
        SqlTypeAnnotation::Double => matches!(compact.as_str(), "DOUBLE" | "DOUBLEPRECISION"),
        _ => false,
    }
}

#[cfg(test)]
mod type_annotation_classification_tests {
    use super::*;

    #[test]
    fn numeric_and_floating_annotations_are_structural_and_closed() {
        for ty in ["NUMERIC", "NUMERIC(10)", "NUMERIC(10,2)", "DECIMAL(8,0)"] {
            assert!(numeric_type_annotation(ty), "rejected valid {ty}");
        }
        for ty in ["REAL", "FLOAT", "FLOAT(24)", "DOUBLE", "DOUBLE PRECISION"] {
            assert!(floating_type_annotation(ty), "rejected valid {ty}");
        }
        for malformed in [
            "NUMERIC(+10,2)",
            "NUMERIC(10,-2)",
            "NUMERIC(10,2) trailing",
            "NUMERIC(10,,2)",
            "FLOAT(+24)",
            "FLOAT(54)",
            "DOUBLE(2)",
            "DOUBLE PRECISION trailing",
        ] {
            assert!(
                !numeric_type_annotation(malformed) && !floating_type_annotation(malformed),
                "accepted malformed annotation {malformed}"
            );
        }
    }
}

fn floating_cast_direct_input(ast: &ScalarAst) -> Option<usize> {
    let ScalarAst::TypeAnnotation { expr, ty } = ast else {
        return None;
    };
    let ScalarAst::Call {
        op: ScalarOp::Cast,
        args,
        ..
    } = expr.as_ref()
    else {
        return None;
    };
    floating_type_annotation(ty)
        .then(|| {
            matches!(args.as_slice(), [argument]
            if direct_input_ref(argument).is_some())
        })
        .filter(|matched| *matched)
        .and_then(|_| direct_input_ref(&args[0]))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumericExpressionKind {
    Numeric,
    Integral,
    Other,
}

fn numeric_expression_kind(ast: &ScalarAst, scope: &Scope) -> NumericExpressionKind {
    match ast {
        ScalarAst::InputRef { index } => match scope.attribute(*index).map(|item| item.formal_ty) {
            Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. }) => {
                NumericExpressionKind::Numeric
            }
            Some(
                FormalAttributeType::Z | FormalAttributeType::Int32 | FormalAttributeType::Int64,
            ) => NumericExpressionKind::Integral,
            _ => NumericExpressionKind::Other,
        },
        ScalarAst::Literal { raw } => {
            if raw.trim().parse::<i128>().is_ok() {
                NumericExpressionKind::Integral
            } else if super::emit::parse_decimal_literal(raw).is_some() {
                NumericExpressionKind::Numeric
            } else {
                NumericExpressionKind::Other
            }
        }
        ScalarAst::TypeAnnotation { expr, ty } => {
            if numeric_type_annotation(ty) {
                NumericExpressionKind::Numeric
            } else if matches!(
                ty.trim().to_ascii_uppercase().as_str(),
                "SMALLINT" | "INTEGER" | "BIGINT"
            ) {
                NumericExpressionKind::Integral
            } else {
                numeric_expression_kind(expr, scope)
            }
        }
        ScalarAst::Call { op, args, .. }
            if matches!(
                op,
                ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
            ) && !args.is_empty() =>
        {
            let kinds = args
                .iter()
                .map(|arg| numeric_expression_kind(arg, scope))
                .collect::<Vec<_>>();
            if kinds.contains(&NumericExpressionKind::Other) {
                NumericExpressionKind::Other
            } else if kinds.contains(&NumericExpressionKind::Numeric) {
                NumericExpressionKind::Numeric
            } else {
                NumericExpressionKind::Integral
            }
        }
        _ => NumericExpressionKind::Other,
    }
}

fn integral_stddev_avg_ratio_filter_parts(ast: &ScalarAst) -> Option<(usize, usize, &ScalarAst)> {
    let ScalarAst::Call {
        op: ScalarOp::Gt,
        args,
        ..
    } = ast
    else {
        return None;
    };
    let [guarded_ratio, threshold] = args.as_slice() else {
        return None;
    };
    let (stddev, avg) = integral_stddev_avg_ratio_case_refs(guarded_ratio, false)?;
    Some((stddev, avg, threshold))
}

fn integral_stddev_avg_ratio_case_refs(
    ast: &ScalarAst,
    null_when_zero: bool,
) -> Option<(usize, usize)> {
    let ScalarAst::Call {
        op: ScalarOp::Case,
        args,
        ..
    } = ast
    else {
        return None;
    };
    let [condition, when_zero, otherwise] = args.as_slice() else {
        return None;
    };
    let ScalarAst::Call {
        op: ScalarOp::Eq,
        args: equality,
        ..
    } = condition
    else {
        return None;
    };
    let [mean, zero] = equality.as_slice() else {
        return None;
    };
    let ScalarAst::Call {
        op: ScalarOp::Divide,
        args: division,
        ..
    } = otherwise
    else {
        return None;
    };
    let [stddev, divisor] = division.as_slice() else {
        return None;
    };
    let stddev = direct_input_ref(stddev)?;
    let divisor = direct_input_ref(divisor)?;
    (direct_input_ref(mean) == Some(divisor)
        && exact_integral_literal(zero, 0)
        && if null_when_zero {
            null_literal(when_zero)
        } else {
            exact_integral_literal(when_zero, 0)
        })
    .then_some((stddev, divisor))
}

fn rewrite_integral_stddev_avg_ratio_case(
    ast: &ScalarAst,
    expected_stddev: usize,
    expected_avg: usize,
    ratio_index: usize,
) -> Option<ScalarAst> {
    let ScalarAst::Call { operator, op, args } = ast else {
        return None;
    };
    if integral_stddev_avg_ratio_case_refs(ast, null_literal(args.get(1)?))
        != Some((expected_stddev, expected_avg))
    {
        return None;
    }
    let mut rewritten = args.clone();
    rewritten[2] = ScalarAst::InputRef { index: ratio_index };
    Some(ScalarAst::Call {
        operator: operator.clone(),
        op: op.clone(),
        args: rewritten,
    })
}

fn rewrite_integral_stddev_avg_ratio_filter(
    ast: &ScalarAst,
    expected_stddev: usize,
    expected_avg: usize,
    ratio_index: usize,
) -> Option<ScalarAst> {
    let ScalarAst::Call { operator, op, args } = ast else {
        return None;
    };
    let (stddev, avg, _) = integral_stddev_avg_ratio_filter_parts(ast)?;
    if (stddev, avg) != (expected_stddev, expected_avg) {
        return None;
    }
    let mut rewritten = args.clone();
    rewritten[0] = rewrite_integral_stddev_avg_ratio_case(
        &args[0],
        expected_stddev,
        expected_avg,
        ratio_index,
    )?;
    Some(ScalarAst::Call {
        operator: operator.clone(),
        op: op.clone(),
        args: rewritten,
    })
}

fn exact_integral_literal(ast: &ScalarAst, expected: i128) -> bool {
    match ast {
        ScalarAst::Literal { raw } => raw.trim().parse::<i128>() == Ok(expected),
        ScalarAst::TypeAnnotation { expr, .. } => exact_integral_literal(expr, expected),
        _ => false,
    }
}

fn null_literal(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::Literal { raw } => raw.trim().eq_ignore_ascii_case("null"),
        ScalarAst::TypeAnnotation { expr, .. } => null_literal(expr),
        _ => false,
    }
}

fn rel_requires_explicit_query_expr(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::TableScan { .. } => false,
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .any(|expr| scalar_ast_requires_explicit_query_expr(&expr.parsed)),
        RelExpr::Project { input, exprs, .. } => {
            rel_requires_explicit_query_expr(input)
                || project_has_top_level_numeric_exp(exprs)
                || exprs
                    .iter()
                    .any(|expr| scalar_ast_requires_explicit_query_expr(&expr.parsed))
        }
        RelExpr::NativeHaving { .. } => true,
        RelExpr::Filter {
            input, predicate, ..
        } => {
            rel_requires_explicit_query_expr(input)
                || scalar_ast_requires_explicit_query_expr(&predicate.parsed)
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            rel_requires_explicit_query_expr(left)
                || rel_requires_explicit_query_expr(right)
                || scalar_ast_requires_explicit_query_expr(&condition.parsed)
        }
        RelExpr::Aggregate {
            input,
            group_keys,
            grouping_sets,
            agg_calls,
            ..
        } => {
            group_keys.is_empty()
                // The ordinary grouped branch has
                // no group for an empty input. The exact QExpr_Group semantics
                // supplies PostgreSQL's mandatory row for the `()` branch.
                || grouping_sets.iter().any(Vec::is_empty)
                || agg_calls
                    .iter()
                    .any(|call| special_aggregate_kind(&call.function).is_some())
                || rel_requires_explicit_query_expr(input)
                || agg_calls.iter().any(|call| {
                    call.args
                        .iter()
                        .any(|expr| scalar_ast_requires_explicit_query_expr(&expr.parsed))
                        || call.filter.as_ref().is_some_and(|expr| {
                            scalar_ast_requires_explicit_query_expr(&expr.parsed)
                        })
                })
        }
        // Source-attested SELECT DISTINCT must reach the query-expression
        // lowering branch even when its child is otherwise representable by
        // the legacy relational subset. Its explicit QExpr_Distinct identity
        // is semantically observable under capped EXISTS demand.
        RelExpr::Distinct { .. } => true,
        RelExpr::Set { inputs, .. } => inputs.iter().any(rel_requires_explicit_query_expr),
        RelExpr::Sort {
            input,
            collation,
            fetch,
            offset,
            ..
        } => {
            let identity = collation.is_empty() && fetch.is_none() && offset.is_none();
            rel_requires_explicit_query_expr(input) || !identity
        }
    }
}

fn scalar_ast_requires_explicit_query_expr(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::RelSubquery { rel } => rel_requires_explicit_query_expr(rel),
        ScalarAst::Call {
            op: ScalarOp::Exists,
            args,
            ..
        } if matches!(args.as_slice(), [ScalarAst::RelSubquery { rel }]
            if rel_expr_may_raise_runtime(rel)) =>
        {
            true
        }
        ScalarAst::Call {
            op: logos_ir::ir::ScalarOp::In,
            args,
            ..
        } => {
            let row_valued = args
                .split_last()
                .is_some_and(|(_, left_args)| left_args.len() != 1);
            row_valued || args.iter().any(scalar_ast_requires_explicit_query_expr)
        }
        ScalarAst::Call { op, args, .. } => {
            // CASE is branch-sensitive and may suppress errors in branches that
            // are not selected. Keep it in the exact FormulaExpr/QueryExpr
            // semantics, just like AND/OR short-circuiting, rather than hiding
            // it inside a deterministic relational query whose row order would
            // choose one otherwise-unobservable first error.
            matches!(
                op,
                ScalarOp::And | ScalarOp::Or | ScalarOp::Case | ScalarOp::ScalarQuery
            ) || args.iter().any(scalar_ast_requires_explicit_query_expr)
        }
        ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_requires_explicit_query_expr(expr),
        // Every window is relational: even a scalar-only window specification
        // consumes a partition/frame rather than one current row.  Supported
        // shapes must therefore enter the exact query-expression lowering;
        // unsupported shapes are rejected there instead of falling through to
        // ordinary scalar-term lowering.
        ScalarAst::Window { .. } => true,
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => false,
    }
}

fn decimal_typmod_mismatch(expr_ty: &FormalAttributeType, output_ty: &FormalAttributeType) -> bool {
    match (expr_ty, output_ty) {
        (
            FormalAttributeType::Decimal {
                precision: expr_precision,
                scale: expr_scale,
            },
            FormalAttributeType::Decimal {
                precision: output_precision,
                scale: output_scale,
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

fn integer_output_type_mismatch(
    expr_ty: &FormalAttributeType,
    output_ty: &FormalAttributeType,
) -> bool {
    (matches!(
        expr_ty,
        FormalAttributeType::Int32 | FormalAttributeType::Int64
    ) || matches!(
        output_ty,
        FormalAttributeType::Int32 | FormalAttributeType::Int64
    )) && expr_ty != output_ty
}

fn string_output_typmod_mismatch(
    expr_ty: &FormalAttributeType,
    output_ty: &FormalAttributeType,
) -> bool {
    (matches!(expr_ty, FormalAttributeType::String { .. })
        || matches!(output_ty, FormalAttributeType::String { .. }))
        && expr_ty != output_ty
}

fn set_case_mapping_text_positions(inputs: &[RelExpr], output_len: usize) -> Vec<usize> {
    (0..output_len)
        .filter(|index| {
            inputs.iter().all(|input| {
                let RelExpr::Project { exprs, .. } = input else {
                    return false;
                };
                exprs
                    .get(*index)
                    .is_some_and(|expr| top_level_string_case_mapping(&expr.parsed).is_some())
            })
        })
        .collect()
}

/// Bare source NULL and string literals have PostgreSQL's `unknown`
/// pseudo-type until their owning set node resolves a common type. Calcite
/// annotates the corresponding Rex literals contextually, and child Project
/// hydration independently defaults bare strings to text, so neither type may
/// be trusted as evidence of an explicit cast. Keep the proof source-attested;
/// an ambiguous literal or a propagated unknown through an extra Project is
/// rejected rather than silently treated as known.
fn source_set_literal_provenance(input: &RelExpr) -> Option<Vec<SetInputLiteralProvenance>> {
    let output_len = input.output().len();
    match input {
        RelExpr::Project {
            input,
            exprs,
            correlations: _,
            ..
        } => {
            if exprs.len() != output_len {
                return None;
            }
            let child_provenance = source_set_literal_provenance(input)?;
            let mut positions = Vec::with_capacity(output_len);
            for expr in exprs {
                let provenance = match &expr.parsed {
                    ScalarAst::Literal { raw } if raw.eq_ignore_ascii_case("NULL") => {
                        let source_attests_unknown = expr.source.as_ref().is_some_and(|source| {
                            source
                                .kind
                                .as_deref()
                                .is_some_and(|kind| kind.eq_ignore_ascii_case("LITERAL"))
                                && source.operator.is_none()
                                && source.clause_ownership.is_none()
                                && source.operands.is_empty()
                                && exact_source_tokens(source).is_some_and(|tokens| {
                                    matches!(
                                        tokens.as_slice(),
                                        [AttestedSqlToken::Identifier(value)] if value == "null"
                                    )
                                })
                        });
                        if !source_attests_unknown {
                            return None;
                        }
                        SetInputLiteralProvenance::UnknownNull
                    }
                    ScalarAst::Literal { raw } if sql_string_literal_content(raw).is_some() => {
                        if !expr
                            .source
                            .as_ref()
                            .is_some_and(|source| source_is_bare_string_literal(source, raw))
                        {
                            return None;
                        }
                        SetInputLiteralProvenance::UnknownString
                    }
                    ScalarAst::InputRef { index }
                        if child_provenance
                            .get(*index)
                            .is_some_and(|provenance| provenance.is_unknown()) =>
                    {
                        return None;
                    }
                    _ => SetInputLiteralProvenance::Known,
                };
                positions.push(provenance);
            }
            Some(positions)
        }
        RelExpr::Filter { input, output, .. }
        | RelExpr::NativeHaving { input, output, .. }
        | RelExpr::Sort { input, output, .. }
            if output.len() == input.output().len() =>
        {
            source_set_literal_provenance(input)
        }
        _ => Some(vec![SetInputLiteralProvenance::Known; output_len]),
    }
}

/// PostgreSQL resolves each binary set node from the independently typed
/// children, before considering its parent.  Equal types retain their exact
/// typmod. NUMERIC/DECIMAL share one PostgreSQL base OID, so any typmod
/// disagreement produces unconstrained NUMERIC. The built-in text, varchar,
/// and bpchar base types have implicit casts in both directions; consequently
/// PostgreSQL keeps the left base type and drops the typmod for every
/// cross-base or same-base/different-typmod pair.
fn postgres_binary_set_common_type(
    left: FormalAttributeType,
    right: FormalAttributeType,
    left_is_unknown: bool,
    right_is_unknown: bool,
) -> Option<FormalAttributeType> {
    match (left_is_unknown, right_is_unknown) {
        (true, true) => {
            return Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            });
        }
        (true, false) => return Some(postgres_typmodless_set_type(right)),
        (false, true) => return Some(postgres_typmodless_set_type(left)),
        (false, false) => {}
    }
    if left == right {
        return Some(left);
    }
    match (left, right) {
        (
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Some(FormalAttributeType::Numeric),
        (FormalAttributeType::String { typmod: left }, FormalAttributeType::String { .. }) => {
            Some(FormalAttributeType::String {
                typmod: match left {
                    SqlStringType::Text => SqlStringType::Text,
                    SqlStringType::Varchar { .. } => SqlStringType::Varchar { length: None },
                    SqlStringType::Char { .. } | SqlStringType::Bpchar => SqlStringType::Bpchar,
                },
            })
        }
        _ => None,
    }
}

fn postgres_typmodless_set_type(ty: FormalAttributeType) -> FormalAttributeType {
    match ty {
        FormalAttributeType::Decimal { .. } => FormalAttributeType::Numeric,
        FormalAttributeType::String { typmod } => FormalAttributeType::String {
            typmod: match typmod {
                SqlStringType::Text => SqlStringType::Text,
                SqlStringType::Varchar { .. } => SqlStringType::Varchar { length: None },
                SqlStringType::Char { .. } | SqlStringType::Bpchar => SqlStringType::Bpchar,
            },
        },
        FormalAttributeType::Timestamp { .. } => FormalAttributeType::Timestamp { precision: None },
        FormalAttributeType::Timestamptz { .. } => {
            FormalAttributeType::Timestamptz { precision: None }
        }
        other => other,
    }
}

fn set_string_common_type_target(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Text
                | SqlStringType::Varchar { length: None }
                | SqlStringType::Bpchar
        }
    )
}

fn string_implicit_coercion_term(
    input: FormalFunctionTerm,
    output_ty: FormalAttributeType,
) -> Option<FormalFunctionTerm> {
    let (tag, length) = string_typmod_codes(output_ty)?;
    Some(FormalFunctionTerm::ScalarCall {
        operator: ScalarOperator::Cast(ScalarCast::StringImplicit),
        args: vec![input, z_constant_function(tag), z_constant_function(length)],
    })
}

fn lower_values_string_cast_cell(args: Vec<FormalFunctionTerm>) -> Option<ValuesCell> {
    let [
        FormalFunctionTerm::Constant { raw, .. },
        FormalFunctionTerm::Constant { raw: tag, .. },
        FormalFunctionTerm::Constant { raw: length, .. },
    ] = args.as_slice()
    else {
        return None;
    };
    let tag = tag.parse::<u32>().ok()?;
    let length = length.parse::<u32>().ok()?;
    let typmod = match (tag, length) {
        (0, 0) => SqlStringType::Text,
        (1, 0) => SqlStringType::Varchar { length: None },
        (2, length) => SqlStringType::Varchar {
            length: Some(length),
        },
        (3, length) => SqlStringType::Char { length },
        (4, 0) => SqlStringType::Bpchar,
        _ => return None,
    };
    Some(ValuesCell {
        raw: raw.clone(),
        ty: Some(FormalAttributeType::String { typmod }),
        source_ty: None,
    })
}

fn attribute_types_compatible_for_values(
    literal_ty: FormalAttributeType,
    output_ty: FormalAttributeType,
) -> bool {
    match (literal_ty, output_ty) {
        (FormalAttributeType::Int32, FormalAttributeType::Int64) => true,
        (
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => true,
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

/// Closed admission for PostgreSQL's direct fixed-typmod DECIMAL statistic.
/// Calcite reports the argument typmod as the aggregate result typmod, while
/// PostgreSQL returns unconstrained NUMERIC. The override is authoritative
/// only when the typed direct input and independently parsed source AST agree
/// on the same one-column STDDEV_SAMP call.
fn attested_postgres_stddev_samp_numeric_fixed(
    call: &AggregateCall,
    scope: &Scope,
) -> Option<(u32, u32)> {
    if !call.function.eq_ignore_ascii_case("STDDEV_SAMP")
        || call.distinct
        || call.filter.is_some()
        || call.modifiers.has_semantic_modifiers()
        || call.modifiers.source_distinct != Some(false)
    {
        return None;
    }
    let [argument] = call.args.as_slice() else {
        return None;
    };
    let ScalarAst::InputRef { index } = &argument.parsed else {
        return None;
    };
    let attribute = scope.attribute(*index)?;
    let FormalAttributeType::Decimal { precision, scale } = attribute.formal_ty else {
        return None;
    };
    let source = call.modifiers.source.as_ref()?;
    if !source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("OTHER_FUNCTION"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("STDDEV_SAMP"))
        || !source_has_exact_binding(source)
    {
        return None;
    }
    let source_argument = exact_source_unary_function(source, "STDDEV_SAMP")?;
    (source_argument.operands.is_empty()
        && source_is_direct_identifier(source_argument, attribute.visible_name.as_str()))
    .then_some((precision, scale))
}

fn aggregate_result_follows_argument_type(function: &str) -> bool {
    matches!(
        function.to_ascii_lowercase().as_str(),
        "sum" | "max" | "min" | "bit_and" | "bit_or"
    )
}

fn postgres_integral_statistic(function: &str) -> bool {
    matches!(
        function.to_ascii_lowercase().as_str(),
        "var_pop" | "var_samp" | "variance" | "stddev_pop" | "stddev_samp" | "stddev"
    )
}

fn is_integral_aggregate_type(ty: FormalAttributeType) -> bool {
    matches!(ty, FormalAttributeType::Int32 | FormalAttributeType::Int64)
}

fn aggregate_term_contains_bare_decimal_division(term: &FormalAggregateTerm) -> bool {
    match term {
        FormalAggregateTerm::Expr { term } => function_term_contains_bare_decimal_division(term),
        FormalAggregateTerm::Aggregate { arg, .. } => {
            function_term_contains_bare_decimal_division(arg)
        }
        FormalAggregateTerm::CountStar => false,
        FormalAggregateTerm::ScalarCall { operator, args } => {
            if matches!(
                operator,
                ScalarOperator::Cast(ScalarCast::ToNumericTypmod(_))
            ) {
                false
            } else {
                *operator == ScalarOperator::Divide(ScalarNumericKind::Numeric)
                    || args
                        .iter()
                        .any(aggregate_term_contains_bare_decimal_division)
            }
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
        FormalFunctionTerm::ScalarCall { operator, args } => {
            if matches!(
                operator,
                ScalarOperator::Cast(ScalarCast::ToNumericTypmod(_))
            ) {
                false
            } else {
                *operator == ScalarOperator::Divide(ScalarNumericKind::Numeric)
                    || args
                        .iter()
                        .any(function_term_contains_bare_decimal_division)
            }
        }
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
