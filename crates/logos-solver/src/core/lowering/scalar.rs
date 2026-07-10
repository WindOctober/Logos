use super::*;
use logos_ir::ir::{RelExpr, ScalarAst, ScalarOp};

impl LoweringContext {
    pub(super) fn lower_formula(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalFormula> {
        match ast {
            ScalarAst::Literal { raw } if raw.eq_ignore_ascii_case("true") => {
                Some(FormalFormula::True)
            }
            ScalarAst::Literal { raw } if raw.eq_ignore_ascii_case("false") => {
                Some(FormalFormula::False)
            }
            ScalarAst::Call { op, args, .. } => match op {
                ScalarOp::And | ScalarOp::Or if !args.is_empty() => {
                    self.lower_variadic_formula(path, op.clone(), args, scope)
                }
                ScalarOp::Not if args.len() == 1 => Some(FormalFormula::Not {
                    formula: Box::new(self.lower_formula(
                        &format!("{path}.arg"),
                        &args[0],
                        scope,
                    )?),
                }),
                ScalarOp::Eq
                | ScalarOp::NotEq
                | ScalarOp::Lt
                | ScalarOp::Lte
                | ScalarOp::Gt
                | ScalarOp::Gte
                | ScalarOp::IsNull
                | ScalarOp::IsNotNull
                | ScalarOp::IsTrue
                | ScalarOp::IsNotTrue
                | ScalarOp::IsFalse
                | ScalarOp::IsNotFalse
                | ScalarOp::IsNotDistinctFrom => {
                    let predicate = self.predicate_name_for_args(
                        &format!("{path}.predicateType"),
                        op,
                        args,
                        scope,
                    )?;
                    let lowered_args = args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
                        })
                        .collect::<Option<Vec<_>>>()?;
                    if predicate_requires_external_interpretation(op) {
                        self.warning(
                            path,
                            "predicate_interpretation_required",
                            "Lowered SQL predicate requires a matching FormalSQL Tuple.predicate interpretation in Rocq.",
                        );
                    }
                    Some(FormalFormula::Predicate {
                        predicate,
                        args: lowered_args,
                    })
                }
                ScalarOp::Like => {
                    self.error(
                        path,
                        "like_predicate_not_supported",
                        "LIKE needs dialect-specific pattern and escape semantics before it can be mapped to a FormalSQL predicate.",
                    );
                    None
                }
                ScalarOp::In => self.lower_in_formula(path, args, scope),
                ScalarOp::Exists => self.lower_exists_formula(path, args),
                ScalarOp::Case => {
                    let lowered = self.lower_aggregate_term(path, ast, scope)?;
                    Some(FormalFormula::Predicate {
                        predicate: "is_true".to_owned(),
                        args: vec![lowered],
                    })
                }
                _ => {
                    self.error(
                        path,
                        "formula_operator_not_supported",
                        &format!("Scalar operator {op:?} is not supported as a FormalSQL formula."),
                    );
                    None
                }
            },
            ScalarAst::TypeAnnotation { expr, .. } => self.lower_formula(path, expr, scope),
            _ => {
                self.error(
                    path,
                    "formula_ast_not_supported",
                    "Scalar AST cannot be lowered to FormalSQL sql_formula.",
                );
                None
            }
        }
    }

    fn lower_exists_formula(&mut self, path: &str, args: &[ScalarAst]) -> Option<FormalFormula> {
        match args {
            [ScalarAst::RelSubquery { rel }] => {
                let query = self.lower_rel(&format!("{path}.subquery"), rel)?;
                Some(FormalFormula::Exists {
                    query: Box::new(query),
                })
            }
            [_] => {
                self.error(
                    path,
                    "exists_subquery_not_supported",
                    "EXISTS predicates require a structured Calcite subquery operand.",
                );
                None
            }
            _ => {
                self.error(
                    path,
                    "exists_predicate_arity_mismatch",
                    "EXISTS predicate requires exactly one subquery operand.",
                );
                None
            }
        }
    }

    fn predicate_name_for_args(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<String> {
        if args.len() != 2 {
            return Some(predicate_name(op).to_owned());
        }
        let left = self.direct_function_type(&format!("{path}.leftType"), &args[0], scope);
        let right = self.direct_function_type(&format!("{path}.rightType"), &args[1], scope);
        if is_floating_comparison_mismatch(left, right) {
            self.error(
                path,
                "floating_comparison_predicate_not_supported",
                "FLOAT/DOUBLE predicates are lowered only when both operands have the same modeled floating type.",
            );
            return None;
        }
        if !is_order_predicate(op) {
            return Some(predicate_name(op).to_owned());
        }
        match (left, right) {
            (Some(FormalAttributeType::Float), Some(FormalAttributeType::Float)) => {
                Some(format!("{}.", predicate_name(op)))
            }
            (Some(FormalAttributeType::Double), Some(FormalAttributeType::Double)) => {
                Some(format!("{}_double", predicate_name(op)))
            }
            _ => Some(predicate_name(op).to_owned()),
        }
    }

    fn lower_in_formula(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalFormula> {
        let Some((right, left_args)) = args.split_last() else {
            self.error(
                path,
                "in_predicate_arity_mismatch",
                "IN predicate requires at least one left expression and one right operand.",
            );
            return None;
        };
        match right {
            ScalarAst::RelSubquery { rel } => {
                self.lower_in_rel_subquery_formula(path, left_args, rel, scope)
            }
            _ => {
                // TODO: Support literal/expression IN lists by expanding SQL's three-valued
                // membership semantics, including NULL and row-value cases.
                self.error(
                    path,
                    "in_list_not_supported",
                    "IN predicates are currently supported only when the right operand is a structured Calcite subquery.",
                );
                None
            }
        }
    }

    fn lower_in_rel_subquery_formula(
        &mut self,
        path: &str,
        left_args: &[ScalarAst],
        rel: &RelExpr,
        scope: &Scope,
    ) -> Option<FormalFormula> {
        let query = self.lower_rel(&format!("{path}.subquery"), rel)?;
        let output = rel.output().to_vec();
        if left_args.len() != output.len() {
            self.error(
                path,
                "in_predicate_arity_mismatch",
                "IN predicate left arity does not match subquery output arity.",
            );
            return None;
        }
        let (renamed_query, renamed_output) =
            self.rename_in_subquery_output(path, query, &output, scope)?;
        let equality = self.in_equality_formula(path, left_args, &renamed_output, scope)?;
        Some(FormalFormula::Exists {
            query: Box::new(FormalQuery::Selection {
                predicate: equality,
                input: Box::new(renamed_query),
            }),
        })
    }

    fn rename_in_subquery_output(
        &mut self,
        path: &str,
        query: FormalQuery,
        output: &[Column],
        outer_scope: &Scope,
    ) -> Option<(FormalQuery, Vec<Column>)> {
        let mut renamed = Vec::with_capacity(output.len());
        for (index, column) in output.iter().enumerate() {
            let fresh_name = format!("__logos_in_{index}");
            if outer_scope
                .attributes
                .iter()
                .any(|attribute| attribute.name == fresh_name)
                || output.iter().any(|column| column.name == fresh_name)
            {
                self.error(
                    path,
                    "in_subquery_fresh_name_collision",
                    "Generated IN-subquery attribute name collides with an existing attribute.",
                );
                return None;
            }
            renamed.push(Column {
                name: fresh_name,
                ty: column.ty.clone(),
                nullable: column.nullable,
            });
        }
        let select = output
            .iter()
            .zip(&renamed)
            .enumerate()
            .map(|(index, (input, output))| {
                Some(FormalSelectItem {
                    expr: FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Attribute {
                            name: input.name.clone(),
                            ty: self.lower_attribute_type(
                                &format!("{path}.input[{index}]"),
                                input,
                                AttributeTypeContext::QueryInput,
                            )?,
                        },
                    },
                    alias: output.name.clone(),
                    alias_ty: self.lower_attribute_type(
                        &format!("{path}.output[{index}]"),
                        output,
                        AttributeTypeContext::QueryOutput,
                    )?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some((
            FormalQuery::Projection {
                select,
                input: Box::new(query),
            },
            renamed,
        ))
    }

    fn in_equality_formula(
        &mut self,
        path: &str,
        left_args: &[ScalarAst],
        right_output: &[Column],
        outer_scope: &Scope,
    ) -> Option<FormalFormula> {
        let mut terms = left_args.iter().zip(right_output).enumerate().map(
            |(index, (left_arg, right_column))| {
                let left_ty =
                    self.direct_function_type(&format!("{path}.left[{index}].type"), left_arg, outer_scope);
                let right_ty = self.lower_attribute_type(
                    &format!("{path}.right[{index}]"),
                    right_column,
                    AttributeTypeContext::QueryInput,
                )?;
                if is_floating_comparison_mismatch(left_ty, Some(right_ty)) {
                    self.error(
                        &format!("{path}.equality[{index}]"),
                        "floating_comparison_predicate_not_supported",
                        "FLOAT/DOUBLE IN-subquery equality is lowered only when both operands have the same modeled floating type.",
                    );
                    return None;
                }
                let left = self.lower_aggregate_term(
                    &format!("{path}.left[{index}]"),
                    left_arg,
                    outer_scope,
                )?;
                let right = FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: right_column.name.clone(),
                        ty: right_ty,
                    },
                };
                Some(FormalFormula::Predicate {
                    predicate: "=".to_owned(),
                    args: vec![left, right],
                })
            },
        );
        let mut acc = terms.next()??;
        for term in terms {
            acc = FormalFormula::And {
                left: Box::new(acc),
                right: Box::new(term?),
            };
        }
        Some(acc)
    }

    fn lower_variadic_formula(
        &mut self,
        path: &str,
        op: ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalFormula> {
        let mut iter = args.iter().enumerate();
        let (first_index, first_arg) = iter.next()?;
        let mut acc =
            self.lower_formula(&format!("{path}.args[{first_index}]"), first_arg, scope)?;
        for (index, arg) in iter {
            let right = self.lower_formula(&format!("{path}.args[{index}]"), arg, scope)?;
            acc = if op == ScalarOp::And {
                FormalFormula::And {
                    left: Box::new(acc),
                    right: Box::new(right),
                }
            } else {
                FormalFormula::Or {
                    left: Box::new(acc),
                    right: Box::new(right),
                }
            };
        }
        Some(acc)
    }

    pub(super) fn lower_aggregate_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        match ast {
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus)
                    && args.len() == 2
                    && timestamp_interval_function(op, &args[0], &args[1]).is_some() =>
            {
                let TimestampIntervalFunction {
                    symbol,
                    timestamp_arg,
                    interval_arg,
                } = timestamp_interval_function(op, &args[0], &args[1])?;
                let timestamp =
                    self.lower_aggregate_term(&format!("{path}.timestamp"), timestamp_arg, scope)?;
                let interval =
                    self.lower_interval_term(&format!("{path}.interval"), interval_arg, op)?;
                Some(FormalAggregateTerm::Function {
                    symbol,
                    args: vec![timestamp, interval],
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus)
                    && args.len() == 2
                    && date_interval_function(op, &args[0], &args[1]).is_some() =>
            {
                let DateIntervalFunction {
                    symbol,
                    date_arg,
                    interval_arg,
                } = date_interval_function(op, &args[0], &args[1])?;
                let date = self.lower_aggregate_term(&format!("{path}.date"), date_arg, scope)?;
                let interval =
                    self.lower_interval_term(&format!("{path}.interval"), interval_arg, op)?;
                Some(FormalAggregateTerm::Function {
                    symbol,
                    args: vec![date, interval],
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus)
                    && args.len() == 2
                    && has_temporal_interval_pair(&args[0], &args[1]) =>
            {
                self.error(
                    path,
                    "temporal_interval_arithmetic_not_supported",
                    "This temporal type and INTERVAL unit combination is not supported by the FormalSQL timestamp/date lowering.",
                );
                None
            }
            ScalarAst::Call {
                op: ScalarOp::Case,
                args,
                ..
            } => self.lower_case_aggregate_term(path, args, scope),
            ScalarAst::Call { op, args, .. }
                if matches!(
                    op,
                    ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
                ) && args.len() == 2
                    && self
                        .homogeneous_float_binary_type(&format!("{path}.floatArgs"), args, scope)
                        .is_some() =>
            {
                let ty =
                    self.homogeneous_float_binary_type(&format!("{path}.floatArgs"), args, scope)?;
                Some(FormalAggregateTerm::Function {
                    symbol: floating_function_symbol(op, ty)?.to_owned(),
                    args: args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(
                    op,
                    ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
                ) && self.has_float_argument(&format!("{path}.floatArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "floating_mixed_arithmetic_not_supported",
                    "FLOAT/DOUBLE arithmetic is lowered only when all operands have the same modeled floating type.",
                );
                None
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1
                && self
                    .direct_function_type(&format!("{path}.argType"), &args[0], scope)
                    .is_some_and(is_float_type) =>
            {
                let ty = self.direct_function_type(&format!("{path}.argType"), &args[0], scope)?;
                Some(FormalAggregateTerm::Function {
                    symbol: floating_unary_minus_symbol(ty)?.to_owned(),
                    args: vec![self.lower_aggregate_term(
                        &format!("{path}.arg"),
                        &args[0],
                        scope,
                    )?],
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && args.len() == 2
                    && self.decimal_binary_args(&format!("{path}.decimalArgs"), args, scope) =>
            {
                let symbol = match op {
                    ScalarOp::Plus => "plus_decimal",
                    ScalarOp::Minus => "minus_decimal",
                    ScalarOp::Multiply => "mult_decimal",
                    _ => unreachable!("decimal arithmetic guard checked"),
                };
                Some(FormalAggregateTerm::Function {
                    symbol: symbol.to_owned(),
                    args: args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && self.has_decimal_argument(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "decimal_mixed_arithmetic_not_supported",
                    "Decimal arithmetic is lowered only when all operands are known DECIMAL values.",
                );
                None
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1 && self.decimal_unary_arg(path, &args[0], scope) => {
                Some(FormalAggregateTerm::Function {
                    symbol: "opp_decimal".to_owned(),
                    args: vec![self.lower_aggregate_term(
                        &format!("{path}.arg"),
                        &args[0],
                        scope,
                    )?],
                })
            }
            ScalarAst::Call {
                op: ScalarOp::Divide,
                args,
                ..
            } if args.len() == 2
                && self.decimal_binary_args(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.lower_decimal_division_aggregate_term(path, args, scope, None)
            }
            ScalarAst::Call {
                op: ScalarOp::Divide,
                args,
                ..
            } if args.len() == 2
                && self.has_decimal_argument(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "decimal_mixed_arithmetic_not_supported",
                    "Decimal division is lowered only when both operands are known DECIMAL values.",
                );
                None
            }
            ScalarAst::Call { op, args, .. } if matches!(op, ScalarOp::And | ScalarOp::Or) => {
                self.lower_variadic_boolean_aggregate_term(path, op, args, scope)
            }
            ScalarAst::Call { op, args, .. }
                if is_comparison_predicate(op)
                    && self.floating_comparison_args_mismatch(
                        &format!("{path}.floatArgs"),
                        args,
                        scope,
                    ) =>
            {
                self.error(
                    path,
                    "floating_comparison_value_not_supported",
                    "FLOAT/DOUBLE comparisons in value context are lowered only when both operands have the same modeled floating type.",
                );
                None
            }
            ScalarAst::Call { op, args, .. }
                if is_order_predicate(op)
                    && self.has_float_argument(&format!("{path}.floatArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "floating_order_value_not_supported",
                    "FLOAT/DOUBLE order comparisons are supported only in predicate context; boolean-valued projection expressions need a FormalSQL symbol interpretation first.",
                );
                None
            }
            ScalarAst::Call { op, args, .. }
                if is_function_term_function(op)
                    && self.has_decimal_argument(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "decimal_function_not_supported",
                    "This DECIMAL-valued scalar function is outside the currently modeled FormalSQL Decimal subset.",
                );
                None
            }
            ScalarAst::Call { op, args, .. } if is_aggregate_term_function(op) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
                    })
                    .collect::<Option<Vec<_>>>()?;
                if function_requires_external_interpretation(op) {
                    self.warning(
                        path,
                        "aggregate_term_symbol_interpretation_required",
                        "Lowered SQL expression requires a matching FormalSQL Tuple.symbol interpretation in Rocq.",
                    );
                }
                Some(FormalAggregateTerm::Function {
                    symbol: function_symbol(op),
                    args,
                })
            }
            ScalarAst::TypeAnnotation { ty, .. }
                if type_annotation_is_date(ty)
                    || type_annotation_is_time(ty)
                    || type_annotation_is_timestamp(ty)
                    || type_annotation_is_timestamp_tz(ty)
                    || type_annotation_is_interval(ty) =>
            {
                Some(FormalAggregateTerm::Expr {
                    term: self.lower_function_term(path, ast, scope)?,
                })
            }
            ScalarAst::TypeAnnotation { expr, ty } => {
                if type_annotation_is_decimal(ty) && formal_type_from_annotation(ty).is_none() {
                    self.error(
                        path,
                        "decimal_typmod_not_supported",
                        "FormalSQL DECIMAL lowering supports PostgreSQL DECIMAL(p,s) for 1 <= p <= 1000 and 0 <= s <= 1000; negative scales are not modeled yet.",
                    );
                    return None;
                }
                if let (Some(raw), Some(formal_ty)) =
                    (typed_literal_raw(expr), formal_type_from_annotation(ty))
                {
                    if matches!(
                        formal_ty,
                        FormalAttributeType::Float | FormalAttributeType::Double
                    ) && !raw.eq_ignore_ascii_case("null")
                        && super::emit::float_literal_bits_for_type(raw, Some(&formal_ty)).is_none()
                    {
                        self.error(
                            path,
                            "float_literal_not_supported",
                            "FormalSQL lowering supports FLOAT/DOUBLE literals only for finite SQL numeric literals that fit the target floating-point type.",
                        );
                        return None;
                    }
                    if matches!(formal_ty, FormalAttributeType::Decimal { .. })
                        && !raw.eq_ignore_ascii_case("null")
                        && super::emit::decimal_literal_for_type(raw, Some(&formal_ty)).is_none()
                    {
                        self.error(
                            path,
                            "decimal_literal_not_supported",
                            "FormalSQL DECIMAL lowering supports PostgreSQL-style fixed-scale decimal literals only when coercion to DECIMAL(p,s) succeeds without precision overflow.",
                        );
                        return None;
                    }
                    return Some(FormalAggregateTerm::Expr {
                        term: FormalFunctionTerm::Constant {
                            raw: raw.to_owned(),
                            ty: Some(formal_ty),
                        },
                    });
                }
                if let Some(formal_ty) = formal_type_from_annotation(ty)
                    && is_float_type(formal_ty)
                {
                    self.validate_floating_expression_annotation(path, expr, formal_ty, scope)?;
                }
                if let Some(target_ty) = explicit_decimal_annotation_type(ty) {
                    if let Some(args) = decimal_division_cast_args(expr)
                        && args.len() == 2
                        && self.decimal_binary_args(&format!("{path}.decimalArgs"), args, scope)
                    {
                        return self.lower_decimal_division_aggregate_term(
                            path,
                            args,
                            scope,
                            Some(target_ty),
                        );
                    }
                }
                if let Some(cast_arg) = cast_arg(expr) {
                    let target_ty = formal_type_from_annotation(ty).or_else(|| {
                        self.error(
                            path,
                            "cast_target_type_not_supported",
                            "FormalSQL lowering cannot infer the target type of this explicit CAST.",
                        );
                        None
                    })?;
                    let source_ty = self
                        .infer_cast_operand_type(&format!("{path}.castArg"), cast_arg, scope)
                        .or_else(|| {
                            self.error(
                                path,
                                "cast_source_type_not_supported",
                                "FormalSQL lowering cannot infer the source type of this explicit CAST.",
                            );
                            None
                        })?;
                    if source_ty == target_ty {
                        self.lower_aggregate_term(&format!("{path}.castArg"), cast_arg, scope)
                    } else if let Some(function) =
                        decimal_typmod_cast_function(&source_ty, &target_ty)
                    {
                        self.lower_decimal_cast_aggregate_term(
                            &format!("{path}.castArg"),
                            cast_arg,
                            function,
                            target_ty,
                            scope,
                        )
                    } else {
                        self.error(
                            path,
                            "cast_not_supported",
                            &format!(
                                "Explicit CAST from {source_ty:?} to {target_ty:?} is not in the FormalSQL cast whitelist.",
                            ),
                        );
                        None
                    }
                } else {
                    if matches!(
                        formal_type_from_annotation(ty),
                        Some(FormalAttributeType::Decimal { .. })
                    ) {
                        self.error(
                            path,
                            "decimal_expression_not_supported",
                            "DECIMAL expression annotation is supported only for fixed-scale literals, no-op casts, or explicitly cast Decimal division.",
                        );
                        return None;
                    }
                    self.lower_aggregate_term(path, expr, scope)
                }
            }
            _ => Some(FormalAggregateTerm::Expr {
                term: self.lower_function_term(path, ast, scope)?,
            }),
        }
    }

    fn decimal_binary_args(&mut self, path: &str, args: &[ScalarAst], scope: &Scope) -> bool {
        let left = self.direct_function_type(&format!("{path}.leftType"), &args[0], scope);
        let right = self.direct_function_type(&format!("{path}.rightType"), &args[1], scope);
        matches!(left, Some(FormalAttributeType::Decimal { .. }))
            && matches!(right, Some(FormalAttributeType::Decimal { .. }))
    }

    fn decimal_unary_arg(&mut self, path: &str, arg: &ScalarAst, scope: &Scope) -> bool {
        matches!(
            self.direct_function_type(&format!("{path}.argType"), arg, scope),
            Some(FormalAttributeType::Decimal { .. })
        )
    }

    fn has_decimal_argument(&mut self, path: &str, args: &[ScalarAst], scope: &Scope) -> bool {
        args.iter().enumerate().any(|(index, arg)| {
            matches!(
                self.direct_function_type(&format!("{path}[{index}]"), arg, scope),
                Some(FormalAttributeType::Decimal { .. })
            )
        })
    }

    fn homogeneous_float_binary_type(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        if args.len() != 2 {
            return None;
        }
        let left = self.direct_function_type(&format!("{path}.leftType"), &args[0], scope);
        let right = self.direct_function_type(&format!("{path}.rightType"), &args[1], scope);
        match (left, right) {
            (Some(FormalAttributeType::Float), Some(FormalAttributeType::Float)) => {
                Some(FormalAttributeType::Float)
            }
            (Some(FormalAttributeType::Double), Some(FormalAttributeType::Double)) => {
                Some(FormalAttributeType::Double)
            }
            _ => None,
        }
    }

    fn has_float_argument(&mut self, path: &str, args: &[ScalarAst], scope: &Scope) -> bool {
        args.iter().enumerate().any(|(index, arg)| {
            self.direct_function_type(&format!("{path}[{index}]"), arg, scope)
                .is_some_and(is_float_type)
        })
    }

    fn floating_comparison_args_mismatch(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> bool {
        if args.len() != 2 {
            return false;
        }
        let left = self.direct_function_type(&format!("{path}.leftType"), &args[0], scope);
        let right = self.direct_function_type(&format!("{path}.rightType"), &args[1], scope);
        is_floating_comparison_mismatch(left, right)
    }

    fn validate_floating_expression_annotation(
        &mut self,
        path: &str,
        expr: &ScalarAst,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<()> {
        match self.direct_function_type(&format!("{path}.floatAnnotationSource"), expr, scope) {
            Some(source_ty) if source_ty == target_ty => Some(()),
            Some(source_ty) => {
                self.error(
                    path,
                    "floating_cast_not_supported",
                    &format!(
                        "FLOAT/DOUBLE expression annotation from {source_ty:?} to {target_ty:?} is not modeled as a FormalSQL cast.",
                    ),
                );
                None
            }
            None => {
                self.error(
                    path,
                    "floating_expression_type_not_supported",
                    "FLOAT/DOUBLE expression annotation is supported only when the inner expression type can be inferred exactly.",
                );
                None
            }
        }
    }

    fn lower_decimal_division_aggregate_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
        annotated_ty: Option<FormalAttributeType>,
    ) -> Option<FormalAggregateTerm> {
        if !decimal_divisor_is_static_nonzero(&args[1]) {
            self.error(
                path,
                "decimal_divisor_not_statically_nonzero",
                "DECIMAL division is lowered only when the divisor is a statically nonzero DECIMAL literal, because SQL division by zero is a runtime error.",
            );
            return None;
        }
        let result_ty = self.decimal_division_result_type(path, args, scope, annotated_ty)?;
        let mut lowered_args = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
            })
            .collect::<Option<Vec<_>>>()?;
        let symbol = if let Some(result_ty) = result_ty {
            let result_precision = decimal_type_precision(&result_ty)?;
            let result_scale = decimal_type_scale(&result_ty)?;
            lowered_args.push(z_constant_aggregate(result_precision));
            lowered_args.push(z_constant_aggregate(result_scale));
            "divide_decimal_typmod"
        } else {
            "divide_decimal"
        };
        Some(FormalAggregateTerm::Function {
            symbol: symbol.to_owned(),
            args: lowered_args,
        })
    }

    fn lower_decimal_division_function_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
        annotated_ty: Option<FormalAttributeType>,
    ) -> Option<FormalFunctionTerm> {
        if !decimal_divisor_is_static_nonzero(&args[1]) {
            self.error(
                path,
                "decimal_divisor_not_statically_nonzero",
                "DECIMAL division is lowered only when the divisor is a statically nonzero DECIMAL literal, because SQL division by zero is a runtime error.",
            );
            return None;
        }
        let result_ty = self.decimal_division_result_type(path, args, scope, annotated_ty)?;
        let mut lowered_args = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)
            })
            .collect::<Option<Vec<_>>>()?;
        let symbol = if let Some(result_ty) = result_ty {
            let result_precision = decimal_type_precision(&result_ty)?;
            let result_scale = decimal_type_scale(&result_ty)?;
            lowered_args.push(z_constant_function(result_precision));
            lowered_args.push(z_constant_function(result_scale));
            "divide_decimal_typmod"
        } else {
            "divide_decimal"
        };
        Some(FormalFunctionTerm::Function {
            symbol: symbol.to_owned(),
            args: lowered_args,
        })
    }

    fn lower_decimal_cast_aggregate_term(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        function: &str,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        let result_precision = decimal_type_precision(&target_ty)?;
        let result_scale = decimal_type_scale(&target_ty)?;
        Some(FormalAggregateTerm::Function {
            symbol: function.to_owned(),
            args: vec![
                self.lower_aggregate_term(path, arg, scope)?,
                z_constant_aggregate(result_precision),
                z_constant_aggregate(result_scale),
            ],
        })
    }

    fn lower_decimal_cast_function_term(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        function: &str,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        let result_precision = decimal_type_precision(&target_ty)?;
        let result_scale = decimal_type_scale(&target_ty)?;
        Some(FormalFunctionTerm::Function {
            symbol: function.to_owned(),
            args: vec![
                self.lower_function_term(path, arg, scope)?,
                z_constant_function(result_precision),
                z_constant_function(result_scale),
            ],
        })
    }

    fn decimal_division_result_type(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
        annotated_ty: Option<FormalAttributeType>,
    ) -> Option<Option<FormalAttributeType>> {
        let left_ty = self.direct_function_type(&format!("{path}.leftType"), &args[0], scope)?;
        let right_ty = self.direct_function_type(&format!("{path}.rightType"), &args[1], scope)?;
        let Some(result_ty) = annotated_ty else {
            return Some(None);
        };
        if !decimal_division_precision_is_safe(&left_ty, &right_ty, &result_ty) {
            self.error(
                path,
                "decimal_division_precision_not_supported",
                "FormalSQL DECIMAL division is lowered only when the result DECIMAL precision can contain the worst-case integral digits.",
            );
            return None;
        }
        Some(Some(result_ty))
    }

    pub(super) fn direct_function_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        match ast {
            ScalarAst::InputRef { index } => Some(scope.attribute(*index)?.formal_ty),
            ScalarAst::CorrelatedRef {
                correlation,
                field,
                index,
                ..
            } => Some(
                self.correlated_attribute(path, correlation, *index, field)?
                    .formal_ty,
            ),
            ScalarAst::TypeAnnotation { ty, .. } => formal_type_from_annotation(ty),
            ScalarAst::Call {
                op: op @ (ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply),
                args,
                ..
            } if args.len() == 2 && self.decimal_binary_args(path, args, scope) => {
                let left_ty =
                    self.direct_function_type(&format!("{path}.leftType"), &args[0], scope)?;
                let right_ty =
                    self.direct_function_type(&format!("{path}.rightType"), &args[1], scope)?;
                decimal_binary_result_type(op, &left_ty, &right_ty)
            }
            ScalarAst::Call {
                op: ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide,
                args,
                ..
            } if args.len() == 2 => self.homogeneous_float_binary_type(path, args, scope),
            ScalarAst::Call {
                op: ScalarOp::Divide,
                args,
                ..
            } if args.len() == 2 && self.decimal_binary_args(path, args, scope) => None,
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1 && self.decimal_unary_arg(path, &args[0], scope) => {
                self.direct_function_type(&format!("{path}.argType"), &args[0], scope)
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1
                && self
                    .direct_function_type(&format!("{path}.argType"), &args[0], scope)
                    .is_some_and(is_float_type) =>
            {
                self.direct_function_type(&format!("{path}.argType"), &args[0], scope)
            }
            _ => None,
        }
    }

    fn lower_case_aggregate_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        if args.len() < 3 || args.len() % 2 == 0 {
            self.error(
                path,
                "case_arity_not_supported",
                "FormalSQL CASE lowering expects Calcite searched-CASE operands as WHEN/THEN pairs followed by an ELSE expression.",
            );
            return None;
        }

        let result_ty = self.infer_case_type(&format!("{path}.resultType"), args, scope);
        let mut branches = Vec::with_capacity(args.len() / 2);
        for (branch_index, pair) in args[..args.len() - 1].chunks_exact(2).enumerate() {
            if !self.case_when_is_boolean(
                &format!("{path}.branches[{branch_index}].when"),
                &pair[0],
                scope,
            ) {
                return None;
            }
            branches.push(FormalCaseBranch {
                when: self.lower_aggregate_term(
                    &format!("{path}.branches[{branch_index}].when"),
                    &pair[0],
                    scope,
                )?,
                then_expr: self
                    .lower_aggregate_term(
                        &format!("{path}.branches[{branch_index}].then"),
                        &pair[1],
                        scope,
                    )
                    .map(|term| annotate_case_literal_term(term, result_ty))?,
            });
        }

        Some(FormalAggregateTerm::Case {
            branches,
            else_expr: Box::new(
                self.lower_aggregate_term(
                    &format!("{path}.else"),
                    args.last().expect("CASE arity checked"),
                    scope,
                )
                .map(|term| annotate_case_literal_term(term, result_ty))?,
            ),
        })
    }

    fn case_when_is_boolean(&mut self, path: &str, ast: &ScalarAst, scope: &Scope) -> bool {
        let ok = match ast {
            ScalarAst::Literal { raw } => {
                raw.eq_ignore_ascii_case("true") || raw.eq_ignore_ascii_case("false")
            }
            ScalarAst::InputRef { index } => scope
                .attribute(*index)
                .is_some_and(|attr| attr.formal_ty == FormalAttributeType::Bool),
            ScalarAst::CorrelatedRef {
                correlation,
                field,
                index,
                ..
            } => self
                .correlated_attribute(path, correlation, *index, field)
                .is_some_and(|attr| attr.formal_ty == FormalAttributeType::Bool),
            ScalarAst::TypeAnnotation { ty, .. } => {
                formal_type_from_annotation(ty) == Some(FormalAttributeType::Bool)
            }
            ScalarAst::Call { op, .. } => is_boolean_value_function(op),
            _ => false,
        };
        if !ok {
            self.error(
                path,
                "case_when_condition_not_boolean",
                "FormalSQL CASE lowering requires each WHEN operand to be a boolean-valued SQL expression.",
            );
        }
        ok
    }

    fn lower_variadic_boolean_aggregate_term(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        if args.is_empty() {
            self.error(
                path,
                "boolean_value_operator_arity_not_supported",
                "FormalSQL boolean value lowering expects AND/OR to have at least one argument.",
            );
            return None;
        }
        let mut lowered = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter();
        let mut acc = lowered.next().expect("non-empty AND/OR checked");
        for right in lowered {
            acc = FormalAggregateTerm::Function {
                symbol: function_symbol(op),
                args: vec![acc, right],
            };
        }
        Some(acc)
    }

    pub(super) fn lower_function_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        match ast {
            ScalarAst::InputRef { index } => {
                let attr = scope.attribute(*index).or_else(|| {
                    self.error(
                        path,
                        "input_ref_out_of_range",
                        "Input reference is out of range.",
                    );
                    None
                })?;
                Some(FormalFunctionTerm::Attribute {
                    name: attr.name,
                    ty: attr.formal_ty,
                })
            }
            ScalarAst::CorrelatedRef {
                correlation,
                field,
                index,
                ..
            } => {
                let attr = self.correlated_attribute(path, correlation, *index, field)?;
                Some(FormalFunctionTerm::Attribute {
                    name: attr.name,
                    ty: attr.formal_ty,
                })
            }
            ScalarAst::Literal { raw } => {
                if literal_requires_external_encoding(raw) {
                    self.warning(
                        path,
                        "value_encoding_required",
                        "Lowered SQL literal requires a typed FormalSQL Tuple.value encoding in Rocq.",
                    );
                }
                Some(FormalFunctionTerm::Constant {
                    raw: raw.clone(),
                    ty: None,
                })
            }
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_date(ty) => self
                .lower_temporal_type_annotation(path, expr, ty, scope, FormalAttributeType::Date),
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_time(ty) => self
                .lower_temporal_type_annotation(path, expr, ty, scope, FormalAttributeType::Time),
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_timestamp_tz(ty) => {
                let raw = typed_literal_raw(expr)
                    .or_else(|| cast_literal_raw(expr))
                    .or_else(|| {
                        self.error(
                            path,
                            "timestamp_tz_literal_not_supported",
                            "TIMESTAMP WITH TIME ZONE annotations are supported only for literal CAST/typed literals.",
                        );
                        None
                })?;
                let precision = type_annotation_precision(ty);
                if is_null_literal(raw) {
                    return Some(FormalFunctionTerm::Constant {
                        raw: raw.to_owned(),
                        ty: Some(FormalAttributeType::Timestamptz { precision }),
                    });
                }
                let Some(micros) = super::emit::timestamptz_literal_to_utc_micros(
                    raw,
                    timestamp_precision(precision),
                    &self.config.sql_time_zone,
                ) else {
                    self.error(
                            path,
                            "timestamp_tz_literal_not_supported",
                            "TIMESTAMP WITH TIME ZONE literal could not be encoded as a UTC instant with the configured SQL time zone.",
                        );
                    return None;
                };
                Some(FormalFunctionTerm::Constant {
                    raw: micros.to_string(),
                    ty: Some(FormalAttributeType::Timestamptz { precision }),
                })
            }
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_timestamp(ty) => self
                .lower_temporal_type_annotation(
                    path,
                    expr,
                    ty,
                    scope,
                    FormalAttributeType::Timestamp {
                        precision: type_annotation_precision(ty),
                    },
                ),
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_interval(ty) => {
                let raw = typed_literal_raw(expr).or_else(|| {
                    self.error(
                        path,
                        "interval_literal_not_supported",
                        "INTERVAL annotations are supported only for numeric literal values.",
                    );
                    None
                })?;
                let interval = parse_interval_literal(raw, ty).or_else(|| {
                    self.error(
                        path,
                        "interval_literal_not_supported",
                        "INTERVAL literal could not be encoded for FormalSQL DATE arithmetic.",
                    );
                    None
                })?;
                Some(FormalFunctionTerm::Constant {
                    raw: interval.to_string(),
                    ty: Some(FormalAttributeType::Z),
                })
            }
            ScalarAst::TypeAnnotation { expr, ty } => {
                if type_annotation_is_decimal(ty) && formal_type_from_annotation(ty).is_none() {
                    self.error(
                        path,
                        "decimal_typmod_not_supported",
                        "FormalSQL DECIMAL lowering supports PostgreSQL DECIMAL(p,s) for 1 <= p <= 1000 and 0 <= s <= 1000; negative scales are not modeled yet.",
                    );
                    return None;
                }
                if let (Some(raw), Some(formal_ty)) =
                    (typed_literal_raw(expr), formal_type_from_annotation(ty))
                {
                    if matches!(
                        formal_ty,
                        FormalAttributeType::Float | FormalAttributeType::Double
                    ) && !raw.eq_ignore_ascii_case("null")
                        && super::emit::float_literal_bits_for_type(raw, Some(&formal_ty)).is_none()
                    {
                        self.error(
                            path,
                            "float_literal_not_supported",
                            "FormalSQL lowering supports FLOAT/DOUBLE literals only for finite SQL numeric literals that fit the target floating-point type.",
                        );
                        return None;
                    }
                    if matches!(formal_ty, FormalAttributeType::Decimal { .. })
                        && !raw.eq_ignore_ascii_case("null")
                        && super::emit::decimal_literal_for_type(raw, Some(&formal_ty)).is_none()
                    {
                        self.error(
                            path,
                            "decimal_literal_not_supported",
                            "FormalSQL DECIMAL lowering supports PostgreSQL-style fixed-scale decimal literals only when coercion to DECIMAL(p,s) succeeds without precision overflow.",
                        );
                        return None;
                    }
                    if let FormalAttributeType::Timestamp { precision }
                    | FormalAttributeType::Timestamptz { precision } = formal_ty
                    {
                        if !super::emit::timestamp_literal_conforms_to_precision(
                            raw,
                            timestamp_precision(precision),
                        ) {
                            self.error(
                                path,
                                "timestamp_precision_not_supported",
                                "TIMESTAMP literal has more fractional precision than its annotated SQL precision.",
                            );
                            return None;
                        }
                    }
                    return Some(FormalFunctionTerm::Constant {
                        raw: raw.to_owned(),
                        ty: Some(formal_ty),
                    });
                }
                if let Some(formal_ty) = formal_type_from_annotation(ty)
                    && is_float_type(formal_ty)
                {
                    self.validate_floating_expression_annotation(path, expr, formal_ty, scope)?;
                }
                if let Some(FormalAttributeType::Decimal { .. }) = formal_type_from_annotation(ty) {
                    if let Some(args) = decimal_division_cast_args(expr)
                        && args.len() == 2
                        && self.decimal_binary_args(&format!("{path}.decimalArgs"), args, scope)
                    {
                        return self.lower_decimal_division_function_term(
                            path,
                            args,
                            scope,
                            explicit_decimal_annotation_type(ty),
                        );
                    }
                    if let Some(cast_arg) = cast_arg(expr) {
                        let target_ty = formal_type_from_annotation(ty).or_else(|| {
                            self.error(
                                path,
                                "cast_target_type_not_supported",
                                "FormalSQL lowering cannot infer the target type of this explicit CAST.",
                            );
                            None
                        })?;
                        let source_ty = self
                            .infer_cast_operand_type(&format!("{path}.castArg"), cast_arg, scope)
                            .or_else(|| {
                                self.error(
                                    path,
                                    "cast_source_type_not_supported",
                                    "FormalSQL lowering cannot infer the source type of this explicit CAST.",
                                );
                                None
                            })?;
                        if source_ty == target_ty {
                            return self.lower_function_term(
                                &format!("{path}.castArg"),
                                cast_arg,
                                scope,
                            );
                        }
                        if let Some(function) = decimal_typmod_cast_function(&source_ty, &target_ty)
                        {
                            return self.lower_decimal_cast_function_term(
                                &format!("{path}.castArg"),
                                cast_arg,
                                function,
                                target_ty,
                                scope,
                            );
                        }
                    }
                }
                if matches!(
                    formal_type_from_annotation(ty),
                    Some(FormalAttributeType::Decimal { .. })
                ) {
                    self.error(
                        path,
                        "decimal_expression_not_supported",
                        "DECIMAL expression annotation is supported only for fixed-scale literals, no-op casts, or explicitly cast Decimal division.",
                    );
                    return None;
                }
                self.lower_function_term(path, expr, scope)
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && args.len() == 2
                    && self.decimal_binary_args(&format!("{path}.decimalArgs"), args, scope) =>
            {
                let symbol = match op {
                    ScalarOp::Plus => "plus_decimal",
                    ScalarOp::Minus => "minus_decimal",
                    ScalarOp::Multiply => "mult_decimal",
                    _ => unreachable!("decimal arithmetic guard checked"),
                };
                Some(FormalFunctionTerm::Function {
                    symbol: symbol.to_owned(),
                    args: args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(
                    op,
                    ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
                ) && args.len() == 2
                    && self
                        .homogeneous_float_binary_type(&format!("{path}.floatArgs"), args, scope)
                        .is_some() =>
            {
                let ty =
                    self.homogeneous_float_binary_type(&format!("{path}.floatArgs"), args, scope)?;
                Some(FormalFunctionTerm::Function {
                    symbol: floating_function_symbol(op, ty)?.to_owned(),
                    args: args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(
                    op,
                    ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
                ) && self.has_float_argument(&format!("{path}.floatArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "floating_mixed_arithmetic_not_supported",
                    "FLOAT/DOUBLE arithmetic is lowered only when all operands have the same modeled floating type.",
                );
                None
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1
                && self
                    .direct_function_type(&format!("{path}.argType"), &args[0], scope)
                    .is_some_and(is_float_type) =>
            {
                let ty = self.direct_function_type(&format!("{path}.argType"), &args[0], scope)?;
                Some(FormalFunctionTerm::Function {
                    symbol: floating_unary_minus_symbol(ty)?.to_owned(),
                    args: vec![self.lower_function_term(
                        &format!("{path}.arg"),
                        &args[0],
                        scope,
                    )?],
                })
            }
            ScalarAst::Call { op, args, .. }
                if is_comparison_predicate(op)
                    && self.floating_comparison_args_mismatch(
                        &format!("{path}.floatArgs"),
                        args,
                        scope,
                    ) =>
            {
                self.error(
                    path,
                    "floating_comparison_value_not_supported",
                    "FLOAT/DOUBLE comparisons in value context are lowered only when both operands have the same modeled floating type.",
                );
                None
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && self.has_decimal_argument(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "decimal_mixed_arithmetic_not_supported",
                    "Decimal arithmetic is lowered only when all operands are known DECIMAL values.",
                );
                None
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1 && self.decimal_unary_arg(path, &args[0], scope) => {
                Some(FormalFunctionTerm::Function {
                    symbol: "opp_decimal".to_owned(),
                    args: vec![self.lower_function_term(
                        &format!("{path}.arg"),
                        &args[0],
                        scope,
                    )?],
                })
            }
            ScalarAst::Call {
                op: ScalarOp::Divide,
                args,
                ..
            } if args.len() == 2
                && self.decimal_binary_args(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.lower_decimal_division_function_term(path, args, scope, None)
            }
            ScalarAst::Call {
                op: ScalarOp::Divide,
                args,
                ..
            } if args.len() == 2
                && self.has_decimal_argument(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "decimal_mixed_arithmetic_not_supported",
                    "Decimal division is lowered only when both operands are known DECIMAL values.",
                );
                None
            }
            ScalarAst::Call { op, args, .. }
                if is_function_term_function(op)
                    && self.has_decimal_argument(&format!("{path}.decimalArgs"), args, scope) =>
            {
                self.error(
                    path,
                    "decimal_function_not_supported",
                    "This DECIMAL-valued scalar function is outside the currently modeled FormalSQL Decimal subset.",
                );
                None
            }
            ScalarAst::Call { op, args, .. } if is_function_term_function(op) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)
                    })
                    .collect::<Option<Vec<_>>>()?;
                if function_requires_external_interpretation(op) {
                    self.warning(
                        path,
                        "function_symbol_interpretation_required",
                        "Lowered SQL scalar function requires a matching FormalSQL Tuple.symbol interpretation in Rocq.",
                    );
                }
                Some(FormalFunctionTerm::Function {
                    symbol: function_symbol(op),
                    args,
                })
            }
            ScalarAst::Call {
                op: ScalarOp::In, ..
            } => {
                // TODO: Support boolean-valued IN in SELECT/projection expressions.
                // Predicate-context IN is lowered by `lower_formula`; SELECT-list IN needs a
                // value-level encoding of SQL's three-valued boolean result.
                self.error(
                    path,
                    "select_in_not_supported",
                    "IN predicates in SELECT expressions require boolean-valued predicate lowering.",
                );
                None
            }
            ScalarAst::Sarg { .. }
            | ScalarAst::Window { .. }
            | ScalarAst::RelSubquery { .. }
            | ScalarAst::Flag { .. }
            | ScalarAst::Call { .. } => {
                self.error(
                    path,
                    "function_term_not_supported",
                    "Scalar AST cannot be lowered to a FormalSQL function term.",
                );
                None
            }
        }
    }

    fn lower_interval_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        op: &ScalarOp,
    ) -> Option<FormalAggregateTerm> {
        let ScalarAst::TypeAnnotation { expr, ty } = ast else {
            self.error(
                path,
                "interval_literal_not_supported",
                "Temporal arithmetic currently requires an explicitly typed Calcite INTERVAL literal.",
            );
            return None;
        };
        let raw = typed_literal_raw(expr).or_else(|| {
            self.error(
                path,
                "interval_literal_not_supported",
                "INTERVAL annotations are supported only for numeric literal values.",
            );
            None
        })?;
        let mut interval = parse_interval_literal(raw, ty).or_else(|| {
            self.error(
                path,
                "interval_literal_not_supported",
                "INTERVAL literal could not be encoded for FormalSQL DATE arithmetic.",
            );
            None
        })?;
        if matches!(op, ScalarOp::Minus) {
            interval = -interval;
        }
        Some(FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant {
                raw: interval.to_string(),
                ty: Some(FormalAttributeType::Z),
            },
        })
    }

    fn lower_temporal_type_annotation(
        &mut self,
        path: &str,
        expr: &ScalarAst,
        ty: &str,
        scope: &Scope,
        target_ty: FormalAttributeType,
    ) -> Option<FormalFunctionTerm> {
        if let Some(raw) = typed_literal_raw(expr).or_else(|| cast_literal_raw(expr)) {
            return self.lower_temporal_constant(path, raw, target_ty);
        }

        if let Some(cast_arg) = cast_arg(expr) {
            let source_ty = self
                .infer_cast_operand_type(&format!("{path}.castArg"), cast_arg, scope)
                .or_else(|| {
                    self.error(
                        path,
                        "cast_source_type_not_supported",
                        "FormalSQL lowering cannot infer the source type of this explicit CAST.",
                    );
                    None
                })?;
            let function = temporal_cast_function(&source_ty, &target_ty).or_else(|| {
                self.error(
                    path,
                    "cast_not_supported",
                    &format!(
                        "Explicit CAST from {source_ty:?} to {target_ty:?} is not in the FormalSQL temporal cast whitelist.",
                    ),
                );
                None
            })?;
            let arg = self.lower_function_term(&format!("{path}.castArg"), cast_arg, scope)?;
            return Some(FormalFunctionTerm::Cast {
                function: function.to_owned(),
                arg: Box::new(arg),
                ty: target_ty,
            });
        }

        self.error(
            path,
            "temporal_annotation_not_supported",
            &format!("{ty} annotations are supported only for typed literals or explicit CAST expressions."),
        );
        None
    }

    fn lower_temporal_constant(
        &mut self,
        path: &str,
        raw: &str,
        target_ty: FormalAttributeType,
    ) -> Option<FormalFunctionTerm> {
        match target_ty {
            FormalAttributeType::Date => Some(FormalFunctionTerm::Constant {
                raw: raw.to_owned(),
                ty: Some(FormalAttributeType::Date),
            }),
            FormalAttributeType::Time => {
                if !is_null_literal(raw) && !super::emit::time_literal_conforms_to_day(raw) {
                    self.error(
                        path,
                        "time_literal_not_supported",
                        "TIME literal must be a valid time-of-day with at most microsecond precision.",
                    );
                    return None;
                }
                Some(FormalFunctionTerm::Constant {
                    raw: raw.to_owned(),
                    ty: Some(FormalAttributeType::Time),
                })
            }
            FormalAttributeType::Timestamp { precision } => {
                if !is_null_literal(raw)
                    && !super::emit::timestamp_literal_conforms_to_precision(
                        raw,
                        timestamp_precision(precision),
                    )
                {
                    self.error(
                        path,
                        "timestamp_precision_not_supported",
                        "TIMESTAMP literal has more fractional precision than its annotated SQL precision.",
                    );
                    return None;
                }
                Some(FormalFunctionTerm::Constant {
                    raw: raw.to_owned(),
                    ty: Some(FormalAttributeType::Timestamp { precision }),
                })
            }
            _ => {
                self.error(
                    path,
                    "temporal_constant_type_not_supported",
                    "This temporal constant target type is not supported by the explicit CAST whitelist.",
                );
                None
            }
        }
    }

    pub(super) fn infer_function_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        if let Some(ty) = self.direct_function_type(path, ast, scope) {
            return Some(ty);
        }
        match ast {
            ScalarAst::InputRef { index } => Some(scope.attribute(*index)?.formal_ty),
            ScalarAst::CorrelatedRef {
                correlation,
                field,
                index,
                ..
            } => Some(
                self.correlated_attribute(path, correlation, *index, field)?
                    .formal_ty,
            ),
            ScalarAst::TypeAnnotation { ty, .. } => formal_type_from_annotation(ty),
            ScalarAst::Literal { .. } => None,
            ScalarAst::Call { op, .. } => {
                if let Some(ty) = self.infer_call_type(path, op, ast, scope) {
                    return Some(ty);
                }
                self.error(
                    path,
                    "cast_source_expression_not_supported",
                    &format!(
                        "Cannot infer the result type of scalar operator {op:?} for CAST lowering."
                    ),
                );
                None
            }
            ScalarAst::Flag { .. }
            | ScalarAst::Window { .. }
            | ScalarAst::RelSubquery { .. }
            | ScalarAst::Sarg { .. } => None,
        }
    }

    fn infer_call_type(
        &mut self,
        path: &str,
        op: &ScalarOp,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        let ScalarAst::Call { args, .. } = ast else {
            return None;
        };
        match op {
            ScalarOp::Cast if args.len() == 1 => self.infer_cast_operand_type(
                &format!("{path}.castArg"),
                args.first().expect("CAST arity checked"),
                scope,
            ),
            ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide => {
                self.infer_arithmetic_type(path, op, args, scope)
            }
            ScalarOp::Power => self.infer_power_type(path, args, scope),
            ScalarOp::Case => self.infer_case_type(path, args, scope),
            op if is_boolean_value_function(op) => Some(FormalAttributeType::Bool),
            _ => None,
        }
    }

    fn infer_arithmetic_type(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        match args {
            [arg] if matches!(op, ScalarOp::Minus) => {
                let ty = self.infer_function_type(&format!("{path}.arg"), arg, scope)?;
                is_numeric_type(ty).then_some(ty)
            }
            [left, right] => {
                let left_ty =
                    self.infer_numeric_operand_type(&format!("{path}.left"), left, scope)?;
                let right_ty =
                    self.infer_numeric_operand_type(&format!("{path}.right"), right, scope)?;
                if left_ty == FormalAttributeType::Z && right_ty == FormalAttributeType::Z {
                    return Some(FormalAttributeType::Z);
                }
                if is_float_type(left_ty) || is_float_type(right_ty) {
                    return (left_ty == right_ty && is_float_type(left_ty)).then_some(left_ty);
                }
                if matches!(
                    (left_ty, right_ty),
                    (
                        FormalAttributeType::Decimal { .. },
                        FormalAttributeType::Decimal { .. }
                    )
                ) {
                    if matches!(op, ScalarOp::Divide) {
                        return None;
                    }
                    return decimal_binary_result_type(op, &left_ty, &right_ty);
                }
                None
            }
            _ => None,
        }
    }

    fn infer_power_type(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        let [left, right] = args else {
            return None;
        };
        let left_ty = self.infer_numeric_operand_type(&format!("{path}.left"), left, scope)?;
        let right_ty = self.infer_numeric_operand_type(&format!("{path}.right"), right, scope)?;
        if left_ty == FormalAttributeType::Double && right_ty == FormalAttributeType::Double {
            Some(FormalAttributeType::Double)
        } else {
            None
        }
    }

    fn infer_case_type(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        if args.len() < 3 || args.len() % 2 == 0 {
            return None;
        }
        let mut result_ty = None;
        for (branch_index, pair) in args[..args.len() - 1].chunks_exact(2).enumerate() {
            let branch_ty = self.infer_case_result_operand_type(
                &format!("{path}.branches[{branch_index}].then"),
                &pair[1],
                scope,
            );
            result_ty = merge_case_result_type(result_ty, branch_ty)?;
        }
        merge_case_result_type(
            result_ty,
            self.infer_case_result_operand_type(
                &format!("{path}.else"),
                args.last().expect("CASE arity checked"),
                scope,
            ),
        )?
    }

    fn infer_numeric_operand_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        self.infer_function_type(path, ast, scope)
            .or_else(|| match ast {
                ScalarAst::Literal { raw } => infer_untyped_integer_literal_type(raw),
                _ => None,
            })
    }

    fn infer_cast_operand_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        self.infer_function_type(path, ast, scope)
            .or_else(|| match ast {
                ScalarAst::Literal { raw } => infer_literal_cast_source_type(raw),
                _ => None,
            })
    }

    fn infer_case_result_operand_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        self.infer_function_type(path, ast, scope)
            .or_else(|| match ast {
                ScalarAst::Literal { raw } => infer_literal_cast_source_type(raw),
                _ => None,
            })
    }
}

struct DateIntervalFunction<'a> {
    symbol: String,
    date_arg: &'a ScalarAst,
    interval_arg: &'a ScalarAst,
}

struct TimestampIntervalFunction<'a> {
    symbol: String,
    timestamp_arg: &'a ScalarAst,
    interval_arg: &'a ScalarAst,
}

fn timestamp_interval_function<'a>(
    op: &ScalarOp,
    left: &'a ScalarAst,
    right: &'a ScalarAst,
) -> Option<TimestampIntervalFunction<'a>> {
    let (timestamp_arg, interval_arg) =
        if type_annotation_is_timestamp_ast(left) && type_annotation_is_interval_ast(right) {
            (left, right)
        } else if matches!(op, ScalarOp::Plus)
            && type_annotation_is_interval_ast(left)
            && type_annotation_is_timestamp_ast(right)
        {
            (right, left)
        } else {
            return None;
        };
    let ScalarAst::TypeAnnotation { ty, .. } = interval_arg else {
        return None;
    };
    let unit = interval_unit(ty)?;
    let symbol = match unit {
        "MICROSECOND" => "timestamp_add_microseconds",
        "SECOND" => "timestamp_add_seconds",
        "MINUTE" => "timestamp_add_minutes",
        "HOUR" => "timestamp_add_hours",
        "DAY" => "timestamp_add_days",
        "MONTH" => "timestamp_add_months",
        "YEAR" => "timestamp_add_years",
        _ => return None,
    };
    Some(TimestampIntervalFunction {
        symbol: symbol.to_owned(),
        timestamp_arg,
        interval_arg,
    })
}

fn date_interval_function<'a>(
    op: &ScalarOp,
    left: &'a ScalarAst,
    right: &'a ScalarAst,
) -> Option<DateIntervalFunction<'a>> {
    let (date_arg, interval_arg) =
        if type_annotation_is_date_ast(left) && type_annotation_is_interval_ast(right) {
            (left, right)
        } else if matches!(op, ScalarOp::Plus)
            && type_annotation_is_interval_ast(left)
            && type_annotation_is_date_ast(right)
        {
            (right, left)
        } else {
            return None;
        };
    let ScalarAst::TypeAnnotation { ty, .. } = interval_arg else {
        return None;
    };
    let unit = interval_unit(ty)?;
    let symbol = match unit {
        "DAY" => "date_add_days",
        "MONTH" => "date_add_months",
        "YEAR" => "date_add_years",
        _ => return None,
    };
    Some(DateIntervalFunction {
        symbol: symbol.to_owned(),
        date_arg,
        interval_arg,
    })
}

fn type_annotation_is_date_ast(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_date(ty))
}

fn type_annotation_is_timestamp_ast(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_timestamp(ty))
}

fn type_annotation_is_temporal_instant_ast(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_timestamp(ty) || type_annotation_is_timestamp_tz(ty))
}

fn type_annotation_is_interval_ast(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_interval(ty))
}

fn has_temporal_interval_pair(left: &ScalarAst, right: &ScalarAst) -> bool {
    (type_annotation_is_date_ast(left)
        || type_annotation_is_temporal_instant_ast(left)
        || type_annotation_is_interval_ast(left))
        && (type_annotation_is_date_ast(right)
            || type_annotation_is_temporal_instant_ast(right)
            || type_annotation_is_interval_ast(right))
        && (type_annotation_is_interval_ast(left) || type_annotation_is_interval_ast(right))
}

fn type_annotation_is_date(ty: &str) -> bool {
    type_annotation_head(ty) == Some("DATE")
}

fn type_annotation_is_timestamp(ty: &str) -> bool {
    type_annotation_head(ty) == Some("TIMESTAMP")
}

fn type_annotation_is_timestamp_tz(ty: &str) -> bool {
    type_annotation_head(ty) == Some("TIMESTAMP_WITH_TIME_ZONE")
}

fn type_annotation_is_interval(ty: &str) -> bool {
    ty.trim().to_ascii_uppercase().starts_with("INTERVAL")
}

fn type_annotation_is_time(ty: &str) -> bool {
    type_annotation_head(ty) == Some("TIME")
}

fn type_annotation_is_decimal(ty: &str) -> bool {
    matches!(type_annotation_head(ty), Some("DECIMAL" | "NUMERIC"))
}

fn formal_type_from_annotation(ty: &str) -> Option<FormalAttributeType> {
    let head = type_annotation_head(ty)?;
    match head {
        "INTEGER" | "INT" | "BIGINT" | "SMALLINT" | "TINYINT" => Some(FormalAttributeType::Z),
        "REAL" | "FLOAT4" => Some(FormalAttributeType::Float),
        "FLOAT" => float_type_from_precision(type_annotation_precision(ty)),
        "DOUBLE" | "FLOAT8" => Some(FormalAttributeType::Double),
        "DECIMAL" | "NUMERIC" => {
            let (precision, scale) = decimal_annotation_typmod(ty)?;
            Some(FormalAttributeType::Decimal { precision, scale })
        }
        "VARCHAR" | "CHAR" | "STRING" => Some(FormalAttributeType::String),
        "BOOLEAN" | "BOOL" => Some(FormalAttributeType::Bool),
        "DATE" => Some(FormalAttributeType::Date),
        "TIME" => Some(FormalAttributeType::Time),
        "TIMESTAMP" => Some(FormalAttributeType::Timestamp {
            precision: type_annotation_precision(ty),
        }),
        "TIMESTAMP_WITH_TIME_ZONE" => Some(FormalAttributeType::Timestamptz {
            precision: type_annotation_precision(ty),
        }),
        _ => None,
    }
}

fn float_type_from_precision(precision: Option<u32>) -> Option<FormalAttributeType> {
    match precision {
        None => Some(FormalAttributeType::Double),
        Some(1..=24) => Some(FormalAttributeType::Float),
        Some(25..=53) => Some(FormalAttributeType::Double),
        Some(_) => None,
    }
}

fn decimal_type_scale(ty: &FormalAttributeType) -> Option<u32> {
    match ty {
        FormalAttributeType::Decimal { scale, .. } => *scale,
        _ => None,
    }
}

fn decimal_type_precision(ty: &FormalAttributeType) -> Option<u32> {
    match ty {
        FormalAttributeType::Decimal { precision, .. } => *precision,
        _ => None,
    }
}

fn decimal_divisor_is_static_nonzero(ast: &ScalarAst) -> bool {
    let (raw, ty) = match ast {
        ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_decimal(ty) => {
            let Some(raw) = typed_literal_raw(expr) else {
                return false;
            };
            let Some(ty) = formal_type_from_annotation(ty) else {
                return false;
            };
            (raw, ty)
        }
        _ => return false,
    };
    super::emit::decimal_literal_for_type(raw, Some(&ty))
        .is_some_and(|(coeff, _, _)| coeff.parse::<i128>().is_ok_and(|value| value != 0))
}

fn explicit_decimal_annotation_type(ty: &str) -> Option<FormalAttributeType> {
    if !type_annotation_is_decimal(ty) {
        return None;
    }
    let formal_ty = formal_type_from_annotation(ty)?;
    match formal_ty {
        FormalAttributeType::Decimal {
            precision: Some(_),
            scale: Some(_),
        } => Some(formal_ty),
        _ => None,
    }
}

fn decimal_typmod_cast_function(
    source: &FormalAttributeType,
    target: &FormalAttributeType,
) -> Option<&'static str> {
    match (source, target) {
        (
            FormalAttributeType::Decimal { .. },
            FormalAttributeType::Decimal {
                precision: Some(_),
                scale: Some(_),
            },
        ) => Some("cast_decimal_typmod"),
        (
            FormalAttributeType::Z,
            FormalAttributeType::Decimal {
                precision: Some(_),
                scale: Some(_),
            },
        ) => Some("cast_z_to_decimal_typmod"),
        _ => None,
    }
}

fn decimal_annotation_typmod(ty: &str) -> Option<(Option<u32>, Option<u32>)> {
    let args = type_annotation_arg_strings(ty)?;
    match args.as_slice() {
        [] => None,
        [precision] => {
            let precision = parse_decimal_typmod_part(precision)?;
            if precision == 0 || precision > 1000 {
                return None;
            }
            Some((Some(precision), Some(0)))
        }
        [precision, scale] => {
            let precision = parse_decimal_typmod_part(precision)?;
            let scale = parse_decimal_typmod_part(scale)?;
            if precision == 0 || precision > 1000 || scale > 1000 {
                return None;
            }
            Some((Some(precision), Some(scale)))
        }
        _ => None,
    }
}

fn decimal_division_cast_args(expr: &ScalarAst) -> Option<&[ScalarAst]> {
    match expr {
        ScalarAst::Call {
            op: ScalarOp::Divide,
            args,
            ..
        } => Some(args),
        other => cast_arg(other).and_then(decimal_division_cast_args),
    }
}

fn decimal_binary_result_scale(
    op: &ScalarOp,
    left_ty: &FormalAttributeType,
    right_ty: &FormalAttributeType,
) -> Option<u32> {
    let left = decimal_type_scale(left_ty)?;
    let right = decimal_type_scale(right_ty)?;
    match op {
        ScalarOp::Plus | ScalarOp::Minus => Some(left.max(right)),
        ScalarOp::Multiply => left.checked_add(right),
        _ => None,
    }
}

fn decimal_binary_result_type(
    op: &ScalarOp,
    left_ty: &FormalAttributeType,
    right_ty: &FormalAttributeType,
) -> Option<FormalAttributeType> {
    let left_precision = decimal_type_precision(left_ty)?;
    let right_precision = decimal_type_precision(right_ty)?;
    let result_scale = decimal_binary_result_scale(op, left_ty, right_ty)?;
    let result_precision = match op {
        ScalarOp::Plus | ScalarOp::Minus => {
            let left_integral = left_precision.checked_sub(decimal_type_scale(left_ty)?)?;
            let right_integral = right_precision.checked_sub(decimal_type_scale(right_ty)?)?;
            left_integral
                .max(right_integral)
                .checked_add(1)?
                .checked_add(result_scale)?
        }
        ScalarOp::Multiply => left_precision.checked_add(right_precision)?,
        _ => return None,
    };
    if result_precision == 0 || result_precision > 1000 || result_scale > 1000 {
        return None;
    }
    Some(FormalAttributeType::Decimal {
        precision: Some(result_precision),
        scale: Some(result_scale),
    })
}

fn infer_untyped_integer_literal_type(raw: &str) -> Option<FormalAttributeType> {
    let raw = raw.trim();
    if is_null_literal(raw) {
        return None;
    }
    if raw.parse::<i64>().is_ok() {
        return Some(FormalAttributeType::Z);
    }
    None
}

fn infer_literal_cast_source_type(raw: &str) -> Option<FormalAttributeType> {
    let raw = raw.trim();
    if is_null_literal(raw) {
        return None;
    }
    if raw.starts_with('\'') && raw.ends_with('\'') {
        return Some(FormalAttributeType::String);
    }
    if raw.eq_ignore_ascii_case("true") || raw.eq_ignore_ascii_case("false") {
        return Some(FormalAttributeType::Bool);
    }
    infer_untyped_integer_literal_type(raw)
}

fn merge_case_result_type(
    current: Option<FormalAttributeType>,
    next: Option<FormalAttributeType>,
) -> Option<Option<FormalAttributeType>> {
    match (current, next) {
        (None, ty) | (ty, None) => Some(ty),
        (Some(left), Some(right)) if left == right => Some(Some(left)),
        _ => None,
    }
}

fn annotate_case_literal_term(
    term: FormalAggregateTerm,
    result_ty: Option<FormalAttributeType>,
) -> FormalAggregateTerm {
    match result_ty {
        Some(ty) => annotate_literal_term(term, ty),
        None => term,
    }
}

fn decimal_division_precision_is_safe(
    left_ty: &FormalAttributeType,
    right_ty: &FormalAttributeType,
    result_ty: &FormalAttributeType,
) -> bool {
    let Some(digit_count) = decimal_division_integral_digit_bound(left_ty, right_ty) else {
        return false;
    };
    let Some(result_integral_digits) = decimal_type_integral_digits(result_ty) else {
        return false;
    };
    digit_count <= result_integral_digits
}

fn decimal_division_integral_digit_bound(
    left_ty: &FormalAttributeType,
    right_ty: &FormalAttributeType,
) -> Option<i64> {
    let p1 = i64::from(decimal_type_precision(left_ty)?);
    let s1 = i64::from(decimal_type_scale(left_ty)?);
    let s2 = i64::from(decimal_type_scale(right_ty)?);
    Some(p1 - s1 + s2)
}

fn decimal_type_integral_digits(ty: &FormalAttributeType) -> Option<i64> {
    let precision = i64::from(decimal_type_precision(ty)?);
    let scale = i64::from(decimal_type_scale(ty)?);
    Some(precision - scale)
}

fn z_constant_aggregate(value: u32) -> FormalAggregateTerm {
    FormalAggregateTerm::Expr {
        term: z_constant_function(value),
    }
}

fn z_constant_function(value: u32) -> FormalFunctionTerm {
    FormalFunctionTerm::Constant {
        raw: value.to_string(),
        ty: Some(FormalAttributeType::Z),
    }
}

fn temporal_cast_function(
    source: &FormalAttributeType,
    target: &FormalAttributeType,
) -> Option<&'static str> {
    if source == target {
        return Some("cast_identity");
    }
    match (source, target) {
        (FormalAttributeType::Date, FormalAttributeType::Timestamp { .. }) => {
            Some("cast_date_to_timestamp")
        }
        (FormalAttributeType::Timestamp { .. }, FormalAttributeType::Date) => {
            Some("cast_timestamp_to_date")
        }
        _ => None,
    }
}

fn type_annotation_precision(ty: &str) -> Option<u32> {
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    ty[start..end].split(',').next()?.trim().parse().ok()
}

fn type_annotation_arg_strings(ty: &str) -> Option<Vec<&str>> {
    let has_open = ty.contains('(');
    let has_close = ty.contains(')');
    if !has_open && !has_close {
        return Some(Vec::new());
    }
    if !has_open || !has_close {
        return None;
    }
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    let trailing = ty[end + 1..].trim();
    if !trailing.is_empty() {
        return None;
    }
    let args = ty[start..end].split(',').map(str::trim).collect::<Vec<_>>();
    if args.iter().any(|arg| arg.is_empty()) {
        return None;
    }
    Some(args)
}

fn parse_decimal_typmod_part(raw: &str) -> Option<u32> {
    if raw.starts_with(['+', '-']) {
        return None;
    }
    raw.parse().ok()
}

fn type_annotation_head(ty: &str) -> Option<&'static str> {
    let upper = ty.trim().to_ascii_uppercase();
    let head = upper
        .split(|c: char| c.is_ascii_whitespace() || c == '(')
        .next()?;
    match head {
        "INTEGER" => Some("INTEGER"),
        "INT" => Some("INT"),
        "BIGINT" => Some("BIGINT"),
        "SMALLINT" => Some("SMALLINT"),
        "TINYINT" => Some("TINYINT"),
        "FLOAT" => Some("FLOAT"),
        "REAL" => Some("REAL"),
        "FLOAT4" => Some("FLOAT4"),
        "DOUBLE" => Some("DOUBLE"),
        "FLOAT8" => Some("FLOAT8"),
        "DECIMAL" => Some("DECIMAL"),
        "NUMERIC" => Some("NUMERIC"),
        "VARCHAR" => Some("VARCHAR"),
        "CHAR" => Some("CHAR"),
        "STRING" => Some("STRING"),
        "BOOLEAN" => Some("BOOLEAN"),
        "BOOL" => Some("BOOL"),
        "DATE" => Some("DATE"),
        "TIME" => Some("TIME"),
        "TIMESTAMP" => Some("TIMESTAMP"),
        "TIMESTAMPTZ"
        | "TIMESTAMPZ"
        | "TIMESTAMP_WITH_TIME_ZONE"
        | "TIMESTAMP_WITH_LOCAL_TIME_ZONE" => Some("TIMESTAMP_WITH_TIME_ZONE"),
        _ => None,
    }
}

fn interval_unit(ty: &str) -> Option<&'static str> {
    let upper = ty.trim().to_ascii_uppercase();
    if upper.contains("MICROSECOND") {
        Some("MICROSECOND")
    } else if upper.contains("SECOND") {
        Some("SECOND")
    } else if upper.contains("MINUTE") {
        Some("MINUTE")
    } else if upper.contains("HOUR") {
        Some("HOUR")
    } else if upper.contains("DAY") {
        Some("DAY")
    } else if upper.contains("MONTH") {
        Some("MONTH")
    } else if upper.contains("YEAR") {
        Some("YEAR")
    } else {
        None
    }
}

fn typed_literal_raw(ast: &ScalarAst) -> Option<&str> {
    match ast {
        ScalarAst::Literal { raw } => Some(raw),
        _ => None,
    }
}

fn is_null_literal(raw: &str) -> bool {
    raw.trim().eq_ignore_ascii_case("null")
}

fn cast_literal_raw(ast: &ScalarAst) -> Option<&str> {
    match ast {
        ScalarAst::Call {
            op: ScalarOp::Cast,
            args,
            ..
        } if args.len() == 1 => typed_literal_raw(&args[0]),
        _ => None,
    }
}

fn cast_arg(ast: &ScalarAst) -> Option<&ScalarAst> {
    match ast {
        ScalarAst::Call {
            op: ScalarOp::Cast,
            args,
            ..
        } if args.len() == 1 => args.first(),
        _ => None,
    }
}

fn parse_interval_literal(raw: &str, ty: &str) -> Option<i64> {
    let value = raw.trim().parse::<i64>().ok()?;
    match interval_unit(ty)? {
        "MICROSECOND" | "SECOND" | "MINUTE" | "HOUR" | "DAY" | "MONTH" | "YEAR" => Some(value),
        _ => None,
    }
}

fn is_function_term_function(op: &ScalarOp) -> bool {
    matches!(
        op,
        &ScalarOp::Plus
            | &ScalarOp::Minus
            | &ScalarOp::Multiply
            | &ScalarOp::Divide
            | &ScalarOp::StringConcat
            | &ScalarOp::Cast
            | &ScalarOp::Lower
            | &ScalarOp::Upper
            | &ScalarOp::Substring
            | &ScalarOp::Exp
            | &ScalarOp::Power
            | &ScalarOp::Extract
            | &ScalarOp::Other(_)
    )
}

fn is_aggregate_term_function(op: &ScalarOp) -> bool {
    is_function_term_function(op) || is_boolean_value_function(op)
}

fn function_symbol(op: &ScalarOp) -> String {
    match op {
        ScalarOp::Eq => "=".to_owned(),
        ScalarOp::NotEq => "<>".to_owned(),
        ScalarOp::Lt => "<".to_owned(),
        ScalarOp::Lte => "<=".to_owned(),
        ScalarOp::Gt => ">".to_owned(),
        ScalarOp::Gte => ">=".to_owned(),
        ScalarOp::And => "and".to_owned(),
        ScalarOp::Or => "or".to_owned(),
        ScalarOp::Not => "not".to_owned(),
        ScalarOp::IsNull => "is_null".to_owned(),
        ScalarOp::IsNotNull => "is_not_null".to_owned(),
        ScalarOp::IsTrue => "is_true".to_owned(),
        ScalarOp::IsNotTrue => "is_not_true".to_owned(),
        ScalarOp::IsFalse => "is_false".to_owned(),
        ScalarOp::IsNotFalse => "is_not_false".to_owned(),
        ScalarOp::IsNotDistinctFrom => "is_not_distinct_from".to_owned(),
        ScalarOp::Plus => "plus".to_owned(),
        ScalarOp::Minus => "minus".to_owned(),
        ScalarOp::Multiply => "mult".to_owned(),
        ScalarOp::Divide => "divide".to_owned(),
        ScalarOp::StringConcat => "string_concat".to_owned(),
        ScalarOp::Cast => "cast".to_owned(),
        ScalarOp::Lower => "lower".to_owned(),
        ScalarOp::Upper => "upper".to_owned(),
        ScalarOp::Substring => "substring".to_owned(),
        ScalarOp::Exp => "exp".to_owned(),
        ScalarOp::Power => "power".to_owned(),
        ScalarOp::Extract => "extract".to_owned(),
        ScalarOp::Other(operator) => operator.clone(),
        _ => "unknown".to_owned(),
    }
}

fn is_boolean_value_function(op: &ScalarOp) -> bool {
    matches!(
        op,
        ScalarOp::Eq
            | ScalarOp::NotEq
            | ScalarOp::Lt
            | ScalarOp::Lte
            | ScalarOp::Gt
            | ScalarOp::Gte
            | ScalarOp::And
            | ScalarOp::Or
            | ScalarOp::Not
            | ScalarOp::IsNull
            | ScalarOp::IsNotNull
            | ScalarOp::IsTrue
            | ScalarOp::IsNotTrue
            | ScalarOp::IsFalse
            | ScalarOp::IsNotFalse
            | ScalarOp::IsNotDistinctFrom
    )
}

fn predicate_name(op: &ScalarOp) -> &'static str {
    match op {
        ScalarOp::Eq => "=",
        ScalarOp::NotEq => "<>",
        ScalarOp::Lt => "<",
        ScalarOp::Lte => "<=",
        ScalarOp::Gt => ">",
        ScalarOp::Gte => ">=",
        ScalarOp::IsNull => "is_null",
        ScalarOp::IsNotNull => "is_not_null",
        ScalarOp::IsTrue => "is_true",
        ScalarOp::IsNotTrue => "is_not_true",
        ScalarOp::IsFalse => "is_false",
        ScalarOp::IsNotFalse => "is_not_false",
        ScalarOp::IsNotDistinctFrom => "is_not_distinct_from",
        ScalarOp::Like => "like",
        _ => "unknown",
    }
}

fn is_order_predicate(op: &ScalarOp) -> bool {
    matches!(
        op,
        ScalarOp::Lt | ScalarOp::Lte | ScalarOp::Gt | ScalarOp::Gte
    )
}

fn is_comparison_predicate(op: &ScalarOp) -> bool {
    matches!(
        op,
        ScalarOp::Eq
            | ScalarOp::NotEq
            | ScalarOp::Lt
            | ScalarOp::Lte
            | ScalarOp::Gt
            | ScalarOp::Gte
            | ScalarOp::IsNotDistinctFrom
    )
}

fn is_float_type(ty: FormalAttributeType) -> bool {
    matches!(ty, FormalAttributeType::Float | FormalAttributeType::Double)
}

fn is_numeric_type(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Z
            | FormalAttributeType::Float
            | FormalAttributeType::Double
            | FormalAttributeType::Decimal { .. }
    )
}

fn is_floating_comparison_mismatch(
    left: Option<FormalAttributeType>,
    right: Option<FormalAttributeType>,
) -> bool {
    match (left, right) {
        (Some(left), Some(right)) if is_float_type(left) || is_float_type(right) => left != right,
        (Some(left), None) => is_float_type(left),
        (None, Some(right)) => is_float_type(right),
        _ => false,
    }
}

fn floating_function_symbol(op: &ScalarOp, ty: FormalAttributeType) -> Option<&'static str> {
    match (op, ty) {
        (ScalarOp::Plus, FormalAttributeType::Float) => Some("plus."),
        (ScalarOp::Minus, FormalAttributeType::Float) => Some("minus."),
        (ScalarOp::Multiply, FormalAttributeType::Float) => Some("mult."),
        (ScalarOp::Divide, FormalAttributeType::Float) => Some("divide."),
        (ScalarOp::Plus, FormalAttributeType::Double) => Some("plus_double"),
        (ScalarOp::Minus, FormalAttributeType::Double) => Some("minus_double"),
        (ScalarOp::Multiply, FormalAttributeType::Double) => Some("mult_double"),
        (ScalarOp::Divide, FormalAttributeType::Double) => Some("divide_double"),
        _ => None,
    }
}

fn floating_unary_minus_symbol(ty: FormalAttributeType) -> Option<&'static str> {
    match ty {
        FormalAttributeType::Float => Some("opp."),
        FormalAttributeType::Double => Some("opp_double"),
        _ => None,
    }
}

fn predicate_requires_external_interpretation(op: &ScalarOp) -> bool {
    !matches!(
        op,
        ScalarOp::Eq
            | ScalarOp::NotEq
            | ScalarOp::Lt
            | ScalarOp::Lte
            | ScalarOp::Gt
            | ScalarOp::Gte
            | ScalarOp::IsNull
            | ScalarOp::IsNotNull
            | ScalarOp::IsTrue
            | ScalarOp::IsNotTrue
            | ScalarOp::IsFalse
            | ScalarOp::IsNotFalse
            | ScalarOp::IsNotDistinctFrom
    )
}

fn function_requires_external_interpretation(op: &ScalarOp) -> bool {
    !(matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
        || is_boolean_value_function(op)
        || matches!(op, ScalarOp::Lower | ScalarOp::Upper))
}

fn literal_requires_external_encoding(raw: &str) -> bool {
    let trimmed = raw.trim();
    !(trimmed.eq_ignore_ascii_case("true")
        || trimmed.eq_ignore_ascii_case("false")
        || trimmed.eq_ignore_ascii_case("null")
        || sql_string_literal_content(trimmed).is_some()
        || is_integer_literal(trimmed))
}

pub(super) fn aggregate_function_name_for_type(
    function: &str,
    arg_ty: Option<&FormalAttributeType>,
) -> Option<String> {
    let name = function.to_ascii_lowercase();
    match (name.as_str(), arg_ty) {
        ("sum" | "max" | "min" | "avg", Some(FormalAttributeType::Float)) => {
            Some(format!("{name}."))
        }
        ("sum" | "max" | "min" | "avg", Some(FormalAttributeType::Double)) => {
            Some(format!("{name}_double"))
        }
        ("max" | "min", Some(FormalAttributeType::Decimal { .. })) => {
            Some(format!("{name}_decimal"))
        }
        _ => Some(name),
    }
}

pub(super) fn aggregate_function_is_supported(function: &str) -> bool {
    matches!(
        function.to_ascii_lowercase().as_str(),
        "count" | "sum" | "max" | "min" | "avg"
    )
}

pub(super) fn annotate_literal_term(
    term: FormalAggregateTerm,
    ty: FormalAttributeType,
) -> FormalAggregateTerm {
    match term {
        FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant { raw, ty: None },
        } => FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant { raw, ty: Some(ty) },
        },
        other => other,
    }
}
