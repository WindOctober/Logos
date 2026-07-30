use super::*;
use logos_ir::calcite::ty::{
    SqlTypeAnnotation, TimestampTypeKind, TypeAnnotationErrorKind, classify_type_annotation,
    classify_type_annotation_checked, type_annotation_precision,
};
use logos_ir::ir::{
    Column, JoinType, RelExpr, ScalarAst, ScalarOp, SetOp, SqlStringType, SqlType, WindowFrameAst,
    WindowFrameUnits,
};

struct ModeledLikePattern {
    kind: ModeledLikeKind,
    value: String,
}

#[derive(Clone, Copy)]
enum ModeledLikeKind {
    Prefix,
    Percent,
}

impl ModeledLikeKind {
    fn predicate(self) -> FormalPredicate {
        match self {
            Self::Prefix => FormalPredicate::LikePrefix,
            Self::Percent => FormalPredicate::LikePercent,
        }
    }
}

impl LoweringContext {
    fn validate_closed_type_annotation(
        &mut self,
        path: &str,
        ty: &str,
    ) -> Option<SqlTypeAnnotation> {
        match classify_type_annotation_checked(ty) {
            Ok(annotation) => Some(annotation),
            Err(TypeAnnotationErrorKind::DecimalTypmod) => {
                self.error(
                    path,
                    "decimal_typmod_not_supported",
                    "FormalSQL DECIMAL lowering supports PostgreSQL DECIMAL(p,s) for 1 <= p <= 1000 and 0 <= s <= 1000; negative scales are not modeled yet.",
                );
                None
            }
            Err(TypeAnnotationErrorKind::Unsupported) => {
                self.error(
                    path,
                    "type_annotation_not_supported",
                    "The SQL type annotation is not one complete supported PostgreSQL/Calcite type spelling.",
                );
                None
            }
        }
    }

    fn reject_locale_dependent_string_case_mapping(
        &mut self,
        path: &str,
        ast: &ScalarAst,
    ) -> Option<()> {
        if !scalar_ast_contains_locale_dependent_case_mapping(ast)
            || self
                .config
                .sql_environment
                .has_postgres_utf8_c_text_semantics()
        {
            return Some(());
        }
        self.error(
            path,
            "string_case_locale_semantics_not_supported",
            "PostgreSQL UPPER/LOWER use the active collation, character classification, and locale provider. FormalSQL's ASCII-only mapping is enabled only for an explicitly attested PostgreSQL UTF8 database with libc provider, default collation C, and character classification C.",
        );
        None
    }

    /// Lower one SQL value into the native exact-query scalar AST.
    ///
    /// Flat aggregate terms remain the mature value-only leaves. Query-valued
    /// constructs are represented directly, so a scalar subquery is neither
    /// replayed as a relation nor approximated by existential quantification.
    pub(super) fn lower_native_scalar_value_expr(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
        result_ty: FormalAttributeType,
    ) -> Option<FormalScalarExpr> {
        self.reject_locale_dependent_string_case_mapping(path, ast)?;
        match ast {
            ScalarAst::TypeAnnotation { expr, ty } => {
                self.validate_closed_type_annotation(path, ty)?;
                let annotated_ty = formal_type_from_annotation(ty).unwrap_or(result_ty);
                if annotated_ty != result_ty {
                    self.error(
                        path,
                        "native_scalar_result_type_mismatch",
                        "The scalar expression annotation does not match its resolved PostgreSQL output type.",
                    );
                    return None;
                }
                self.lower_native_scalar_value_expr(path, expr, scope, result_ty)
            }
            ScalarAst::RelSubquery { rel } => {
                self.lower_native_scalar_subquery_value(path, rel, result_ty)
            }
            ScalarAst::Call {
                op: ScalarOp::ScalarQuery,
                args,
                ..
            } => {
                let [ScalarAst::RelSubquery { rel }] = args.as_slice() else {
                    self.error(
                        path,
                        "scalar_subquery_shape_not_supported",
                        "SCALAR_QUERY requires exactly one structured relational subquery operand.",
                    );
                    return None;
                };
                self.lower_native_scalar_subquery_value(path, rel, result_ty)
            }
            ScalarAst::Call {
                op: ScalarOp::Case,
                args,
                ..
            } if scalar_ast_has_rel_subquery(ast) => {
                self.lower_native_scalar_case_value(path, args, scope, result_ty)
            }
            ScalarAst::Call { op, .. }
                if is_boolean_value_function(op)
                    || op.is_comparison()
                    || matches!(op, ScalarOp::In | ScalarOp::Exists) =>
            {
                if result_ty != FormalAttributeType::Bool {
                    self.error(
                        path,
                        "native_boolean_value_type_mismatch",
                        "A Boolean scalar expression must have PostgreSQL BOOLEAN result type.",
                    );
                    return None;
                }
                Some(FormalScalarExpr::BooleanValue {
                    expression: Box::new(self.lower_native_scalar_boolean_expr(path, ast, scope)?),
                })
            }
            ScalarAst::Call { op, args, .. } if scalar_ast_has_rel_subquery(ast) => {
                self.lower_native_scalar_call_value(path, op, args, scope, result_ty)
            }
            _ if scalar_ast_has_rel_subquery(ast) => {
                self.error(
                    path,
                    "scalar_subquery_value_operator_not_supported",
                    "A scalar subquery is native in SELECT, predicates, and searched CASE arms. This surrounding scalar operator still needs an exact typed FormalSQL call lowering and is conservatively blocked.",
                );
                None
            }
            _ => {
                let term =
                    annotate_literal_term(self.lower_aggregate_term(path, ast, scope)?, result_ty);
                Some(FormalScalarExpr::Leaf { result_ty, term })
            }
        }
    }

    fn lower_native_scalar_call_value(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
        result_ty: FormalAttributeType,
    ) -> Option<FormalScalarExpr> {
        let subquery_may_error = args.iter().any(scalar_ast_rel_subquery_may_raise_runtime);
        let sibling_may_error = args.iter().any(|arg| {
            !scalar_ast_has_rel_subquery(arg)
                && self.scalar_ast_may_raise_runtime_in_scope(arg, scope)
        });
        if subquery_may_error && sibling_may_error {
            self.error(
                path,
                "scalar_subquery_argument_error_order_not_supported",
                "Both a scalar-subquery child and a sibling scalar operand may raise PostgreSQL errors. FormalSQL does not impose one operand evaluation order at this boundary, so the call is conservatively blocked.",
            );
            return None;
        }
        let operand_types = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                self.native_scalar_operand_type(&format!("{path}.args[{index}].type"), arg, scope)
            })
            .collect::<Option<Vec<_>>>()?;
        let operator = match (op, args.len(), result_ty) {
            (
                ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply,
                2,
                FormalAttributeType::Numeric,
            ) if operand_types
                .iter()
                .all(|ty| *ty == FormalAttributeType::Numeric) =>
            {
                match op {
                    ScalarOp::Plus => ScalarOperator::Add(ScalarNumericKind::Numeric),
                    ScalarOp::Minus => ScalarOperator::Subtract(ScalarNumericKind::Numeric),
                    ScalarOp::Multiply => ScalarOperator::Multiply(ScalarNumericKind::Numeric),
                    _ => unreachable!("guarded numeric operator"),
                }
            }
            (ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply, 2, ty)
                if operand_types.iter().all(|operand| *operand == ty) =>
            {
                floating_operator(op, ty).or_else(|| integer_binary_operator(op, ty))?
            }
            (ScalarOp::Minus, 1, ty) if operand_types.as_slice() == [ty] => {
                floating_unary_minus_operator(ty).or_else(|| integer_unary_minus_operator(ty))?
            }
            (ScalarOp::Lower, 1, FormalAttributeType::String { .. }) => {
                ScalarOperator::StringCase(ScalarStringCase::Lower)
            }
            (ScalarOp::Upper, 1, FormalAttributeType::String { .. }) => {
                ScalarOperator::StringCase(ScalarStringCase::Upper)
            }
            (ScalarOp::StringConcat, 2, FormalAttributeType::String { .. })
                if operand_types
                    .iter()
                    .all(|ty| matches!(ty, FormalAttributeType::String { .. })) =>
            {
                ScalarOperator::StringConcat
            }
            _ => {
                self.error(
                    path,
                    "scalar_subquery_value_operator_not_supported",
                    "The scalar operator surrounding this subquery has no exact result/operand signature in the native FormalSQL scalar layer. Numeric division, typmod casts, and other representation-sensitive calls remain fail-closed.",
                );
                return None;
            }
        };
        let lowered_args = args
            .iter()
            .zip(operand_types)
            .enumerate()
            .map(|(index, (arg, operand_ty))| {
                self.lower_native_scalar_value_expr(
                    &format!("{path}.args[{index}]"),
                    arg,
                    scope,
                    operand_ty,
                )
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalScalarExpr::Call {
            result_ty,
            operator,
            args: lowered_args,
        })
    }

    fn lower_native_scalar_subquery_value(
        &mut self,
        path: &str,
        rel: &RelExpr,
        result_ty: FormalAttributeType,
    ) -> Option<FormalScalarExpr> {
        let query = self.lower_query_expr(&format!("{path}.subquery"), rel)?;
        let signature = query_expr_output_signature(&query).or_else(|| {
            self.error(
                &format!("{path}.subquery.output"),
                "scalar_subquery_output_signature_inconsistent",
                "The lowered scalar subquery has no authoritative ordered output signature.",
            );
            None
        })?;
        let [output] = signature.as_slice() else {
            self.error(
                &format!("{path}.subquery.output"),
                "scalar_subquery_output_arity_mismatch",
                "PostgreSQL scalar subqueries must expose exactly one output column.",
            );
            return None;
        };
        if output.ty != result_ty {
            self.error(
                &format!("{path}.subquery.output"),
                "scalar_subquery_output_type_mismatch",
                "The scalar subquery output type does not match the surrounding PostgreSQL scalar expression type.",
            );
            return None;
        }
        Some(FormalScalarExpr::Subquery {
            result_ty,
            query: Box::new(query),
        })
    }

    fn probe_native_scalar_subquery_output_type(
        &mut self,
        path: &str,
        rel: &RelExpr,
    ) -> Option<FormalAttributeType> {
        let diagnostics_len = self.diagnostics.len();
        let next_scope_barrier = self.next_scope_barrier;
        let scope_barrier_names = self.scope_barrier_names.clone();
        let query = self.lower_query_expr(&format!("{path}.queryType"), rel)?;
        let signature = query_expr_output_signature(&query).or_else(|| {
            self.error(
                path,
                "scalar_subquery_output_signature_inconsistent",
                "The scalar subquery type probe found no authoritative ordered output signature.",
            );
            None
        })?;
        let [column] = signature.as_slice() else {
            self.error(
                path,
                "scalar_subquery_output_arity_mismatch",
                "A scalar subquery operand must expose exactly one output column.",
            );
            return None;
        };
        let ty = column.ty;
        self.diagnostics.truncate(diagnostics_len);
        self.next_scope_barrier = next_scope_barrier;
        self.scope_barrier_names = scope_barrier_names;
        Some(ty)
    }

    fn lower_native_scalar_case_value(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
        result_ty: FormalAttributeType,
    ) -> Option<FormalScalarExpr> {
        if args.len() < 3 || args.len().is_multiple_of(2) {
            self.error(
                path,
                "case_arity_not_supported",
                "FormalSQL CASE lowering expects WHEN/THEN pairs followed by one ELSE expression.",
            );
            return None;
        }
        let inferred = self.infer_case_type(&format!("{path}.resultType"), args, scope)?;
        if inferred != result_ty {
            self.error(
                path,
                "case_result_type_not_supported",
                "The native CASE common type differs from the resolved PostgreSQL output type.",
            );
            return None;
        }
        let else_ast = args.last().expect("CASE arity checked");
        let mut nested = self.lower_native_scalar_value_expr(
            &format!("{path}.else"),
            else_ast,
            scope,
            result_ty,
        )?;
        for (branch_index, pair) in args[..args.len() - 1].chunks_exact(2).enumerate().rev() {
            let condition = self.lower_native_scalar_boolean_expr(
                &format!("{path}.branches[{branch_index}].when"),
                &pair[0],
                scope,
            )?;
            let then_expr = self.lower_native_scalar_value_expr(
                &format!("{path}.branches[{branch_index}].then"),
                &pair[1],
                scope,
                result_ty,
            )?;
            nested = FormalScalarExpr::Case {
                result_ty,
                condition: Box::new(condition),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(nested),
            };
        }
        Some(nested)
    }

    /// Lower one SQL search condition into the Boolean index of the native
    /// scalar AST. Nullable BOOLEAN values cross through ValueBoolean, which
    /// preserves UNKNOWN (unlike rewriting a value as `IS TRUE`).
    pub(super) fn lower_native_scalar_boolean_expr(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalScalarExpr> {
        self.reject_locale_dependent_string_case_mapping(path, ast)?;
        if let Some(rewritten) = complementary_text_order_disjunction(ast, scope) {
            return self.lower_native_scalar_boolean_expr(path, &rewritten, scope);
        }
        match ast {
            ScalarAst::Literal { raw } if raw.eq_ignore_ascii_case("true") => {
                Some(FormalScalarExpr::True)
            }
            ScalarAst::Literal { raw } if raw.eq_ignore_ascii_case("false") => {
                Some(FormalScalarExpr::Not {
                    expression: Box::new(FormalScalarExpr::True),
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::And | ScalarOp::Or) && !args.is_empty() =>
            {
                let lowered = args
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        self.lower_native_scalar_boolean_expr(
                            &format!("{path}.args[{index}]"),
                            argument,
                            scope,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                if args
                    .iter()
                    .any(|argument| self.scalar_ast_may_raise_runtime_in_scope(argument, scope))
                {
                    self.error(
                        path,
                        "boolean_short_circuit_runtime_error_not_supported",
                        "PostgreSQL may reorganize AND/OR operands and does not provide source-order evaluation authority. FormalSQL's ordered Boolean connective is therefore restricted to operands proved runtime-total.",
                    );
                    return None;
                }
                let mut lowered = lowered.into_iter();
                let first = lowered.next().expect("non-empty AND/OR checked");
                Some(lowered.fold(first, |left, right| match op {
                    ScalarOp::And => FormalScalarExpr::And {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    ScalarOp::Or => FormalScalarExpr::Or {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    _ => unreachable!("guarded by And/Or"),
                }))
            }
            ScalarAst::Call {
                op: ScalarOp::Not,
                args,
                ..
            } if matches!(args.as_slice(), [_]) => Some(FormalScalarExpr::Not {
                expression: Box::new(self.lower_native_scalar_boolean_expr(
                    &format!("{path}.arg"),
                    &args[0],
                    scope,
                )?),
            }),
            ScalarAst::Call {
                op: ScalarOp::Exists,
                args,
                ..
            } => self.lower_native_exists_scalar(path, args),
            ScalarAst::Call {
                op: ScalarOp::In,
                args,
                ..
            } => self.lower_native_in_scalar(path, args, scope),
            ScalarAst::Call { op, args, .. } if formal_predicate(op).is_some() => {
                if predicate_requires_external_interpretation(op) {
                    self.error(
                        path,
                        "predicate_interpretation_not_supported",
                        "FormalSQL lowering requires a built-in interpretation for the predicate.",
                    );
                    return None;
                }
                if !args.iter().any(scalar_ast_has_rel_subquery) {
                    let raw_types = args
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| {
                            self.comparison_predicate_operand_type(
                                &format!("{path}.args[{index}].type"),
                                argument,
                                scope,
                            )
                        })
                        .collect::<Vec<_>>();
                    let (predicate, terms) =
                        self.lower_predicate_aggregate_call(path, op, args, scope)?;
                    let scalar_args = terms
                        .into_iter()
                        .enumerate()
                        .map(|(index, term)| {
                            let contextual = (args.len() == 2)
                                .then(|| raw_types[1 - index])
                                .flatten();
                            let raw = raw_types[index];
                            let result_ty = match (raw, contextual) {
                                (Some(ty), Some(other))
                                    if is_integral_type(ty)
                                        && is_exact_numeric_type(other) =>
                                {
                                    FormalAttributeType::Numeric
                                }
                                (_, Some(other))
                                    if is_untyped_null_literal(&args[index]) =>
                                {
                                    other
                                }
                                (_, Some(other))
                                    if is_untyped_string_literal(&args[index]) =>
                                {
                                    comparison_unknown_string_type(other)
                                }
                                (Some(ty), _) => ty,
                                (None, Some(ty)) => ty,
                                (None, None) => {
                                    self.error(
                                        &format!("{path}.args[{index}].type"),
                                        "predicate_operand_type_not_supported",
                                        "The predicate operand has no exact modeled PostgreSQL type or contextual peer type.",
                                    );
                                    return None;
                                }
                            };
                            Some(FormalScalarExpr::Leaf {
                                result_ty,
                                term: annotate_literal_term(term, result_ty),
                            })
                        })
                        .collect::<Option<Vec<_>>>()?;
                    return Some(FormalScalarExpr::Predicate {
                        predicate,
                        args: scalar_args,
                    });
                }
                let operand_types = args
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        self.native_scalar_operand_type(
                            &format!("{path}.args[{index}].type"),
                            argument,
                            scope,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                let predicate = match operand_types.as_slice() {
                    [left, right] => self.predicate_name_for_types(
                        &format!("{path}.predicateType"),
                        op,
                        Some(*left),
                        Some(*right),
                    )?,
                    _ => {
                        let predicate = formal_predicate(op)?;
                        if !predicate.accepts_arity(args.len()) {
                            self.error(
                                &format!("{path}.predicateType"),
                                "predicate_arity_mismatch",
                                &format!(
                                    "SQL predicate {op:?} does not accept {} arguments.",
                                    args.len()
                                ),
                            );
                            return None;
                        }
                        predicate
                    }
                };
                let lowered_args = args
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let contextual_ty = if args.len() == 2 {
                            operand_types[1 - index]
                        } else {
                            operand_types[index]
                        };
                        self.lower_native_scalar_value_expr(
                            &format!("{path}.args[{index}]"),
                            argument,
                            scope,
                            if is_untyped_null_literal(argument)
                                || is_untyped_string_literal(argument)
                            {
                                contextual_ty
                            } else {
                                operand_types[index]
                            },
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(FormalScalarExpr::Predicate {
                    predicate,
                    args: lowered_args,
                })
            }
            ScalarAst::Call {
                op: ScalarOp::Like,
                args,
                ..
            } => {
                let (kind, legacy_args) =
                    self.lower_modeled_like_aggregate_args(path, args, scope)?;
                let scalar_args = legacy_args
                    .into_iter()
                    .enumerate()
                    .map(|(index, term)| FormalScalarExpr::Leaf {
                        result_ty: if index == 0 {
                            self.native_scalar_operand_type(
                                &format!("{path}.args[0].type"),
                                &args[0],
                                scope,
                            )
                            .unwrap_or(FormalAttributeType::String {
                                typmod: SqlStringType::Text,
                            })
                        } else {
                            FormalAttributeType::String {
                                typmod: SqlStringType::Text,
                            }
                        },
                        term,
                    })
                    .collect();
                Some(FormalScalarExpr::Predicate {
                    predicate: kind.predicate(),
                    args: scalar_args,
                })
            }
            ScalarAst::TypeAnnotation { expr, ty }
                if formal_type_from_annotation(ty) == Some(FormalAttributeType::Bool) =>
            {
                self.lower_native_scalar_boolean_expr(path, expr, scope)
            }
            _ => {
                let value = self.lower_native_scalar_value_expr(
                    path,
                    ast,
                    scope,
                    FormalAttributeType::Bool,
                )?;
                Some(FormalScalarExpr::ValueBoolean {
                    expression: Box::new(value),
                })
            }
        }
    }

    fn lower_native_exists_scalar(
        &mut self,
        path: &str,
        args: &[ScalarAst],
    ) -> Option<FormalScalarExpr> {
        let [ScalarAst::RelSubquery { rel }] = args else {
            self.error(
                path,
                "exists_subquery_not_supported",
                "EXISTS requires exactly one structured relational subquery operand.",
            );
            return None;
        };
        if exists_subquery_has_incomplete_capped_runtime_path(rel) {
            self.error(
                path,
                "exists_capped_runtime_path_not_supported",
                "Direct EXISTS over a runtime-error-capable UNION or join is conservatively unsupported. FormalSQL currently evaluates those operators exhaustively, while PostgreSQL may stop after the first existence witness and skip dead target or predicate errors.",
            );
            return None;
        }
        Some(FormalScalarExpr::Exists {
            query: Box::new(self.lower_query_expr(&format!("{path}.subquery"), rel)?),
        })
    }

    fn lower_native_in_scalar(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalScalarExpr> {
        let Some((right, left_args)) = args.split_last() else {
            self.error(
                path,
                "in_predicate_arity_mismatch",
                "IN requires at least one left value and one subquery operand.",
            );
            return None;
        };
        let ScalarAst::RelSubquery { rel } = right else {
            self.error(
                path,
                "in_list_not_supported",
                "Native IN currently requires a structured relational subquery operand.",
            );
            return None;
        };
        let query = self.lower_query_expr(&format!("{path}.subquery"), rel)?;
        let signature = query_expr_output_signature(&query)?;
        if left_args.is_empty() || left_args.len() != signature.len() {
            self.error(
                path,
                "in_predicate_arity_mismatch",
                "IN left-value arity does not match the subquery output arity.",
            );
            return None;
        }
        let values = left_args
            .iter()
            .zip(&signature)
            .enumerate()
            .map(|(index, (argument, output))| {
                let actual = self.native_scalar_operand_type(
                    &format!("{path}.left[{index}].type"),
                    argument,
                    scope,
                )?;
                if actual != output.ty
                    && !is_untyped_null_literal(argument)
                    && !is_untyped_string_literal(argument)
                {
                    self.error(
                        &format!("{path}.left[{index}]"),
                        "comparison_operand_type_not_supported",
                        "IN requires each left value to use the same modeled PostgreSQL representation as its aligned subquery column.",
                    );
                    return None;
                }
                self.lower_native_scalar_value_expr(
                    &format!("{path}.left[{index}]"),
                    argument,
                    scope,
                    output.ty,
                )
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalScalarExpr::In {
            args: values,
            query: Box::new(query),
        })
    }

    pub(super) fn native_scalar_operand_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        match ast {
            ScalarAst::RelSubquery { rel } => {
                self.probe_native_scalar_subquery_output_type(path, rel)
            }
            ScalarAst::Call {
                op: ScalarOp::ScalarQuery,
                args,
                ..
            } => {
                let [ScalarAst::RelSubquery { rel }] = args.as_slice() else {
                    self.error(
                        path,
                        "scalar_subquery_shape_not_supported",
                        "SCALAR_QUERY requires exactly one structured relational subquery operand.",
                    );
                    return None;
                };
                self.probe_native_scalar_subquery_output_type(path, rel)
            }
            ScalarAst::Call { op, args, .. }
                if scalar_ast_has_rel_subquery(ast)
                    && matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && matches!(args.as_slice(), [_, _]) =>
            {
                let left =
                    self.native_scalar_operand_type(&format!("{path}.left"), &args[0], scope)?;
                let right =
                    self.native_scalar_operand_type(&format!("{path}.right"), &args[1], scope)?;
                if left == right {
                    Some(left)
                } else if (is_exact_numeric_type(left) || is_integral_type(left))
                    && (is_exact_numeric_type(right) || is_integral_type(right))
                {
                    Some(FormalAttributeType::Numeric)
                } else {
                    self.error(
                        path,
                        "scalar_subquery_value_operator_not_supported",
                        "The arithmetic operands surrounding a scalar subquery do not resolve to one exact modeled PostgreSQL result type.",
                    );
                    None
                }
            }
            ScalarAst::TypeAnnotation { ty, .. } => formal_type_from_annotation(ty).or_else(|| {
                self.error(
                    path,
                    "type_annotation_not_supported",
                    "The scalar operand has an unsupported PostgreSQL type annotation.",
                );
                None
            }),
            _ => self
                .comparison_predicate_operand_type(path, ast, scope)
                .or_else(|| self.infer_function_type(path, ast, scope)),
        }
    }

    fn scalar_ast_may_raise_runtime_in_scope(&self, ast: &ScalarAst, scope: &Scope) -> bool {
        let input_types = scope
            .attributes
            .iter()
            .map(|attribute| Some(attribute.formal_ty))
            .collect::<Vec<_>>();
        scalar_ast_may_raise_runtime_with_types(ast, &input_types)
    }

    /// Compatibility bridge for query constructors whose mature bag theory
    /// still carries a formula. Every SQL predicate is nevertheless lowered
    /// through the same native scalar AST used by SELECT and WHERE.
    pub(super) fn lower_formula_expr(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalFormulaExpr> {
        Some(FormalFormulaExpr::Scalar {
            expression: Box::new(self.lower_native_scalar_boolean_expr(path, ast, scope)?),
        })
    }

    fn predicate_name_for_args(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalPredicate> {
        let predicate = formal_predicate(op)?;
        if !predicate.accepts_arity(args.len()) {
            self.error(
                path,
                "predicate_arity_mismatch",
                &format!(
                    "SQL predicate {op:?} does not accept {} arguments.",
                    args.len()
                ),
            );
            return None;
        }
        if args.len() != 2 {
            return Some(predicate);
        }
        let left =
            self.comparison_predicate_operand_type(&format!("{path}.leftType"), &args[0], scope);
        let right =
            self.comparison_predicate_operand_type(&format!("{path}.rightType"), &args[1], scope);
        self.predicate_name_for_types(path, op, left, right)
    }

    fn scalar_operator_for_args(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<ScalarOperator> {
        if formal_predicate(op).is_some() {
            return self
                .predicate_name_for_args(path, op, args, scope)
                .map(ScalarOperator::PredicateValue);
        }
        scalar_operator(op)
    }

    /// Lower one closed SQL predicate independently of how its result is
    /// observed. Search conditions consume the returned predicate directly;
    /// value contexts wrap it in `ScalarPredicateValue`. Keeping coercion and
    /// contextual literal typing here prevents those two observations from
    /// assigning different truth values to the same SQL expression.
    fn lower_predicate_aggregate_call(
        &mut self,
        path: &str,
        op: &ScalarOp,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<(FormalPredicate, Vec<FormalAggregateTerm>)> {
        let predicate =
            self.predicate_name_for_args(&format!("{path}.predicateType"), op, args, scope)?;
        if predicate_requires_external_interpretation(op) {
            self.error(
                path,
                "predicate_interpretation_not_supported",
                "FormalSQL lowering requires a built-in Rocq interpretation for every emitted SQL predicate.",
            );
            return None;
        }
        let contextual_types = if args.len() == 2 {
            vec![
                self.comparison_operand_type(
                    &format!("{path}.args[1].contextType"),
                    &args[1],
                    scope,
                ),
                self.comparison_operand_type(
                    &format!("{path}.args[0].contextType"),
                    &args[0],
                    scope,
                ),
            ]
        } else {
            vec![None; args.len()]
        };
        let lowered_args = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                let arg_path = format!("{path}.args[{index}]");
                let arg_ty =
                    self.comparison_operand_type(&format!("{arg_path}.operandType"), arg, scope);
                let lowered = match (arg_ty, contextual_types[index]) {
                    (Some(arg_ty), Some(other_ty))
                        if is_integral_type(arg_ty) && is_exact_numeric_type(other_ty) =>
                    {
                        self.lower_numeric_coerced_aggregate_term(&arg_path, arg, arg_ty, scope)?
                    }
                    _ => self.lower_aggregate_term(&arg_path, arg, scope)?,
                };
                Some(match contextual_types[index] {
                    Some(ty) if is_untyped_null_literal(arg) => annotate_literal_term(lowered, ty),
                    Some(ty) if is_untyped_string_literal(arg) => {
                        annotate_literal_term(lowered, comparison_unknown_string_type(ty))
                    }
                    _ => lowered,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some((predicate, lowered_args))
    }

    /// Recover the runtime type of an operand before choosing a comparison
    /// predicate. Calcite's scalar AST does not carry a result annotation for
    /// `date +/- interval`, and its surrounding metadata can therefore still
    /// describe that expression as DATE. PostgreSQL actually promotes the
    /// DATE to TIMESTAMP before applying the interval; using the stale DATE
    /// metadata here would select the homogeneous generic comparator for a
    /// heterogeneous DATE/TIMESTAMP value pair.
    fn comparison_predicate_operand_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        if let ScalarAst::Call { op, args, .. } = ast
            && matches!(op, ScalarOp::Plus | ScalarOp::Minus)
            && let [left, right] = args.as_slice()
            && self
                .date_interval_function_in_scope(path, op, left, right, scope)
                .is_some()
        {
            return Some(FormalAttributeType::Timestamp { precision: None });
        }
        self.comparison_operand_type(path, ast, scope)
    }

    pub(super) fn predicate_name_for_types(
        &mut self,
        path: &str,
        op: &ScalarOp,
        left: Option<FormalAttributeType>,
        right: Option<FormalAttributeType>,
    ) -> Option<FormalPredicate> {
        if matches!(
            (left.as_ref(), right.as_ref()),
            (
                Some(FormalAttributeType::Date),
                Some(FormalAttributeType::Timestamp { .. })
            )
        ) {
            return match op {
                ScalarOp::Lt => Some(FormalPredicate::DateLtTimestamp),
                ScalarOp::Lte => Some(FormalPredicate::DateLteTimestamp),
                ScalarOp::Gt => Some(FormalPredicate::DateGtTimestamp),
                ScalarOp::Gte => Some(FormalPredicate::DateGteTimestamp),
                _ => {
                    self.error(
                        path,
                        "date_timestamp_comparison_predicate_not_supported",
                        "FormalSQL currently models PostgreSQL DATE-to-TIMESTAMP ordering comparisons with the DATE operand on the left; equality and NULL-safe cross-type predicates remain conservatively unsupported.",
                    );
                    None
                }
            };
        }
        if matches!(
            (left.as_ref(), right.as_ref()),
            (
                Some(FormalAttributeType::Timestamp { .. }),
                Some(FormalAttributeType::Date)
            )
        ) {
            self.error(
                path,
                "timestamp_date_comparison_predicate_not_supported",
                "FormalSQL does not yet model PostgreSQL TIMESTAMP-to-DATE comparison with the TIMESTAMP operand on the left.",
            );
            return None;
        }
        if is_floating_comparison_mismatch(left, right) {
            self.error(
                path,
                "floating_comparison_predicate_not_supported",
                "FLOAT/DOUBLE predicates are lowered only when both operands have the same modeled floating type.",
            );
            return None;
        }
        if !comparison_types_are_supported(left, right) {
            self.error(
                path,
                "comparison_operand_type_not_supported",
                "FormalSQL comparison lowering requires operands from the same modeled SQL comparison domain.",
            );
            return None;
        }
        if !is_order_predicate(op) {
            return formal_predicate(op);
        }
        if matches!(
            (left.as_ref(), right.as_ref()),
            (
                Some(FormalAttributeType::String { .. }),
                Some(FormalAttributeType::String { .. })
            )
        ) && !self
            .config
            .sql_environment
            .has_postgres_utf8_c_text_semantics()
        {
            self.error(
                path,
                "string_collation_predicate_not_supported",
                "PostgreSQL string ordering is lowered only for an explicitly attested UTF8 database with libc provider, default collation C, and character classification C.",
            );
            return None;
        }
        match (left, right) {
            (Some(FormalAttributeType::Float), Some(FormalAttributeType::Float)) => match op {
                ScalarOp::Lt => Some(FormalPredicate::FloatLt),
                ScalarOp::Lte => Some(FormalPredicate::FloatLte),
                ScalarOp::Gt => Some(FormalPredicate::FloatGt),
                ScalarOp::Gte => Some(FormalPredicate::FloatGte),
                _ => None,
            },
            (Some(FormalAttributeType::Double), Some(FormalAttributeType::Double)) => match op {
                ScalarOp::Lt => Some(FormalPredicate::DoubleLt),
                ScalarOp::Lte => Some(FormalPredicate::DoubleLte),
                ScalarOp::Gt => Some(FormalPredicate::DoubleGt),
                ScalarOp::Gte => Some(FormalPredicate::DoubleGte),
                _ => None,
            },
            _ => formal_predicate(op),
        }
    }

    fn comparison_operand_type(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAttributeType> {
        self.direct_function_type(path, ast, scope)
            .or_else(|| match ast {
                ScalarAst::Literal { raw } => infer_literal_cast_source_type(raw),
                ScalarAst::Call { op, .. } => self.infer_call_type(path, op, ast, scope),
                _ => None,
            })
    }

    pub(super) fn lower_aggregate_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        self.reject_locale_dependent_string_case_mapping(path, ast)?;
        match ast {
            ScalarAst::Call {
                op: ScalarOp::Extract,
                args,
                ..
            } => {
                let (operator, arg) = self.lower_extract_date_aggregate_arg(path, args, scope)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator,
                    args: vec![arg],
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus)
                    && args.len() == 2
                    && self
                        .timestamp_interval_function_in_scope(
                            &format!("{path}.timestampType"),
                            op,
                            &args[0],
                            &args[1],
                            scope,
                        )
                        .is_some() =>
            {
                let TimestampIntervalFunction {
                    operator,
                    timestamp_arg,
                    interval_arg,
                } = self.timestamp_interval_function_in_scope(
                    &format!("{path}.timestampType"),
                    op,
                    &args[0],
                    &args[1],
                    scope,
                )?;
                let timestamp =
                    self.lower_aggregate_term(&format!("{path}.timestamp"), timestamp_arg, scope)?;
                let interval =
                    self.lower_interval_term(&format!("{path}.interval"), interval_arg, op)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator,
                    args: vec![timestamp, interval],
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus)
                    && args.len() == 2
                    && self
                        .date_interval_function_in_scope(
                            &format!("{path}.dateType"),
                            op,
                            &args[0],
                            &args[1],
                            scope,
                        )
                        .is_some() =>
            {
                let DateIntervalFunction {
                    operator,
                    date_arg,
                    interval_arg,
                } = self.date_interval_function_in_scope(
                    &format!("{path}.dateType"),
                    op,
                    &args[0],
                    &args[1],
                    scope,
                )?;
                let date = self.lower_aggregate_term(&format!("{path}.date"), date_arg, scope)?;
                let timestamp = FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::Cast(ScalarCast::DateToTimestamp),
                    args: vec![date],
                };
                let interval =
                    self.lower_interval_term(&format!("{path}.interval"), interval_arg, op)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator,
                    args: vec![timestamp, interval],
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus)
                    && args.len() == 2
                    && self.has_temporal_interval_pair_in_scope(
                        &format!("{path}.temporalType"),
                        &args[0],
                        &args[1],
                        scope,
                    ) =>
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
                Some(FormalAggregateTerm::ScalarCall {
                    operator: floating_operator(op, ty)?,
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
            ScalarAst::Call { op, args, .. }
                if matches!(
                    op,
                    ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
                ) && args.len() == 2
                    && self
                        .integral_binary_type(&format!("{path}.integerArgs"), args, scope)
                        .is_some() =>
            {
                let ty = self.integral_binary_type(&format!("{path}.integerArgs"), args, scope)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator: integer_binary_operator(op, ty)?,
                    args: args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_integral_coerced_aggregate_term(
                                &format!("{path}.args[{index}]"),
                                arg,
                                ty,
                                scope,
                            )
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1
                && self
                    .infer_function_type(&format!("{path}.argType"), &args[0], scope)
                    .is_some_and(is_integral_type) =>
            {
                let ty = self.infer_function_type(&format!("{path}.argType"), &args[0], scope)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator: integer_unary_minus_operator(ty)?,
                    args: vec![
                        self.lower_aggregate_term(&format!("{path}.arg"), &args[0], scope)
                            .map(|term| annotate_literal_term(term, ty))?,
                    ],
                })
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
                Some(FormalAggregateTerm::ScalarCall {
                    operator: floating_unary_minus_operator(ty)?,
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
                    && self
                        .numeric_binary_arg_types(&format!("{path}.decimalArgs"), args, scope)
                        .is_some() =>
            {
                let arg_types =
                    self.numeric_binary_arg_types(&format!("{path}.decimalArgs"), args, scope)?;
                let operator = match op {
                    ScalarOp::Plus => ScalarOperator::Add(ScalarNumericKind::Numeric),
                    ScalarOp::Minus => ScalarOperator::Subtract(ScalarNumericKind::Numeric),
                    ScalarOp::Multiply => ScalarOperator::Multiply(ScalarNumericKind::Numeric),
                    _ => unreachable!("decimal arithmetic guard checked"),
                };
                Some(FormalAggregateTerm::ScalarCall {
                    operator,
                    args: args
                        .iter()
                        .enumerate()
                        .zip(arg_types)
                        .map(|((index, arg), ty)| {
                            self.lower_numeric_coerced_aggregate_term(
                                &format!("{path}.args[{index}]"),
                                arg,
                                ty,
                                scope,
                            )
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && args.len() == 2
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
                Some(FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::Negate(ScalarNumericKind::Numeric),
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
                && self
                    .numeric_binary_arg_types(&format!("{path}.decimalArgs"), args, scope)
                    .is_some() =>
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
                if op.is_comparison()
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
                    "FLOAT/DOUBLE order comparisons are supported only in predicate context; boolean-valued projection expressions need a FormalSQL operator interpretation first.",
                );
                None
            }
            ScalarAst::Call { op, args, .. } if formal_predicate(op).is_some() => {
                let (predicate, args) =
                    self.lower_predicate_aggregate_call(path, op, args, scope)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::PredicateValue(predicate),
                    args,
                })
            }
            ScalarAst::Call {
                op: ScalarOp::StringConcat,
                args,
                ..
            } => self.lower_string_concat_aggregate_term(path, args, scope),
            ScalarAst::Call {
                op: ScalarOp::Substring,
                args,
                ..
            } => self.lower_substring_aggregate_term(path, args, scope),
            ScalarAst::Call {
                op: ScalarOp::Like,
                args,
                ..
            } => {
                let (kind, args) = self.lower_modeled_like_aggregate_args(path, args, scope)?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::PredicateValue(kind.predicate()),
                    args,
                })
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
                if function_requires_external_interpretation(op) {
                    self.error(
                        path,
                        "function_interpretation_not_supported",
                        "FormalSQL lowering requires a built-in Rocq interpretation for every emitted SQL scalar function.",
                    );
                    return None;
                }
                let operator = self.scalar_operator_for_args(path, op, args, scope)?;
                let lowered_args = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(FormalAggregateTerm::ScalarCall {
                    operator,
                    args: lowered_args,
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
                self.validate_closed_type_annotation(path, ty)?;
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
                    if matches!(
                        formal_ty,
                        FormalAttributeType::Int32 | FormalAttributeType::Int64
                    ) && !raw.eq_ignore_ascii_case("null")
                        && !integer_literal_fits_type(raw, formal_ty)
                    {
                        self.error(
                            path,
                            "integer_literal_out_of_range",
                            "FormalSQL INTEGER/BIGINT lowering rejects literals outside the target SQL integer range.",
                        );
                        return None;
                    }
                    if is_exact_numeric_type(formal_ty)
                        && !raw.eq_ignore_ascii_case("null")
                        && !numeric_literal_fits_type(raw, formal_ty)
                    {
                        self.error(
                            path,
                            "numeric_literal_not_supported",
                            "FormalSQL NUMERIC/DECIMAL lowering accepts finite decimal literals within PostgreSQL runtime bounds; constrained values must also fit DECIMAL(p,s). NaN and infinities are rejected.",
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
                if let Some(cast_arg) = cast_arg(expr) {
                    let target_ty = formal_type_from_annotation(ty).or_else(|| {
                        self.error(
                            path,
                            "cast_target_type_not_supported",
                            "FormalSQL lowering cannot infer the target type of this explicit CAST.",
                        );
                        None
                    })?;
                    if target_ty == FormalAttributeType::Int32
                        && let Some(base) = postgres_power_half_int64_base(cast_arg)
                        && self.infer_numeric_operand_type(
                            &format!("{path}.powerHalfBase"),
                            base,
                            scope,
                        ) == Some(FormalAttributeType::Int64)
                    {
                        return Some(FormalAggregateTerm::ScalarCall {
                            operator: ScalarOperator::PowerHalfInt64ToInt32,
                            args: vec![self.lower_aggregate_term(
                                &format!("{path}.powerHalfBase"),
                                base,
                                scope,
                            )?],
                        });
                    }
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
                    } else if let Some(operator) =
                        simple_numeric_cast_operator(&source_ty, &target_ty)
                    {
                        Some(FormalAggregateTerm::ScalarCall {
                            operator,
                            args: vec![self.lower_aggregate_term(
                                &format!("{path}.castArg"),
                                cast_arg,
                                scope,
                            )?],
                        })
                    } else if let Some(operator) =
                        string_integer_cast_operator(&source_ty, &target_ty)
                    {
                        let source = annotate_literal_term(
                            self.lower_aggregate_term(&format!("{path}.castArg"), cast_arg, scope)?,
                            source_ty,
                        );
                        Some(FormalAggregateTerm::ScalarCall {
                            operator,
                            args: vec![source],
                        })
                    } else if let Some(operator) =
                        decimal_typmod_cast_operator(&source_ty, &target_ty)
                    {
                        self.lower_decimal_cast_aggregate_term(
                            &format!("{path}.castArg"),
                            cast_arg,
                            operator,
                            target_ty,
                            scope,
                        )
                    } else if is_string_type(source_ty)
                        && target_ty == FormalAttributeType::Bool
                        && let Some(raw) = typed_literal_raw(cast_arg)
                        && let Some(value) = parse_postgres_boolean_source_literal(raw)
                    {
                        Some(FormalAggregateTerm::Expr {
                            term: FormalFunctionTerm::Constant {
                                raw: value.to_string(),
                                ty: Some(FormalAttributeType::Bool),
                            },
                        })
                    } else if is_string_type(source_ty) && is_string_type(target_ty) {
                        self.lower_string_cast_aggregate_term(
                            &format!("{path}.castArg"),
                            cast_arg,
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
                    // Rex type annotations describe Calcite's inferred result type; they
                    // are not source-level SQL casts and must not introduce typmod rounding.
                    self.lower_aggregate_term(path, expr, scope)
                }
            }
            _ => Some(FormalAggregateTerm::Expr {
                term: self.lower_function_term(path, ast, scope)?,
            }),
        }
    }

    fn numeric_binary_arg_types(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<[FormalAttributeType; 2]> {
        let [left, right] = args else {
            return None;
        };
        let left = self.infer_numeric_operand_type(&format!("{path}.leftType"), left, scope)?;
        let right = self.infer_numeric_operand_type(&format!("{path}.rightType"), right, scope)?;
        let supported = |ty| is_exact_numeric_type(ty) || is_integral_type(ty);
        (supported(left)
            && supported(right)
            && (is_exact_numeric_type(left) || is_exact_numeric_type(right)))
        .then_some([left, right])
    }

    fn lower_numeric_coerced_aggregate_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        let term = annotate_literal_term(self.lower_aggregate_term(path, ast, scope)?, ty);
        if is_exact_numeric_type(ty) {
            return Some(term);
        }
        let operator = decimal_typmod_cast_operator(&ty, &FormalAttributeType::Numeric)?;
        Some(FormalAggregateTerm::ScalarCall {
            operator,
            args: vec![term],
        })
    }

    fn lower_numeric_coerced_function_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        let term = annotate_function_literal_term(self.lower_function_term(path, ast, scope)?, ty);
        if is_exact_numeric_type(ty) {
            return Some(term);
        }
        let operator = decimal_typmod_cast_operator(&ty, &FormalAttributeType::Numeric)?;
        Some(FormalFunctionTerm::ScalarCall {
            operator,
            args: vec![term],
        })
    }

    fn decimal_unary_arg(&mut self, path: &str, arg: &ScalarAst, scope: &Scope) -> bool {
        matches!(
            self.direct_function_type(&format!("{path}.argType"), arg, scope),
            Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })
        )
    }

    fn has_decimal_argument(&mut self, path: &str, args: &[ScalarAst], scope: &Scope) -> bool {
        args.iter().enumerate().any(|(index, arg)| {
            matches!(
                self.direct_function_type(&format!("{path}[{index}]"), arg, scope),
                Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })
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
        if target_ty == FormalAttributeType::Double
            && let Some(arg) = cast_arg(expr)
            && matches!(
                self.infer_cast_operand_type(&format!("{path}.floatCastArg"), arg, scope),
                Some(FormalAttributeType::Int32)
            )
        {
            return Some(());
        }
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
        // `divide_numeric*` has a built-in outer runtime-error interpretation
        // for division by zero and numeric overflow. Dynamic failures must
        // reach the generated runtime-safety obligations, not be discarded by
        // a static-totality requirement here.
        let left_scale = self.lower_numeric_dscale_aggregate_term(
            &format!("{path}.leftScale"),
            &args[0],
            scope,
        )?;
        let right_scale = self.lower_numeric_dscale_aggregate_term(
            &format!("{path}.rightScale"),
            &args[1],
            scope,
        )?;
        let [left_ty, right_ty] =
            self.numeric_binary_arg_types(&format!("{path}.argTypes"), args, scope)?;
        let mut lowered_args = vec![
            self.lower_numeric_coerced_aggregate_term(
                &format!("{path}.args[0]"),
                &args[0],
                left_ty,
                scope,
            )?,
            left_scale,
            self.lower_numeric_coerced_aggregate_term(
                &format!("{path}.args[1]"),
                &args[1],
                right_ty,
                scope,
            )?,
            right_scale,
        ];
        let operator = if let Some(result_ty) = annotated_ty {
            let result_precision = decimal_type_precision(&result_ty)?;
            let result_scale = decimal_type_scale(&result_ty)?;
            lowered_args.push(z_constant_aggregate(result_precision));
            lowered_args.push(z_constant_aggregate(result_scale));
            ScalarOperator::NumericDivideTypmod
        } else {
            ScalarOperator::Divide(ScalarNumericKind::Numeric)
        };
        Some(FormalAggregateTerm::ScalarCall {
            operator,
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
        let left_scale =
            self.lower_numeric_dscale_function_term(&format!("{path}.leftScale"), &args[0], scope)?;
        let right_scale = self.lower_numeric_dscale_function_term(
            &format!("{path}.rightScale"),
            &args[1],
            scope,
        )?;
        let [left_ty, right_ty] =
            self.numeric_binary_arg_types(&format!("{path}.argTypes"), args, scope)?;
        let mut lowered_args = vec![
            self.lower_numeric_coerced_function_term(
                &format!("{path}.args[0]"),
                &args[0],
                left_ty,
                scope,
            )?,
            left_scale,
            self.lower_numeric_coerced_function_term(
                &format!("{path}.args[1]"),
                &args[1],
                right_ty,
                scope,
            )?,
            right_scale,
        ];
        let operator = if let Some(result_ty) = annotated_ty {
            let result_precision = decimal_type_precision(&result_ty)?;
            let result_scale = decimal_type_scale(&result_ty)?;
            lowered_args.push(z_constant_function(result_precision));
            lowered_args.push(z_constant_function(result_scale));
            ScalarOperator::NumericDivideTypmod
        } else {
            ScalarOperator::Divide(ScalarNumericKind::Numeric)
        };
        Some(FormalFunctionTerm::ScalarCall {
            operator,
            args: lowered_args,
        })
    }

    fn lower_decimal_cast_aggregate_term(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        operator: ScalarOperator,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        // Typmod cast operators report overflow through the same outer
        // runtime-error interpretation used by generated safety obligations.
        self.validate_numeric_cast_literal(path, arg, target_ty)?;
        let mut args = vec![self.lower_aggregate_term(path, arg, scope)?];
        if let FormalAttributeType::Decimal { precision, scale } = target_ty {
            args.push(z_constant_aggregate(precision));
            args.push(z_constant_aggregate(scale));
        }
        Some(FormalAggregateTerm::ScalarCall { operator, args })
    }

    fn lower_decimal_cast_function_term(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        operator: ScalarOperator,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        self.validate_numeric_cast_literal(path, arg, target_ty)?;
        let mut args = vec![self.lower_function_term(path, arg, scope)?];
        if let FormalAttributeType::Decimal { precision, scale } = target_ty {
            args.push(z_constant_function(precision));
            args.push(z_constant_function(scale));
        }
        Some(FormalFunctionTerm::ScalarCall { operator, args })
    }

    fn lower_string_cast_aggregate_term(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        if typed_literal_raw(arg).is_some_and(is_null_literal) {
            return Some(FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Constant {
                    raw: "NULL".to_owned(),
                    ty: Some(target_ty),
                },
            });
        }
        let (tag, length) = string_typmod_codes(target_ty)?;
        let source = annotate_literal_term(
            self.lower_aggregate_term(path, arg, scope)?,
            FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
        );
        Some(FormalAggregateTerm::ScalarCall {
            operator: ScalarOperator::Cast(ScalarCast::StringExplicit),
            args: vec![
                source,
                z_constant_aggregate(tag),
                z_constant_aggregate(length),
            ],
        })
    }

    fn lower_string_cast_function_term(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        target_ty: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        if typed_literal_raw(arg).is_some_and(is_null_literal) {
            return Some(FormalFunctionTerm::Constant {
                raw: "NULL".to_owned(),
                ty: Some(target_ty),
            });
        }
        let (tag, length) = string_typmod_codes(target_ty)?;
        let source = annotate_function_literal_term(
            self.lower_function_term(path, arg, scope)?,
            FormalAttributeType::String {
                typmod: SqlStringType::Text,
            },
        );
        Some(FormalFunctionTerm::ScalarCall {
            operator: ScalarOperator::Cast(ScalarCast::StringExplicit),
            args: vec![
                source,
                z_constant_function(tag),
                z_constant_function(length),
            ],
        })
    }

    fn validate_numeric_cast_literal(
        &mut self,
        path: &str,
        arg: &ScalarAst,
        target_ty: FormalAttributeType,
    ) -> Option<()> {
        if matches!(target_ty, FormalAttributeType::Decimal { .. })
            && let Some(raw) = typed_literal_raw(arg)
            && !numeric_literal_fits_type(raw, target_ty)
        {
            self.error(
                path,
                "numeric_cast_literal_overflow",
                "The NUMERIC literal does not fit the target DECIMAL(p,s) typmod.",
            );
            None
        } else {
            Some(())
        }
    }

    fn static_numeric_operand_dscale(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<u32> {
        self.infer_numeric_dscale(ast, scope)
            .and_then(|provenance| numeric_dscale_representative(&provenance))
            .or_else(|| {
                self.direct_function_type(&format!("{path}.integralType"), ast, scope)
                    .filter(|ty| is_integral_type(*ty))
                    .map(|_| 0)
            })
    }

    fn lower_numeric_dscale_aggregate_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        if let Some(NumericDscaleProvenance::Attribute(name)) =
            self.infer_numeric_dscale(ast, scope)
        {
            return Some(FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name,
                    ty: FormalAttributeType::Z,
                },
            });
        }
        if let Some(scale) = self.static_numeric_operand_dscale(path, ast, scope) {
            return Some(z_constant_aggregate(scale));
        }
        let Some(args) = numeric_division_dscale_args(ast) else {
            self.error(
                path,
                "numeric_display_scale_not_available",
                "PostgreSQL scale-sensitive NUMERIC evaluation requires a static display scale or an exact modeled NUMERIC division whose runtime-selected result scale can be reconstructed.",
            );
            return None;
        };
        let [left_ty, right_ty] =
            self.numeric_binary_arg_types(&format!("{path}.argTypes"), args, scope)?;
        Some(FormalAggregateTerm::ScalarCall {
            operator: ScalarOperator::NumericDivideResultScale,
            args: vec![
                self.lower_numeric_coerced_aggregate_term(
                    &format!("{path}.args[0]"),
                    &args[0],
                    left_ty,
                    scope,
                )?,
                self.lower_numeric_dscale_aggregate_term(
                    &format!("{path}.args[0].scale"),
                    &args[0],
                    scope,
                )?,
                self.lower_numeric_coerced_aggregate_term(
                    &format!("{path}.args[1]"),
                    &args[1],
                    right_ty,
                    scope,
                )?,
                self.lower_numeric_dscale_aggregate_term(
                    &format!("{path}.args[1].scale"),
                    &args[1],
                    scope,
                )?,
            ],
        })
    }

    fn lower_numeric_dscale_function_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        if let Some(NumericDscaleProvenance::Attribute(name)) =
            self.infer_numeric_dscale(ast, scope)
        {
            return Some(FormalFunctionTerm::Attribute {
                name,
                ty: FormalAttributeType::Z,
            });
        }
        if let Some(scale) = self.static_numeric_operand_dscale(path, ast, scope) {
            return Some(z_constant_function(scale));
        }
        let Some(args) = numeric_division_dscale_args(ast) else {
            self.error(
                path,
                "numeric_display_scale_not_available",
                "PostgreSQL scale-sensitive NUMERIC evaluation requires a static display scale or an exact modeled NUMERIC division whose runtime-selected result scale can be reconstructed.",
            );
            return None;
        };
        let [left_ty, right_ty] =
            self.numeric_binary_arg_types(&format!("{path}.argTypes"), args, scope)?;
        Some(FormalFunctionTerm::ScalarCall {
            operator: ScalarOperator::NumericDivideResultScale,
            args: vec![
                self.lower_numeric_coerced_function_term(
                    &format!("{path}.args[0]"),
                    &args[0],
                    left_ty,
                    scope,
                )?,
                self.lower_numeric_dscale_function_term(
                    &format!("{path}.args[0].scale"),
                    &args[0],
                    scope,
                )?,
                self.lower_numeric_coerced_function_term(
                    &format!("{path}.args[1]"),
                    &args[1],
                    right_ty,
                    scope,
                )?,
                self.lower_numeric_dscale_function_term(
                    &format!("{path}.args[1].scale"),
                    &args[1],
                    scope,
                )?,
            ],
        })
    }

    pub(super) fn infer_numeric_dscale(
        &mut self,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> Option<NumericDscaleProvenance> {
        match ast {
            ScalarAst::InputRef { index } => scope.attribute(*index)?.numeric_dscale,
            ScalarAst::CorrelatedRef {
                correlation,
                field,
                index,
                ..
            } => {
                self.correlated_attribute("numericDscale", correlation, *index, field)?
                    .numeric_dscale
            }
            ScalarAst::Literal { raw } => super::emit::parse_decimal_literal(raw)
                .map(|(_, scale)| NumericDscaleProvenance::Exact(scale)),
            ScalarAst::TypeAnnotation { expr, ty } => {
                if let Some(arg) = cast_arg(expr) {
                    return match formal_type_from_annotation(ty) {
                        Some(FormalAttributeType::Decimal { scale, .. }) => {
                            Some(NumericDscaleProvenance::Exact(scale))
                        }
                        Some(FormalAttributeType::Numeric) => self.infer_numeric_dscale(arg, scope),
                        _ => self.infer_numeric_dscale(expr, scope),
                    };
                }
                if let Some(raw) = typed_literal_raw(expr) {
                    return match formal_type_from_annotation(ty) {
                        Some(FormalAttributeType::Decimal { .. })
                        | Some(FormalAttributeType::Numeric) => {
                            super::emit::parse_decimal_literal(raw)
                                .map(|(_, scale)| NumericDscaleProvenance::Exact(scale))
                        }
                        Some(
                            FormalAttributeType::Z
                            | FormalAttributeType::Int32
                            | FormalAttributeType::Int64,
                        ) => Some(NumericDscaleProvenance::Exact(0)),
                        _ => self.infer_numeric_dscale(expr, scope),
                    };
                }
                self.infer_numeric_dscale(expr, scope)
            }
            ScalarAst::Call { op, args, .. } if args.len() == 2 => {
                let left = self.infer_numeric_dscale(&args[0], scope)?;
                let right = self.infer_numeric_dscale(&args[1], scope)?;
                match op {
                    ScalarOp::Plus | ScalarOp::Minus => numeric_dscale_add(left, right),
                    ScalarOp::Multiply => numeric_dscale_multiply(left, right),
                    _ => None,
                }
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1 => self.infer_numeric_dscale(&args[0], scope),
            ScalarAst::Call {
                op: ScalarOp::Case,
                args,
                ..
            } if args.len() >= 3 && !args.len().is_multiple_of(2) => {
                let results = args[..args.len() - 1]
                    .chunks_exact(2)
                    .map(|pair| &pair[1])
                    .chain(args.last());
                let mut nonzero = None;
                let mut greatest_zero_scale = None;
                for result in results {
                    // NULL contributes no NumericVar value and therefore no
                    // display scale to the value selected by CASE.  In
                    // particular, PostgreSQL's common CASE type may be
                    // typmodless NUMERIC for `DECIMAL(p,s) ELSE NULL`, while
                    // every observable non-NULL result still has scale s.
                    if is_untyped_null_literal(result)
                        || typed_literal_raw(result).is_some_and(is_null_literal)
                    {
                        continue;
                    }
                    let provenance = self.infer_numeric_dscale(result, scope)?;
                    if numeric_ast_is_exact_zero(result) {
                        let scale = numeric_dscale_representative(&provenance)?;
                        greatest_zero_scale = Some(
                            greatest_zero_scale.map_or(scale, |current: u32| current.max(scale)),
                        );
                    } else {
                        nonzero = Some(match nonzero {
                            None => provenance,
                            Some(current) => numeric_dscale_same_branch(current, provenance)?,
                        });
                    }
                }
                match (nonzero, greatest_zero_scale) {
                    (Some(provenance), None) => Some(provenance),
                    (Some(provenance), Some(zero_scale)) => {
                        let scale = numeric_dscale_representative(&provenance)?;
                        (zero_scale <= scale)
                            .then_some(NumericDscaleProvenance::Representative(scale))
                    }
                    (None, Some(zero_scale)) => {
                        Some(NumericDscaleProvenance::Representative(zero_scale))
                    }
                    (None, None) => None,
                }
            }
            _ => None,
        }
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
            ScalarAst::TypeAnnotation { expr, ty }
                if matches!(
                    formal_type_from_annotation(ty),
                    Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })
                ) && matches!(
                    expr.as_ref(),
                    ScalarAst::Call {
                        op: ScalarOp::Plus
                            | ScalarOp::Minus
                            | ScalarOp::Multiply
                            | ScalarOp::Divide,
                        ..
                    }
                ) =>
            {
                // Calcite attaches a derived DECIMAL precision/scale to Rex
                // arithmetic. PostgreSQL numeric operators return base type
                // numeric and exprTypmod does not propagate an OpExpr typmod.
                // Only the explicit ScalarOp::Cast representation below may
                // impose a DECIMAL(p,s) result typmod.
                self.direct_function_type(path, expr, scope)
            }
            ScalarAst::TypeAnnotation { expr, .. }
                if top_level_string_case_mapping(expr).is_some() =>
            {
                Some(FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                })
            }
            ScalarAst::TypeAnnotation { ty, .. } => formal_type_from_annotation(ty),
            ScalarAst::Call {
                op: ScalarOp::Case,
                args,
                ..
            } => self.infer_case_type(path, args, scope),
            ScalarAst::Call {
                op: op @ (ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide),
                args,
                ..
            } if args.len() == 2 => self.infer_arithmetic_type(path, op, args, scope),
            ScalarAst::Call {
                op: op @ ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1 => self.infer_arithmetic_type(path, op, args, scope),
            ScalarAst::Call {
                op: ScalarOp::StringConcat,
                args,
                ..
            } if args.len() == 2 => Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
            ScalarAst::Call {
                op: ScalarOp::Lower | ScalarOp::Upper,
                args,
                ..
            } if args.len() == 1 => Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
            ScalarAst::Call {
                op: ScalarOp::Substring,
                args,
                ..
            } if args.len() == 3 => Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
            ScalarAst::Call {
                op: ScalarOp::Extract,
                args,
                ..
            } => extract_date_field(args).and_then(|(_, arg)| {
                (self.infer_function_type(&format!("{path}.date"), arg, scope)
                    == Some(FormalAttributeType::Date))
                .then_some(FormalAttributeType::Numeric)
            }),
            _ => None,
        }
    }

    fn validate_string_concat_args(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<()> {
        if args.len() != 2 {
            self.error(
                path,
                "string_concat_arity_not_supported",
                "PostgreSQL || is a binary operator, so string concatenation lowering requires exactly two operands per AST node.",
            );
            return None;
        }
        for (index, arg) in args.iter().enumerate() {
            let arg_path = format!("{path}.args[{index}]");
            let ty = self.direct_function_type(&arg_path, arg, scope).or_else(|| {
                if matches!(arg, ScalarAst::Literal { raw } if sql_string_literal_content(raw).is_some())
                {
                    Some(FormalAttributeType::String {
                        typmod: SqlStringType::Text,
                    })
                } else {
                    None
                }
            });
            if !ty.is_some_and(is_string_type) {
                self.error(
                    &arg_path,
                    "string_concat_operand_type_not_supported",
                    "The modeled PostgreSQL || operator currently accepts only character-string operands with recoverable SQL types.",
                );
                return None;
            }
        }
        let input_types = scope
            .attributes
            .iter()
            .map(|attribute| Some(attribute.formal_ty))
            .collect::<Vec<_>>();
        let payload_bytes = args.iter().try_fold(0_u64, |total, arg| {
            total.checked_add(string_expr_max_bytes(arg, &input_types)?)
        });
        if !payload_bytes.is_some_and(|bytes| {
            bytes
                .checked_add(POSTGRES_VARLENA_HEADER_BYTES)
                .is_some_and(|allocation| allocation <= POSTGRES_MAX_ALLOC_SIZE)
        }) {
            self.error(
                path,
                "string_concat_size_not_provably_total",
                "PostgreSQL text concatenation raises program_limit_exceeded when the two payloads plus the varlena header exceed MaxAllocSize. Lowering requires bounded literals/CHAR(n)/VARCHAR(n) operands whose worst-case encoded size is within that limit.",
            );
            return None;
        }
        Some(())
    }

    fn lower_string_concat_aggregate_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        self.validate_string_concat_args(path, args, scope)?;
        Some(FormalAggregateTerm::ScalarCall {
            operator: ScalarOperator::StringConcat,
            args: args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let ty = self
                        .direct_function_type(&format!("{path}.args[{index}].type"), arg, scope)
                        .or_else(|| {
                            is_untyped_string_literal(arg).then_some(FormalAttributeType::String {
                                typmod: SqlStringType::Text,
                            })
                        })?;
                    Some(annotate_literal_term(
                        self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)?,
                        ty,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn lower_string_concat_function_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        self.validate_string_concat_args(path, args, scope)?;
        Some(FormalFunctionTerm::ScalarCall {
            operator: ScalarOperator::StringConcat,
            args: args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let ty = self
                        .direct_function_type(&format!("{path}.args[{index}].type"), arg, scope)
                        .or_else(|| {
                            is_untyped_string_literal(arg).then_some(FormalAttributeType::String {
                                typmod: SqlStringType::Text,
                            })
                        })?;
                    Some(annotate_function_literal_term(
                        self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)?,
                        ty,
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn validate_substring_args(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<()> {
        let [value, start, count] = args else {
            self.error(
                path,
                "substring_shape_not_supported",
                "Exact PostgreSQL SUBSTRING lowering requires three operands: a bounded character value, a literal start, and a literal count.",
            );
            return None;
        };
        let value_ty = self.direct_function_type(&format!("{path}.args[0]"), value, scope);
        if !matches!(
            value_ty,
            Some(FormalAttributeType::String {
                typmod: SqlStringType::Char { .. } | SqlStringType::Varchar { length: Some(_) },
            })
        ) || !value_ty
            .and_then(string_type_max_bytes)
            .is_some_and(|bytes| {
                bytes
                    .checked_add(POSTGRES_VARLENA_HEADER_BYTES)
                    .is_some_and(|allocation| allocation <= POSTGRES_MAX_ALLOC_SIZE)
            })
        {
            self.error(
                &format!("{path}.args[0]"),
                "substring_operand_type_not_supported",
                "Exact PostgreSQL SUBSTRING lowering currently requires an authoritative bounded CHAR(n) or VARCHAR(n) operand whose maximum text result fits PostgreSQL MaxAllocSize.",
            );
            return None;
        }
        let start_value = typed_literal_raw(start)
            .and_then(|raw| raw.trim().parse::<i32>().ok())
            .filter(|_| {
                self.direct_function_type(&format!("{path}.args[1]"), start, scope)
                    == Some(FormalAttributeType::Int32)
            });
        if start_value.is_none_or(|value| value < 1) {
            self.error(
                &format!("{path}.args[1]"),
                "substring_start_not_supported",
                "Exact PostgreSQL SUBSTRING lowering currently requires a typed INTEGER literal start of at least one.",
            );
            return None;
        }
        let count_value = typed_literal_raw(count)
            .and_then(|raw| raw.trim().parse::<i32>().ok())
            .filter(|_| {
                self.direct_function_type(&format!("{path}.args[2]"), count, scope)
                    == Some(FormalAttributeType::Int32)
            });
        if count_value.is_none_or(|value| value < 0) {
            self.error(
                &format!("{path}.args[2]"),
                "substring_count_not_supported",
                "Exact PostgreSQL SUBSTRING lowering currently requires a typed nonnegative INTEGER literal count; negative and dynamic counts remain unsupported.",
            );
            return None;
        }
        Some(())
    }

    fn lower_substring_aggregate_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        self.validate_substring_args(path, args, scope)?;
        Some(FormalAggregateTerm::ScalarCall {
            operator: ScalarOperator::SubstringNonnegative,
            args: args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)
                })
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn lower_substring_function_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        self.validate_substring_args(path, args, scope)?;
        Some(FormalFunctionTerm::ScalarCall {
            operator: ScalarOperator::SubstringNonnegative,
            args: args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)
                })
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn modeled_like_pattern_for_args(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<ModeledLikePattern> {
        let [value, ScalarAst::Literal { raw: pattern_raw }] = args else {
            self.error(
                path,
                "like_pattern_not_supported",
                "FormalSQL LIKE lowering requires one string operand and one non-NULL source literal pattern.",
            );
            return None;
        };
        let value_ty = self.infer_function_type(&format!("{path}.valueType"), value, scope);
        if !value_ty.is_some_and(is_string_type) {
            self.error(
                &format!("{path}.args[0]"),
                "like_operand_type_not_supported",
                "The modeled LIKE subset requires an authoritative PostgreSQL character-string operand type.",
            );
            return None;
        }
        if matches!(
            value_ty,
            Some(FormalAttributeType::String {
                typmod: SqlStringType::Bpchar,
            })
        ) {
            self.error(
                &format!("{path}.args[0]"),
                "like_typmodless_bpchar_not_supported",
                "PostgreSQL LIKE observes the physical trailing spaces of typmodless bpchar values, but the current logical carrier has no width from which to reconstruct them. Fixed-width CHAR(n), VARCHAR, and text operands remain supported.",
            );
            return None;
        }
        let pattern = sql_string_literal_content(pattern_raw).or_else(|| {
            self.error(
                &format!("{path}.args[1]"),
                "like_pattern_not_supported",
                "The LIKE pattern must be a non-NULL SQL string literal.",
            );
            None
        })?;
        if pattern.contains(['_', '\\']) {
            self.error(
                &format!("{path}.args[1]"),
                "like_pattern_not_supported",
                "The exact LIKE subset accepts literal characters and unescaped percent wildcards; underscore and escape syntax remain unsupported.",
            );
            return None;
        }
        if let Some(prefix) = pattern.strip_suffix('%')
            && !prefix.contains('%')
            && !prefix.ends_with(' ')
        {
            return Some(ModeledLikePattern {
                kind: ModeledLikeKind::Prefix,
                value: prefix.to_owned(),
            });
        }
        Some(ModeledLikePattern {
            kind: ModeledLikeKind::Percent,
            value: pattern,
        })
    }

    fn lower_modeled_like_aggregate_args(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<(ModeledLikeKind, Vec<FormalAggregateTerm>)> {
        let pattern = self.modeled_like_pattern_for_args(path, args, scope)?;
        Some((
            pattern.kind,
            vec![
                self.lower_aggregate_term(&format!("{path}.args[0]"), &args[0], scope)?,
                FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Constant {
                        raw: format!("'{}'", pattern.value.replace('\'', "''")),
                        ty: Some(FormalAttributeType::String {
                            typmod: SqlStringType::Text,
                        }),
                    },
                },
            ],
        ))
    }

    fn lower_modeled_like_function_args(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<(ScalarOperator, Vec<FormalFunctionTerm>)> {
        let pattern = self.modeled_like_pattern_for_args(path, args, scope)?;
        Some((
            ScalarOperator::PredicateValue(pattern.kind.predicate()),
            vec![
                self.lower_function_term(&format!("{path}.args[0]"), &args[0], scope)?,
                FormalFunctionTerm::Constant {
                    raw: format!("'{}'", pattern.value.replace('\'', "''")),
                    ty: Some(FormalAttributeType::String {
                        typmod: SqlStringType::Text,
                    }),
                },
            ],
        ))
    }

    fn lower_case_aggregate_term(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        if args.len() < 3 || args.len().is_multiple_of(2) {
            self.error(
                path,
                "case_arity_not_supported",
                "FormalSQL CASE lowering expects Calcite searched-CASE operands as WHEN/THEN pairs followed by an ELSE expression.",
            );
            return None;
        }
        let result_ty = self
            .infer_case_type(&format!("{path}.resultType"), args, scope)
            .or_else(|| {
                self.error(
                    path,
                    "case_result_type_not_supported",
                    "FormalSQL CASE lowering could not recover PostgreSQL's common result type from the structured alternatives.",
                );
                None
            })?;
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
                then_expr: {
                    let branch_path = format!("{path}.branches[{branch_index}].then");
                    let term = self.lower_aggregate_term(&branch_path, &pair[1], scope)?;
                    self.coerce_case_result(&branch_path, &pair[1], term, result_ty, scope)?
                },
            });
        }

        let else_path = format!("{path}.else");
        let else_ast = args.last().expect("CASE arity checked");
        let else_term = self.lower_aggregate_term(&else_path, else_ast, scope)?;
        Some(FormalAggregateTerm::Case {
            branches,
            else_expr: Box::new(
                self.coerce_case_result(&else_path, else_ast, else_term, result_ty, scope)?,
            ),
        })
    }

    fn coerce_case_result(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        term: FormalAggregateTerm,
        target: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        match self.case_result_type_source(path, ast, scope) {
            CaseResultTypeSource::UnknownNull | CaseResultTypeSource::UnknownString => {
                Some(annotate_case_result_literal_term(term, ast, target))
            }
            CaseResultTypeSource::Known(source) if source == target => {
                Some(annotate_case_result_literal_term(term, ast, target))
            }
            CaseResultTypeSource::Known(source)
                if is_string_type(source) && is_string_type(target) =>
            {
                string_implicit_coercion_aggregate_term(term, target)
            }
            CaseResultTypeSource::Known(source)
                if is_exact_numeric_type(source) && target == FormalAttributeType::Numeric =>
            {
                Some(FormalAggregateTerm::ScalarCall {
                    operator: decimal_typmod_cast_operator(&source, &target)?,
                    args: vec![term],
                })
            }
            CaseResultTypeSource::Known(source)
                if is_integral_type(source) && target == FormalAttributeType::Numeric =>
            {
                Some(FormalAggregateTerm::ScalarCall {
                    operator: decimal_typmod_cast_operator(&source, &target)?,
                    args: vec![annotate_literal_term(term, source)],
                })
            }
            CaseResultTypeSource::Known(source) => {
                self.error(
                    path,
                    "case_result_coercion_not_supported",
                    &format!(
                        "FormalSQL CASE result requires an unmodeled implicit coercion from {source:?} to {target:?}."
                    ),
                );
                None
            }
            CaseResultTypeSource::Unsupported => {
                self.error(
                    path,
                    "case_result_type_not_supported",
                    "FormalSQL CASE result type is unavailable for PostgreSQL common-type coercion.",
                );
                None
            }
        }
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
                Some(annotate_literal_term(
                    self.lower_aggregate_term(&format!("{path}.args[{index}]"), arg, scope)?,
                    FormalAttributeType::Bool,
                ))
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter();
        let mut acc = lowered.next().expect("non-empty AND/OR checked");
        for right in lowered {
            acc = FormalAggregateTerm::ScalarCall {
                operator: self.scalar_operator_for_args(path, op, args, scope)?,
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
        self.reject_locale_dependent_string_case_mapping(path, ast)?;
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
            ScalarAst::Call {
                op: ScalarOp::Case,
                args,
                ..
            } => {
                let term = self.lower_case_aggregate_term(path, args, scope)?;
                aggregate_term_into_function_term(term).or_else(|| {
                    self.error(
                        path,
                        "case_function_term_not_supported",
                        "A scalar CASE used as an aggregate argument unexpectedly contains an aggregate subterm.",
                    );
                    None
                })
            }
            ScalarAst::Call {
                op: ScalarOp::Extract,
                args,
                ..
            } => {
                let (operator, arg) = self.lower_extract_date_function_arg(path, args, scope)?;
                Some(FormalFunctionTerm::ScalarCall {
                    operator,
                    args: vec![arg],
                })
            }
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_date(ty) => self
                .lower_temporal_type_annotation(path, expr, ty, scope, FormalAttributeType::Date),
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_time(ty) => {
                if !time_annotation_precision_is_supported(ty) {
                    self.error(
                        path,
                        "time_precision_semantics_not_supported",
                        "FormalSQL TIME currently models PostgreSQL's default microsecond precision only; explicit TIME precision below 6 changes rounding and output typing.",
                    );
                    return None;
                }
                self.lower_temporal_type_annotation(
                    path,
                    expr,
                    ty,
                    scope,
                    FormalAttributeType::Time,
                )
            }
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_timestamp_tz(ty) => {
                let typed_raw = typed_literal_raw(expr);
                let cast_raw = cast_literal_raw(expr);
                let raw = typed_raw.or(cast_raw).or_else(|| {
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
                let micros = if cast_raw.is_some() {
                    super::emit::source_timestamptz_cast_to_utc_micros(
                        raw,
                        timestamp_precision(precision),
                        &self.config.sql_time_zone,
                    )
                } else {
                    super::emit::timestamptz_literal_to_utc_micros(
                        raw,
                        timestamp_precision(precision),
                        &self.config.sql_time_zone,
                    )
                };
                let Some(micros) = micros else {
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
                self.validate_closed_type_annotation(path, ty)?;
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
                    if is_exact_numeric_type(formal_ty)
                        && !raw.eq_ignore_ascii_case("null")
                        && !numeric_literal_fits_type(raw, formal_ty)
                    {
                        self.error(
                            path,
                            "numeric_literal_not_supported",
                            "FormalSQL NUMERIC/DECIMAL lowering accepts finite decimal literals within PostgreSQL runtime bounds; constrained values must also fit DECIMAL(p,s). NaN and infinities are rejected.",
                        );
                        return None;
                    }
                    if let FormalAttributeType::Timestamp { precision }
                    | FormalAttributeType::Timestamptz { precision } = formal_ty
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
                if let Some(cast_arg) = cast_arg(expr) {
                    let target_ty = formal_type_from_annotation(ty).or_else(|| {
                        self.error(
                            path,
                            "cast_target_type_not_supported",
                            "FormalSQL lowering cannot infer the target type of this explicit CAST.",
                        );
                        None
                    })?;
                    if target_ty == FormalAttributeType::Int32
                        && let Some(base) = postgres_power_half_int64_base(cast_arg)
                        && self.infer_numeric_operand_type(
                            &format!("{path}.powerHalfBase"),
                            base,
                            scope,
                        ) == Some(FormalAttributeType::Int64)
                    {
                        return Some(FormalFunctionTerm::ScalarCall {
                            operator: ScalarOperator::PowerHalfInt64ToInt32,
                            args: vec![self.lower_function_term(
                                &format!("{path}.powerHalfBase"),
                                base,
                                scope,
                            )?],
                        });
                    }
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
                    if let Some(operator) = simple_numeric_cast_operator(&source_ty, &target_ty) {
                        return Some(FormalFunctionTerm::ScalarCall {
                            operator,
                            args: vec![self.lower_function_term(
                                &format!("{path}.castArg"),
                                cast_arg,
                                scope,
                            )?],
                        });
                    }
                    if let Some(operator) = string_integer_cast_operator(&source_ty, &target_ty) {
                        let source = annotate_function_literal_term(
                            self.lower_function_term(&format!("{path}.castArg"), cast_arg, scope)?,
                            source_ty,
                        );
                        return Some(FormalFunctionTerm::ScalarCall {
                            operator,
                            args: vec![source],
                        });
                    }
                    if let Some(operator) = decimal_typmod_cast_operator(&source_ty, &target_ty) {
                        return self.lower_decimal_cast_function_term(
                            &format!("{path}.castArg"),
                            cast_arg,
                            operator,
                            target_ty,
                            scope,
                        );
                    }
                    if is_string_type(source_ty)
                        && target_ty == FormalAttributeType::Bool
                        && let Some(raw) = typed_literal_raw(cast_arg)
                        && let Some(value) = parse_postgres_boolean_source_literal(raw)
                    {
                        return Some(FormalFunctionTerm::Constant {
                            raw: value.to_string(),
                            ty: Some(FormalAttributeType::Bool),
                        });
                    }
                    if is_string_type(source_ty) && is_string_type(target_ty) {
                        return self.lower_string_cast_function_term(
                            &format!("{path}.castArg"),
                            cast_arg,
                            target_ty,
                            scope,
                        );
                    }
                    self.error(
                        path,
                        "cast_not_supported",
                        &format!(
                            "Explicit CAST from {source_ty:?} to {target_ty:?} is not in the FormalSQL cast whitelist.",
                        ),
                    );
                    return None;
                }
                // Ignore inferred Rex typmods. Only an explicit ScalarOp::Cast above
                // is allowed to round a PostgreSQL NUMERIC value to DECIMAL(p,s).
                self.lower_function_term(path, expr, scope)
            }
            ScalarAst::Call { op, args, .. }
                if matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
                    && args.len() == 2
                    && self
                        .numeric_binary_arg_types(&format!("{path}.decimalArgs"), args, scope)
                        .is_some() =>
            {
                let arg_types =
                    self.numeric_binary_arg_types(&format!("{path}.decimalArgs"), args, scope)?;
                let operator = match op {
                    ScalarOp::Plus => ScalarOperator::Add(ScalarNumericKind::Numeric),
                    ScalarOp::Minus => ScalarOperator::Subtract(ScalarNumericKind::Numeric),
                    ScalarOp::Multiply => ScalarOperator::Multiply(ScalarNumericKind::Numeric),
                    _ => unreachable!("decimal arithmetic guard checked"),
                };
                Some(FormalFunctionTerm::ScalarCall {
                    operator,
                    args: args
                        .iter()
                        .enumerate()
                        .zip(arg_types)
                        .map(|((index, arg), ty)| {
                            self.lower_numeric_coerced_function_term(
                                &format!("{path}.args[{index}]"),
                                arg,
                                ty,
                                scope,
                            )
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
                Some(FormalFunctionTerm::ScalarCall {
                    operator: floating_operator(op, ty)?,
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
            ScalarAst::Call { op, args, .. }
                if matches!(
                    op,
                    ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
                ) && args.len() == 2
                    && self
                        .integral_binary_type(&format!("{path}.integerArgs"), args, scope)
                        .is_some() =>
            {
                let ty = self.integral_binary_type(&format!("{path}.integerArgs"), args, scope)?;
                Some(FormalFunctionTerm::ScalarCall {
                    operator: integer_binary_operator(op, ty)?,
                    args: args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            self.lower_integral_coerced_function_term(
                                &format!("{path}.args[{index}]"),
                                arg,
                                ty,
                                scope,
                            )
                        })
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            ScalarAst::Call {
                op: ScalarOp::Minus,
                args,
                ..
            } if args.len() == 1
                && self
                    .infer_function_type(&format!("{path}.argType"), &args[0], scope)
                    .is_some_and(is_integral_type) =>
            {
                let ty = self.infer_function_type(&format!("{path}.argType"), &args[0], scope)?;
                Some(FormalFunctionTerm::ScalarCall {
                    operator: integer_unary_minus_operator(ty)?,
                    args: vec![
                        self.lower_function_term(&format!("{path}.arg"), &args[0], scope)
                            .map(|term| annotate_function_literal_term(term, ty))?,
                    ],
                })
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
                Some(FormalFunctionTerm::ScalarCall {
                    operator: floating_unary_minus_operator(ty)?,
                    args: vec![self.lower_function_term(
                        &format!("{path}.arg"),
                        &args[0],
                        scope,
                    )?],
                })
            }
            ScalarAst::Call { op, args, .. }
                if op.is_comparison()
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
                    && args.len() == 2
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
                Some(FormalFunctionTerm::ScalarCall {
                    operator: ScalarOperator::Negate(ScalarNumericKind::Numeric),
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
                && self
                    .numeric_binary_arg_types(&format!("{path}.decimalArgs"), args, scope)
                    .is_some() =>
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
            ScalarAst::Call {
                op: ScalarOp::StringConcat,
                args,
                ..
            } => self.lower_string_concat_function_term(path, args, scope),
            ScalarAst::Call {
                op: ScalarOp::Substring,
                args,
                ..
            } => self.lower_substring_function_term(path, args, scope),
            ScalarAst::Call {
                op: ScalarOp::Like,
                args,
                ..
            } => {
                let (operator, args) = self.lower_modeled_like_function_args(path, args, scope)?;
                Some(FormalFunctionTerm::ScalarCall { operator, args })
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
                if function_requires_external_interpretation(op) {
                    self.error(
                        path,
                        "function_interpretation_not_supported",
                        "FormalSQL lowering requires a built-in Rocq interpretation for every emitted SQL scalar function.",
                    );
                    return None;
                }
                let operator = self.scalar_operator_for_args(path, op, args, scope)?;
                let lowered_args = args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        self.lower_function_term(&format!("{path}.args[{index}]"), arg, scope)
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(FormalFunctionTerm::ScalarCall {
                    operator,
                    args: lowered_args,
                })
            }
            ScalarAst::Call {
                op: ScalarOp::In, ..
            } => {
                self.error(
                    path,
                    "flat_leaf_in_not_supported",
                    "Query-valued IN is represented by the native scalar AST and cannot be embedded in a legacy flat function-term leaf.",
                );
                None
            }
            ScalarAst::Call {
                op: ScalarOp::ScalarQuery,
                ..
            } => {
                self.error(
                    path,
                    "flat_leaf_scalar_subquery_not_supported",
                    "Scalar subqueries are represented natively and cannot be embedded in a legacy flat function-term leaf.",
                );
                None
            }
            ScalarAst::Window { .. }
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

    fn lower_extract_date_aggregate_arg(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<(ScalarOperator, FormalAggregateTerm)> {
        let (part, arg) = self.extract_date_arg(path, args, scope)?;
        Some((
            ScalarOperator::ExtractDate(part),
            self.lower_aggregate_term(&format!("{path}.date"), arg, scope)?,
        ))
    }

    fn lower_extract_date_function_arg(
        &mut self,
        path: &str,
        args: &[ScalarAst],
        scope: &Scope,
    ) -> Option<(ScalarOperator, FormalFunctionTerm)> {
        let (part, arg) = self.extract_date_arg(path, args, scope)?;
        Some((
            ScalarOperator::ExtractDate(part),
            self.lower_function_term(&format!("{path}.date"), arg, scope)?,
        ))
    }

    fn extract_date_arg<'a>(
        &mut self,
        path: &str,
        args: &'a [ScalarAst],
        scope: &Scope,
    ) -> Option<(ScalarDatePart, &'a ScalarAst)> {
        let Some((part, arg)) = extract_date_field(args) else {
            self.error(
                path,
                "extract_shape_not_supported",
                "FormalSQL EXTRACT currently supports exactly YEAR or MONTH from a PostgreSQL DATE.",
            );
            return None;
        };
        if self.infer_function_type(&format!("{path}.dateType"), arg, scope)
            != Some(FormalAttributeType::Date)
        {
            self.error(
                &format!("{path}.date"),
                "extract_source_type_not_supported",
                "EXTRACT(YEAR/MONTH ...) lowering requires a PostgreSQL DATE operand.",
            );
            return None;
        }
        Some((part, arg))
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
        if let Some(raw) = typed_literal_raw(expr) {
            return self.lower_temporal_constant(path, raw, target_ty);
        }
        if let Some(raw) = cast_literal_raw(expr) {
            return self.lower_temporal_source_cast_constant(path, raw, target_ty);
        }

        if matches!(
            expr,
            ScalarAst::InputRef { .. } | ScalarAst::CorrelatedRef { .. }
        ) {
            let source_ty =
                self.infer_function_type(&format!("{path}.annotatedExpression"), expr, scope)?;
            if !temporal_annotation_types_match(source_ty, target_ty) {
                self.error(
                    path,
                    "temporal_annotation_type_mismatch",
                    "An inferred temporal Rex annotation must preserve the input expression's modeled SQL type and precision.",
                );
                return None;
            }
            return self.lower_function_term(path, expr, scope);
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
            let operator = temporal_cast_operator(&source_ty, &target_ty).or_else(|| {
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
            return Some(FormalFunctionTerm::ScalarCall {
                operator,
                args: vec![arg],
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
            FormalAttributeType::Date => {
                if !is_null_literal(raw) && !super::emit::date_literal_conforms_to_day(raw) {
                    self.error(
                        path,
                        "date_literal_not_supported",
                        "DATE literal must be within PostgreSQL's finite DATE range.",
                    );
                    return None;
                }
                Some(FormalFunctionTerm::Constant {
                    raw: raw.to_owned(),
                    ty: Some(FormalAttributeType::Date),
                })
            }
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
                        "TIMESTAMP literal is outside PostgreSQL's finite range or has more fractional precision than its annotated SQL precision.",
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

    fn lower_temporal_source_cast_constant(
        &mut self,
        path: &str,
        raw: &str,
        target_ty: FormalAttributeType,
    ) -> Option<FormalFunctionTerm> {
        if is_null_literal(raw) {
            return Some(FormalFunctionTerm::Constant {
                raw: raw.to_owned(),
                ty: Some(target_ty),
            });
        }
        let encoded = match target_ty {
            FormalAttributeType::Date => super::emit::parse_source_date_cast_literal(raw),
            FormalAttributeType::Time => super::emit::parse_source_time_cast_literal(raw),
            FormalAttributeType::Timestamp { precision } => {
                super::emit::parse_source_timestamp_cast_literal(
                    raw,
                    timestamp_precision(precision),
                )
            }
            _ => None,
        };
        let Some(encoded) = encoded else {
            self.error(
                path,
                "temporal_source_cast_literal_not_supported",
                "The source string is outside the exact PostgreSQL temporal input subset modeled by FormalSQL lowering.",
            );
            return None;
        };
        Some(FormalFunctionTerm::Constant {
            raw: encoded.to_string(),
            ty: Some(target_ty),
        })
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
            ScalarAst::Flag { .. } | ScalarAst::Window { .. } | ScalarAst::RelSubquery { .. } => {
                None
            }
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
            ScalarOp::Extract => extract_date_field(args).and_then(|(_, arg)| {
                (self.infer_function_type(&format!("{path}.date"), arg, scope)
                    == Some(FormalAttributeType::Date))
                .then_some(FormalAttributeType::Numeric)
            }),
            ScalarOp::Case => self.infer_case_type(path, args, scope),
            ScalarOp::StringConcat if args.len() == 2 => Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
            ScalarOp::Lower | ScalarOp::Upper if args.len() == 1 => {
                Some(FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                })
            }
            ScalarOp::Substring if args.len() == 3 => Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
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
                if is_exact_numeric_type(ty) {
                    Some(FormalAttributeType::Numeric)
                } else {
                    is_numeric_type(ty).then_some(ty)
                }
            }
            [left, right] => {
                let left_ty =
                    self.infer_numeric_operand_type(&format!("{path}.left"), left, scope)?;
                let right_ty =
                    self.infer_numeric_operand_type(&format!("{path}.right"), right, scope)?;
                if left_ty == FormalAttributeType::Z && right_ty == FormalAttributeType::Z {
                    return Some(FormalAttributeType::Z);
                }
                if is_integral_type(left_ty) && is_integral_type(right_ty) {
                    return Some(integral_binary_result_type(left_ty, right_ty));
                }
                if is_float_type(left_ty) || is_float_type(right_ty) {
                    return (left_ty == right_ty && is_float_type(left_ty)).then_some(left_ty);
                }
                if is_exact_numeric_type(left_ty) && is_exact_numeric_type(right_ty) {
                    return Some(FormalAttributeType::Numeric);
                }
                if (is_exact_numeric_type(left_ty) && is_integral_type(right_ty))
                    || (is_integral_type(left_ty) && is_exact_numeric_type(right_ty))
                {
                    return Some(FormalAttributeType::Numeric);
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
        let left_is_exact = is_exact_numeric_type(left_ty);
        let right_is_exact = is_exact_numeric_type(right_ty);
        let left_is_integral = is_integral_type(left_ty);
        let right_is_integral = is_integral_type(right_ty);
        let left_is_float = is_float_type(left_ty);
        let right_is_float = is_float_type(right_ty);

        // PostgreSQL exposes exactly two POWER overloads: numeric/numeric ->
        // numeric and double precision/double precision -> double precision.
        // An exact numeric argument selects the numeric overload when the
        // other argument is exact or integral.  Any floating argument selects
        // the double-precision overload, and two integral arguments also pick
        // that preferred numeric-category overload.  A constrained DECIMAL
        // result loses its input typmod, as PostgreSQL's numeric POWER does.
        if (left_is_exact && (right_is_exact || right_is_integral))
            || (right_is_exact && left_is_integral)
        {
            Some(FormalAttributeType::Numeric)
        } else if (left_is_exact || left_is_integral || left_is_float)
            && (right_is_exact || right_is_integral || right_is_float)
            && (left_is_float || right_is_float || (left_is_integral && right_is_integral))
        {
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
        if args.len() < 3 || args.len().is_multiple_of(2) {
            return None;
        }

        // PostgreSQL considers ELSE before THEN alternatives for CASE common
        // type selection. Unknown string/NULL literals participate in base-type
        // resolution and force constrained character typmods to be discarded.
        let mut sources = Vec::with_capacity(args.len() / 2 + 1);
        sources.push(self.case_result_type_source(
            &format!("{path}.else"),
            args.last().expect("CASE arity checked"),
            scope,
        ));
        for (branch_index, pair) in args[..args.len() - 1].chunks_exact(2).enumerate() {
            sources.push(self.case_result_type_source(
                &format!("{path}.branches[{branch_index}].then"),
                &pair[1],
                scope,
            ));
        }
        postgres_case_common_type(&sources)
    }

    pub(super) fn infer_numeric_operand_type(
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

    fn case_result_type_source(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        scope: &Scope,
    ) -> CaseResultTypeSource {
        if is_untyped_null_literal(ast) {
            return CaseResultTypeSource::UnknownNull;
        }
        if is_untyped_string_literal(ast) {
            return CaseResultTypeSource::UnknownString;
        }
        if let ScalarAst::TypeAnnotation { expr, .. } = ast
            && cast_arg(expr).is_none()
            && typed_literal_raw(expr).is_some_and(is_null_literal)
        {
            // Calcite commonly annotates an originally unknown NULL with the
            // selected CASE base type. PostgreSQL coerces it with typmod -1;
            // only an explicit ScalarOp::Cast carries an authoritative typmod.
            return CaseResultTypeSource::UnknownNull;
        }
        self.infer_function_type(path, ast, scope)
            .or_else(|| match ast {
                ScalarAst::Literal { raw } => infer_literal_cast_source_type(raw),
                _ => None,
            })
            .map(|ty| {
                if matches!(ty, FormalAttributeType::Decimal { .. })
                    && matches!(ast, ScalarAst::TypeAnnotation { expr, .. }
                        if cast_arg(expr).is_none() && typed_literal_raw(expr).is_some())
                {
                    // A bare Rex literal annotation is derived metadata, not
                    // a source-level numeric typmod coercion. Numeric Consts
                    // and Calcite-coerced integer alternatives both have
                    // PostgreSQL typmod -1 at this CASE boundary.
                    FormalAttributeType::Numeric
                } else {
                    ty
                }
            })
            .map(CaseResultTypeSource::Known)
            .unwrap_or(CaseResultTypeSource::Unsupported)
    }

    fn integral_binary_type(
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
        (is_integral_type(left_ty) && is_integral_type(right_ty))
            .then_some(integral_binary_result_type(left_ty, right_ty))
    }

    fn lower_integral_coerced_aggregate_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        target: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalAggregateTerm> {
        let source = self.infer_numeric_operand_type(&format!("{path}.type"), ast, scope)?;
        let term = annotate_literal_term(self.lower_aggregate_term(path, ast, scope)?, source);
        match (source, target) {
            (source, target) if source == target => Some(term),
            (FormalAttributeType::Int32, FormalAttributeType::Int64) => {
                Some(FormalAggregateTerm::ScalarCall {
                    operator: ScalarOperator::Cast(ScalarCast::Int32ToInt64),
                    args: vec![term],
                })
            }
            _ => {
                self.error(
                    path,
                    "integer_implicit_coercion_not_supported",
                    "FormalSQL integral arithmetic models PostgreSQL's INTEGER-to-BIGINT widening but rejects other implicit carrier changes.",
                );
                None
            }
        }
    }

    fn lower_integral_coerced_function_term(
        &mut self,
        path: &str,
        ast: &ScalarAst,
        target: FormalAttributeType,
        scope: &Scope,
    ) -> Option<FormalFunctionTerm> {
        let source = self.infer_numeric_operand_type(&format!("{path}.type"), ast, scope)?;
        let term =
            annotate_function_literal_term(self.lower_function_term(path, ast, scope)?, source);
        match (source, target) {
            (source, target) if source == target => Some(term),
            (FormalAttributeType::Int32, FormalAttributeType::Int64) => {
                Some(FormalFunctionTerm::ScalarCall {
                    operator: ScalarOperator::Cast(ScalarCast::Int32ToInt64),
                    args: vec![term],
                })
            }
            _ => {
                self.error(
                    path,
                    "integer_implicit_coercion_not_supported",
                    "FormalSQL integral arithmetic models PostgreSQL's INTEGER-to-BIGINT widening but rejects other implicit carrier changes.",
                );
                None
            }
        }
    }

    fn timestamp_interval_function_in_scope<'a>(
        &mut self,
        path: &str,
        op: &ScalarOp,
        left: &'a ScalarAst,
        right: &'a ScalarAst,
        scope: &Scope,
    ) -> Option<TimestampIntervalFunction<'a>> {
        let pair = if type_annotation_is_interval_ast(right)
            && self
                .direct_function_type(&format!("{path}.left"), left, scope)
                .is_some_and(|ty| matches!(ty, FormalAttributeType::Timestamp { .. }))
        {
            Some((left, right))
        } else if matches!(op, ScalarOp::Plus)
            && type_annotation_is_interval_ast(left)
            && self
                .direct_function_type(&format!("{path}.right"), right, scope)
                .is_some_and(|ty| matches!(ty, FormalAttributeType::Timestamp { .. }))
        {
            Some((right, left))
        } else {
            None
        }?;
        timestamp_interval_function_for_operands(pair.0, pair.1)
    }

    fn date_interval_function_in_scope<'a>(
        &mut self,
        path: &str,
        op: &ScalarOp,
        left: &'a ScalarAst,
        right: &'a ScalarAst,
        scope: &Scope,
    ) -> Option<DateIntervalFunction<'a>> {
        let pair = if type_annotation_is_interval_ast(right)
            && self.direct_function_type(&format!("{path}.left"), left, scope)
                == Some(FormalAttributeType::Date)
        {
            Some((left, right))
        } else if matches!(op, ScalarOp::Plus)
            && type_annotation_is_interval_ast(left)
            && self.direct_function_type(&format!("{path}.right"), right, scope)
                == Some(FormalAttributeType::Date)
        {
            Some((right, left))
        } else {
            None
        }?;
        date_interval_function_for_operands(pair.0, pair.1)
    }

    fn has_temporal_interval_pair_in_scope(
        &mut self,
        path: &str,
        left: &ScalarAst,
        right: &ScalarAst,
        scope: &Scope,
    ) -> bool {
        (type_annotation_is_interval_ast(right)
            && self
                .direct_function_type(&format!("{path}.left"), left, scope)
                .is_some_and(is_temporal_type))
            || (type_annotation_is_interval_ast(left)
                && self
                    .direct_function_type(&format!("{path}.right"), right, scope)
                    .is_some_and(is_temporal_type))
    }
}

struct DateIntervalFunction<'a> {
    operator: ScalarOperator,
    date_arg: &'a ScalarAst,
    interval_arg: &'a ScalarAst,
}

struct TimestampIntervalFunction<'a> {
    operator: ScalarOperator,
    timestamp_arg: &'a ScalarAst,
    interval_arg: &'a ScalarAst,
}

fn timestamp_interval_function_for_operands<'a>(
    timestamp_arg: &'a ScalarAst,
    interval_arg: &'a ScalarAst,
) -> Option<TimestampIntervalFunction<'a>> {
    let ScalarAst::TypeAnnotation { ty, .. } = interval_arg else {
        return None;
    };
    let unit = interval_unit(ty)?;
    let unit = match unit {
        "MICROSECOND" => ScalarTimestampUnit::Microsecond,
        "SECOND" => ScalarTimestampUnit::Second,
        "MINUTE" => ScalarTimestampUnit::Minute,
        "HOUR" => ScalarTimestampUnit::Hour,
        "DAY" => ScalarTimestampUnit::Day,
        "MONTH" => ScalarTimestampUnit::Month,
        "YEAR" => ScalarTimestampUnit::Year,
        _ => return None,
    };
    Some(TimestampIntervalFunction {
        operator: ScalarOperator::TimestampAdd(unit),
        timestamp_arg,
        interval_arg,
    })
}

fn date_interval_function_for_operands<'a>(
    date_arg: &'a ScalarAst,
    interval_arg: &'a ScalarAst,
) -> Option<DateIntervalFunction<'a>> {
    let ScalarAst::TypeAnnotation { ty, .. } = interval_arg else {
        return None;
    };
    let unit = interval_unit(ty)?;
    let unit = match unit {
        "DAY" => ScalarTimestampUnit::Day,
        "MONTH" => ScalarTimestampUnit::Month,
        "YEAR" => ScalarTimestampUnit::Year,
        _ => return None,
    };
    Some(DateIntervalFunction {
        // PostgreSQL DATE +/- INTERVAL yields TIMESTAMP. The caller inserts
        // the DATE-to-TIMESTAMP cast before this operator.
        operator: ScalarOperator::TimestampAdd(unit),
        date_arg,
        interval_arg,
    })
}

fn type_annotation_is_interval_ast(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_interval(ty))
}

fn type_annotation_is_date(ty: &str) -> bool {
    classify_type_annotation(ty) == Some(SqlTypeAnnotation::Date)
}

fn type_annotation_is_timestamp(ty: &str) -> bool {
    matches!(
        classify_type_annotation(ty),
        Some(SqlTypeAnnotation::Timestamp {
            kind: TimestampTypeKind::WithoutTimeZone,
            ..
        })
    )
}

fn type_annotation_is_timestamp_tz(ty: &str) -> bool {
    matches!(
        classify_type_annotation(ty),
        Some(SqlTypeAnnotation::Timestamp {
            kind: TimestampTypeKind::WithTimeZone,
            ..
        })
    )
}

fn type_annotation_is_interval(ty: &str) -> bool {
    matches!(
        classify_type_annotation(ty),
        Some(SqlTypeAnnotation::Interval(_))
    )
}

fn type_annotation_is_time(ty: &str) -> bool {
    matches!(
        classify_type_annotation(ty),
        Some(SqlTypeAnnotation::Time { .. })
    )
}

fn time_annotation_precision_is_supported(ty: &str) -> bool {
    matches!(
        classify_type_annotation(ty),
        Some(SqlTypeAnnotation::Time {
            precision: None | Some(DEFAULT_TIMESTAMP_PRECISION)
        })
    )
}

fn temporal_annotation_types_match(
    source: FormalAttributeType,
    target: FormalAttributeType,
) -> bool {
    match (source, target) {
        (
            FormalAttributeType::Timestamp { precision: source },
            FormalAttributeType::Timestamp { precision: target },
        )
        | (
            FormalAttributeType::Timestamptz { precision: source },
            FormalAttributeType::Timestamptz { precision: target },
        ) => timestamp_precision(source) == timestamp_precision(target),
        _ => source == target,
    }
}

fn formal_type_from_annotation(ty: &str) -> Option<FormalAttributeType> {
    match classify_type_annotation(ty)? {
        SqlTypeAnnotation::Integer => Some(FormalAttributeType::Int32),
        SqlTypeAnnotation::BigInt => Some(FormalAttributeType::Int64),
        SqlTypeAnnotation::Real => Some(FormalAttributeType::Float),
        SqlTypeAnnotation::Float { precision } => float_type_from_precision(precision),
        SqlTypeAnnotation::Double => Some(FormalAttributeType::Double),
        SqlTypeAnnotation::Decimal {
            precision: None,
            scale: None,
        } => Some(FormalAttributeType::Numeric),
        SqlTypeAnnotation::Decimal {
            precision: Some(precision),
            scale: Some(scale),
        } => Some(FormalAttributeType::Decimal { precision, scale }),
        SqlTypeAnnotation::Text => Some(FormalAttributeType::String {
            typmod: SqlStringType::Text,
        }),
        SqlTypeAnnotation::Varchar { length } => Some(FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length },
        }),
        SqlTypeAnnotation::Char { length } => Some(FormalAttributeType::String {
            typmod: SqlStringType::Char {
                length: length.unwrap_or(1),
            },
        }),
        SqlTypeAnnotation::Bpchar { length: None } => Some(FormalAttributeType::String {
            typmod: SqlStringType::Bpchar,
        }),
        SqlTypeAnnotation::Boolean => Some(FormalAttributeType::Bool),
        SqlTypeAnnotation::Date => Some(FormalAttributeType::Date),
        SqlTypeAnnotation::Time {
            precision: None | Some(DEFAULT_TIMESTAMP_PRECISION),
        } => Some(FormalAttributeType::Time),
        SqlTypeAnnotation::Timestamp {
            precision,
            kind: TimestampTypeKind::WithoutTimeZone,
        } => Some(FormalAttributeType::Timestamp { precision }),
        SqlTypeAnnotation::Timestamp {
            precision,
            kind: TimestampTypeKind::WithTimeZone,
        } => Some(FormalAttributeType::Timestamptz { precision }),
        SqlTypeAnnotation::Any
        | SqlTypeAnnotation::Null
        | SqlTypeAnnotation::Decimal { .. }
        | SqlTypeAnnotation::Bpchar { .. }
        | SqlTypeAnnotation::Time { .. }
        | SqlTypeAnnotation::Interval(_) => None,
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
        FormalAttributeType::Decimal { scale, .. } => Some(*scale),
        _ => None,
    }
}

fn decimal_type_precision(ty: &FormalAttributeType) -> Option<u32> {
    match ty {
        FormalAttributeType::Decimal { precision, .. } => Some(*precision),
        _ => None,
    }
}

fn decimal_typmod_cast_operator(
    source: &FormalAttributeType,
    target: &FormalAttributeType,
) -> Option<ScalarOperator> {
    match (source, target) {
        (
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
            FormalAttributeType::Numeric,
        ) => Some(ScalarOperator::Cast(ScalarCast::ToNumeric(
            ScalarNumericSource::Numeric,
        ))),
        (FormalAttributeType::Z, FormalAttributeType::Numeric) => Some(ScalarOperator::Cast(
            ScalarCast::ToNumeric(ScalarNumericSource::Z),
        )),
        (FormalAttributeType::Int32, FormalAttributeType::Numeric) => Some(ScalarOperator::Cast(
            ScalarCast::ToNumeric(ScalarNumericSource::Int32),
        )),
        (FormalAttributeType::Int64, FormalAttributeType::Numeric) => Some(ScalarOperator::Cast(
            ScalarCast::ToNumeric(ScalarNumericSource::Int64),
        )),
        (
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
            FormalAttributeType::Decimal { .. },
        ) => Some(ScalarOperator::Cast(ScalarCast::ToNumericTypmod(
            ScalarNumericSource::Numeric,
        ))),
        (FormalAttributeType::Z, FormalAttributeType::Decimal { .. }) => Some(
            ScalarOperator::Cast(ScalarCast::ToNumericTypmod(ScalarNumericSource::Z)),
        ),
        (FormalAttributeType::Int32, FormalAttributeType::Decimal { .. }) => Some(
            ScalarOperator::Cast(ScalarCast::ToNumericTypmod(ScalarNumericSource::Int32)),
        ),
        (FormalAttributeType::Int64, FormalAttributeType::Decimal { .. }) => Some(
            ScalarOperator::Cast(ScalarCast::ToNumericTypmod(ScalarNumericSource::Int64)),
        ),
        _ => None,
    }
}

fn simple_numeric_cast_operator(
    source: &FormalAttributeType,
    target: &FormalAttributeType,
) -> Option<ScalarOperator> {
    match (source, target) {
        (FormalAttributeType::Int32, FormalAttributeType::Int64) => {
            Some(ScalarOperator::Cast(ScalarCast::Int32ToInt64))
        }
        (FormalAttributeType::Int32, FormalAttributeType::Double) => {
            Some(ScalarOperator::Cast(ScalarCast::Int32ToDouble))
        }
        (FormalAttributeType::Int64, FormalAttributeType::Int32) => {
            Some(ScalarOperator::Cast(ScalarCast::Int64ToInt32))
        }
        (
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
            FormalAttributeType::Int32,
        ) => Some(ScalarOperator::Cast(ScalarCast::NumericToInt32)),
        _ => None,
    }
}

fn string_integer_cast_operator(
    source: &FormalAttributeType,
    target: &FormalAttributeType,
) -> Option<ScalarOperator> {
    if !is_string_type(*source) {
        return None;
    }
    match target {
        FormalAttributeType::Int32 => Some(ScalarOperator::Cast(ScalarCast::StringToInt32)),
        FormalAttributeType::Int64 => Some(ScalarOperator::Cast(ScalarCast::StringToInt64)),
        _ => None,
    }
}

pub(super) fn string_typmod_codes(ty: FormalAttributeType) -> Option<(u32, u32)> {
    match ty {
        FormalAttributeType::String {
            typmod: SqlStringType::Text,
        } => Some((0, 0)),
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar { length: None },
        } => Some((1, 0)),
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar {
                length: Some(length),
            },
        } => Some((2, length)),
        FormalAttributeType::String {
            typmod: SqlStringType::Char { length },
        } => Some((3, length)),
        FormalAttributeType::String {
            typmod: SqlStringType::Bpchar,
        } => Some((4, 0)),
        _ => None,
    }
}

fn infer_untyped_integer_literal_type(raw: &str) -> Option<FormalAttributeType> {
    let raw = raw.trim();
    if is_null_literal(raw) {
        return None;
    }
    if raw.parse::<i64>().is_ok() {
        if raw.parse::<i32>().is_ok() {
            return Some(FormalAttributeType::Int32);
        }
        return Some(FormalAttributeType::Int64);
    }
    None
}

fn integer_literal_fits_type(raw: &str, ty: FormalAttributeType) -> bool {
    let raw = raw.trim();
    match ty {
        FormalAttributeType::Int32 => raw.parse::<i32>().is_ok(),
        FormalAttributeType::Int64 => raw.parse::<i64>().is_ok(),
        FormalAttributeType::Z => raw.parse::<i64>().is_ok(),
        _ => false,
    }
}

fn infer_literal_cast_source_type(raw: &str) -> Option<FormalAttributeType> {
    let raw = raw.trim();
    if is_null_literal(raw) {
        return None;
    }
    if raw.starts_with('\'') && raw.ends_with('\'') {
        return Some(FormalAttributeType::String {
            typmod: SqlStringType::Text,
        });
    }
    if raw.eq_ignore_ascii_case("true") || raw.eq_ignore_ascii_case("false") {
        return Some(FormalAttributeType::Bool);
    }
    infer_untyped_integer_literal_type(raw)
}

fn is_untyped_null_literal(ast: &ScalarAst) -> bool {
    let ScalarAst::Literal { raw } = ast else {
        return false;
    };
    raw.trim().eq_ignore_ascii_case("NULL")
}

fn is_untyped_string_literal(ast: &ScalarAst) -> bool {
    let ScalarAst::Literal { raw } = ast else {
        return false;
    };
    let raw = raw.trim();
    raw.starts_with('\'') && raw.ends_with('\'')
}

fn comparison_unknown_string_type(other: FormalAttributeType) -> FormalAttributeType {
    FormalAttributeType::String {
        typmod: match other {
            FormalAttributeType::String {
                typmod: SqlStringType::Char { .. } | SqlStringType::Bpchar,
            } => SqlStringType::Bpchar,
            _ => SqlStringType::Text,
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CaseResultTypeSource {
    UnknownNull,
    UnknownString,
    Known(FormalAttributeType),
    Unsupported,
}

fn postgres_case_common_type(sources: &[CaseResultTypeSource]) -> Option<FormalAttributeType> {
    if sources
        .iter()
        .any(|source| matches!(source, CaseResultTypeSource::Unsupported))
    {
        return None;
    }

    let known = sources
        .iter()
        .filter_map(|source| match source {
            CaseResultTypeSource::Known(ty) => Some(*ty),
            _ => None,
        })
        .collect::<Vec<_>>();
    if known.is_empty() {
        return Some(FormalAttributeType::String {
            typmod: SqlStringType::Text,
        });
    }

    if known.iter().any(|ty| is_string_type(*ty)) {
        if known.iter().any(|ty| !is_string_type(*ty)) {
            return None;
        }
        let typmods = known
            .iter()
            .map(|ty| match ty {
                FormalAttributeType::String { typmod } => *typmod,
                _ => unreachable!("string type checked"),
            })
            .collect::<Vec<_>>();
        let has_unknown = sources.iter().any(|source| {
            matches!(
                source,
                CaseResultTypeSource::UnknownNull | CaseResultTypeSource::UnknownString
            )
        });
        if !has_unknown && typmods.iter().all(|typmod| *typmod == typmods[0]) {
            return Some(FormalAttributeType::String { typmod: typmods[0] });
        }
        let candidate = typmods
            .iter()
            .copied()
            .find(|typmod| matches!(typmod, SqlStringType::Text))
            .unwrap_or(typmods[0]);
        return Some(FormalAttributeType::String {
            typmod: match candidate {
                SqlStringType::Text => SqlStringType::Text,
                SqlStringType::Varchar { .. } => SqlStringType::Varchar { length: None },
                SqlStringType::Char { .. } | SqlStringType::Bpchar => SqlStringType::Bpchar,
            },
        });
    }

    if sources
        .iter()
        .any(|source| matches!(source, CaseResultTypeSource::UnknownString))
    {
        return None;
    }
    if known.iter().all(|ty| is_exact_numeric_type(*ty)) {
        // PostgreSQL CASE resolution selects the NUMERIC base type. A typmod
        // survives only when every alternative has exactly the same typmod;
        // an OpExpr result is typmodless and therefore makes the CASE result
        // typmodless as well.
        let has_unknown_null = sources
            .iter()
            .any(|source| matches!(source, CaseResultTypeSource::UnknownNull));
        return if !has_unknown_null && known.iter().all(|ty| *ty == known[0]) {
            Some(known[0])
        } else {
            Some(FormalAttributeType::Numeric)
        };
    }
    if known
        .iter()
        .all(|ty| is_exact_numeric_type(*ty) || is_integral_type(*ty))
        && known.iter().any(|ty| is_exact_numeric_type(*ty))
    {
        return Some(FormalAttributeType::Numeric);
    }
    known.iter().all(|ty| *ty == known[0]).then_some(known[0])
}

fn string_implicit_coercion_aggregate_term(
    term: FormalAggregateTerm,
    target: FormalAttributeType,
) -> Option<FormalAggregateTerm> {
    let (tag, length) = string_typmod_codes(target)?;
    Some(FormalAggregateTerm::ScalarCall {
        operator: ScalarOperator::Cast(ScalarCast::StringImplicit),
        args: vec![
            term,
            z_constant_aggregate(tag),
            z_constant_aggregate(length),
        ],
    })
}

fn z_constant_aggregate(value: u32) -> FormalAggregateTerm {
    FormalAggregateTerm::Expr {
        term: z_constant_function(value),
    }
}

fn numeric_dscale_representative(provenance: &NumericDscaleProvenance) -> Option<u32> {
    match provenance {
        NumericDscaleProvenance::Exact(scale) | NumericDscaleProvenance::Representative(scale) => {
            Some(*scale)
        }
        NumericDscaleProvenance::Attribute(_) => None,
    }
}

/// Recover the operands of a NUMERIC division whose result display scale is
/// selected at runtime by PostgreSQL. Calcite result annotations are derived
/// metadata and may be peeled. An explicit unconstrained-NUMERIC cast also
/// preserves the operand dscale, while a DECIMAL(p,s) cast is handled by the
/// static typmod branch before this helper is reached.
fn numeric_division_dscale_args(ast: &ScalarAst) -> Option<&[ScalarAst]> {
    match ast {
        ScalarAst::Call {
            op: ScalarOp::Divide,
            args,
            ..
        } if args.len() == 2 => Some(args),
        ScalarAst::TypeAnnotation { expr, ty } => {
            if let Some(arg) = cast_arg(expr) {
                (formal_type_from_annotation(ty) == Some(FormalAttributeType::Numeric))
                    .then(|| numeric_division_dscale_args(arg))
                    .flatten()
            } else {
                numeric_division_dscale_args(expr)
            }
        }
        _ => None,
    }
}

/// Recognize a structurally constant exact-numeric zero through only
/// zero-preserving integral/NUMERIC annotations, casts, and unary negation.
/// This is used solely when combining CASE branch dscales: PostgreSQL may
/// return a smaller dscale for a zero branch without changing its numeric
/// value, while every possible nonzero branch must retain one exact common
/// dscale. Standalone zero expressions keep their exact inferred scale.
fn numeric_ast_is_exact_zero(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::Literal { raw } => {
            super::emit::parse_decimal_literal(raw).is_some_and(|(coefficient, _)| {
                coefficient
                    .trim_start_matches(['+', '-'])
                    .chars()
                    .all(|digit| digit == '0')
            })
        }
        ScalarAst::TypeAnnotation { expr, ty }
            if matches!(
                formal_type_from_annotation(ty),
                Some(
                    FormalAttributeType::Z
                        | FormalAttributeType::Int32
                        | FormalAttributeType::Int64
                        | FormalAttributeType::Numeric
                        | FormalAttributeType::Decimal { .. }
                )
            ) =>
        {
            if let Some(arg) = cast_arg(expr) {
                numeric_ast_is_exact_zero(arg)
            } else {
                numeric_ast_is_exact_zero(expr)
            }
        }
        ScalarAst::Call {
            op: ScalarOp::Minus,
            args,
            ..
        } if args.len() == 1 => numeric_ast_is_exact_zero(&args[0]),
        _ => false,
    }
}

fn numeric_dscale_same_branch(
    left: NumericDscaleProvenance,
    right: NumericDscaleProvenance,
) -> Option<NumericDscaleProvenance> {
    let left_scale = numeric_dscale_representative(&left)?;
    let right_scale = numeric_dscale_representative(&right)?;
    if left_scale != right_scale {
        return None;
    }
    Some(
        if matches!(
            (left, right),
            (
                NumericDscaleProvenance::Exact(_),
                NumericDscaleProvenance::Exact(_)
            )
        ) {
            NumericDscaleProvenance::Exact(left_scale)
        } else {
            NumericDscaleProvenance::Representative(left_scale)
        },
    )
}

fn numeric_dscale_add(
    left: NumericDscaleProvenance,
    right: NumericDscaleProvenance,
) -> Option<NumericDscaleProvenance> {
    match (left, right) {
        (NumericDscaleProvenance::Exact(left), NumericDscaleProvenance::Exact(right)) => {
            Some(NumericDscaleProvenance::Exact(left.max(right)))
        }
        (left, right) => numeric_dscale_same_branch(left, right),
    }
}

fn numeric_dscale_multiply(
    left: NumericDscaleProvenance,
    right: NumericDscaleProvenance,
) -> Option<NumericDscaleProvenance> {
    let scale = numeric_dscale_representative(&left)?
        .checked_add(numeric_dscale_representative(&right)?)?;
    Some(
        if matches!(
            (left, right),
            (
                NumericDscaleProvenance::Exact(_),
                NumericDscaleProvenance::Exact(_)
            )
        ) {
            NumericDscaleProvenance::Exact(scale)
        } else {
            NumericDscaleProvenance::Representative(scale)
        },
    )
}

pub(super) fn z_constant_function(value: u32) -> FormalFunctionTerm {
    FormalFunctionTerm::Constant {
        raw: value.to_string(),
        ty: Some(FormalAttributeType::Z),
    }
}

fn temporal_cast_operator(
    source: &FormalAttributeType,
    target: &FormalAttributeType,
) -> Option<ScalarOperator> {
    if source == target {
        return Some(ScalarOperator::Cast(ScalarCast::Identity));
    }
    match (source, target) {
        (FormalAttributeType::Date, FormalAttributeType::Timestamp { .. }) => {
            Some(ScalarOperator::Cast(ScalarCast::DateToTimestamp))
        }
        (FormalAttributeType::Timestamp { .. }, FormalAttributeType::Date) => {
            Some(ScalarOperator::Cast(ScalarCast::TimestampToDate))
        }
        _ => None,
    }
}

fn interval_unit(ty: &str) -> Option<&'static str> {
    let SqlTypeAnnotation::Interval(kind) = classify_type_annotation(ty)? else {
        return None;
    };
    kind.terminal_unit()
}

fn typed_literal_raw(ast: &ScalarAst) -> Option<&str> {
    match ast {
        ScalarAst::Literal { raw } => Some(raw),
        ScalarAst::TypeAnnotation { expr, .. } => typed_literal_raw(expr),
        _ => None,
    }
}

fn extract_date_field(args: &[ScalarAst]) -> Option<(ScalarDatePart, &ScalarAst)> {
    match args {
        [ScalarAst::Flag { name }, arg] if name.eq_ignore_ascii_case("YEAR") => {
            Some((ScalarDatePart::Year, arg))
        }
        [ScalarAst::Flag { name }, arg] if name.eq_ignore_ascii_case("MONTH") => {
            Some((ScalarDatePart::Month, arg))
        }
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

/// Recognize only the PostgreSQL exact-numeric square-root shape exercised by
/// the frozen Calcite statistic rewrites.  The exponent annotation matters:
/// two integral POWER arguments resolve to the float8 overload, while the
/// bare `0.5` token is typmodless NUMERIC. An explicit DECIMAL(2,1) `0.5`
/// selects the same numeric/numeric overload and is equally exact.
fn postgres_power_half_int64_base(ast: &ScalarAst) -> Option<&ScalarAst> {
    let ScalarAst::Call {
        op: ScalarOp::Power,
        args,
        ..
    } = ast
    else {
        return None;
    };
    let [base, exponent] = args.as_slice() else {
        return None;
    };
    let ScalarAst::TypeAnnotation { expr, ty } = exponent else {
        return None;
    };
    if !matches!(
        formal_type_from_annotation(ty),
        Some(
            FormalAttributeType::Numeric
                | FormalAttributeType::Decimal {
                    precision: 2,
                    scale: 1
                }
        )
    ) || !matches!(expr.as_ref(), ScalarAst::Literal { raw } if raw.trim() == "0.5")
    {
        return None;
    }
    Some(base)
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

fn scalar_operator(op: &ScalarOp) -> Option<ScalarOperator> {
    if let Some(predicate) = formal_predicate(op) {
        return Some(ScalarOperator::PredicateValue(predicate));
    }
    match op {
        ScalarOp::And => Some(ScalarOperator::Boolean(ScalarBooleanOperator::And)),
        ScalarOp::Or => Some(ScalarOperator::Boolean(ScalarBooleanOperator::Or)),
        ScalarOp::Not => Some(ScalarOperator::Boolean(ScalarBooleanOperator::Not)),
        ScalarOp::Lower => Some(ScalarOperator::StringCase(ScalarStringCase::Lower)),
        ScalarOp::Upper => Some(ScalarOperator::StringCase(ScalarStringCase::Upper)),
        _ => None,
    }
}

fn is_boolean_value_function(op: &ScalarOp) -> bool {
    op.is_comparison()
        || matches!(
            op,
            ScalarOp::And
                | ScalarOp::Or
                | ScalarOp::Not
                | ScalarOp::IsNull
                | ScalarOp::IsNotNull
                | ScalarOp::IsTrue
                | ScalarOp::IsNotTrue
                | ScalarOp::IsFalse
                | ScalarOp::IsNotFalse
                | ScalarOp::IsNotDistinctFrom
                | ScalarOp::Like
        )
}

fn scalar_ast_has_rel_subquery(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::RelSubquery { .. } => true,
        ScalarAst::Call { args, .. } => args.iter().any(scalar_ast_has_rel_subquery),
        ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_has_rel_subquery(expr),
        ScalarAst::Window { parsed } => {
            parsed.args.iter().any(scalar_ast_has_rel_subquery)
                || parsed.partition_by.iter().any(scalar_ast_has_rel_subquery)
                || parsed
                    .order_by
                    .iter()
                    .any(|key| scalar_ast_has_rel_subquery(&key.expr))
                || parsed
                    .frame
                    .as_ref()
                    .is_some_and(|frame| frame.offset_exprs().any(scalar_ast_has_rel_subquery))
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => false,
    }
}

fn scalar_ast_rel_subquery_may_raise_runtime(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::RelSubquery { rel } => !scalar_subquery_rel_is_provably_runtime_total(rel),
        ScalarAst::Call {
            op: ScalarOp::Exists,
            args,
            ..
        } => match args.as_slice() {
            [ScalarAst::RelSubquery { rel }] => rel_expr_may_raise_runtime(rel),
            _ => true,
        },
        ScalarAst::Call {
            op: ScalarOp::In,
            args,
            ..
        } => {
            let Some((right, left)) = args.split_last() else {
                return true;
            };
            left.iter().any(scalar_ast_rel_subquery_may_raise_runtime)
                || match right {
                    ScalarAst::RelSubquery { rel } => rel_expr_may_raise_runtime(rel),
                    _ => true,
                }
        }
        ScalarAst::Call { args, .. } => args.iter().any(scalar_ast_rel_subquery_may_raise_runtime),
        ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_rel_subquery_may_raise_runtime(expr),
        ScalarAst::Window { parsed } => {
            parsed
                .args
                .iter()
                .any(scalar_ast_rel_subquery_may_raise_runtime)
                || parsed
                    .partition_by
                    .iter()
                    .any(scalar_ast_rel_subquery_may_raise_runtime)
                || parsed
                    .order_by
                    .iter()
                    .any(|key| scalar_ast_rel_subquery_may_raise_runtime(&key.expr))
                || parsed.frame.as_ref().is_some_and(|frame| {
                    frame
                        .offset_exprs()
                        .any(scalar_ast_rel_subquery_may_raise_runtime)
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => false,
    }
}

fn formal_predicate(op: &ScalarOp) -> Option<FormalPredicate> {
    match op {
        ScalarOp::Eq => Some(FormalPredicate::Eq),
        ScalarOp::NotEq => Some(FormalPredicate::Neq),
        ScalarOp::Lt => Some(FormalPredicate::Lt),
        ScalarOp::Lte => Some(FormalPredicate::Lte),
        ScalarOp::Gt => Some(FormalPredicate::Gt),
        ScalarOp::Gte => Some(FormalPredicate::Gte),
        ScalarOp::IsNull => Some(FormalPredicate::IsNull),
        ScalarOp::IsNotNull => Some(FormalPredicate::IsNotNull),
        ScalarOp::IsTrue => Some(FormalPredicate::IsTrue),
        ScalarOp::IsNotTrue => Some(FormalPredicate::IsNotTrue),
        ScalarOp::IsFalse => Some(FormalPredicate::IsFalse),
        ScalarOp::IsNotFalse => Some(FormalPredicate::IsNotFalse),
        ScalarOp::IsNotDistinctFrom => Some(FormalPredicate::IsNotDistinctFrom),
        _ => None,
    }
}

/// Under the existing deterministic-default-collation contract, PostgreSQL
/// TEXT comparison has trichotomy for two non-NULL values.  This exact, closed
/// shape can therefore eliminate collation-dependent ordering without adding
/// an ordering interpretation: `(x < c OR x > c)` is `x <> c`, and both sides
/// are UNKNOWN when `x` is NULL.  Direct references/literals also ensure the
/// rewrite neither deduplicates volatile work nor changes runtime-error order.
fn complementary_text_order_disjunction(ast: &ScalarAst, scope: &Scope) -> Option<ScalarAst> {
    let ScalarAst::Call {
        op: ScalarOp::Or,
        args,
        ..
    } = ast
    else {
        return None;
    };
    let [first, second] = args.as_slice() else {
        return None;
    };
    let (first_op, first_index, first_literal) = direct_text_order_literal_comparison(first)?;
    let (second_op, second_index, second_literal) = direct_text_order_literal_comparison(second)?;
    if !matches!(
        (first_op, second_op),
        (ScalarOp::Lt, ScalarOp::Gt) | (ScalarOp::Gt, ScalarOp::Lt)
    ) || first_index != second_index
        || first_literal != second_literal
        || !matches!(
            scope
                .attributes
                .get(first_index)
                .map(|attribute| attribute.formal_ty),
            Some(FormalAttributeType::String {
                typmod: SqlStringType::Text
            })
        )
    {
        return None;
    }
    Some(ScalarAst::Call {
        operator: "<>".to_owned(),
        op: ScalarOp::NotEq,
        args: vec![
            ScalarAst::InputRef { index: first_index },
            first_literal.clone(),
        ],
    })
}

fn direct_text_order_literal_comparison(ast: &ScalarAst) -> Option<(ScalarOp, usize, &ScalarAst)> {
    let ScalarAst::Call { op, args, .. } = ast else {
        return None;
    };
    if !matches!(op, ScalarOp::Lt | ScalarOp::Gt) {
        return None;
    }
    let [ScalarAst::InputRef { index }, literal] = args.as_slice() else {
        return None;
    };
    is_untyped_string_literal(literal).then_some((op.clone(), *index, literal))
}

fn is_order_predicate(op: &ScalarOp) -> bool {
    op.is_ordering_comparison()
}

fn is_float_type(ty: FormalAttributeType) -> bool {
    matches!(ty, FormalAttributeType::Float | FormalAttributeType::Double)
}

fn is_string_type(ty: FormalAttributeType) -> bool {
    matches!(ty, FormalAttributeType::String { .. })
}

fn is_temporal_type(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Date
            | FormalAttributeType::Time
            | FormalAttributeType::Timestamp { .. }
            | FormalAttributeType::Timestamptz { .. }
    )
}

fn is_integral_type(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Z | FormalAttributeType::Int32 | FormalAttributeType::Int64
    )
}

fn integral_binary_result_type(
    left: FormalAttributeType,
    right: FormalAttributeType,
) -> FormalAttributeType {
    match (left, right) {
        (FormalAttributeType::Int64, _)
        | (_, FormalAttributeType::Int64)
        | (FormalAttributeType::Z, _)
        | (_, FormalAttributeType::Z) => FormalAttributeType::Int64,
        _ => FormalAttributeType::Int32,
    }
}

fn is_numeric_type(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Z
            | FormalAttributeType::Int32
            | FormalAttributeType::Int64
            | FormalAttributeType::Float
            | FormalAttributeType::Double
            | FormalAttributeType::Numeric
            | FormalAttributeType::Decimal { .. }
    )
}

pub(super) fn is_exact_numeric_type(ty: FormalAttributeType) -> bool {
    matches!(
        ty,
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. }
    )
}

fn numeric_literal_fits_type(raw: &str, ty: FormalAttributeType) -> bool {
    match ty {
        FormalAttributeType::Numeric => super::emit::numeric_literal_fits_postgres_runtime(raw),
        FormalAttributeType::Decimal { .. } => {
            super::emit::decimal_literal_for_type(raw, Some(&ty)).is_some()
        }
        _ => false,
    }
}

pub(super) fn numeric_literal_rounds_to_int32(raw: &str) -> Option<bool> {
    if !super::emit::numeric_literal_fits_postgres_runtime(raw) {
        return None;
    }
    let (coefficient, scale) = super::emit::parse_decimal_literal(raw)?;
    Some(numeric_coefficient_rounds_to_int32(&coefficient, scale))
}

fn numeric_coefficient_rounds_to_int32(coefficient: &str, scale: u32) -> bool {
    let negative = coefficient.starts_with('-');
    let digits = coefficient.strip_prefix('-').unwrap_or(coefficient);
    let Ok(scale) = usize::try_from(scale) else {
        return false;
    };
    let integer_len = digits.len().saturating_sub(scale);
    let integer_part = if integer_len == 0 {
        "0"
    } else {
        &digits[..integer_len]
    };
    // PostgreSQL's NUMERIC-to-integer coercion rounds ties away from zero.
    // For a finite base-10 coefficient the first discarded digit alone
    // determines whether the integral magnitude increases by one.
    let rounds_away_from_zero =
        scale > 0 && digits.len() >= scale && digits.as_bytes()[digits.len() - scale] >= b'5';
    let bound = if negative { "2147483648" } else { "2147483647" };
    match compare_unsigned_decimal(integer_part, bound) {
        std::cmp::Ordering::Less => true,
        std::cmp::Ordering::Equal => !rounds_away_from_zero,
        std::cmp::Ordering::Greater => false,
    }
}

fn compare_unsigned_decimal(left: &str, right: &str) -> std::cmp::Ordering {
    let left = left.trim_start_matches('0');
    let right = right.trim_start_matches('0');
    let left = if left.is_empty() { "0" } else { left };
    let right = if right.is_empty() { "0" } else { right };
    left.len()
        .cmp(&right.len())
        .then_with(|| left.as_bytes().cmp(right.as_bytes()))
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

fn comparison_types_are_supported(
    left: Option<FormalAttributeType>,
    right: Option<FormalAttributeType>,
) -> bool {
    let (Some(left), Some(right)) = (left, right) else {
        return true;
    };
    if left == right {
        return true;
    }
    if is_integral_type(left) && is_integral_type(right) {
        return true;
    }
    if is_string_type(left) && is_string_type(right) {
        return true;
    }
    (is_exact_numeric_type(left) && is_exact_numeric_type(right))
        || (is_exact_numeric_type(left) && is_integral_type(right))
        || (is_integral_type(left) && is_exact_numeric_type(right))
}

fn floating_operator(op: &ScalarOp, ty: FormalAttributeType) -> Option<ScalarOperator> {
    let kind = match ty {
        FormalAttributeType::Float => ScalarNumericKind::Float,
        FormalAttributeType::Double => ScalarNumericKind::Double,
        _ => return None,
    };
    match (op, ty) {
        (ScalarOp::Plus, _) => Some(ScalarOperator::Add(kind)),
        (ScalarOp::Minus, _) => Some(ScalarOperator::Subtract(kind)),
        (ScalarOp::Multiply, _) => Some(ScalarOperator::Multiply(kind)),
        (ScalarOp::Divide, FormalAttributeType::Float) => {
            Some(ScalarOperator::Divide(ScalarNumericKind::Float))
        }
        (ScalarOp::Divide, FormalAttributeType::Double) => {
            Some(ScalarOperator::Divide(ScalarNumericKind::Double))
        }
        _ => None,
    }
}

fn floating_unary_minus_operator(ty: FormalAttributeType) -> Option<ScalarOperator> {
    match ty {
        FormalAttributeType::Float => Some(ScalarOperator::Negate(ScalarNumericKind::Float)),
        FormalAttributeType::Double => Some(ScalarOperator::Negate(ScalarNumericKind::Double)),
        _ => None,
    }
}

fn integer_binary_operator(op: &ScalarOp, ty: FormalAttributeType) -> Option<ScalarOperator> {
    let kind = match ty {
        FormalAttributeType::Int32 => ScalarNumericKind::Int32,
        FormalAttributeType::Int64 | FormalAttributeType::Z => ScalarNumericKind::Int64,
        _ => return None,
    };
    match op {
        ScalarOp::Plus => Some(ScalarOperator::Add(kind)),
        ScalarOp::Minus => Some(ScalarOperator::Subtract(kind)),
        ScalarOp::Multiply => Some(ScalarOperator::Multiply(kind)),
        ScalarOp::Divide if kind == ScalarNumericKind::Int32 => {
            Some(ScalarOperator::Divide(ScalarNumericKind::Int32))
        }
        ScalarOp::Divide => Some(ScalarOperator::Divide(ScalarNumericKind::Int64)),
        _ => None,
    }
}

fn integer_unary_minus_operator(ty: FormalAttributeType) -> Option<ScalarOperator> {
    match ty {
        FormalAttributeType::Int32 => Some(ScalarOperator::Negate(ScalarNumericKind::Int32)),
        FormalAttributeType::Int64 | FormalAttributeType::Z => {
            Some(ScalarOperator::Negate(ScalarNumericKind::Int64))
        }
        _ => None,
    }
}

fn predicate_requires_external_interpretation(op: &ScalarOp) -> bool {
    !(op.is_comparison()
        || matches!(
            op,
            ScalarOp::IsNull
                | ScalarOp::IsNotNull
                | ScalarOp::IsTrue
                | ScalarOp::IsNotTrue
                | ScalarOp::IsFalse
                | ScalarOp::IsNotFalse
        ))
}

fn function_requires_external_interpretation(op: &ScalarOp) -> bool {
    !is_boolean_value_function(op) && !matches!(op, ScalarOp::Lower | ScalarOp::Upper)
}

pub(super) fn top_level_string_case_mapping(ast: &ScalarAst) -> Option<&ScalarOp> {
    match ast {
        ScalarAst::TypeAnnotation { expr, .. } => top_level_string_case_mapping(expr),
        ScalarAst::Call {
            op: op @ (ScalarOp::Lower | ScalarOp::Upper),
            args,
            ..
        } if args.len() == 1 => Some(op),
        _ => None,
    }
}

fn scalar_ast_contains_locale_dependent_case_mapping(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::Call { op, args, .. } => {
            matches!(op, ScalarOp::Lower | ScalarOp::Upper)
                || args
                    .iter()
                    .any(scalar_ast_contains_locale_dependent_case_mapping)
        }
        ScalarAst::TypeAnnotation { expr, .. } => {
            scalar_ast_contains_locale_dependent_case_mapping(expr)
        }
        ScalarAst::Window { parsed } => {
            parsed
                .args
                .iter()
                .chain(&parsed.partition_by)
                .any(scalar_ast_contains_locale_dependent_case_mapping)
                || parsed
                    .order_by
                    .iter()
                    .any(|key| scalar_ast_contains_locale_dependent_case_mapping(&key.expr))
                || parsed.frame.as_ref().is_some_and(|frame| {
                    frame
                        .offset_exprs()
                        .any(scalar_ast_contains_locale_dependent_case_mapping)
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::RelSubquery { .. } => false,
    }
}

fn literal_requires_external_encoding(raw: &str) -> bool {
    let trimmed = raw.trim();
    !(trimmed.eq_ignore_ascii_case("true")
        || trimmed.eq_ignore_ascii_case("false")
        || trimmed.eq_ignore_ascii_case("null")
        || sql_string_literal_content(trimmed).is_some()
        || is_integer_literal(trimmed))
}

#[derive(Clone, Copy)]
enum ProvableConstant {
    Int32(i32),
    Int64(i64),
    Numeric { coeff: i128, scale: u32 },
    DateLiteral(i64),
    Interval { amount: i64, unit: IntervalUnit },
    Total(FormalAttributeType),
}

#[derive(Clone, Copy)]
enum IntervalUnit {
    Day,
    Month,
    Year,
}

impl ProvableConstant {
    fn formal_type(self) -> Option<FormalAttributeType> {
        match self {
            Self::Int32(_) => Some(FormalAttributeType::Int32),
            Self::Int64(_) => Some(FormalAttributeType::Int64),
            Self::Numeric { .. } => Some(FormalAttributeType::Numeric),
            Self::DateLiteral(_) => Some(FormalAttributeType::Date),
            Self::Total(ty) => Some(ty),
            Self::Interval { .. } => None,
        }
    }

    fn numeric_parts(self) -> Option<(i128, u32)> {
        match self {
            Self::Int32(value) => Some((i128::from(value), 0)),
            Self::Int64(value) => Some((i128::from(value), 0)),
            Self::Numeric { coeff, scale } => Some((coeff, scale)),
            _ => None,
        }
    }
}

fn provable_constant_value(ast: &ScalarAst) -> Option<ProvableConstant> {
    match ast {
        ScalarAst::Literal { raw } => {
            let raw = raw.trim();
            if let Ok(value) = raw.parse::<i32>() {
                return Some(ProvableConstant::Int32(value));
            }
            if let Ok(value) = raw.parse::<i64>() {
                return Some(ProvableConstant::Int64(value));
            }
            let (coeff, scale) = super::emit::parse_decimal_literal(raw)?;
            Some(ProvableConstant::Numeric {
                coeff: coeff.parse().ok()?,
                scale,
            })
        }
        ScalarAst::TypeAnnotation { expr, ty } => {
            if let Some(arg) = cast_arg(expr) {
                let raw = typed_literal_raw(arg)?;
                return match formal_type_from_annotation(ty)? {
                    FormalAttributeType::Date => super::emit::parse_source_date_cast_literal(raw)
                        .map(ProvableConstant::DateLiteral),
                    FormalAttributeType::Time
                        if super::emit::parse_source_time_cast_literal(raw).is_some() =>
                    {
                        Some(ProvableConstant::Total(FormalAttributeType::Time))
                    }
                    FormalAttributeType::Timestamp { precision }
                        if super::emit::parse_source_timestamp_cast_literal(
                            raw,
                            timestamp_precision(precision),
                        )
                        .is_some() =>
                    {
                        Some(ProvableConstant::Total(FormalAttributeType::Timestamp {
                            precision,
                        }))
                    }
                    _ => None,
                };
            }
            if type_annotation_is_interval(ty) {
                let raw = typed_literal_raw(expr)?;
                let amount = parse_interval_literal(raw, ty)?;
                let unit = match interval_unit(ty)? {
                    "DAY" => IntervalUnit::Day,
                    "MONTH" => IntervalUnit::Month,
                    "YEAR" => IntervalUnit::Year,
                    _ => return None,
                };
                return Some(ProvableConstant::Interval { amount, unit });
            }
            let Some(formal_ty) = formal_type_from_annotation(ty) else {
                return provable_constant_value(expr);
            };
            if let Some(raw) = typed_literal_raw(expr) {
                let raw = raw.trim();
                return match formal_ty {
                    FormalAttributeType::Int32 => Some(ProvableConstant::Int32(raw.parse().ok()?)),
                    FormalAttributeType::Int64 | FormalAttributeType::Z => {
                        Some(ProvableConstant::Int64(raw.parse().ok()?))
                    }
                    FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. }
                        if numeric_literal_fits_type(raw, formal_ty) =>
                    {
                        let (coeff, scale) = super::emit::parse_decimal_literal(raw)?;
                        Some(ProvableConstant::Numeric {
                            coeff: coeff.parse().ok()?,
                            scale,
                        })
                    }
                    FormalAttributeType::Date => {
                        let value = raw.parse().ok()?;
                        super::emit::valid_postgres_date_days(value)
                            .then_some(ProvableConstant::DateLiteral(value))
                    }
                    _ => None,
                };
            }
            // A non-CAST type annotation is Calcite metadata. The inner
            // expression, not that derived typmod, determines totality.
            provable_constant_value(expr)
        }
        ScalarAst::Call { op, args, .. }
            if matches!(
                op,
                ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
            ) =>
        {
            provable_constant_arithmetic(op, args)
        }
        _ => None,
    }
}

fn provable_constant_arithmetic(op: &ScalarOp, args: &[ScalarAst]) -> Option<ProvableConstant> {
    if let [arg] = args
        && matches!(op, ScalarOp::Minus)
    {
        return match provable_constant_value(arg)? {
            ProvableConstant::Int32(value) => value.checked_neg().map(ProvableConstant::Int32),
            ProvableConstant::Int64(value) => value.checked_neg().map(ProvableConstant::Int64),
            ProvableConstant::Numeric { coeff, scale } => Some(ProvableConstant::Numeric {
                coeff: coeff.checked_neg()?,
                scale,
            }),
            _ => None,
        };
    }
    let [left, right] = args else {
        return None;
    };
    let left = provable_constant_value(left)?;
    let right = provable_constant_value(right)?;

    if let Some(total) = provable_constant_date_arithmetic(op, left, right) {
        return Some(total);
    }

    match (left, right) {
        (ProvableConstant::Int32(left), ProvableConstant::Int32(right)) => {
            let value = match op {
                ScalarOp::Plus => left.checked_add(right),
                ScalarOp::Minus => left.checked_sub(right),
                ScalarOp::Multiply => left.checked_mul(right),
                ScalarOp::Divide => left.checked_div(right),
                _ => None,
            }?;
            Some(ProvableConstant::Int32(value))
        }
        (ProvableConstant::Int32(left), ProvableConstant::Int64(right)) => {
            provable_constant_int64_arithmetic(op, i64::from(left), right)
        }
        (ProvableConstant::Int64(left), ProvableConstant::Int32(right)) => {
            provable_constant_int64_arithmetic(op, left, i64::from(right))
        }
        (ProvableConstant::Int64(left), ProvableConstant::Int64(right)) => {
            provable_constant_int64_arithmetic(op, left, right)
        }
        (left, right) => {
            let (left_coeff, left_scale) = left.numeric_parts()?;
            let (right_coeff, right_scale) = right.numeric_parts()?;
            match op {
                ScalarOp::Plus | ScalarOp::Minus => {
                    let scale = left_scale.max(right_scale);
                    let left_coeff = scale_numeric_coeff(left_coeff, scale - left_scale)?;
                    let right_coeff = scale_numeric_coeff(right_coeff, scale - right_scale)?;
                    let coeff = if matches!(op, ScalarOp::Plus) {
                        left_coeff.checked_add(right_coeff)?
                    } else {
                        left_coeff.checked_sub(right_coeff)?
                    };
                    Some(ProvableConstant::Numeric { coeff, scale })
                }
                ScalarOp::Multiply => Some(ProvableConstant::Numeric {
                    coeff: left_coeff.checked_mul(right_coeff)?,
                    scale: left_scale.checked_add(right_scale)?,
                }),
                // Exact rational evaluation is unnecessary for the current
                // proof of totality. Keep constant division conservative.
                ScalarOp::Divide => None,
                _ => None,
            }
        }
    }
}

fn provable_constant_int64_arithmetic(
    op: &ScalarOp,
    left: i64,
    right: i64,
) -> Option<ProvableConstant> {
    let value = match op {
        ScalarOp::Plus => left.checked_add(right),
        ScalarOp::Minus => left.checked_sub(right),
        ScalarOp::Multiply => left.checked_mul(right),
        ScalarOp::Divide => left.checked_div(right),
        _ => None,
    }?;
    Some(ProvableConstant::Int64(value))
}

fn scale_numeric_coeff(coeff: i128, scale_delta: u32) -> Option<i128> {
    coeff.checked_mul(10i128.checked_pow(scale_delta)?)
}

fn provable_constant_date_arithmetic(
    op: &ScalarOp,
    left: ProvableConstant,
    right: ProvableConstant,
) -> Option<ProvableConstant> {
    let (date, interval) = match (left, right) {
        (ProvableConstant::DateLiteral(date), ProvableConstant::Interval { amount, unit }) => {
            (date, (amount, unit))
        }
        (ProvableConstant::Interval { amount, unit }, ProvableConstant::DateLiteral(date))
            if matches!(op, ScalarOp::Plus) =>
        {
            (date, (amount, unit))
        }
        _ => return None,
    };
    if !matches!(op, ScalarOp::Plus | ScalarOp::Minus) {
        return None;
    }
    let magnitude = i128::from(interval.0).checked_abs()?;
    let maximum_days = match interval.1 {
        IntervalUnit::Day => magnitude,
        IntervalUnit::Month => magnitude.checked_mul(31)?,
        IntervalUnit::Year => magnitude.checked_mul(366)?,
    };
    // PostgreSQL resolves DATE +/- INTERVAL by first promoting DATE to
    // TIMESTAMP. The DATE carrier extends far beyond TIMESTAMP, so proving
    // only that the resulting civil date is valid would accept a cast-time
    // overflow. Bound the complete result in PostgreSQL's timestamp domain.
    const MICROS_PER_DAY: i128 = 86_400_000_000;
    const POSTGRES_TIMESTAMP_MIN_MICROS: i128 = -210_866_803_200_000_000;
    const POSTGRES_TIMESTAMP_END_MICROS: i128 = 9_224_318_016_000_000_000;
    let lower_days = i128::from(date).checked_sub(maximum_days)?;
    let upper_days = i128::from(date).checked_add(maximum_days)?;
    let lower_micros = lower_days.checked_mul(MICROS_PER_DAY)?;
    let upper_micros = upper_days.checked_mul(MICROS_PER_DAY)?;
    (lower_micros >= POSTGRES_TIMESTAMP_MIN_MICROS && upper_micros < POSTGRES_TIMESTAMP_END_MICROS)
        .then_some(ProvableConstant::Total(FormalAttributeType::Timestamp {
            precision: None,
        }))
}

/// A scalar subquery is runtime-total only when its relational child cannot
/// raise and its structure proves that PostgreSQL can never observe a second
/// row.  Relational uses of the same child under EXISTS/IN do not inherit this
/// scalar-cardinality condition.
fn scalar_subquery_rel_is_provably_runtime_total(rel: &RelExpr) -> bool {
    // PostgreSQL returns NULL for zero rows and the sole value for one row;
    // only a second row introduces the scalar-subquery cardinality error.
    // Retain every error from evaluating the subquery itself independently of
    // that structural row bound.
    super::rel::rel_structural_max_rows(rel).is_some_and(|maximum| maximum <= 1)
        && !rel_expr_may_raise_runtime(rel)
}

fn scalar_query_is_provably_runtime_total(args: &[ScalarAst]) -> bool {
    matches!(args, [ScalarAst::RelSubquery { rel }]
        if scalar_subquery_rel_is_provably_runtime_total(rel))
}

fn scalar_call_has_intrinsic_runtime_risk(op: &ScalarOp, args: &[ScalarAst]) -> bool {
    matches!(
        op,
        ScalarOp::Plus
            | ScalarOp::Minus
            | ScalarOp::Multiply
            | ScalarOp::Divide
            | ScalarOp::Cast
            | ScalarOp::Substring
            | ScalarOp::Exp
            | ScalarOp::Power
            | ScalarOp::Extract
    ) || matches!(op, ScalarOp::ScalarQuery) && !scalar_query_is_provably_runtime_total(args)
}

pub(super) fn scalar_ast_may_raise_runtime(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::Call {
            op: ScalarOp::Exists,
            args,
            ..
        } => match args.as_slice() {
            [ScalarAst::RelSubquery { rel }] => rel_expr_may_raise_runtime(rel),
            _ => true,
        },
        ScalarAst::Call {
            op: ScalarOp::In,
            args,
            ..
        } => {
            let Some((right, left)) = args.split_last() else {
                return true;
            };
            left.iter().any(scalar_ast_may_raise_runtime)
                || match right {
                    ScalarAst::RelSubquery { rel } => rel_expr_may_raise_runtime(rel),
                    _ => true,
                }
        }
        ScalarAst::Call { op, args, .. } => {
            (scalar_call_has_intrinsic_runtime_risk(op, args)
                && provable_constant_value(ast).is_none())
                && !(matches!(op, ScalarOp::Substring) && substring_is_provably_total(ast, &[]))
                || (matches!(op, ScalarOp::StringConcat)
                    && !string_concat_is_provably_total(ast, &[]))
                || args.iter().any(scalar_ast_may_raise_runtime)
        }
        ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_may_raise_runtime(expr),
        ScalarAst::RelSubquery { rel } => !scalar_subquery_rel_is_provably_runtime_total(rel),
        ScalarAst::Window { parsed } => {
            let argument_type = parsed
                .args
                .first()
                .and_then(|arg| static_cast_operand_type(arg, &[]));
            postgres_window_function_may_raise_runtime(&parsed.function, argument_type)
                || parsed.args.iter().any(scalar_ast_may_raise_runtime)
                || parsed.partition_by.iter().any(scalar_ast_may_raise_runtime)
                || parsed
                    .order_by
                    .iter()
                    .any(|key| scalar_ast_may_raise_runtime(&key.expr))
                || parsed.frame.as_ref().is_some_and(|frame| {
                    window_frame_may_raise_runtime(frame, scalar_ast_may_raise_runtime)
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => false,
    }
}

pub(super) fn scalar_ast_may_raise_runtime_in_columns(ast: &ScalarAst, columns: &[Column]) -> bool {
    let input_types = columns
        .iter()
        .map(|column| formal_type_for_runtime_risk(&column.ty))
        .collect::<Vec<_>>();
    scalar_ast_may_raise_runtime_with_types(ast, &input_types)
}

fn scalar_ast_may_raise_runtime_with_types(
    ast: &ScalarAst,
    input_types: &[Option<FormalAttributeType>],
) -> bool {
    match ast {
        ScalarAst::TypeAnnotation { expr, ty } if cast_arg(expr).is_some() => {
            let arg = cast_arg(expr).expect("guarded explicit CAST");
            scalar_ast_may_raise_runtime_with_types(arg, input_types)
                || !cast_is_provably_total(arg, ty, input_types)
        }
        ScalarAst::Call {
            op: ScalarOp::Exists,
            args,
            ..
        } => match args.as_slice() {
            [ScalarAst::RelSubquery { rel }] => rel_expr_may_raise_runtime(rel),
            _ => true,
        },
        ScalarAst::Call {
            op: ScalarOp::In,
            args,
            ..
        } => {
            let Some((right, left)) = args.split_last() else {
                return true;
            };
            left.iter()
                .any(|arg| scalar_ast_may_raise_runtime_with_types(arg, input_types))
                || match right {
                    ScalarAst::RelSubquery { rel } => rel_expr_may_raise_runtime(rel),
                    _ => true,
                }
        }
        ScalarAst::Call { op, args, .. } => {
            ((scalar_call_has_intrinsic_runtime_risk(op, args)
                && provable_constant_value(ast).is_none()
                && !(matches!(op, ScalarOp::Substring)
                    && substring_is_provably_total(ast, input_types))
                && !(matches!(op, ScalarOp::Extract)
                    && extract_date_field(args).is_some_and(|(_, arg)| {
                        static_cast_operand_type(arg, input_types)
                            == Some(FormalAttributeType::Date)
                    })))
                || (matches!(op, ScalarOp::StringConcat)
                    && !string_concat_is_provably_total(ast, input_types)))
                || args
                    .iter()
                    .any(|arg| scalar_ast_may_raise_runtime_with_types(arg, input_types))
        }
        ScalarAst::TypeAnnotation { expr, .. } => {
            scalar_ast_may_raise_runtime_with_types(expr, input_types)
        }
        ScalarAst::RelSubquery { rel } => !scalar_subquery_rel_is_provably_runtime_total(rel),
        ScalarAst::Window { parsed } => {
            let argument_type = parsed
                .args
                .first()
                .and_then(|arg| static_cast_operand_type(arg, input_types));
            postgres_window_function_may_raise_runtime(&parsed.function, argument_type)
                || parsed
                    .args
                    .iter()
                    .chain(&parsed.partition_by)
                    .any(|arg| scalar_ast_may_raise_runtime_with_types(arg, input_types))
                || parsed
                    .order_by
                    .iter()
                    .any(|key| scalar_ast_may_raise_runtime_with_types(&key.expr, input_types))
                || parsed.frame.as_ref().is_some_and(|frame| {
                    window_frame_may_raise_runtime(frame, |offset| {
                        scalar_ast_may_raise_runtime_with_types(offset, input_types)
                    })
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => false,
    }
}

/// Keep aggregate overloads whose active FormalSQL callback can report an
/// error visible to query-shape decisions.  Integral AVG and INTEGER
/// statistics are total under the supported input authority, while
/// floating/NUMERIC AVG and fixed-NUMERIC sample standard deviation retain
/// error-capable finalization.  Unknown overloads fail closed instead of
/// borrowing Calcite's non-authoritative result type.
fn postgres_aggregate_function_may_raise_runtime(
    function: &str,
    argument_type: Option<FormalAttributeType>,
) -> bool {
    match function.to_ascii_lowercase().as_str() {
        "count" | "sum" | "single_value" => true,
        "avg" => !matches!(
            argument_type,
            Some(FormalAttributeType::Int32 | FormalAttributeType::Int64 | FormalAttributeType::Z)
        ),
        "stddev_samp" | "stddev" => argument_type != Some(FormalAttributeType::Int32),
        _ => false,
    }
}

/// PostgreSQL ROW_NUMBER/RANK embed an unbounded logical position in signed
/// BIGINT, while supported window aggregates use the same error-capable
/// transition callbacks as ordinary aggregates.  Preserve those intrinsic
/// errors even when arguments, partition keys, ordering keys, and frames are
/// themselves total.
fn postgres_window_function_may_raise_runtime(
    function: &str,
    argument_type: Option<FormalAttributeType>,
) -> bool {
    function.eq_ignore_ascii_case("row_number")
        || function.eq_ignore_ascii_case("rank")
        || postgres_aggregate_function_may_raise_runtime(function, argument_type)
}

/// Window-frame offsets are evaluated as SQL expressions and PostgreSQL then
/// rejects NULL or negative ROWS offsets.  RANGE offsets additionally depend
/// on the ordered expression's operator family, which this local target-risk
/// classifier does not possess.  Traverse every offset for ordinary scalar
/// errors, prove only a nonnegative integral ROWS constant total, and retain
/// every other offset-bearing window target so downstream declarative window
/// validation can model it or fail closed.
fn window_frame_may_raise_runtime(
    frame: &WindowFrameAst,
    mut expr_may_raise: impl FnMut(&ScalarAst) -> bool,
) -> bool {
    if !frame.is_valid_postgres() {
        return true;
    }
    frame.offset_exprs().any(|offset| {
        expr_may_raise(offset)
            || match frame.units {
                WindowFrameUnits::Rows => match provable_constant_value(offset) {
                    Some(ProvableConstant::Int32(value)) => value < 0,
                    Some(ProvableConstant::Int64(value)) => value < 0,
                    _ => true,
                },
                WindowFrameUnits::Range => true,
            }
    })
}

// PostgreSQL varlena allocations use a four-byte header and ordinary palloc
// rejects any allocation above MaxAllocSize (0x3fffffff). Character typmods
// count characters, so four bytes per character is a conservative bound for
// every PostgreSQL server encoding supported by this frontend.
const POSTGRES_MAX_ALLOC_SIZE: u64 = 0x3fff_ffff;
const POSTGRES_VARLENA_HEADER_BYTES: u64 = 4;
const POSTGRES_MAX_BYTES_PER_CHARACTER: u64 = 4;

fn string_concat_is_provably_total(
    ast: &ScalarAst,
    input_types: &[Option<FormalAttributeType>],
) -> bool {
    string_expr_max_bytes(ast, input_types).is_some_and(|bytes| {
        bytes
            .checked_add(POSTGRES_VARLENA_HEADER_BYTES)
            .is_some_and(|allocation| allocation <= POSTGRES_MAX_ALLOC_SIZE)
    })
}

fn string_expr_max_bytes(
    ast: &ScalarAst,
    input_types: &[Option<FormalAttributeType>],
) -> Option<u64> {
    match ast {
        ScalarAst::Literal { raw } => {
            sql_string_literal_content(raw).and_then(|literal| u64::try_from(literal.len()).ok())
        }
        ScalarAst::InputRef { index } => input_types
            .get(*index)
            .copied()
            .flatten()
            .and_then(string_type_max_bytes),
        ScalarAst::TypeAnnotation { expr, ty } => {
            match formal_type_from_annotation(ty).and_then(string_type_max_bytes) {
                Some(bound) => Some(bound),
                None => string_expr_max_bytes(expr, input_types),
            }
        }
        ScalarAst::Call {
            op: ScalarOp::StringConcat,
            args,
            ..
        } if args.len() == 2 => args.iter().try_fold(0_u64, |total, arg| {
            total.checked_add(string_expr_max_bytes(arg, input_types)?)
        }),
        ScalarAst::Call {
            op: ScalarOp::Case,
            args,
            ..
        } if args.len() >= 3 && !args.len().is_multiple_of(2) => {
            let branch_max = args[..args.len() - 1]
                .chunks_exact(2)
                .map(|pair| string_expr_max_bytes(&pair[1], input_types))
                .try_fold(0_u64, |maximum, bound| Some(maximum.max(bound?)))?;
            Some(branch_max.max(string_expr_max_bytes(args.last()?, input_types)?))
        }
        _ => None,
    }
}

fn string_type_max_bytes(ty: FormalAttributeType) -> Option<u64> {
    let characters = match ty {
        FormalAttributeType::String {
            typmod: SqlStringType::Varchar {
                length: Some(length),
            },
        }
        | FormalAttributeType::String {
            typmod: SqlStringType::Char { length },
        } => u64::from(length),
        _ => return None,
    };
    characters.checked_mul(POSTGRES_MAX_BYTES_PER_CHARACTER)
}

fn substring_is_provably_total(
    ast: &ScalarAst,
    input_types: &[Option<FormalAttributeType>],
) -> bool {
    let ScalarAst::Call {
        op: ScalarOp::Substring,
        args,
        ..
    } = ast
    else {
        return false;
    };
    let [value, start, count] = args.as_slice() else {
        return false;
    };
    let Some(value_ty) = static_cast_operand_type(value, input_types) else {
        return false;
    };
    if !matches!(
        value_ty,
        FormalAttributeType::String {
            typmod: SqlStringType::Char { .. } | SqlStringType::Varchar { length: Some(_) },
        }
    ) || !string_type_max_bytes(value_ty).is_some_and(|bytes| {
        bytes
            .checked_add(POSTGRES_VARLENA_HEADER_BYTES)
            .is_some_and(|allocation| allocation <= POSTGRES_MAX_ALLOC_SIZE)
    }) {
        return false;
    }
    static_cast_operand_type(start, input_types) == Some(FormalAttributeType::Int32)
        && static_cast_operand_type(count, input_types) == Some(FormalAttributeType::Int32)
        && typed_literal_raw(start)
            .and_then(|raw| raw.trim().parse::<i32>().ok())
            .is_some_and(|value| value >= 1)
        && typed_literal_raw(count)
            .and_then(|raw| raw.trim().parse::<i32>().ok())
            .is_some_and(|value| value >= 0)
}

fn cast_is_provably_total(
    arg: &ScalarAst,
    target_annotation: &str,
    input_types: &[Option<FormalAttributeType>],
) -> bool {
    let Some(target_ty) = formal_type_from_annotation(target_annotation) else {
        return false;
    };
    if let Some(total) = constant_cast_is_provably_total(arg, target_ty) {
        return total;
    }
    let Some(source_ty) = static_cast_operand_type(arg, input_types) else {
        return false;
    };
    if source_ty == target_ty {
        return true;
    }
    if is_string_type(source_ty) && is_string_type(target_ty) {
        // PostgreSQL explicit casts to CHAR(n)/VARCHAR(n) truncate rather than
        // raising a string-data-right-truncation error.
        return true;
    }
    match (source_ty, target_ty) {
        (FormalAttributeType::Int32, FormalAttributeType::Int64) => true,
        (FormalAttributeType::Int32, FormalAttributeType::Double) => true,
        (
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
            FormalAttributeType::Numeric,
        )
        | (FormalAttributeType::Int32 | FormalAttributeType::Int64, FormalAttributeType::Numeric) => {
            true
        }
        (
            FormalAttributeType::Decimal {
                precision: source_precision,
                scale: source_scale,
            },
            FormalAttributeType::Decimal {
                precision: target_precision,
                scale: target_scale,
            },
        ) if source_scale <= source_precision && target_scale <= target_precision => {
            let source_integral = source_precision - source_scale;
            let target_integral = target_precision - target_scale;
            let rounding_carry = u32::from(target_scale < source_scale);
            target_integral >= source_integral.saturating_add(rounding_carry)
        }
        (FormalAttributeType::Int32, FormalAttributeType::Decimal { precision, scale })
            if scale <= precision =>
        {
            precision - scale >= 10
        }
        (FormalAttributeType::Int64, FormalAttributeType::Decimal { precision, scale })
            if scale <= precision =>
        {
            precision - scale >= 19
        }
        _ => false,
    }
}

/// Decide totality for constants without relying on Calcite's derived result
/// metadata. Returning `None` means that the cast is not one of the exact
/// constant cases handled here and the authoritative source-type rules must be
/// consulted instead.
fn constant_cast_is_provably_total(
    arg: &ScalarAst,
    target_ty: FormalAttributeType,
) -> Option<bool> {
    if typed_literal_raw(arg).is_some_and(is_null_literal) {
        return Some(true);
    }
    if let Some(raw) = typed_literal_raw(arg) {
        match target_ty {
            FormalAttributeType::Int32 => {
                return numeric_literal_rounds_to_int32(raw);
            }
            FormalAttributeType::Bool => {
                return Some(parse_postgres_boolean_source_literal(raw).is_some());
            }
            FormalAttributeType::Date => {
                return Some(super::emit::parse_source_date_cast_literal(raw).is_some());
            }
            FormalAttributeType::Time => {
                return Some(super::emit::parse_source_time_cast_literal(raw).is_some());
            }
            FormalAttributeType::Timestamp { precision } => {
                return Some(
                    super::emit::parse_source_timestamp_cast_literal(
                        raw,
                        timestamp_precision(precision),
                    )
                    .is_some(),
                );
            }
            _ => {}
        }
    }
    let constant = provable_constant_value(arg)?;
    let (coeff, scale) = constant.numeric_parts()?;
    match target_ty {
        FormalAttributeType::Int32 => Some(numeric_coefficient_rounds_to_int32(
            &coeff.to_string(),
            scale,
        )),
        FormalAttributeType::Numeric => Some(true),
        FormalAttributeType::Decimal {
            precision,
            scale: target_scale,
        } => Some(constant_numeric_fits_typmod(
            coeff,
            scale,
            precision,
            target_scale,
        )),
        _ => None,
    }
}

/// Exact, deliberately narrow subset of PostgreSQL's boolean input syntax.
/// PostgreSQL also accepts unique prefixes of several longer words; those
/// remain conservatively rejected until a benchmark needs them.
fn parse_postgres_boolean_source_literal(raw: &str) -> Option<bool> {
    let value = sql_string_literal_content(raw)?;
    match value.as_str() {
        value if value.eq_ignore_ascii_case("t") || value.eq_ignore_ascii_case("true") => {
            Some(true)
        }
        value if value.eq_ignore_ascii_case("f") || value.eq_ignore_ascii_case("false") => {
            Some(false)
        }
        _ => None,
    }
}

fn constant_numeric_fits_typmod(
    coeff: i128,
    source_scale: u32,
    precision: u32,
    target_scale: u32,
) -> bool {
    if precision == 0 || target_scale > precision {
        return false;
    }
    let target_coeff = if source_scale <= target_scale {
        let Some(factor) = 10i128.checked_pow(target_scale - source_scale) else {
            return false;
        };
        let Some(value) = coeff.checked_mul(factor) else {
            return false;
        };
        value
    } else {
        let Some(divisor) = 10i128.checked_pow(source_scale - target_scale) else {
            return false;
        };
        let quotient = coeff / divisor;
        let remainder = coeff % divisor;
        let Some(twice_remainder) = remainder
            .checked_abs()
            .and_then(|value| value.checked_mul(2))
        else {
            return false;
        };
        if twice_remainder >= divisor {
            let Some(rounded) = quotient.checked_add(if coeff < 0 { -1 } else { 1 }) else {
                return false;
            };
            rounded
        } else {
            quotient
        }
    };
    let Some(magnitude) = target_coeff.checked_abs() else {
        return false;
    };
    magnitude.to_string().len() <= precision as usize
}

fn static_cast_operand_type(
    ast: &ScalarAst,
    input_types: &[Option<FormalAttributeType>],
) -> Option<FormalAttributeType> {
    match ast {
        ScalarAst::InputRef { index } => input_types.get(*index).copied().flatten(),
        ScalarAst::CorrelatedRef { .. } => {
            // The reference-local Calcite type can be stale. Correlated
            // lowering resolves the authoritative type from the enclosing
            // correlation scope, which is not threaded through this static
            // risk classifier. Treat the source as unknown rather than
            // incorrectly proving a narrowing cast total.
            None
        }
        ScalarAst::TypeAnnotation { expr, ty } => {
            // A non-CAST Rex annotation is descriptive metadata, not a
            // runtime coercion. Numeric lowering deliberately ignores stale
            // inferred typmods on projected/arithmetic values, so such an
            // annotation can prove a cast total only when it agrees with the
            // recursively authoritative operand type.
            let annotated = formal_type_from_annotation(ty)?;
            let operand = static_cast_operand_type(expr, input_types)?;
            (annotated == operand).then_some(operand)
        }
        _ => provable_constant_value(ast).and_then(ProvableConstant::formal_type),
    }
}

fn formal_type_for_runtime_risk(ty: &SqlType) -> Option<FormalAttributeType> {
    match ty {
        SqlType::Integer => Some(FormalAttributeType::Int32),
        SqlType::BigInt => Some(FormalAttributeType::Int64),
        SqlType::Float => Some(FormalAttributeType::Float),
        SqlType::Double => Some(FormalAttributeType::Double),
        SqlType::Decimal {
            precision: None,
            scale: None,
        } => Some(FormalAttributeType::Numeric),
        SqlType::Decimal {
            precision: Some(precision),
            scale: Some(scale),
        } => Some(FormalAttributeType::Decimal {
            precision: *precision,
            scale: *scale,
        }),
        SqlType::String(typmod) => Some(FormalAttributeType::String { typmod: *typmod }),
        SqlType::Boolean => Some(FormalAttributeType::Bool),
        SqlType::Date => Some(FormalAttributeType::Date),
        SqlType::Time => Some(FormalAttributeType::Time),
        SqlType::Timestamp { precision } => Some(FormalAttributeType::Timestamp {
            precision: *precision,
        }),
        SqlType::TimestampTz { precision } => Some(FormalAttributeType::Timestamptz {
            precision: *precision,
        }),
        SqlType::Any | SqlType::Null | SqlType::Decimal { .. } => None,
    }
}

/// Independently justified source types for each relational output position.
///
/// Calcite-derived output metadata is not authority: the importer can
/// deliberately override it where PostgreSQL resolves a different NUMERIC
/// typmod. Preserve a type only through a position whose lineage is exact.
/// This permits one safe column beside unrelated derived columns without
/// letting those unknown siblings manufacture CAST-totality evidence.
fn runtime_risk_authoritative_output_types(rel: &RelExpr) -> Vec<Option<FormalAttributeType>> {
    match rel {
        // TableScan rows are closed against the parsed schema by logos-ir.
        // Values retains the pre-existing authority boundary established by
        // the structured tuple/common-type importer.
        RelExpr::TableScan { output, .. } | RelExpr::Values { output, .. } => output
            .iter()
            .map(|column| formal_type_for_runtime_risk(&column.ty))
            .collect(),
        RelExpr::Filter { input, output, .. }
        | RelExpr::NativeHaving { input, output, .. }
        | RelExpr::Distinct { input, output }
        | RelExpr::Sort { input, output, .. } => {
            align_passthrough_runtime_risk_types(input, output)
        }
        RelExpr::Project {
            input,
            exprs,
            correlations,
            output,
        } => {
            if !correlations.is_empty() || exprs.len() != output.len() {
                return vec![None; output.len()];
            }
            let input_types = runtime_risk_authoritative_output_types(input);
            exprs
                .iter()
                .zip(output)
                .map(|(expr, output_column)| {
                    let ScalarAst::InputRef { index } = &expr.parsed else {
                        return None;
                    };
                    let input_column = input.output().get(*index)?;
                    let input_ty = input_types.get(*index).copied().flatten()?;
                    (input_column.ty == output_column.ty
                        && formal_type_for_runtime_risk(&output_column.ty) == Some(input_ty))
                    .then_some(input_ty)
                })
                .collect()
        }
        RelExpr::Join {
            left,
            right,
            join_type,
            output,
            ..
        } => runtime_risk_authoritative_join_types(left, right, *join_type, output),
        RelExpr::Set {
            op,
            all,
            inputs,
            output,
        } => {
            if *op != SetOp::Union
                || !*all
                || inputs.len() < 2
                || inputs
                    .iter()
                    .any(|input| input.output().len() != output.len())
            {
                return vec![None; output.len()];
            }
            let input_types = inputs
                .iter()
                .map(runtime_risk_authoritative_output_types)
                .collect::<Vec<_>>();
            (0..output.len())
                .map(|index| {
                    let first_column = inputs.first()?.output().get(index)?;
                    let first_ty = input_types.first()?.get(index).copied().flatten()?;
                    let exact_branches = inputs.iter().zip(&input_types).all(|(input, types)| {
                        input.output().get(index).is_some_and(|column| {
                            column.ty == first_column.ty
                                && types.get(index).copied().flatten() == Some(first_ty)
                        })
                    });
                    (exact_branches
                        && output[index].ty == first_column.ty
                        && formal_type_for_runtime_risk(&output[index].ty) == Some(first_ty))
                    .then_some(first_ty)
                })
                .collect()
        }
        // Aggregate outputs are computed values even when Calcite reuses an
        // input typmod for a group key. Admit them only through a future
        // source-specific proof, never through derived row metadata.
        RelExpr::Aggregate { output, .. } => vec![None; output.len()],
    }
}

fn align_passthrough_runtime_risk_types(
    input: &RelExpr,
    output: &[Column],
) -> Vec<Option<FormalAttributeType>> {
    if input.output().len() != output.len() {
        return vec![None; output.len()];
    }
    let input_types = runtime_risk_authoritative_output_types(input);
    input
        .output()
        .iter()
        .zip(input_types)
        .zip(output)
        .map(|((input_column, input_ty), output_column)| {
            input_ty.filter(|ty| {
                input_column.ty == output_column.ty
                    && formal_type_for_runtime_risk(&output_column.ty) == Some(*ty)
            })
        })
        .collect()
}

fn runtime_risk_authoritative_join_types(
    left: &RelExpr,
    right: &RelExpr,
    join_type: JoinType,
    output: &[Column],
) -> Vec<Option<FormalAttributeType>> {
    let left_types = runtime_risk_authoritative_output_types(left);
    let right_types = runtime_risk_authoritative_output_types(right);
    let child_columns = match join_type {
        JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => left
            .output()
            .iter()
            .chain(right.output())
            .collect::<Vec<_>>(),
        JoinType::Semi | JoinType::Anti => left.output().iter().collect::<Vec<_>>(),
    };
    let child_types = match join_type {
        JoinType::Inner | JoinType::Left | JoinType::Right | JoinType::Full => left_types
            .into_iter()
            .chain(right_types)
            .collect::<Vec<_>>(),
        JoinType::Semi | JoinType::Anti => left_types,
    };
    if output.len() != child_columns.len() || child_types.len() != child_columns.len() {
        return vec![None; output.len()];
    }
    child_columns
        .into_iter()
        .zip(child_types)
        .zip(output)
        .map(|((child_column, child_ty), output_column)| {
            child_ty.filter(|ty| {
                child_column.ty == output_column.ty
                    && formal_type_for_runtime_risk(&output_column.ty) == Some(*ty)
            })
        })
        .collect()
}

fn scalar_ast_may_raise_runtime_with_authoritative_types(
    ast: &ScalarAst,
    input_types: &[Option<FormalAttributeType>],
) -> bool {
    if input_types.iter().all(Option::is_none) {
        // Preserve the old scope-free classifier when no position has an
        // independent type proof. This avoids deriving any new conclusion
        // from a row of unknowns.
        scalar_ast_may_raise_runtime(ast)
    } else {
        scalar_ast_may_raise_runtime_with_types(ast, input_types)
    }
}

pub(super) fn scalar_ast_may_raise_runtime_for_input(ast: &ScalarAst, input: &RelExpr) -> bool {
    let input_types = runtime_risk_authoritative_output_types(input);
    scalar_ast_may_raise_runtime_with_authoritative_types(ast, &input_types)
}

/// Classify a join condition's language-level runtime-error behavior using
/// authoritative positional types from both logical inputs.
pub(super) fn join_condition_may_raise_runtime(
    left: &RelExpr,
    right: &RelExpr,
    condition: &ScalarAst,
) -> bool {
    let mut input_types = runtime_risk_authoritative_output_types(left);
    input_types.extend(runtime_risk_authoritative_output_types(right));
    scalar_ast_may_raise_runtime_with_authoritative_types(condition, &input_types)
}

fn exists_subquery_has_incomplete_capped_runtime_path(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::Distinct { input, .. }
        | RelExpr::Sort { input, .. } => exists_subquery_has_incomplete_capped_runtime_path(input),
        RelExpr::Set { op, inputs, .. } if matches!(op, SetOp::Union) => {
            rel_expr_may_raise_runtime(rel)
                || inputs
                    .iter()
                    .any(exists_subquery_has_incomplete_capped_runtime_path)
        }
        RelExpr::Join { left, right, .. } => {
            rel_expr_may_raise_runtime(rel)
                || exists_subquery_has_incomplete_capped_runtime_path(left)
                || exists_subquery_has_incomplete_capped_runtime_path(right)
        }
        RelExpr::NativeHaving { .. }
        | RelExpr::Aggregate { .. }
        | RelExpr::Set { .. }
        | RelExpr::TableScan { .. }
        | RelExpr::Values { .. } => false,
    }
}

pub(super) fn rel_expr_may_raise_runtime(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::TableScan { .. } => false,
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .any(|expr| scalar_ast_may_raise_runtime_in_columns(&expr.parsed, &[])),
        RelExpr::Project { input, exprs, .. } => {
            rel_expr_may_raise_runtime(input)
                || exprs
                    .iter()
                    .any(|expr| scalar_ast_may_raise_runtime_for_input(&expr.parsed, input))
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            rel_expr_may_raise_runtime(input)
                || scalar_ast_may_raise_runtime_for_input(&predicate.parsed, input)
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            rel_expr_may_raise_runtime(left)
                || rel_expr_may_raise_runtime(right)
                || join_condition_may_raise_runtime(left, right, &condition.parsed)
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            let input_types = runtime_risk_authoritative_output_types(input);
            rel_expr_may_raise_runtime(input)
                || agg_calls.iter().any(|call| {
                    let argument_type = call
                        .args
                        .first()
                        .and_then(|arg| static_cast_operand_type(&arg.parsed, &input_types));
                    postgres_aggregate_function_may_raise_runtime(&call.function, argument_type)
                        || call
                            .args
                            .iter()
                            .any(|expr| scalar_ast_may_raise_runtime_for_input(&expr.parsed, input))
                        || call.filter.as_ref().is_some_and(|expr| {
                            scalar_ast_may_raise_runtime_for_input(&expr.parsed, input)
                        })
                })
        }
        RelExpr::Distinct { input, .. } => rel_expr_may_raise_runtime(input),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            rel_expr_may_raise_runtime(input)
                || fetch.as_ref().is_some_and(|expr| {
                    scalar_ast_may_raise_runtime_in_columns(&expr.parsed, input.output())
                })
                || offset.as_deref().is_some_and(|expr| {
                    scalar_ast_may_raise_runtime_in_columns(&expr.parsed, input.output())
                })
        }
        RelExpr::Set { inputs, .. } => inputs.iter().any(rel_expr_may_raise_runtime),
    }
}

pub(super) fn aggregate_function_for_type(
    function: &str,
    arg_ty: Option<&FormalAttributeType>,
) -> Option<FormalAggregateFunction> {
    let name = function.to_ascii_lowercase();
    match (name.as_str(), arg_ty) {
        ("count", _) => Some(FormalAggregateFunction::Count),
        ("sum", Some(FormalAttributeType::Int32)) => Some(FormalAggregateFunction::SumInt32),
        ("sum", Some(FormalAttributeType::Int64)) => Some(FormalAggregateFunction::SumInt64Numeric),
        ("avg", Some(FormalAttributeType::Int32)) => {
            Some(FormalAggregateFunction::AverageInt32Numeric)
        }
        ("avg", Some(FormalAttributeType::Int64)) => {
            Some(FormalAggregateFunction::AverageInt64Numeric)
        }
        ("single_value", Some(FormalAttributeType::Int32)) => {
            Some(FormalAggregateFunction::SingleValueInt32)
        }
        ("var_pop", Some(FormalAttributeType::Int32)) => {
            Some(FormalAggregateFunction::VariancePopulationInt32)
        }
        ("var_samp" | "variance", Some(FormalAttributeType::Int32)) => {
            Some(FormalAggregateFunction::VarianceSampleInt32)
        }
        ("stddev_pop", Some(FormalAttributeType::Int32)) => {
            Some(FormalAggregateFunction::StddevPopulationInt32)
        }
        ("stddev_samp" | "stddev", Some(FormalAttributeType::Int32)) => {
            Some(FormalAggregateFunction::StddevSampleInt32)
        }
        ("bit_and", Some(FormalAttributeType::Int32)) => Some(FormalAggregateFunction::BitAndInt32),
        ("bit_or", Some(FormalAttributeType::Int32)) => Some(FormalAggregateFunction::BitOrInt32),
        ("bit_and", Some(FormalAttributeType::Int64)) => Some(FormalAggregateFunction::BitAndInt64),
        ("bit_or", Some(FormalAttributeType::Int64)) => Some(FormalAggregateFunction::BitOrInt64),
        ("max", Some(FormalAttributeType::Int32)) => Some(FormalAggregateFunction::MaxInt32),
        ("min", Some(FormalAttributeType::Int32)) => Some(FormalAggregateFunction::MinInt32),
        ("max", Some(FormalAttributeType::Int64)) => Some(FormalAggregateFunction::MaxInt64),
        ("min", Some(FormalAttributeType::Int64)) => Some(FormalAggregateFunction::MinInt64),
        (
            "max",
            Some(FormalAttributeType::String {
                typmod: SqlStringType::Text,
            }),
        ) => Some(FormalAggregateFunction::MaxString),
        ("sum", Some(FormalAttributeType::Float)) => Some(FormalAggregateFunction::SumFloat),
        ("max", Some(FormalAttributeType::Float)) => Some(FormalAggregateFunction::MaxFloat),
        ("min", Some(FormalAttributeType::Float)) => Some(FormalAggregateFunction::MinFloat),
        ("avg", Some(FormalAttributeType::Float)) => Some(FormalAggregateFunction::AverageFloat),
        ("sum", Some(FormalAttributeType::Double)) => Some(FormalAggregateFunction::SumDouble),
        ("max", Some(FormalAttributeType::Double)) => Some(FormalAggregateFunction::MaxDouble),
        ("min", Some(FormalAttributeType::Double)) => Some(FormalAggregateFunction::MinDouble),
        ("avg", Some(FormalAttributeType::Double)) => Some(FormalAggregateFunction::AverageDouble),
        ("sum", Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })) => {
            Some(FormalAggregateFunction::SumNumeric)
        }
        ("max", Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })) => {
            Some(FormalAggregateFunction::MaxNumeric)
        }
        ("min", Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })) => {
            Some(FormalAggregateFunction::MinNumeric)
        }
        // Exact NUMERIC AVG requires typmod or dscale provenance and is
        // selected by the aggregate lowering path.
        ("avg", Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. })) => None,
        ("sum", Some(FormalAttributeType::Z)) => Some(FormalAggregateFunction::SumZ),
        ("max", Some(FormalAttributeType::Z)) => Some(FormalAggregateFunction::MaxZ),
        ("min", Some(FormalAttributeType::Z)) => Some(FormalAggregateFunction::MinZ),
        ("avg", Some(FormalAttributeType::Z)) => Some(FormalAggregateFunction::AverageZ),
        _ => None,
    }
}

pub(super) fn aggregate_function_is_supported(function: &str) -> bool {
    matches!(
        function.to_ascii_lowercase().as_str(),
        "count"
            | "sum"
            | "max"
            | "min"
            | "avg"
            | "bit_and"
            | "bit_or"
            | "var_pop"
            | "var_samp"
            | "variance"
            | "stddev_pop"
            | "stddev_samp"
            | "stddev"
            | "single_value"
    )
}

/// A scalar aggregate argument is represented by FormalSQL's `funterm`,
/// while the general SELECT language uses `aggterm`.  Searched CASE is
/// non-strict in both contexts: the Rocq runtime-error interpreter gives the
/// `case` operator all branch observations and selects only the first true arm.
/// Convert only aggregate-free terms, preserving that exact operator rather
/// than materializing CASE in an eager child projection.
fn aggregate_term_into_function_term(term: FormalAggregateTerm) -> Option<FormalFunctionTerm> {
    match term {
        FormalAggregateTerm::Expr { term } => Some(term),
        FormalAggregateTerm::ScalarCall { operator, args } => {
            Some(FormalFunctionTerm::ScalarCall {
                operator,
                args: args
                    .into_iter()
                    .map(aggregate_term_into_function_term)
                    .collect::<Option<Vec<_>>>()?,
            })
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            let mut args = Vec::with_capacity(branches.len() * 2 + 1);
            for branch in branches {
                args.push(aggregate_term_into_function_term(branch.when)?);
                args.push(aggregate_term_into_function_term(branch.then_expr)?);
            }
            args.push(aggregate_term_into_function_term(*else_expr)?);
            Some(FormalFunctionTerm::ScalarCall {
                operator: ScalarOperator::Case,
                args,
            })
        }
        FormalAggregateTerm::Aggregate { .. } | FormalAggregateTerm::CountStar => None,
    }
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

fn annotate_case_result_literal_term(
    term: FormalAggregateTerm,
    ast: &ScalarAst,
    ty: FormalAttributeType,
) -> FormalAggregateTerm {
    let derived_annotation = matches!(ast, ScalarAst::TypeAnnotation { expr, .. }
        if cast_arg(expr).is_none() && typed_literal_raw(expr).is_some());
    if !derived_annotation {
        return annotate_literal_term(term, ty);
    }
    // Calcite assigns a result typmod to otherwise bare CASE literals and
    // NULLs. PostgreSQL common-type selection deliberately discards that
    // derived typmod, so the already annotated constant must be retagged.
    // An explicit CAST has a ScalarOp::Cast child and never enters this path.
    match term {
        FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant { raw, .. },
        } => FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Constant { raw, ty: Some(ty) },
        },
        other => other,
    }
}

pub(super) fn annotate_function_literal_term(
    term: FormalFunctionTerm,
    ty: FormalAttributeType,
) -> FormalFunctionTerm {
    match term {
        FormalFunctionTerm::Constant { raw, ty: None } => {
            FormalFunctionTerm::Constant { raw, ty: Some(ty) }
        }
        other => other,
    }
}
