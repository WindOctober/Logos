use super::*;
use logos_ir::ir::{ScalarAst, ScalarOp};

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
                        predicate: predicate_name(op).to_owned(),
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
                ScalarOp::Case => {
                    let lowered = self.lower_aggregate_term(path, ast, scope)?;
                    self.warning(
                        path,
                        "boolean_expression_interpretation_required",
                        "Lowered SQL boolean expression requires a matching FormalSQL Tuple.symbol/predicate interpretation in Rocq.",
                    );
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
            ScalarAst::TypeAnnotation { expr, .. } => self.lower_aggregate_term(path, expr, scope),
            _ => Some(FormalAggregateTerm::Expr {
                term: self.lower_function_term(path, ast, scope)?,
            }),
        }
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
                if is_temporal_type(&attr.ty) {
                    self.warning(
                        path,
                        "temporal_type_encoded_as_string",
                        "FormalSQL proof-of-concept attributes have no Date/Time/Timestamp constructor; this query-visible attribute reference is encoded as Attr_string and requires a Rocq-side semantic encoding before proofs are trusted.",
                    );
                }
                Some(FormalFunctionTerm::Attribute {
                    name: attr.name,
                    constructor: attr.constructor,
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
            ScalarAst::TypeAnnotation { expr, .. } => self.lower_function_term(path, expr, scope),
            ScalarAst::Sarg { .. }
            | ScalarAst::Window { .. }
            | ScalarAst::RelText { .. }
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
    is_function_term_function(op) || is_boolean_value_function(op) || matches!(op, ScalarOp::Case)
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
        ScalarOp::Case => "case".to_owned(),
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
    !matches!(op, ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply)
}

fn literal_requires_external_encoding(raw: &str) -> bool {
    let trimmed = raw.trim();
    !(trimmed.eq_ignore_ascii_case("true")
        || trimmed.eq_ignore_ascii_case("false")
        || trimmed.eq_ignore_ascii_case("null")
        || sql_string_literal_content(trimmed).is_some()
        || is_integer_literal(trimmed))
}

pub(super) fn aggregate_function_name(function: &str) -> String {
    function.to_ascii_lowercase()
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

pub(super) fn formal_attribute_constructor(ty: FormalAttributeType) -> &'static str {
    match ty {
        FormalAttributeType::String => "Attr_string",
        FormalAttributeType::Z => "Attr_Z",
        FormalAttributeType::Bool => "Attr_bool",
        FormalAttributeType::Float => "Attr_float",
    }
}
