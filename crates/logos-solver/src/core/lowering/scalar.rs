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
                    || type_annotation_is_timestamp(ty)
                    || type_annotation_is_interval(ty) =>
            {
                Some(FormalAggregateTerm::Expr {
                    term: self.lower_function_term(path, ast, scope)?,
                })
            }
            ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_time(ty) => {
                self.error(
                    path,
                    "temporal_literal_not_supported",
                    "TIME literals require a dedicated FormalSQL temporal semantics before they can be lowered soundly.",
                );
                None
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
                if is_unsupported_temporal_type(&attr.ty) {
                    self.warning(
                        path,
                        "temporal_type_encoded_as_string",
                        "FormalSQL proof-of-concept attributes have no TIME constructor; this query-visible attribute reference is encoded as Attr_string and requires a Rocq-side semantic encoding before proofs are trusted.",
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
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_date(ty) => {
                let raw = typed_literal_raw(expr)
                    .or_else(|| cast_literal_raw(expr))
                    .or_else(|| {
                        self.error(
                            path,
                            "date_literal_not_supported",
                            "DATE annotations are supported only for literal CAST/typed literals.",
                        );
                        None
                    })?;
                Some(FormalFunctionTerm::Constant {
                    raw: raw.to_owned(),
                    ty: Some(FormalAttributeType::Date),
                })
            }
            ScalarAst::TypeAnnotation { expr, ty } if type_annotation_is_timestamp(ty) => {
                let raw = typed_literal_raw(expr)
                    .or_else(|| cast_literal_raw(expr))
                    .or_else(|| {
                        self.error(
                            path,
                            "timestamp_literal_not_supported",
                            "TIMESTAMP annotations are supported only for literal CAST/typed literals.",
                        );
                        None
                    })?;
                let precision = type_annotation_precision(ty);
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
                Some(FormalFunctionTerm::Constant {
                    raw: raw.to_owned(),
                    ty: Some(FormalAttributeType::Timestamp { precision }),
                })
            }
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
            ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_time(ty) => {
                self.error(
                    path,
                    "temporal_literal_not_supported",
                    "TIME literals require a dedicated FormalSQL temporal semantics before they can be lowered soundly.",
                );
                None
            }
            ScalarAst::TypeAnnotation { expr, ty } => {
                if let (Some(raw), Some(formal_ty)) =
                    (typed_literal_raw(expr), formal_type_from_annotation(ty))
                {
                    if formal_ty == FormalAttributeType::Float
                        && !raw.eq_ignore_ascii_case("null")
                        && raw.trim().parse::<i64>().is_err()
                    {
                        self.error(
                            path,
                            "float_literal_not_supported",
                            "FormalSQL lowering does not yet encode non-integer FLOAT/DECIMAL literals.",
                        );
                        return None;
                    }
                    if let FormalAttributeType::Timestamp { precision } = formal_ty {
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
                self.lower_function_term(path, expr, scope)
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

fn type_annotation_is_interval_ast(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::TypeAnnotation { ty, .. } if type_annotation_is_interval(ty))
}

fn has_temporal_interval_pair(left: &ScalarAst, right: &ScalarAst) -> bool {
    (type_annotation_is_date_ast(left)
        || type_annotation_is_timestamp_ast(left)
        || type_annotation_is_interval_ast(left))
        && (type_annotation_is_date_ast(right)
            || type_annotation_is_timestamp_ast(right)
            || type_annotation_is_interval_ast(right))
        && (type_annotation_is_interval_ast(left) || type_annotation_is_interval_ast(right))
}

fn type_annotation_is_date(ty: &str) -> bool {
    type_annotation_head(ty) == Some("DATE")
}

fn type_annotation_is_timestamp(ty: &str) -> bool {
    type_annotation_head(ty) == Some("TIMESTAMP")
}

fn type_annotation_is_interval(ty: &str) -> bool {
    ty.trim().to_ascii_uppercase().starts_with("INTERVAL")
}

fn type_annotation_is_time(ty: &str) -> bool {
    type_annotation_head(ty) == Some("TIME")
}

fn formal_type_from_annotation(ty: &str) -> Option<FormalAttributeType> {
    let head = type_annotation_head(ty)?;
    match head {
        "INTEGER" | "INT" | "BIGINT" | "SMALLINT" | "TINYINT" => Some(FormalAttributeType::Z),
        "FLOAT" | "REAL" | "DOUBLE" | "DECIMAL" | "NUMERIC" => Some(FormalAttributeType::Float),
        "VARCHAR" | "CHAR" | "STRING" => Some(FormalAttributeType::String),
        "BOOLEAN" | "BOOL" => Some(FormalAttributeType::Bool),
        "DATE" => Some(FormalAttributeType::Date),
        "TIMESTAMP" => Some(FormalAttributeType::Timestamp {
            precision: type_annotation_precision(ty),
        }),
        _ => None,
    }
}

fn type_annotation_precision(ty: &str) -> Option<u32> {
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    ty[start..end].trim().parse().ok()
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
        "DOUBLE" => Some("DOUBLE"),
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

pub(super) fn formal_attribute_constructor(ty: FormalAttributeType) -> String {
    match ty {
        FormalAttributeType::String => "Attr_string".to_owned(),
        FormalAttributeType::Z => "Attr_Z".to_owned(),
        FormalAttributeType::Bool => "Attr_bool".to_owned(),
        FormalAttributeType::Float => "Attr_float".to_owned(),
        FormalAttributeType::Date => "Attr_date".to_owned(),
        FormalAttributeType::Timestamp { precision } => {
            format!("Attr_timestamp#{}", timestamp_precision(precision))
        }
    }
}
