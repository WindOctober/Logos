use crate::ir::{ScalarAst, ScalarOp};

use super::ast::{
    CoreArithmeticOp, CoreCaseBranch, CoreNumericFunctionOp, CorePredicateCaseBranch,
    CorePredicateExpr, CoreScalarExpr, CoreStringFunctionOp, CoreValueExpr,
};
use super::error::{CoreScalarFailure, CoreScalarUnsupported};
use super::ops::{comparison_op, is_predicate_op, is_value_op};

pub fn lower_core_scalar(ast: &ScalarAst) -> Result<CoreScalarExpr, CoreScalarUnsupported> {
    CoreScalarLowerer.lower_scalar(ast)
}

pub fn diagnose_core_scalar_failure(ast: &ScalarAst) -> Option<CoreScalarFailure> {
    CoreScalarLowerer.diagnose_failure(ast)
}

#[derive(Debug, Default, Clone, Copy)]
struct CoreScalarLowerer;

impl CoreScalarLowerer {
    fn lower_scalar(&self, ast: &ScalarAst) -> Result<CoreScalarExpr, CoreScalarUnsupported> {
        match ast {
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Window { .. }
            | ScalarAst::TypeAnnotation { .. } => Ok(CoreScalarExpr::Value {
                expr: self.lower_value(ast)?,
            }),
            ScalarAst::Call {
                op: ScalarOp::Case, ..
            } => self.lower_case_scalar(ast),
            ScalarAst::Call { op, .. } if is_value_op(op) => Ok(CoreScalarExpr::Value {
                expr: self.lower_value(ast)?,
            }),
            ScalarAst::Call { op, .. } if is_predicate_op(op) => Ok(CoreScalarExpr::Predicate {
                expr: self.lower_predicate(ast)?,
            }),
            ScalarAst::Call { .. }
            | ScalarAst::Flag { .. }
            | ScalarAst::RelSubquery { .. }
            | ScalarAst::Sarg { .. } => Err(CoreScalarUnsupported::UnsupportedOperator),
        }
    }

    fn lower_case_scalar(&self, ast: &ScalarAst) -> Result<CoreScalarExpr, CoreScalarUnsupported> {
        match self.lower_value(ast) {
            Ok(expr) => Ok(CoreScalarExpr::Value { expr }),
            Err(
                CoreScalarUnsupported::ExpectedValue | CoreScalarUnsupported::ExpectedPredicate,
            ) => Ok(CoreScalarExpr::Predicate {
                expr: self.lower_predicate(ast)?,
            }),
            Err(reason) => Err(reason),
        }
    }

    fn diagnose_failure(&self, ast: &ScalarAst) -> Option<CoreScalarFailure> {
        let reason = self.lower_scalar(ast).err()?;
        Some(self.first_failure(ast, reason))
    }

    fn first_failure(&self, ast: &ScalarAst, reason: CoreScalarUnsupported) -> CoreScalarFailure {
        match ast {
            ScalarAst::Call { op, args, .. } => {
                for arg in args {
                    if let Some(failure) = self.diagnose_failure(arg) {
                        return failure;
                    }
                }
                CoreScalarFailure {
                    reason,
                    operator: Some(format!("{op:?}")),
                }
            }
            ScalarAst::TypeAnnotation { expr, .. } => {
                self.diagnose_failure(expr).unwrap_or(CoreScalarFailure {
                    reason,
                    operator: None,
                })
            }
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. }
            | ScalarAst::Window { .. }
            | ScalarAst::RelSubquery { .. }
            | ScalarAst::Sarg { .. } => CoreScalarFailure {
                reason,
                operator: None,
            },
        }
    }

    fn lower_value(&self, ast: &ScalarAst) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        match ast {
            ScalarAst::InputRef { index } => Ok(CoreValueExpr::InputRef { index: *index }),
            ScalarAst::CorrelatedRef {
                correlation, field, ..
            } => Ok(CoreValueExpr::CorrelatedRef {
                correlation: correlation.clone(),
                field: field.clone(),
            }),
            ScalarAst::Literal { raw } => Ok(CoreValueExpr::Literal { raw: raw.clone() }),
            ScalarAst::Window { raw, .. } => Ok(CoreValueExpr::WindowFunction { raw: raw.clone() }),
            ScalarAst::TypeAnnotation { expr, ty } => self.lower_value_type_annotation(expr, ty),
            ScalarAst::Call { op, args, .. } => self.lower_value_call(op, args),
            ScalarAst::Flag { .. } | ScalarAst::RelSubquery { .. } | ScalarAst::Sarg { .. } => {
                Err(CoreScalarUnsupported::UnsupportedOperator)
            }
        }
    }

    fn lower_value_type_annotation(
        &self,
        expr: &ScalarAst,
        ty: &str,
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        if let ScalarAst::Call {
            op: ScalarOp::Cast,
            args,
            ..
        } = expr
        {
            require_arity(args, 1)?;
            return Ok(CoreValueExpr::Cast {
                expr: Box::new(self.lower_value(&args[0])?),
                ty: ty.to_owned(),
            });
        }

        Ok(CoreValueExpr::TypeAnnotation {
            expr: Box::new(self.lower_value(expr)?),
            ty: ty.to_owned(),
        })
    }

    fn lower_value_call(
        &self,
        op: &ScalarOp,
        args: &[ScalarAst],
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        let arithmetic_op = match op {
            ScalarOp::Plus => {
                require_arity(args, 2)?;
                CoreArithmeticOp::Plus
            }
            ScalarOp::Minus if args.len() == 1 => CoreArithmeticOp::UnaryMinus,
            ScalarOp::Minus if args.len() == 2 => CoreArithmeticOp::Minus,
            ScalarOp::Minus => return Err(CoreScalarUnsupported::BadArity),
            ScalarOp::Multiply => {
                require_arity(args, 2)?;
                CoreArithmeticOp::Multiply
            }
            ScalarOp::Divide => {
                require_arity(args, 2)?;
                CoreArithmeticOp::Divide
            }
            ScalarOp::Case => return self.lower_case_value(args),
            ScalarOp::StringConcat => return self.lower_string_concat_value(args),
            ScalarOp::Lower => {
                return self.lower_string_function_value(CoreStringFunctionOp::Lower, args);
            }
            ScalarOp::Upper => {
                return self.lower_string_function_value(CoreStringFunctionOp::Upper, args);
            }
            ScalarOp::Substring => {
                return self.lower_string_function_value(CoreStringFunctionOp::Substring, args);
            }
            ScalarOp::Exp => {
                return self.lower_numeric_function_value(CoreNumericFunctionOp::Exp, args);
            }
            ScalarOp::Power => {
                return self.lower_numeric_function_value(CoreNumericFunctionOp::Power, args);
            }
            ScalarOp::Extract => return self.lower_extract_value(args),
            ScalarOp::ScalarQuery => return self.lower_scalar_subquery_value(args),
            op if is_predicate_op(op) => return Err(CoreScalarUnsupported::ExpectedValue),
            _ => return Err(CoreScalarUnsupported::UnsupportedOperator),
        };

        Ok(CoreValueExpr::Arithmetic {
            op: arithmetic_op,
            args: self.lower_values(args)?,
        })
    }

    fn lower_string_concat_value(
        &self,
        args: &[ScalarAst],
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        require_min_arity(args, 2)?;
        Ok(CoreValueExpr::StringConcat {
            args: self.lower_values(args)?,
        })
    }

    fn lower_string_function_value(
        &self,
        op: CoreStringFunctionOp,
        args: &[ScalarAst],
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        match op {
            CoreStringFunctionOp::Lower | CoreStringFunctionOp::Upper => require_arity(args, 1)?,
            CoreStringFunctionOp::Substring if args.len() == 2 || args.len() == 3 => {}
            CoreStringFunctionOp::Substring => return Err(CoreScalarUnsupported::BadArity),
        }

        Ok(CoreValueExpr::StringFunction {
            op,
            args: self.lower_values(args)?,
        })
    }

    fn lower_numeric_function_value(
        &self,
        op: CoreNumericFunctionOp,
        args: &[ScalarAst],
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        match op {
            CoreNumericFunctionOp::Exp => require_arity(args, 1)?,
            CoreNumericFunctionOp::Power => require_arity(args, 2)?,
        }

        Ok(CoreValueExpr::NumericFunction {
            op,
            args: self.lower_values(args)?,
        })
    }

    fn lower_scalar_subquery_value(
        &self,
        args: &[ScalarAst],
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        require_arity(args, 1)?;
        Err(CoreScalarUnsupported::UnsupportedOperator)
    }

    fn lower_extract_value(
        &self,
        args: &[ScalarAst],
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        require_arity(args, 2)?;
        let field = expect_flag(&args[0])?.to_owned();
        Ok(CoreValueExpr::Extract {
            field,
            expr: Box::new(self.lower_value_or_predicate_value(&args[1])?),
        })
    }

    fn lower_case_value(&self, args: &[ScalarAst]) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        if args.len() < 3 || args.len() % 2 == 0 {
            return Err(CoreScalarUnsupported::BadArity);
        }

        let mut branches = Vec::new();
        for pair in args[..args.len() - 1].chunks_exact(2) {
            branches.push(CoreCaseBranch {
                when: self.lower_predicate(&pair[0])?,
                then: self.lower_value(&pair[1])?,
            });
        }

        Ok(CoreValueExpr::Case {
            branches,
            else_expr: Box::new(self.lower_value(args.last().expect("CASE arity checked"))?),
        })
    }

    fn lower_case_predicate(
        &self,
        args: &[ScalarAst],
    ) -> Result<CorePredicateExpr, CoreScalarUnsupported> {
        if args.len() < 3 || args.len() % 2 == 0 {
            return Err(CoreScalarUnsupported::BadArity);
        }

        let mut branches = Vec::new();
        for pair in args[..args.len() - 1].chunks_exact(2) {
            branches.push(CorePredicateCaseBranch {
                when: self.lower_predicate(&pair[0])?,
                then: self.lower_predicate(&pair[1])?,
            });
        }

        Ok(CorePredicateExpr::Case {
            branches,
            else_predicate: Box::new(
                self.lower_predicate(args.last().expect("CASE arity checked"))?,
            ),
        })
    }

    fn lower_predicate(&self, ast: &ScalarAst) -> Result<CorePredicateExpr, CoreScalarUnsupported> {
        match ast {
            ScalarAst::Call { op, args, .. } => self.lower_predicate_call(op, args),
            ScalarAst::TypeAnnotation { .. }
            | ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Window { .. } => Ok(CorePredicateExpr::BooleanValue {
                expr: Box::new(self.lower_value(ast)?),
            }),
            ScalarAst::Flag { .. } | ScalarAst::RelSubquery { .. } | ScalarAst::Sarg { .. } => {
                Err(CoreScalarUnsupported::UnsupportedOperator)
            }
        }
    }

    fn lower_predicate_call(
        &self,
        op: &ScalarOp,
        args: &[ScalarAst],
    ) -> Result<CorePredicateExpr, CoreScalarUnsupported> {
        match op {
            ScalarOp::Eq
            | ScalarOp::NotEq
            | ScalarOp::Lt
            | ScalarOp::Lte
            | ScalarOp::Gt
            | ScalarOp::Gte
            | ScalarOp::IsNotDistinctFrom => {
                require_arity(args, 2)?;
                Ok(CorePredicateExpr::Comparison {
                    op: comparison_op(op),
                    left: Box::new(self.lower_value_or_predicate_value(&args[0])?),
                    right: Box::new(self.lower_value_or_predicate_value(&args[1])?),
                })
            }
            ScalarOp::IsNull => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::IsNull {
                    expr: Box::new(self.lower_value_or_predicate_value(&args[0])?),
                })
            }
            ScalarOp::IsNotNull => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::IsNotNull {
                    expr: Box::new(self.lower_value_or_predicate_value(&args[0])?),
                })
            }
            ScalarOp::IsTrue => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::IsTrue {
                    predicate: Box::new(self.lower_predicate(&args[0])?),
                })
            }
            ScalarOp::IsNotTrue => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::IsNotTrue {
                    predicate: Box::new(self.lower_predicate(&args[0])?),
                })
            }
            ScalarOp::IsFalse => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::IsFalse {
                    predicate: Box::new(self.lower_predicate(&args[0])?),
                })
            }
            ScalarOp::IsNotFalse => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::IsNotFalse {
                    predicate: Box::new(self.lower_predicate(&args[0])?),
                })
            }
            ScalarOp::And => {
                require_min_arity(args, 2)?;
                Ok(CorePredicateExpr::And {
                    predicates: self.lower_predicates(args)?,
                })
            }
            ScalarOp::Or => {
                require_min_arity(args, 2)?;
                Ok(CorePredicateExpr::Or {
                    predicates: self.lower_predicates(args)?,
                })
            }
            ScalarOp::Not => {
                require_arity(args, 1)?;
                Ok(CorePredicateExpr::Not {
                    predicate: Box::new(self.lower_predicate(&args[0])?),
                })
            }
            ScalarOp::Like => self.lower_like_predicate(args),
            ScalarOp::Case => self.lower_case_predicate(args),
            ScalarOp::Exists => self.lower_exists_predicate(args),
            ScalarOp::In => self.lower_in_predicate(args),
            op if is_value_op(op) => Err(CoreScalarUnsupported::ExpectedPredicate),
            _ => Err(CoreScalarUnsupported::UnsupportedOperator),
        }
    }

    fn lower_like_predicate(
        &self,
        args: &[ScalarAst],
    ) -> Result<CorePredicateExpr, CoreScalarUnsupported> {
        if args.len() != 2 && args.len() != 3 {
            return Err(CoreScalarUnsupported::BadArity);
        }

        Ok(CorePredicateExpr::Like {
            value: Box::new(self.lower_value(&args[0])?),
            pattern: Box::new(self.lower_value(&args[1])?),
            escape: args
                .get(2)
                .map(|arg| self.lower_value(arg))
                .transpose()?
                .map(Box::new),
        })
    }

    fn lower_exists_predicate(
        &self,
        args: &[ScalarAst],
    ) -> Result<CorePredicateExpr, CoreScalarUnsupported> {
        require_arity(args, 1)?;
        Err(CoreScalarUnsupported::UnsupportedOperator)
    }

    fn lower_in_predicate(
        &self,
        args: &[ScalarAst],
    ) -> Result<CorePredicateExpr, CoreScalarUnsupported> {
        require_min_arity(args, 2)?;
        Err(CoreScalarUnsupported::UnsupportedOperator)
    }

    fn lower_values(
        &self,
        args: &[ScalarAst],
    ) -> Result<Vec<CoreValueExpr>, CoreScalarUnsupported> {
        args.iter().map(|arg| self.lower_value(arg)).collect()
    }

    fn lower_value_or_predicate_value(
        &self,
        ast: &ScalarAst,
    ) -> Result<CoreValueExpr, CoreScalarUnsupported> {
        match self.lower_value(ast) {
            Ok(expr) => Ok(expr),
            Err(
                CoreScalarUnsupported::ExpectedValue | CoreScalarUnsupported::ExpectedPredicate,
            ) => Ok(CoreValueExpr::PredicateAsValue {
                predicate: Box::new(self.lower_predicate(ast)?),
            }),
            Err(reason) => Err(reason),
        }
    }

    fn lower_predicates(
        &self,
        args: &[ScalarAst],
    ) -> Result<Vec<CorePredicateExpr>, CoreScalarUnsupported> {
        args.iter().map(|arg| self.lower_predicate(arg)).collect()
    }
}

fn expect_flag(ast: &ScalarAst) -> Result<&str, CoreScalarUnsupported> {
    match ast {
        ScalarAst::Flag { name } => Ok(name),
        _ => Err(CoreScalarUnsupported::ExpectedValue),
    }
}

fn require_arity(args: &[ScalarAst], expected: usize) -> Result<(), CoreScalarUnsupported> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(CoreScalarUnsupported::BadArity)
    }
}

fn require_min_arity(args: &[ScalarAst], min: usize) -> Result<(), CoreScalarUnsupported> {
    if args.len() >= min {
        Ok(())
    } else {
        Err(CoreScalarUnsupported::BadArity)
    }
}
