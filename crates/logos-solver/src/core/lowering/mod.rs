use logos_ir::ir::{Column, Query, ScalarAst, Schema, SqlType};

use crate::core::VerificationIr;

use super::coverage::feature_coverage;
use super::syntax::{
    DiagnosticSeverity, FormalAggregateTerm, FormalAttribute, FormalAttributeType, FormalFormula,
    FormalFunctionTerm, FormalProofModule, FormalQuery, FormalQueryModule, FormalSchema,
    FormalSelectItem, FormalSetOp, FormalTable, LoweredQuery, LoweredSchema, LoweringDiagnostic,
    LoweringStatus, ProofLoweringReport,
};
use scalar::formal_attribute_constructor;

pub fn lower_verification_input(input: &VerificationIr) -> ProofLoweringReport {
    let schema = lower_schema(input.schema_ir());
    let source = lower_query(input.source_query_ir());
    let target = lower_query(input.target_query_ir());
    let query_module = match (&source.query, &target.query) {
        (Some(source_query), Some(target_query)) => {
            Some(emit_rocq_query_module(source_query, target_query))
        }
        _ => None,
    };
    let proof_module = match (&schema.schema, &source.query, &target.query) {
        (Some(_), Some(_), Some(_)) => Some(emit_rocq_proof_module()),
        _ => None,
    };
    ProofLoweringReport {
        backend: "formal_sql_rocq".to_owned(),
        schema,
        source,
        target,
        query_module,
        proof_module,
    }
}

pub fn lower_schema(schema: &Schema) -> LoweredSchema {
    let mut context = LoweringContext::default();
    let lowered = context.lower_schema("schema", schema);
    let status = if context.has_errors() {
        LoweringStatus::Blocked
    } else {
        LoweringStatus::Lowered
    };
    LoweredSchema {
        status,
        schema: lowered,
        diagnostics: context.diagnostics,
    }
}

pub fn lower_query(query: &Query) -> LoweredQuery {
    let feature_coverage = feature_coverage(&query.features);
    let mut context = LoweringContext::default();
    let lowered = context.lower_rel("rel", &query.rel);
    let status = if context.has_errors() {
        LoweringStatus::Blocked
    } else {
        LoweringStatus::Lowered
    };
    LoweredQuery {
        status,
        query: lowered,
        diagnostics: context.diagnostics,
        feature_coverage,
    }
}

#[derive(Debug, Default)]
struct LoweringContext {
    diagnostics: Vec<LoweringDiagnostic>,
}

mod emit;
mod rel;
mod scalar;
mod schema;
#[cfg(test)]
mod tests;

use emit::{emit_rocq_proof_module, emit_rocq_query_module};

impl LoweringContext {
    fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
    }

    fn warning(&mut self, path: &str, code: &str, message: &str) {
        self.diagnostic(DiagnosticSeverity::Warning, path, code, message);
    }

    fn error(&mut self, path: &str, code: &str, message: &str) {
        self.diagnostic(DiagnosticSeverity::Error, path, code, message);
    }

    fn diagnostic(&mut self, severity: DiagnosticSeverity, path: &str, code: &str, message: &str) {
        self.diagnostics.push(LoweringDiagnostic {
            severity,
            path: path.to_owned(),
            code: code.to_owned(),
            message: message.to_owned(),
        });
    }
}

#[derive(Debug, Clone)]
struct Scope {
    attributes: Vec<ScopeAttribute>,
}

#[derive(Debug, Clone)]
struct ScopeAttribute {
    name: String,
    constructor: String,
    ty: SqlType,
}

impl Scope {
    fn from_columns(columns: &[Column]) -> Self {
        Self {
            attributes: columns
                .iter()
                .map(|column| ScopeAttribute {
                    name: column.name.clone(),
                    ty: column.ty.clone(),
                    constructor: formal_attribute_constructor(query_attribute_type(&column.ty))
                        .to_owned(),
                })
                .collect(),
        }
    }

    fn attribute(&self, index: usize) -> Option<ScopeAttribute> {
        self.attributes.get(index).cloned()
    }
}

fn query_attribute_type(ty: &SqlType) -> FormalAttributeType {
    match ty {
        SqlType::Integer | SqlType::BigInt => FormalAttributeType::Z,
        SqlType::Float | SqlType::Double | SqlType::Decimal => FormalAttributeType::Float,
        SqlType::Varchar | SqlType::Date | SqlType::Time | SqlType::Timestamp => {
            FormalAttributeType::String
        }
        SqlType::Boolean => FormalAttributeType::Bool,
        SqlType::Any | SqlType::Null => FormalAttributeType::String,
    }
}

fn is_temporal_type(ty: &SqlType) -> bool {
    matches!(ty, SqlType::Date | SqlType::Time | SqlType::Timestamp)
}

fn disjoint_columns(left: &[Column], right: &[Column]) -> bool {
    left.iter().all(|left_col| {
        right
            .iter()
            .all(|right_col| left_col.name != right_col.name)
    })
}

fn has_unique_column_names(columns: &[Column]) -> bool {
    columns.iter().enumerate().all(|(index, column)| {
        columns
            .iter()
            .skip(index + 1)
            .all(|other| other.name != column.name)
    })
}

fn sql_string_literal_content(raw: &str) -> Option<String> {
    let inner = raw.strip_prefix('\'')?.strip_suffix('\'')?;
    Some(inner.replace("''", "'"))
}

fn is_integer_literal(raw: &str) -> bool {
    let digits = raw.strip_prefix('-').unwrap_or(raw);
    !digits.is_empty() && digits.chars().all(|ch| ch.is_ascii_digit())
}

fn is_true_literal(ast: &ScalarAst) -> bool {
    matches!(ast, ScalarAst::Literal { raw } if raw.eq_ignore_ascii_case("true"))
}
