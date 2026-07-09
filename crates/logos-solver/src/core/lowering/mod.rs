use chrono::{DateTime, LocalResult, TimeZone, Utc};
use chrono_tz::Tz;
use logos_ir::ir::{Column, CorrelationBinding, Query, ScalarAst, Schema, SqlType};

use crate::core::VerificationIr;

use super::coverage::feature_coverage;
use super::syntax::{
    DiagnosticSeverity, FormalAggregateTerm, FormalAttribute, FormalAttributeType, FormalFormula,
    FormalFunctionTerm, FormalListQuery, FormalNullDirection, FormalProofModule, FormalQuery,
    FormalQueryModule, FormalSchema, FormalSelectItem, FormalSetOp, FormalSortDirection,
    FormalSortKey, FormalTable, LoweredQuery, LoweredSchema, LoweringDiagnostic, LoweringStatus,
    ProofLoweringReport,
};
use scalar::formal_attribute_constructor;

const DEFAULT_TIMESTAMP_PRECISION: u32 = 6;
const MICROS_PER_SECOND: i64 = 1_000_000;

#[allow(dead_code)]
pub fn lower_verification_input(input: &VerificationIr) -> ProofLoweringReport {
    lower_verification_input_with_config(input, &LoweringConfig::default())
}

pub fn lower_verification_input_with_config(
    input: &VerificationIr,
    config: &LoweringConfig,
) -> ProofLoweringReport {
    let schema = lower_schema_with_config(input.schema_ir(), config);
    let source = lower_query_with_schema_config(input.source_query_ir(), input.schema_ir(), config);
    let target = lower_query_with_schema_config(input.target_query_ir(), input.schema_ir(), config);
    let query_module = match (&source.list_query, &target.list_query) {
        (Some(source_query), Some(target_query)) => {
            Some(emit_rocq_query_module(source_query, target_query))
        }
        _ => None,
    };
    let proof_module = match (&schema.schema, &source.list_query, &target.list_query) {
        (Some(_), Some(source_query), Some(target_query))
            if can_emit_bag_bridge_proof(source_query, target_query) =>
        {
            Some(emit_rocq_bag_bridge_proof_module())
        }
        (Some(_), Some(_), Some(_)) => Some(emit_rocq_list_proof_module()),
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

#[allow(dead_code)]
pub fn lower_schema(schema: &Schema) -> LoweredSchema {
    lower_schema_with_config(schema, &LoweringConfig::default())
}

pub fn lower_schema_with_config(schema: &Schema, config: &LoweringConfig) -> LoweredSchema {
    let mut context = LoweringContext::new(config.clone(), None);
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

#[allow(dead_code)]
pub fn lower_query(query: &Query) -> LoweredQuery {
    lower_query_with_config(query, &LoweringConfig::default())
}

pub fn lower_query_with_config(query: &Query, config: &LoweringConfig) -> LoweredQuery {
    lower_query_with_optional_schema_config(query, None, config)
}

fn lower_query_with_schema_config(
    query: &Query,
    schema: &Schema,
    config: &LoweringConfig,
) -> LoweredQuery {
    lower_query_with_optional_schema_config(query, Some(schema), config)
}

fn lower_query_with_optional_schema_config(
    query: &Query,
    schema: Option<&Schema>,
    config: &LoweringConfig,
) -> LoweredQuery {
    let feature_coverage = feature_coverage(&query.features);
    let mut context = LoweringContext::new(config.clone(), schema);
    let (lowered, list_lowered) = if rel_has_list_observation(&query.rel) {
        (None, context.lower_list_rel("rel", &query.rel))
    } else {
        let lowered = context.lower_rel("rel", &query.rel);
        let list_lowered = lowered.clone().map(|query| FormalListQuery::Bag {
            input: Box::new(query),
        });
        (lowered, list_lowered)
    };
    let status = if context.has_errors() {
        LoweringStatus::Blocked
    } else {
        LoweringStatus::Lowered
    };
    LoweredQuery {
        status,
        query: lowered,
        list_query: list_lowered,
        diagnostics: context.diagnostics,
        feature_coverage,
    }
}

fn rel_has_list_observation(rel: &logos_ir::ir::RelExpr) -> bool {
    matches!(rel, logos_ir::ir::RelExpr::Sort { .. })
}

#[derive(Debug, Clone)]
pub struct LoweringConfig {
    pub sql_time_zone: SqlTimeZone,
}

impl Default for LoweringConfig {
    fn default() -> Self {
        Self {
            sql_time_zone: SqlTimeZone::utc(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SqlTimeZone {
    name: String,
    kind: SqlTimeZoneKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SqlTimeZoneKind {
    FixedOffset { offset_micros: i64 },
    Named { zone: Tz },
    Unsupported,
}

impl SqlTimeZone {
    pub fn parse(value: &str) -> Self {
        let name = value.trim().to_owned();
        let kind = parse_fixed_time_zone_offset(&name)
            .map(|offset_micros| SqlTimeZoneKind::FixedOffset { offset_micros })
            .or_else(|| {
                name.parse::<Tz>()
                    .ok()
                    .map(|zone| SqlTimeZoneKind::Named { zone })
            })
            .unwrap_or(SqlTimeZoneKind::Unsupported);
        Self { name, kind }
    }

    pub fn try_parse(value: &str) -> Result<Self, String> {
        let parsed = Self::parse(value);
        if parsed.is_supported() {
            Ok(parsed)
        } else {
            Err(format!(
                "{value:?}; expected UTC, Z, a fixed offset such as +08:00, or an IANA time zone such as Asia/Shanghai"
            ))
        }
    }

    pub fn utc() -> Self {
        Self {
            name: "UTC".to_owned(),
            kind: SqlTimeZoneKind::FixedOffset { offset_micros: 0 },
        }
    }

    pub fn is_supported(&self) -> bool {
        !matches!(self.kind, SqlTimeZoneKind::Unsupported)
    }

    pub fn postgres_set_time_zone_sql(&self) -> Option<String> {
        match self.kind {
            SqlTimeZoneKind::FixedOffset { offset_micros } => Some(format!(
                "SET TIME ZONE INTERVAL '{}' HOUR TO MINUTE",
                fixed_offset_label(offset_micros)
            )),
            SqlTimeZoneKind::Named { zone } => Some(format!(
                "SET TIME ZONE {}",
                quote_sql_string(&zone.to_string())
            )),
            SqlTimeZoneKind::Unsupported => None,
        }
    }

    fn local_timestamp_micros_to_utc_instant(&self, local_micros: i64) -> Option<i64> {
        match self.kind {
            SqlTimeZoneKind::FixedOffset { offset_micros } => Some(local_micros - offset_micros),
            SqlTimeZoneKind::Named { zone } => {
                let local = datetime_utc_from_micros(local_micros)?.naive_utc();
                match zone.from_local_datetime(&local) {
                    LocalResult::Single(datetime) => {
                        Some(datetime.with_timezone(&Utc).timestamp_micros())
                    }
                    LocalResult::Ambiguous(_, _) | LocalResult::None => None,
                }
            }
            SqlTimeZoneKind::Unsupported => None,
        }
    }
}

fn datetime_utc_from_micros(micros: i64) -> Option<DateTime<Utc>> {
    let seconds = micros.div_euclid(MICROS_PER_SECOND);
    let subsecond_micros = micros.rem_euclid(MICROS_PER_SECOND);
    DateTime::<Utc>::from_timestamp(seconds, (subsecond_micros as u32) * 1_000)
}

#[derive(Debug)]
struct LoweringContext {
    diagnostics: Vec<LoweringDiagnostic>,
    config: LoweringConfig,
    correlations: Vec<CorrelationScope>,
}

#[derive(Debug, Clone)]
struct CorrelationScope {
    correlation: String,
    scope: Scope,
    field_names: Vec<String>,
}

mod emit;
mod rel;
mod scalar;
mod schema;
#[cfg(test)]
mod tests;

use emit::{
    can_emit_bag_bridge_proof, emit_rocq_bag_bridge_proof_module, emit_rocq_list_proof_module,
    emit_rocq_query_module,
};

impl LoweringContext {
    fn new(config: LoweringConfig, _schema: Option<&Schema>) -> Self {
        Self {
            diagnostics: Vec::new(),
            config,
            correlations: Vec::new(),
        }
    }

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

    fn with_correlations<T>(
        &mut self,
        bindings: &[CorrelationBinding],
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let scopes = bindings
            .iter()
            .map(|binding| CorrelationScope {
                correlation: binding.correlation.clone(),
                scope: Scope::from_columns(&binding.output),
                field_names: binding
                    .output
                    .iter()
                    .map(|column| column.name.clone())
                    .collect(),
            })
            .collect::<Vec<_>>();
        self.with_correlation_scopes(&scopes, f)
    }

    fn with_correlation_scopes<T>(
        &mut self,
        scopes: &[CorrelationScope],
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let base_len = self.correlations.len();
        self.correlations.extend(scopes.iter().cloned());
        let result = f(self);
        self.correlations.truncate(base_len);
        result
    }

    fn correlated_attribute(
        &mut self,
        path: &str,
        correlation: &str,
        index: Option<usize>,
        field: &str,
    ) -> Option<ScopeAttribute> {
        let Some(index) = index else {
            self.error(
                path,
                "correlated_ref_index_missing",
                "Calcite correlated field access did not expose a field index.",
            );
            return None;
        };
        let Some(binding) = self
            .correlations
            .iter()
            .rev()
            .find(|binding| binding.correlation == correlation)
        else {
            self.error(
                path,
                "correlation_binding_missing",
                "Correlated field access references a correlation variable that is not bound by the current relational context.",
            );
            return None;
        };
        let Some(attribute) = binding.scope.attribute(index) else {
            self.error(
                path,
                "correlated_ref_index_out_of_range",
                "Correlated field access index is outside the bound correlation row type.",
            );
            return None;
        };
        let debug_field = binding
            .field_names
            .get(index)
            .map(String::as_str)
            .unwrap_or(attribute.name.as_str());
        if debug_field != field {
            self.warning(
                path,
                "correlated_ref_field_name_mismatch",
                "Correlated field access was resolved by Calcite field index; the debug field name did not match the bound row type.",
            );
        }
        Some(attribute)
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
    formal_ty: FormalAttributeType,
}

impl Scope {
    fn from_columns(columns: &[Column]) -> Self {
        Self {
            attributes: columns
                .iter()
                .map(|column| ScopeAttribute {
                    name: column.name.clone(),
                    ty: column.ty.clone(),
                    formal_ty: query_attribute_type(column),
                    constructor: formal_attribute_constructor(query_attribute_type(column)),
                })
                .collect(),
        }
    }

    fn attribute(&self, index: usize) -> Option<ScopeAttribute> {
        self.attributes.get(index).cloned()
    }
}

fn query_attribute_type(column: &Column) -> FormalAttributeType {
    sql_type_to_formal_attribute_type(&column.ty, column.precision)
}

fn sql_type_to_formal_attribute_type(ty: &SqlType, precision: Option<u32>) -> FormalAttributeType {
    match ty {
        SqlType::Integer | SqlType::BigInt => FormalAttributeType::Z,
        SqlType::Float | SqlType::Double | SqlType::Decimal => FormalAttributeType::Float,
        SqlType::Varchar | SqlType::Time => FormalAttributeType::String,
        SqlType::Date => FormalAttributeType::Date,
        SqlType::Timestamp => FormalAttributeType::Timestamp { precision },
        SqlType::TimestampTz => FormalAttributeType::Timestamptz { precision },
        SqlType::Boolean => FormalAttributeType::Bool,
        SqlType::Any | SqlType::Null => FormalAttributeType::String,
    }
}

fn timestamp_precision(precision: Option<u32>) -> u32 {
    precision.unwrap_or(DEFAULT_TIMESTAMP_PRECISION)
}

fn is_unsupported_temporal_type(ty: &SqlType) -> bool {
    matches!(ty, SqlType::Time)
}

fn parse_fixed_time_zone_offset(value: &str) -> Option<i64> {
    let upper = value.trim().to_ascii_uppercase();
    if matches!(
        upper.as_str(),
        "UTC" | "GMT" | "Z" | "+00" | "+00:00" | "-00" | "-00:00"
    ) {
        return Some(0);
    }
    if upper.starts_with("UTC+")
        || upper.starts_with("UTC-")
        || upper.starts_with("GMT+")
        || upper.starts_with("GMT-")
    {
        return None;
    }
    let sign = if upper.starts_with('+') {
        1
    } else if upper.starts_with('-') {
        -1
    } else {
        return None;
    };
    let body = &upper[1..];
    let (hour_text, minute_text) = body.split_once(':').unwrap_or((body, "0"));
    if hour_text.len() != 2 || minute_text.len() != 2 {
        return None;
    }
    let hours = hour_text.parse::<i64>().ok()?;
    let minutes = minute_text.parse::<i64>().ok()?;
    if !(0..=14).contains(&hours) || !(0..=59).contains(&minutes) {
        return None;
    }
    if hours == 14 && minutes != 0 {
        return None;
    }
    Some(sign * (hours * 60 + minutes) * 60 * 1_000_000)
}

fn fixed_offset_label(offset_micros: i64) -> String {
    let sign = if offset_micros < 0 { '-' } else { '+' };
    let total_minutes = offset_micros.abs() / MICROS_PER_SECOND / 60;
    let hours = total_minutes / 60;
    let minutes = total_minutes % 60;
    format!("{sign}{hours:02}:{minutes:02}")
}

fn quote_sql_string(value: &str) -> String {
    format!("'{}'", value.replace('\'', "''"))
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

fn sanitize_correlation_name(value: &str) -> String {
    let sanitized = value
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
        .collect::<String>();
    if sanitized.is_empty() {
        "cor".to_owned()
    } else {
        sanitized
    }
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
