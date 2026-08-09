use std::collections::{BTreeMap, BTreeSet};

use crate::core::VerificationIr;
use chrono::{DateTime, LocalResult, TimeZone, Utc};
use chrono_tz::Tz;
use logos_ir::calcite::ty::{SqlTypeAnnotation, classify_type_annotation};
use logos_ir::ir::{
    AggregateCall, Column, CorrelationBinding, ForeignKeyMatch, IntegrityComparison,
    IntegrityPredicate, IntegrityValueExpr, Query, QueryAnalysisError, RelExpr, ScalarAst,
    ScalarExpr, ScalarOp, ScalarSourceClauseOwnership, ScalarSourceProvenance, Schema,
    SourceAnalysisErrorProvenance, SourceClauseKind, SqlEnvironment, SqlStringType, SqlType,
    SqlTypeValidationError,
};

use super::syntax::{
    DiagnosticSeverity, FormalAggregateFunction, FormalAggregateQuantifier, FormalAggregateTerm,
    FormalAttribute, FormalAttributeType, FormalCaseBranch, FormalCheckConstraint,
    FormalConstraintFormula, FormalForeignKeyConstraint, FormalFunctionTerm, FormalGroupingSet,
    FormalNullDirection, FormalNumericAggregate, FormalPredicate, FormalProofModule,
    FormalQueryBinding, FormalQueryError, FormalQueryExpr, FormalQueryJoinKind, FormalQueryModule,
    FormalScalarExpr, FormalScalarSelectItem, FormalSchema, FormalSetOp, FormalSortDirection,
    FormalSortKey, FormalTable, FormalTableConstraints, FormalUniqueConstraint,
    FormalUniqueIndexConstraint, FormalValueLiteral, FormalWindowFunction, FormalWindowItem,
    LoweredProgram, LoweredQuery, LoweredSchema, LoweringDiagnostic, LoweringStatus,
    NumericDscaleProvenance, ProofLoweringReport, ScalarBooleanOperator, ScalarCast,
    ScalarDatePart, ScalarNumericKind, ScalarNumericSource, ScalarOperator, ScalarStringCase,
    ScalarTimestampUnit, query_expr_output_signature, validate_query_expr_scalar_operators,
};
use crate::core::VerificationMode;

const DEFAULT_TIMESTAMP_PRECISION: u32 = 6;
const MAX_TIMESTAMP_PRECISION: u32 = 6;
const MICROS_PER_SECOND: i64 = 1_000_000;

#[cfg(test)]
fn lower_verification_input(input: &VerificationIr) -> ProofLoweringReport {
    lower_verification_input_with_config(input, &LoweringConfig::default())
}

#[cfg(test)]
pub fn lower_verification_input_with_config(
    input: &VerificationIr,
    config: &LoweringConfig,
) -> ProofLoweringReport {
    lower_verification_input_with_mode(input, config, VerificationMode::SafeUnconditional)
}

pub fn lower_verification_input_with_mode(
    input: &VerificationIr,
    config: &LoweringConfig,
    verification_mode: VerificationMode,
) -> ProofLoweringReport {
    let schema = lower_schema_with_config(input.schema_ir(), config);
    let mut source_statements = lower_query_program(
        input.source_program_ir(),
        input.schema_ir(),
        config,
        "source",
    );
    let mut target_statements = lower_query_program(
        input.target_program_ir(),
        input.schema_ir(),
        config,
        "target",
    );
    let mut program_diagnostics = Vec::new();
    if source_statements.len() != target_statements.len() {
        program_diagnostics.push(LoweringDiagnostic {
            severity: DiagnosticSeverity::Warning,
            path: "equivalence.statements".to_owned(),
            code: "statement_count_mismatch".to_owned(),
            message: format!(
                "Source and target contain different numbers of ordered query statements ({} versus {}). Every statement remains lowered and emitted; the generated program-equivalence goal preserves both lengths and is therefore unprovable.",
                source_statements.len(),
                target_statements.len()
            ),
        });
    }
    let paired_statement_count = source_statements.len().min(target_statements.len());
    for index in 0..paired_statement_count {
        normalize_output_pair_for_equivalence(
            &mut source_statements[index],
            &mut target_statements[index],
        );
    }
    let source = summarize_lowered_program(source_statements, &program_diagnostics);
    let target = summarize_lowered_program(target_statements, &program_diagnostics);
    let source_parts = complete_program_parts(&source);
    let target_parts = complete_program_parts(&target);
    let query_module = match (&source_parts, &target_parts) {
        (Some(source_parts), Some(target_parts)) => {
            if program_parts_have_bindings(source_parts)
                || program_parts_have_bindings(target_parts)
            {
                emit_rocq_bound_query_program_module_with_signatures(source_parts, target_parts)
            } else {
                let source_plain = plain_program_parts(source_parts);
                let target_plain = plain_program_parts(target_parts);
                emit_rocq_query_program_module_with_signatures(&source_plain, &target_plain)
            }
        }
        _ => None,
    };
    let proof_module = match (&schema.schema, &source_parts, &target_parts) {
        (Some(_), Some(source_parts), Some(target_parts)) => Some(
            if program_parts_have_bindings(source_parts)
                || program_parts_have_bindings(target_parts)
            {
                emit_rocq_bound_query_proof_module_for_mode(verification_mode)
            } else {
                emit_rocq_query_expr_proof_module_for_mode(verification_mode)
            },
        ),
        _ => None,
    };
    ProofLoweringReport {
        backend: "formal_sql_rocq".to_owned(),
        sql_environment: config.sql_environment,
        input_bindings: None,
        schema,
        source,
        target,
        query_module,
        proof_module,
        goal_module: None,
    }
}

fn lower_query_program(
    queries: &[Query],
    schema: &Schema,
    config: &LoweringConfig,
    side: &str,
) -> Vec<LoweredQuery> {
    let mut statements = Vec::with_capacity(queries.len());
    for (index, query) in queries.iter().enumerate() {
        statements.push(lower_query_with_optional_schema_config(
            query,
            Some(schema),
            config,
            &format!("{side}_{index}"),
        ));
    }
    statements
}

fn summarize_lowered_program(
    statements: Vec<LoweredQuery>,
    program_diagnostics: &[LoweringDiagnostic],
) -> LoweredProgram {
    let status = if !statements.is_empty()
        && statements
            .iter()
            .all(|statement| statement.status == LoweringStatus::Lowered)
    {
        LoweringStatus::Lowered
    } else {
        LoweringStatus::Blocked
    };
    let mut diagnostics = program_diagnostics.to_vec();
    for (index, statement) in statements.iter().enumerate() {
        diagnostics.extend(statement.diagnostics.iter().cloned().map(|mut diagnostic| {
            diagnostic.path = format!("statements[{index}].{}", diagnostic.path);
            diagnostic
        }));
    }
    LoweredProgram {
        status,
        statements,
        diagnostics,
    }
}

type ProgramPart<'a> = emit::BoundProgramPart<'a>;

fn complete_program_parts(program: &LoweredProgram) -> Option<Vec<ProgramPart<'_>>> {
    if program.status != LoweringStatus::Lowered || program.statements.is_empty() {
        return None;
    }
    program
        .statements
        .iter()
        .map(|statement| {
            Some((
                statement.query_expr.as_ref()?,
                statement.output_signature.as_deref()?,
                statement.bindings.as_slice(),
            ))
        })
        .collect()
}

fn program_parts_have_bindings(program: &[ProgramPart<'_>]) -> bool {
    program.iter().any(|(_, _, bindings)| !bindings.is_empty())
}

fn plain_program_parts<'a>(
    program: &'a [ProgramPart<'a>],
) -> Vec<(&'a FormalQueryExpr, &'a [FormalAttribute])> {
    program
        .iter()
        .map(|(query, signature, _)| (*query, *signature))
        .collect()
}

fn normalize_output_pair_for_equivalence(source: &mut LoweredQuery, target: &mut LoweredQuery) {
    if source.status != LoweringStatus::Lowered || target.status != LoweringStatus::Lowered {
        return;
    }
    let (Some(source_signature), Some(target_signature)) = (
        source.output_signature.clone(),
        target.output_signature.clone(),
    ) else {
        return;
    };
    let mut diagnostics = Vec::new();
    if source_signature.len() != target_signature.len() {
        diagnostics.push(LoweringDiagnostic {
            severity: DiagnosticSeverity::Warning,
            path: "equivalence.output".to_owned(),
            code: "output_arity_mismatch".to_owned(),
            message: format!(
                "Source and target lowered output arities differ ({} versus {}). Both queries remain lowered, but their ordered FormalSQL output signatures differ, so the generated equivalence goal requires an unprovable signature equality.",
                source_signature.len(),
                target_signature.len()
            ),
        });
    }
    let paired_attribute_count = source_signature.len().min(target_signature.len());
    for index in 0..paired_attribute_count {
        let source_attribute = &source_signature[index];
        let target_attribute = &target_signature[index];
        if source_attribute.ty != target_attribute.ty {
            diagnostics.push(LoweringDiagnostic {
                severity: DiagnosticSeverity::Warning,
                path: format!("equivalence.output[{index}]"),
                code: "output_type_mismatch".to_owned(),
                message: format!(
                    "Source and target lowered positional output types differ ({:?} versus {:?}). Both queries remain lowered, but exact FormalAttributeType and typmod information is retained in unequal Rocq output signatures.",
                    source_attribute.ty, target_attribute.ty
                ),
            });
        }
    }
    for diagnostic in diagnostics {
        source.diagnostics.push(diagnostic.clone());
        target.diagnostics.push(diagnostic);
    }
    canonicalize_query_output_labels(source);
    canonicalize_query_output_labels(target);
}

fn canonicalize_query_output_labels(lowered: &mut LoweredQuery) {
    if lowered.query_expr.is_none() || lowered.output_signature.is_none() {
        return;
    }
    let query = lowered
        .query_expr
        .take()
        .expect("query expression was checked above");
    let output_signature = lowered
        .output_signature
        .take()
        .expect("output signature was checked above");
    let canonical_signature = output_signature
        .iter()
        .enumerate()
        .map(|(index, attribute)| FormalAttribute {
            name: format!("__logos_output_{index}"),
            ty: attribute.ty,
        })
        .collect::<Vec<_>>();
    // A query-wide analysis error is admissible only at the root. Renaming its
    // declared columns in place preserves that authority; wrapping it in the
    // ordinary output-restoring Projection would turn the same trusted error
    // into a forbidden nested marker and silently suppress module emission.
    let query = match query {
        FormalQueryExpr::Error { error, .. } => FormalQueryExpr::Error {
            columns: canonical_signature.clone(),
            error,
        },
        query => {
            let select = output_signature
                .iter()
                .zip(&canonical_signature)
                .map(|(source, target)| FormalScalarSelectItem {
                    expr: FormalScalarExpr::Leaf {
                        result_ty: source.ty,
                        term: FormalAggregateTerm::Expr {
                            term: FormalFunctionTerm::Attribute {
                                name: source.name.clone(),
                                ty: source.ty,
                            },
                        },
                    },
                    alias: target.name.clone(),
                    alias_ty: target.ty,
                    numeric_dscale: None,
                })
                .collect::<Vec<_>>();
            FormalQueryExpr::Projection {
                select,
                input: Box::new(query),
            }
        }
    };
    if let Err(message) = validate_query_expr_scalar_operators(&query) {
        lowered.status = LoweringStatus::Blocked;
        lowered.query_expr = None;
        lowered.output_signature = None;
        lowered.diagnostics.push(LoweringDiagnostic {
            severity: DiagnosticSeverity::Error,
            path: "equivalence.outputNormalization".to_owned(),
            code: "normalized_query_expression_invalid".to_owned(),
            message: format!(
                "Canonical output-label normalization produced an invalid FormalSQL query expression: {message}. The statement is conservatively blocked instead of emitting inconsistent program artifacts."
            ),
        });
    } else {
        lowered.query_expr = Some(query);
        lowered.output_signature = Some(canonical_signature);
    }
}

#[cfg(test)]
fn lower_schema(schema: &Schema) -> LoweredSchema {
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

#[cfg(test)]
fn lower_query(query: &Query) -> LoweredQuery {
    lower_query_with_config(query, &LoweringConfig::default())
}

#[cfg(test)]
fn lower_query_with_config(query: &Query, config: &LoweringConfig) -> LoweredQuery {
    lower_query_with_optional_schema_config(query, None, config, "test_0")
}

#[cfg(test)]
fn lower_query_with_schema_config(
    query: &Query,
    schema: &Schema,
    config: &LoweringConfig,
) -> LoweredQuery {
    lower_query_with_optional_schema_config(query, Some(schema), config, "test_0")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundAnalysisErrorNormalization {
    Unchanged,
    Promoted,
    CompetingCategories,
    MissingOuterSignature,
}

fn normalize_bound_analysis_errors(
    bindings: &mut Vec<FormalQueryBinding>,
    body: &mut Option<FormalQueryExpr>,
) -> BoundAnalysisErrorNormalization {
    let mut analysis_errors = bindings
        .iter()
        .filter_map(|binding| match &binding.query_expr {
            FormalQueryExpr::Error { error, .. } => Some(*error),
            _ => None,
        })
        .collect::<Vec<_>>();
    let body_error = body.as_ref().and_then(|query_expr| match query_expr {
        FormalQueryExpr::Error { columns, error } => Some((columns.clone(), *error)),
        _ => None,
    });
    analysis_errors.extend(body_error.as_ref().map(|(_, error)| *error));
    let Some(error) = analysis_errors.first().copied() else {
        return BoundAnalysisErrorNormalization::Unchanged;
    };
    if analysis_errors.iter().any(|candidate| *candidate != error) {
        return BoundAnalysisErrorNormalization::CompetingCategories;
    }
    let columns = body_error
        .map(|(columns, _)| columns)
        .or_else(|| body.as_ref().and_then(query_expr_output_signature));
    let Some(columns) = columns else {
        return BoundAnalysisErrorNormalization::MissingOuterSignature;
    };
    *body = Some(FormalQueryExpr::Error { columns, error });
    bindings.clear();
    BoundAnalysisErrorNormalization::Promoted
}

fn lower_query_with_optional_schema_config(
    query: &Query,
    schema: Option<&Schema>,
    config: &LoweringConfig,
    binding_namespace: &str,
) -> LoweredQuery {
    let (raw_bindings, body_rel) = match &query.rel {
        RelExpr::Bindings { bindings, body, .. } => (bindings.as_slice(), body.as_ref()),
        rel => (&[][..], rel),
    };
    let body_query = Query {
        source_sql: query.source_sql.clone(),
        rel: body_rel.clone(),
        analysis_errors: query.analysis_errors.clone(),
    };
    let binding_queries = raw_bindings
        .iter()
        .map(|binding| Query {
            source_sql: query.source_sql.clone(),
            rel: binding.rel.clone(),
            analysis_errors: Vec::new(),
        })
        .collect::<Vec<_>>();
    let invalid_source_binding = binding_queries
        .iter()
        .enumerate()
        .find_map(|(index, binding)| {
            validate_query_scalar_source_bindings(binding, cfg!(test))
                .err()
                .map(|message| (format!("rel.bindings[{index}].sourceProvenance"), message))
        })
        .or_else(|| {
            validate_query_scalar_source_bindings(&body_query, cfg!(test))
                .err()
                .map(|message| ("rel.sourceProvenance".to_owned(), message))
        });
    if let Some((path, message)) = invalid_source_binding {
        return LoweredQuery {
            status: LoweringStatus::Blocked,
            bindings: Vec::new(),
            query_expr: None,
            output_signature: None,
            diagnostics: vec![LoweringDiagnostic {
                severity: DiagnosticSeverity::Error,
                path,
                code: "scalar_source_provenance_not_bound_to_query".to_owned(),
                message,
            }],
        };
    }
    let mut context = LoweringContext::new(config.clone(), schema);
    for (index, binding) in raw_bindings.iter().enumerate() {
        let relation = format!("__logos_{binding_namespace}_cte_{index}");
        if context
            .schema
            .as_ref()
            .is_some_and(|schema| schema.tables.iter().any(|table| table.name == relation))
        {
            context.error(
                &format!("rel.bindings[{index}].relation"),
                "query_binding_relation_not_fresh",
                "The internal CTE relation name collides with an authoritative base-table name.",
            );
            continue;
        }
        if context
            .query_bindings
            .insert(
                binding.id.clone(),
                LoweredQueryBindingSource {
                    relation,
                    output: binding.rel.output().to_vec(),
                    lowered_scope: None,
                },
            )
            .is_some()
        {
            context.error(
                &format!("rel.bindings[{index}].id"),
                "duplicate_query_binding_id",
                "A query-local CTE binding identity occurs more than once in one statement.",
            );
        }
    }

    let mut lowered_bindings = Vec::with_capacity(raw_bindings.len());
    for (index, (binding, binding_query)) in raw_bindings.iter().zip(&binding_queries).enumerate() {
        let diagnostic_start = context.diagnostics.len();
        let lowered = lower_query_after_special_roots(
            &mut context,
            binding_query,
            &format!("rel.binding{index}"),
        )
        .and_then(|query_expr| {
            close_query_root_output(&mut context, binding.rel.output(), query_expr)
        });
        for diagnostic in &mut context.diagnostics[diagnostic_start..] {
            diagnostic.path = format!("rel.bindings[{index}].{}", diagnostic.path);
        }
        let Some(query_expr) = lowered else {
            continue;
        };
        if let Err(message) = validate_query_expr_scalar_operators(&query_expr) {
            context.error(
                &format!("rel.bindings[{index}].scalarOperators"),
                "formal_scalar_operator_shape_invalid",
                &format!(
                    "Lowering constructed a malformed closed FormalSQL scalar call in a CTE definition: {message}."
                ),
            );
            continue;
        }
        let Some(output_signature) = query_expr_output_signature(&query_expr) else {
            context.error(
                &format!("rel.bindings[{index}].outputScope"),
                "query_binding_output_signature_incomplete",
                "A lowered CTE definition has no complete typed output signature.",
            );
            continue;
        };
        let Some(output_scope) = context
            .scope_from_query_expr(&format!("rel.bindings[{index}].outputScope"), &query_expr)
        else {
            continue;
        };
        let Some(binding_source) = context.query_bindings.get_mut(&binding.id) else {
            continue;
        };
        binding_source.lowered_scope = Some(output_scope);
        lowered_bindings.push(FormalQueryBinding {
            id: binding.id.clone(),
            source_name: binding.source_name.clone(),
            relation: binding_source.relation.clone(),
            output_signature,
            query_expr,
        });
    }
    if lowered_bindings.len() != raw_bindings.len() && !context.has_errors() {
        context.error(
            "rel.bindings",
            "query_binding_lowering_incomplete_without_diagnostic",
            "At least one query-local CTE definition produced no FormalSQL expression without recording a specific rejection.",
        );
    }

    let mut query_expr_lowered = if context.has_errors() {
        None
    } else {
        let body_path = if raw_bindings.is_empty() {
            "rel"
        } else {
            "rel.body"
        };
        lower_query_after_special_roots(&mut context, &body_query, body_path).and_then(
            |query_expr| close_query_root_output(&mut context, body_rel.output(), query_expr),
        )
    };
    if let Some(query_expr) = query_expr_lowered.as_ref()
        && let Err(message) = validate_query_expr_scalar_operators(query_expr)
    {
        context.error(
            "rel.scalarOperators",
            "formal_scalar_operator_shape_invalid",
            &format!(
                "Lowering constructed a malformed closed FormalSQL scalar call: {message}. The query is conservatively blocked rather than emitting a call whose invalid arity could be observed as SQL NULL."
            ),
        );
        query_expr_lowered = None;
    }
    if !context.has_errors() {
        match normalize_bound_analysis_errors(&mut lowered_bindings, &mut query_expr_lowered) {
            BoundAnalysisErrorNormalization::Unchanged
            | BoundAnalysisErrorNormalization::Promoted => {}
            BoundAnalysisErrorNormalization::CompetingCategories => {
                context.error(
                    "rel.analysisErrors",
                    "competing_bound_query_analysis_errors_not_supported",
                    "Query-local and statement-body analysis errors disagree on PostgreSQL's SQLSTATE category. Logos cannot recover the first parse-analysis failure from binding order alone, so lowering is fail-closed.",
                );
                query_expr_lowered = None;
            }
            BoundAnalysisErrorNormalization::MissingOuterSignature => {
                context.error(
                    "rel.outputScope",
                    "analysis_error_output_signature_incomplete",
                    "A query-local analysis error cannot be promoted to the statement root because the authoritative outer output signature is incomplete.",
                );
                query_expr_lowered = None;
            }
        }
    }
    let output_signature = query_expr_lowered.as_ref().and_then(|query_expr| {
        let signature = query_expr_output_signature(query_expr)?;
        // Scope analysis is now an enrichment pass only: it validates and
        // attaches NUMERIC display-scale provenance to this authoritative
        // ordered signature, but cannot independently choose names or types.
        context.scope_from_query_expr("rel.outputScope", query_expr)?;
        Some(signature)
    });
    if query_expr_lowered.is_none() && !context.has_errors() {
        context.error(
            "rel",
            "query_expression_lowering_incomplete_without_diagnostic",
            "Lowering produced no declarative FormalSQL query expression without recording a specific rejection. The statement is conservatively blocked.",
        );
    }
    if query_expr_lowered.is_some() && output_signature.is_none() && !context.has_errors() {
        context.error(
            "rel.outputScope",
            "query_output_signature_incomplete_without_diagnostic",
            "A lowered FormalSQL query expression has no complete typed output signature and no specific rejection diagnostic. The statement is conservatively blocked.",
        );
    }
    let status = if context.has_errors() {
        LoweringStatus::Blocked
    } else {
        LoweringStatus::Lowered
    };
    LoweredQuery {
        status,
        bindings: if context.has_errors() {
            Vec::new()
        } else {
            lowered_bindings
        },
        query_expr: query_expr_lowered,
        output_signature,
        diagnostics: context.diagnostics,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExactSourcePosition {
    line: u32,
    column: u32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ExactSourceSpan {
    start: ExactSourcePosition,
    end: ExactSourcePosition,
}

fn parse_exact_source_span(raw: &str) -> Option<ExactSourceSpan> {
    fn parse_position(raw: &str) -> Option<ExactSourcePosition> {
        let (line, column) = raw.split_once(':')?;
        let position = ExactSourcePosition {
            line: line.parse().ok()?,
            column: column.parse().ok()?,
        };
        (position.line > 0 && position.column > 0).then_some(position)
    }

    let (start, end) = raw.split_once('-')?;
    let span = ExactSourceSpan {
        start: parse_position(start)?,
        end: parse_position(end)?,
    };
    (span.start <= span.end).then_some(span)
}

fn exact_source_fragment_at_span(source: &str, span: ExactSourceSpan) -> Option<&str> {
    let byte_offset = |target: ExactSourcePosition| {
        let mut line = 1u32;
        let mut column = 1u32;
        for (offset, ch) in source.char_indices() {
            if line == target.line && column == target.column {
                return Some(offset);
            }
            if ch == '\n' {
                line = line.checked_add(1)?;
                column = 1;
            } else {
                column = column.checked_add(1)?;
            }
        }
        None
    };
    let start = byte_offset(span.start)?;
    let end_start = byte_offset(span.end)?;
    let end = end_start.checked_add(source.get(end_start..)?.chars().next()?.len_utf8())?;
    source.get(start..end)
}

fn exact_source_span_contains(outer: ExactSourceSpan, inner: ExactSourceSpan) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

/// Calcite 1.42 can end an independently parsed `IN (SELECT ...)`/`EXISTS
/// (SELECT ...)` predicate at the subquery's last token while its separately
/// validated scalar source identity includes the mandatory closing delimiter.
/// Admit only that one-character representation split: the complete scalar
/// must end at a complete parenthesized SELECT query expression, and the raw
/// clause-owner span must be its exact prefix with only the final `)` omitted.
/// Query-expression parsing here is intentionally small but structural: a
/// term is SELECT or a fully parenthesized query expression, and only unquoted
/// UNION/INTERSECT/EXCEPT tokens may connect complete terms. This excludes an
/// ordinary IN-list expression that merely contains a scalar subquery.
fn exact_single_query_predicate_close_completion(text: &str) -> bool {
    fn matching_right_paren(tokens: &[AttestedSqlToken], opening: usize) -> Option<usize> {
        if !matches!(tokens.get(opening), Some(AttestedSqlToken::LeftParen)) {
            return None;
        }
        let mut depth = 0usize;
        for (index, token) in tokens.iter().enumerate().skip(opening) {
            match token {
                AttestedSqlToken::LeftParen => depth = depth.checked_add(1)?,
                AttestedSqlToken::RightParen => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        return Some(index);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn is_set_operator(token: &AttestedSqlToken) -> bool {
        matches!(
            token,
            AttestedSqlToken::Union | AttestedSqlToken::Intersect | AttestedSqlToken::Except
        )
    }

    fn is_select_clause_starter(token: &AttestedSqlToken) -> bool {
        is_set_operator(token)
            || matches!(
                token,
                AttestedSqlToken::Identifier(word)
                    if matches!(
                        word.as_str(),
                        "as" | "from" | "into" | "where" | "group" | "having"
                            | "window" | "order" | "limit" | "offset" | "fetch"
                            | "for" | "with"
                    )
            )
    }

    fn query_term_end(tokens: &[AttestedSqlToken], start: usize) -> Option<usize> {
        match tokens.get(start)? {
            AttestedSqlToken::Select => {
                let mut first_body_token = start.checked_add(1)?;
                let distinct = matches!(
                    tokens.get(first_body_token),
                    Some(AttestedSqlToken::Distinct)
                );
                if distinct || matches!(tokens.get(first_body_token), Some(AttestedSqlToken::All)) {
                    first_body_token = first_body_token.checked_add(1)?;
                }
                if distinct
                    && matches!(
                        tokens.get(first_body_token),
                        Some(AttestedSqlToken::Identifier(word)) if word == "on"
                    )
                {
                    let opening = first_body_token.checked_add(1)?;
                    let close = matching_right_paren(tokens, opening)?;
                    // DISTINCT ON requires at least one expression inside its
                    // parentheses and a target list after the modifier.
                    if close == opening.checked_add(1)? {
                        return None;
                    }
                    first_body_token = close.checked_add(1)?;
                }
                if first_body_token >= tokens.len()
                    || is_select_clause_starter(&tokens[first_body_token])
                    || matches!(
                        tokens[first_body_token],
                        AttestedSqlToken::All | AttestedSqlToken::Distinct
                    )
                {
                    return None;
                }
                let mut depth = 0usize;
                let mut bracket_depth = 0usize;
                for (index, token) in tokens.iter().enumerate().skip(start + 1) {
                    match token {
                        AttestedSqlToken::LeftParen => depth = depth.checked_add(1)?,
                        AttestedSqlToken::RightParen => depth = depth.checked_sub(1)?,
                        AttestedSqlToken::LeftBracket => {
                            bracket_depth = bracket_depth.checked_add(1)?
                        }
                        AttestedSqlToken::RightBracket => {
                            bracket_depth = bracket_depth.checked_sub(1)?
                        }
                        token if bracket_depth > 0 && is_set_operator(token) => return None,
                        token if depth == 0 && bracket_depth == 0 && is_set_operator(token) => {
                            // A set operator cannot itself be the SELECT term's
                            // first token.  Apart from rejecting an empty arm,
                            // this keeps the provenance exception from acting
                            // as a permissive substitute for SQL parsing.
                            return (index > first_body_token).then_some(index);
                        }
                        _ => {}
                    }
                }
                (depth == 0 && bracket_depth == 0).then_some(tokens.len())
            }
            AttestedSqlToken::LeftParen => {
                let close = matching_right_paren(tokens, start)?;
                exact_select_query_expression_tokens(&tokens[start + 1..close]).then_some(close + 1)
            }
            _ => None,
        }
    }

    fn exact_select_query_expression_tokens(tokens: &[AttestedSqlToken]) -> bool {
        let Some(mut position) = query_term_end(tokens, 0) else {
            return false;
        };
        while position < tokens.len() {
            if !is_set_operator(&tokens[position]) {
                return false;
            }
            position += 1;
            if matches!(
                tokens.get(position),
                Some(AttestedSqlToken::All | AttestedSqlToken::Distinct)
            ) {
                position += 1;
            }
            let Some(end) = query_term_end(tokens, position) else {
                return false;
            };
            position = end;
        }
        true
    }

    let Some(tokens) = tokenize_attested_sql(text) else {
        return false;
    };
    if !matches!(tokens.last(), Some(AttestedSqlToken::RightParen)) {
        return false;
    }
    let mut complete_delimiters = Vec::new();
    for token in &tokens {
        match token {
            AttestedSqlToken::LeftParen => complete_delimiters.push(AttestedSqlToken::LeftParen),
            AttestedSqlToken::LeftBracket => {
                complete_delimiters.push(AttestedSqlToken::LeftBracket)
            }
            AttestedSqlToken::RightParen
                if complete_delimiters.pop() != Some(AttestedSqlToken::LeftParen) =>
            {
                return false;
            }
            AttestedSqlToken::RightBracket
                if complete_delimiters.pop() != Some(AttestedSqlToken::LeftBracket) =>
            {
                return false;
            }
            _ => {}
        }
    }
    if !complete_delimiters.is_empty() {
        return false;
    }
    let mut depth = 0usize;
    let mut opening = None;
    for (index, token) in tokens.iter().enumerate().rev() {
        match token {
            AttestedSqlToken::RightParen => depth = depth.saturating_add(1),
            AttestedSqlToken::LeftParen => {
                let Some(next_depth) = depth.checked_sub(1) else {
                    return false;
                };
                depth = next_depth;
                if depth == 0 {
                    opening = Some(index);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(opening) = opening else {
        return false;
    };
    let predicate = opening.wrapping_sub(1);
    let query_predicate = matches!(
        tokens.get(predicate),
        Some(AttestedSqlToken::In | AttestedSqlToken::Exists)
    )
        // PostgreSQL permits keywords after a qualification dot.  Such a
        // token is a qualified name component, not an IN/EXISTS predicate.
        && !matches!(
            tokens.get(predicate.wrapping_sub(1)),
            Some(AttestedSqlToken::Dot)
        );
    query_predicate && exact_select_query_expression_tokens(&tokens[opening + 1..tokens.len() - 1])
}

fn validate_scalar_clause_ownership_binding(
    source: &ScalarSourceProvenance,
    statement: Option<&str>,
    ownership: &ScalarSourceClauseOwnership,
    path: &str,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    let statement = statement.ok_or_else(|| {
        format!("{path} carries exact source provenance but the query has no sourceSql")
    })?;
    let query_block = parse_exact_source_span(&ownership.query_block_id).ok_or_else(|| {
        format!(
            "{path} has malformed query-block node ID {:?}",
            ownership.query_block_id
        )
    })?;
    if exact_source_fragment_at_span(statement, query_block).is_none() {
        return Err(format!(
            "{path} query-block node ID escapes query sourceSql"
        ));
    }
    let ownership_span = parse_exact_source_span(&ownership.source_node_id).ok_or_else(|| {
        format!(
            "{path} has malformed exact source node ID {:?}",
            ownership.source_node_id
        )
    })?;
    if !exact_source_span_contains(query_block, ownership_span) {
        return Err(format!(
            "{path} exact source node ID lies outside its query block"
        ));
    }
    let scalar_span = source
        .node_id
        .as_deref()
        .and_then(parse_exact_source_span)
        .ok_or_else(|| format!("{path} does not own an exact scalar-root source node"))?;
    let scalar_text = source
        .text
        .as_deref()
        .ok_or_else(|| format!("{path} does not own exact scalar-root source text"))?;
    if !exact_source_span_contains(query_block, scalar_span) {
        return Err(format!(
            "{path} scalar-root source node lies outside its query block"
        ));
    }

    let direct = validate_exact_source_pair(
        Some(statement),
        Some(&ownership.source_node_id),
        Some(&ownership.source_sql),
        path,
        allow_synthetic_test_bindings,
    );
    if direct.is_ok() {
        if ownership.source_node_id == source.node_id.as_deref().unwrap_or_default()
            && ownership.source_sql == scalar_text
        {
            return Ok(());
        }
        return Err(format!(
            "{path} exact source binding does not own the complete scalar root"
        ));
    }

    let exact_owner = exact_source_fragment_at_span(statement, ownership_span);
    let exact_scalar = exact_source_fragment_at_span(statement, scalar_span);
    let one_query_close = ownership_span.start == scalar_span.start
        && ownership_span.end < scalar_span.end
        && ownership.source_sql == scalar_text
        && exact_scalar == Some(scalar_text)
        && exact_owner
            .zip(exact_scalar)
            .is_some_and(|(owner, scalar)| scalar.strip_prefix(owner) == Some(")"))
        && exact_single_query_predicate_close_completion(scalar_text);
    if one_query_close { Ok(()) } else { direct }
}

fn validate_exact_source_pair(
    statement: Option<&str>,
    node_id: Option<&str>,
    text: Option<&str>,
    path: &str,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    match (node_id, text) {
        (None, None) => Ok(()),
        (Some(node_id), Some(text)) => {
            if node_id.is_empty() || text.is_empty() {
                return Err(format!(
                    "{path} has an empty exact source node ID or text fragment"
                ));
            }
            if allow_synthetic_test_bindings && node_id.starts_with("test:") {
                return Ok(());
            }
            let statement = statement.ok_or_else(|| {
                format!("{path} carries exact source provenance but the query has no sourceSql")
            })?;
            let span = parse_exact_source_span(node_id)
                .ok_or_else(|| format!("{path} has malformed exact source node ID {node_id:?}"))?;
            let actual = exact_source_fragment_at_span(statement, span).ok_or_else(|| {
                format!("{path} exact source node ID {node_id:?} escapes query sourceSql")
            })?;
            if actual != text {
                return Err(format!(
                    "{path} exact source text does not match node ID {node_id:?} in query sourceSql"
                ));
            }
            Ok(())
        }
        _ => Err(format!(
            "{path} must carry exact source node ID and text together"
        )),
    }
}

fn validate_scalar_source_binding_tree(
    source: &ScalarSourceProvenance,
    statement: Option<&str>,
    path: &str,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    validate_exact_source_pair(
        statement,
        source.node_id.as_deref(),
        source.text.as_deref(),
        path,
        allow_synthetic_test_bindings,
    )?;
    let synthetic = allow_synthetic_test_bindings
        && source
            .node_id
            .as_deref()
            .is_some_and(|node_id| node_id.starts_with("test:"));
    if !synthetic && let Some(ownership) = source.clause_ownership.as_ref() {
        validate_scalar_clause_ownership_binding(
            source,
            statement,
            ownership,
            &format!("{path}.clauseOwnership"),
            allow_synthetic_test_bindings,
        )?;
    }
    for (index, operand) in source.operands.iter().enumerate() {
        if let Some(operand) = operand {
            validate_scalar_source_binding_tree(
                operand,
                statement,
                &format!("{path}.operands[{index}]"),
                allow_synthetic_test_bindings,
            )?;
        }
    }
    Ok(())
}

fn validate_scalar_expr_source_bindings(
    expr: &ScalarExpr,
    statement: Option<&str>,
    path: &str,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    if let Some(source) = expr.source.as_ref() {
        validate_scalar_source_binding_tree(
            source,
            statement,
            &format!("{path}.source"),
            allow_synthetic_test_bindings,
        )?;
    }
    validate_scalar_ast_subquery_source_bindings(
        &expr.parsed,
        statement,
        &format!("{path}.parsed"),
        allow_synthetic_test_bindings,
    )
}

fn validate_scalar_ast_subquery_source_bindings(
    ast: &ScalarAst,
    statement: Option<&str>,
    path: &str,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    match ast {
        ScalarAst::Call { args, .. } => {
            for (index, arg) in args.iter().enumerate() {
                validate_scalar_ast_subquery_source_bindings(
                    arg,
                    statement,
                    &format!("{path}.args[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
        }
        ScalarAst::TypeAnnotation { expr, .. } => validate_scalar_ast_subquery_source_bindings(
            expr,
            statement,
            &format!("{path}.expr"),
            allow_synthetic_test_bindings,
        )?,
        ScalarAst::RelSubquery { rel } => validate_rel_scalar_source_bindings(
            rel,
            statement,
            &format!("{path}.rel"),
            allow_synthetic_test_bindings,
        )?,
        ScalarAst::Window { parsed } => {
            for (index, arg) in parsed.args.iter().enumerate() {
                validate_scalar_ast_subquery_source_bindings(
                    arg,
                    statement,
                    &format!("{path}.args[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
            for (index, arg) in parsed.partition_by.iter().enumerate() {
                validate_scalar_ast_subquery_source_bindings(
                    arg,
                    statement,
                    &format!("{path}.partitionBy[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
            for (index, key) in parsed.order_by.iter().enumerate() {
                validate_scalar_ast_subquery_source_bindings(
                    &key.expr,
                    statement,
                    &format!("{path}.orderBy[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
            if let Some(frame) = parsed.frame.as_ref() {
                for (index, offset) in frame.offset_exprs().enumerate() {
                    validate_scalar_ast_subquery_source_bindings(
                        offset,
                        statement,
                        &format!("{path}.frameOffsets[{index}]"),
                        allow_synthetic_test_bindings,
                    )?;
                }
            }
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => {}
    }
    Ok(())
}

fn validate_rel_scalar_source_bindings(
    rel: &RelExpr,
    statement: Option<&str>,
    path: &str,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            for (index, binding) in bindings.iter().enumerate() {
                validate_rel_scalar_source_bindings(
                    &binding.rel,
                    statement,
                    &format!("{path}.bindings[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
            validate_rel_scalar_source_bindings(
                body,
                statement,
                &format!("{path}.body"),
                allow_synthetic_test_bindings,
            )?;
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => {}
        RelExpr::Project { input, exprs, .. } => {
            validate_rel_scalar_source_bindings(
                input,
                statement,
                &format!("{path}.input"),
                allow_synthetic_test_bindings,
            )?;
            for (index, expr) in exprs.iter().enumerate() {
                validate_scalar_expr_source_bindings(
                    expr,
                    statement,
                    &format!("{path}.exprs[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            validate_rel_scalar_source_bindings(
                input,
                statement,
                &format!("{path}.input"),
                allow_synthetic_test_bindings,
            )?;
            validate_scalar_expr_source_bindings(
                predicate,
                statement,
                &format!("{path}.predicate"),
                allow_synthetic_test_bindings,
            )?;
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            validate_rel_scalar_source_bindings(
                left,
                statement,
                &format!("{path}.left"),
                allow_synthetic_test_bindings,
            )?;
            validate_rel_scalar_source_bindings(
                right,
                statement,
                &format!("{path}.right"),
                allow_synthetic_test_bindings,
            )?;
            validate_scalar_expr_source_bindings(
                condition,
                statement,
                &format!("{path}.condition"),
                allow_synthetic_test_bindings,
            )?;
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            validate_rel_scalar_source_bindings(
                input,
                statement,
                &format!("{path}.input"),
                allow_synthetic_test_bindings,
            )?;
            for (call_index, call) in agg_calls.iter().enumerate() {
                if let Some(source) = call.modifiers.source.as_ref() {
                    validate_scalar_source_binding_tree(
                        source,
                        statement,
                        &format!("{path}.aggCalls[{call_index}].source"),
                        allow_synthetic_test_bindings,
                    )?;
                }
                for (arg_index, arg) in call.args.iter().enumerate() {
                    validate_scalar_expr_source_bindings(
                        arg,
                        statement,
                        &format!("{path}.aggCalls[{call_index}].args[{arg_index}]"),
                        allow_synthetic_test_bindings,
                    )?;
                }
                if let Some(filter) = call.filter.as_ref() {
                    validate_scalar_expr_source_bindings(
                        filter,
                        statement,
                        &format!("{path}.aggCalls[{call_index}].filter"),
                        allow_synthetic_test_bindings,
                    )?;
                }
            }
        }
        RelExpr::Distinct { input, .. } => {
            validate_rel_scalar_source_bindings(
                input,
                statement,
                &format!("{path}.input"),
                allow_synthetic_test_bindings,
            )?;
        }
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            validate_rel_scalar_source_bindings(
                input,
                statement,
                &format!("{path}.input"),
                allow_synthetic_test_bindings,
            )?;
            if let Some(fetch) = fetch.as_ref() {
                validate_scalar_expr_source_bindings(
                    fetch,
                    statement,
                    &format!("{path}.fetch"),
                    allow_synthetic_test_bindings,
                )?;
            }
            if let Some(offset) = offset.as_deref() {
                validate_scalar_expr_source_bindings(
                    offset,
                    statement,
                    &format!("{path}.offset"),
                    allow_synthetic_test_bindings,
                )?;
            }
        }
        RelExpr::Set { inputs, .. } => {
            for (index, input) in inputs.iter().enumerate() {
                validate_rel_scalar_source_bindings(
                    input,
                    statement,
                    &format!("{path}.inputs[{index}]"),
                    allow_synthetic_test_bindings,
                )?;
            }
        }
        RelExpr::Values { rows, .. } => {
            for (row_index, row) in rows.iter().enumerate() {
                for (column_index, value) in row.iter().enumerate() {
                    validate_scalar_expr_source_bindings(
                        value,
                        statement,
                        &format!("{path}.rows[{row_index}][{column_index}]"),
                        allow_synthetic_test_bindings,
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn validate_query_scalar_source_bindings(
    query: &Query,
    allow_synthetic_test_bindings: bool,
) -> Result<(), String> {
    if allow_synthetic_test_bindings && query.source_sql.is_none() {
        return Ok(());
    }
    validate_rel_scalar_source_bindings(
        &query.rel,
        query.source_sql.as_deref(),
        "rel",
        allow_synthetic_test_bindings,
    )
}

fn close_query_root_output(
    context: &mut LoweringContext,
    expected: &[Column],
    query: FormalQueryExpr,
) -> Option<FormalQueryExpr> {
    let scope = context.scope_from_query_expr("rel.rootOutput", &query)?;
    let visible_matches = scope.attributes.len() >= expected.len()
        && scope.attributes[..expected.len()]
            .iter()
            .zip(expected)
            .all(|(attribute, expected)| attribute.visible_name == expected.name);
    let has_auxiliaries = scope.attributes.len() > expected.len();
    if !visible_matches
        || (has_auxiliaries && !scope_has_well_formed_auxiliary_dscales(&scope, expected.len()))
    {
        context.error(
            "rel.rootOutput",
            "query_root_output_shape_mismatch",
            "The lowered root must expose exactly the SQL-visible output prefix plus only well-formed hidden runtime display-scale attributes.",
        );
        return None;
    }
    let has_dynamic_scale = scope.attributes[..expected.len()].iter().any(|attribute| {
        matches!(
            attribute.numeric_dscale,
            Some(NumericDscaleProvenance::Attribute(_))
        )
    });
    let needs_public_name_restore = scope.attributes[..expected.len()]
        .iter()
        .zip(expected)
        .any(|(attribute, expected)| attribute.name != expected.name);
    if !has_auxiliaries && !has_dynamic_scale && !needs_public_name_restore {
        return Some(query);
    }
    let select = scope.attributes[..expected.len()]
        .iter()
        .zip(expected)
        .map(|(attribute, expected)| FormalScalarSelectItem {
            expr: FormalScalarExpr::Leaf {
                result_ty: attribute.formal_ty,
                term: FormalAggregateTerm::Expr {
                    term: FormalFunctionTerm::Attribute {
                        name: attribute.name.clone(),
                        ty: attribute.formal_ty,
                    },
                },
            },
            alias: expected.name.clone(),
            alias_ty: attribute.formal_ty,
            // No SQL expression can consume a hidden scale beyond the query
            // boundary. The value remains exact; only internal scale liveness
            // ends here.
            numeric_dscale: None,
        })
        .collect();
    Some(FormalQueryExpr::Projection {
        select,
        input: Box::new(query),
    })
}

fn lower_query_analysis_error(
    context: &mut LoweringContext,
    output: &[Column],
    error: FormalQueryError,
) -> Option<FormalQueryExpr> {
    let columns = output
        .iter()
        .enumerate()
        .map(|(index, column)| {
            Some(FormalAttribute {
                name: column.name.clone(),
                ty: context.lower_attribute_type(
                    &format!("rel.analysisErrorOutput[{index}]"),
                    column,
                    AttributeTypeContext::QueryOutput,
                )?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(FormalQueryExpr::Error { columns, error })
}

fn lower_query_after_special_roots(
    context: &mut LoweringContext,
    query: &Query,
    root_path: &str,
) -> Option<FormalQueryExpr> {
    let query_analysis_errors = query.analysis_errors.as_slice();
    if query_analysis_errors.len() > 1 {
        context.error(
            "rel",
            "multiple_query_analysis_errors_not_supported",
            "The source frontend reported multiple query-level analysis errors. Logos cannot choose PostgreSQL's first parse-analysis failure without a complete source-order error trace, so lowering is fail-closed.",
        );
        return None;
    }
    if let Some(QueryAnalysisError::PostgresAmbiguousDerivedOutputColumn {
        sql_state,
        query_block_id,
        source_identifier_node_id,
        source_identifier_sql,
        source_relation_node_id,
        source_relation_sql,
        identifier_name,
        duplicate_count,
        matching_outputs,
        ..
    }) = query_analysis_errors.first()
    {
        let outputs_are_closed = *duplicate_count == matching_outputs.len()
            && *duplicate_count >= 2
            && matching_outputs
                .iter()
                .enumerate()
                .all(|(position, output)| {
                    output.output_name == *identifier_name
                        && !output.source_output_item_node_id.is_empty()
                        && !output.source_output_item_sql.is_empty()
                        && !output.source_origin_relation_node_id.is_empty()
                        && !output.source_origin_relation_sql.is_empty()
                        && (position == 0
                            || matching_outputs[position - 1].output_index < output.output_index)
                });
        if sql_state != "42702"
            || query.source_sql.as_deref().is_none_or(str::is_empty)
            || query_block_id.is_empty()
            || source_identifier_node_id.is_empty()
            || source_identifier_sql.is_empty()
            || source_relation_node_id.is_empty()
            || source_relation_sql.is_empty()
            || identifier_name.is_empty()
            || !outputs_are_closed
        {
            context.error(
                "rel",
                "query_analysis_error_provenance_invalid",
                "The query-level PostgreSQL ambiguous-column marker is incomplete, has the wrong SQLSTATE, or disagrees with its exact duplicate-output evidence. The frontend translation is fail-closed.",
            );
            return None;
        }
        let mut competing_local_errors = Vec::new();
        collect_rel_analysis_errors(&query.rel, &mut competing_local_errors);
        if rel_generated_invalid_int4_unknown_literal_count(&query.rel) != 0
            || rel_source_attested_invalid_int4_unknown_literal_count(&query.rel) != 0
            || rel_unaccounted_string_literal_cast_count(&query.rel) != 0
            || query_source_analysis_error_marker_count(query) != 0
            || query_boolean_integer_source_mismatch_count(query) != 0
            || query_source_invented_numeric_cast_count(query) != 0
            || !competing_local_errors.is_empty()
        {
            context.error(
                "rel",
                "query_analysis_error_competition_not_supported",
                "The attested ambiguous-column error coexists with another conversion or operator-resolution error candidate. Logos has no complete source-order error trace from which to choose PostgreSQL's first SQLSTATE, so lowering is fail-closed.",
            );
            return None;
        }
        return context
            .validate_all_table_scans_against_schema("rel.analysisErrorScans", &query.rel)
            .and_then(|()| {
                lower_query_analysis_error(
                    context,
                    query.rel.output(),
                    FormalQueryError::AmbiguousColumn,
                )
            });
    }
    let order_by_alias_error = query_analysis_errors.first();
    if let Some(QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
        sql_state,
        query_block_id,
        source_order_item_node_id,
        source_order_item_sql,
        output_alias,
    }) = order_by_alias_error
    {
        if sql_state != "42703"
            || query.source_sql.as_deref().is_none_or(str::is_empty)
            || query_block_id.is_empty()
            || source_order_item_node_id.is_empty()
            || source_order_item_sql.is_empty()
            || output_alias.is_empty()
        {
            context.error(
                "rel",
                "query_analysis_error_provenance_invalid",
                "The query-level PostgreSQL ORDER BY alias marker is incomplete, has the wrong SQLSTATE, or disagrees with the converted root output. The frontend translation is fail-closed.",
            );
            return None;
        }
        let mut competing_local_errors = Vec::new();
        collect_rel_analysis_errors(&query.rel, &mut competing_local_errors);
        if rel_generated_invalid_int4_unknown_literal_count(&query.rel) != 0
            || rel_source_attested_invalid_int4_unknown_literal_count(&query.rel) != 0
            || rel_unaccounted_string_literal_cast_count(&query.rel) != 0
            || query_source_analysis_error_marker_count(query) != 0
            || query_boolean_integer_source_mismatch_count(query) != 0
            || query_source_invented_numeric_cast_count(query) != 0
            || !competing_local_errors.is_empty()
        {
            context.error(
                "rel",
                "query_analysis_error_competition_not_supported",
                "The attested ORDER BY alias error coexists with another conversion or operator-resolution error candidate. Logos has no complete source-order error trace from which to choose PostgreSQL's first SQLSTATE, so lowering is fail-closed.",
            );
            return None;
        }
        return context
            .validate_all_table_scans_against_schema("rel.analysisErrorScans", &query.rel)
            .and_then(|()| {
                lower_query_analysis_error(
                    context,
                    query.rel.output(),
                    FormalQueryError::UndefinedColumn,
                )
            });
    }
    lower_query_after_query_level_analysis_error(context, query, root_path)
}

fn lower_query_after_query_level_analysis_error(
    context: &mut LoweringContext,
    query: &Query,
    root_path: &str,
) -> Option<FormalQueryExpr> {
    let generated_invalid_int4 = rel_generated_invalid_int4_unknown_literal_count(&query.rel);
    let attested_invalid_int4 = rel_source_attested_invalid_int4_unknown_literal_count(&query.rel);
    let invented_numeric_casts = query_source_invented_numeric_cast_count(query);
    let attested_invented_operator_errors =
        query_attested_source_invented_numeric_operator_error_count(query);
    if invented_numeric_casts != attested_invented_operator_errors {
        context.error(
            "rel",
            "source_invented_numeric_cast_analysis_error_not_attested",
            "Calcite IR contains a numeric cast around a PostgreSQL string/unknown relation output that is not consumed one-for-one by an exact source operator-resolution error. Lowering is fail-closed rather than executing Calcite's invented cast.",
        );
        return None;
    }
    if generated_invalid_int4 != attested_invalid_int4 {
        context.error(
            "rel",
            "invalid_int4_unknown_literal_analysis_error_not_attested",
            "Calcite IR contains an INTEGER cast around a definitely invalid string literal without an exact positional binding to that same independently parsed source literal. The query-wide PostgreSQL input error is fail-closed.",
        );
        return None;
    }
    if attested_invalid_int4 != 0 {
        let mut competing_local_errors = Vec::new();
        collect_rel_analysis_errors(&query.rel, &mut competing_local_errors);
        if rel_unaccounted_string_literal_cast_count(&query.rel) != attested_invalid_int4
            || query_source_analysis_error_marker_count(query) != 0
            || query_boolean_integer_source_mismatch_count(query) != 0
            || invented_numeric_casts != 0
            || !competing_local_errors.is_empty()
        {
            context.error(
                "rel",
                "query_analysis_error_competition_not_supported",
                "An attested invalid INT4 input conversion coexists with another string-literal conversion, source marker, or operator-resolution error candidate. Logos cannot choose PostgreSQL's first parse-analysis SQLSTATE from the normalized tree, so lowering is fail-closed.",
            );
            return None;
        }
        return context
            .validate_all_table_scans_against_schema("rel.analysisErrorScans", &query.rel)
            .and_then(|()| {
                lower_query_analysis_error(
                    context,
                    query.rel.output(),
                    FormalQueryError::InvalidTextRepresentation,
                )
            });
    }

    let analysis_error = attested_postgres_query_analysis_error(query);
    match analysis_error {
        Some(_) if rel_unaccounted_string_literal_cast_count(&query.rel) != 0 => {
            context.error(
                "rel",
                "query_analysis_error_unaccounted_string_literal_cast",
                "A local PostgreSQL analysis-error recognizer matched, but the complete typed query also contains a string-literal cast whose target input routine and source-order SQLSTATE are not accounted for by that recognizer. Generic query-wide error lowering is fail-closed.",
            );
            None
        }
        Some(error) => lower_query_analysis_error(context, query.rel.output(), error),
        None if query_source_analysis_error_marker_count(query) != 0
            || query_boolean_integer_source_mismatch_count(query) != 0
            || invented_numeric_casts != 0 =>
        {
            context.error(
                "rel",
                "source_analysis_error_attestation_drift",
                "A converter-validated PostgreSQL analysis-error marker was not consumed by the exact typed relation, scalar, source-provenance, and base-column recognizer. It is fail-closed and cannot fall through to Calcite's coerced executable expression.",
            );
            None
        }
        None => {
            // Preserve the more specific lowering diagnostic when the scalar
            // vocabulary itself is unsupported. The planner-demand check is
            // an additional phase distinction on otherwise modeled queries,
            // not a replacement for their ordinary admission rules.
            let lowered = context.lower_query_expr(root_path, &query.rel)?;
            if scalar::rel_expr_contains_any_closed_immutable_error(&query.rel) {
                context.error(
                    "rel.plannerConstants",
                    "boolean_planner_constant_error_not_supported",
                    "PostgreSQL may evaluate a closed immutable scalar subexpression while planning before executor row demand, laziness, or error order is known. FormalSQL models execution-time scheduling rather than planner evaluation, so the complete query is conservatively unsupported.",
                );
                None
            } else {
                Some(lowered)
            }
        }
    }
}

/// PostgreSQL resolves operators and aggregate overloads before executing a
/// query. Calcite sometimes accepts a different overload and records an
/// inserted cast. This recognizer therefore requires two independent pieces
/// of evidence before producing an always-error query: a closed typed IR
/// shape and an exact, positional association between that same Rex node and
/// its independently parsed source-AST node. Query-wide text search is
/// intentionally forbidden here: it can confuse equal-looking identifiers
/// across lexical scopes. Everything unmatched remains unsupported instead
/// of treating Calcite's cast as PostgreSQL semantics.
fn attested_postgres_query_analysis_error(query: &Query) -> Option<FormalQueryError> {
    query.source_sql.as_deref()?;
    let marker_count = query_source_analysis_error_marker_count(query);
    if marker_count != query_boolean_integer_source_mismatch_count(query) {
        return None;
    }
    if query_source_invented_numeric_cast_count(query)
        != query_attested_source_invented_numeric_operator_error_count(query)
    {
        return None;
    }
    let mut errors = Vec::new();
    let consumed_markers = collect_rel_source_analysis_errors(&query.rel, &mut errors);
    if consumed_markers != marker_count {
        return None;
    }
    collect_rel_analysis_errors(&query.rel, &mut errors);
    let first = *errors.first()?;
    errors.iter().all(|error| *error == first).then_some(first)
}

fn query_source_analysis_error_marker_count(query: &Query) -> usize {
    rel_source_analysis_error_marker_count(&query.rel)
}

fn query_boolean_integer_source_mismatch_count(query: &Query) -> usize {
    rel_boolean_integer_source_mismatch_count(&query.rel)
}

fn rel_boolean_integer_source_mismatch_count(rel: &RelExpr) -> usize {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            bindings
                .iter()
                .map(|binding| rel_boolean_integer_source_mismatch_count(&binding.rel))
                .sum::<usize>()
                + rel_boolean_integer_source_mismatch_count(body)
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => 0,
        RelExpr::Project { input, exprs, .. } => {
            rel_boolean_integer_source_mismatch_count(input)
                + exprs
                    .iter()
                    .map(scalar_boolean_integer_source_mismatch_count)
                    .sum::<usize>()
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            rel_boolean_integer_source_mismatch_count(input)
                + scalar_boolean_integer_source_mismatch_count(predicate)
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            rel_boolean_integer_source_mismatch_count(left)
                + rel_boolean_integer_source_mismatch_count(right)
                + scalar_boolean_integer_source_mismatch_count(condition)
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            rel_boolean_integer_source_mismatch_count(input)
                + agg_calls
                    .iter()
                    .map(|call| {
                        call.args
                            .iter()
                            .map(scalar_boolean_integer_source_mismatch_count)
                            .sum::<usize>()
                            + call
                                .filter
                                .as_ref()
                                .map_or(0, scalar_boolean_integer_source_mismatch_count)
                    })
                    .sum::<usize>()
        }
        RelExpr::Distinct { input, .. } => rel_boolean_integer_source_mismatch_count(input),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            rel_boolean_integer_source_mismatch_count(input)
                + fetch
                    .as_ref()
                    .map_or(0, scalar_boolean_integer_source_mismatch_count)
                + offset
                    .as_deref()
                    .map_or(0, scalar_boolean_integer_source_mismatch_count)
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .map(rel_boolean_integer_source_mismatch_count)
            .sum(),
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .map(scalar_boolean_integer_source_mismatch_count)
            .sum(),
    }
}

fn scalar_boolean_integer_source_mismatch_count(expr: &ScalarExpr) -> usize {
    scalar_ast_boolean_integer_source_mismatch_count(&expr.parsed, expr.source.as_ref())
}

fn scalar_ast_boolean_integer_source_mismatch_count(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
) -> usize {
    let current = usize::from(
        exact_typed_boolean_literal(ast).is_some()
            && source.is_some_and(|source| {
                source_is_bare_integer_literal(source, "0")
                    || source_is_bare_integer_literal(source, "1")
            }),
    );
    current
        + match ast {
            ScalarAst::Call { args, .. } => args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    scalar_ast_boolean_integer_source_mismatch_count(
                        arg,
                        source_operand(source, index),
                    )
                })
                .sum(),
            ScalarAst::TypeAnnotation { expr, .. } => {
                scalar_ast_boolean_integer_source_mismatch_count(expr, source)
            }
            ScalarAst::RelSubquery { rel } => rel_boolean_integer_source_mismatch_count(rel),
            ScalarAst::Window { parsed } => {
                parsed
                    .args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        scalar_ast_boolean_integer_source_mismatch_count(
                            arg,
                            source_operand(source, index),
                        )
                    })
                    .sum::<usize>()
                    + parsed
                        .partition_by
                        .iter()
                        .map(|arg| scalar_ast_boolean_integer_source_mismatch_count(arg, None))
                        .sum::<usize>()
                    + parsed
                        .order_by
                        .iter()
                        .map(|key| {
                            scalar_ast_boolean_integer_source_mismatch_count(&key.expr, None)
                        })
                        .sum::<usize>()
                    + parsed.frame.as_ref().map_or(0, |frame| {
                        frame
                            .offset_exprs()
                            .map(|offset| {
                                scalar_ast_boolean_integer_source_mismatch_count(offset, None)
                            })
                            .sum()
                    })
            }
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. } => 0,
        }
}

fn rel_source_analysis_error_marker_count(rel: &RelExpr) -> usize {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            bindings
                .iter()
                .map(|binding| rel_source_analysis_error_marker_count(&binding.rel))
                .sum::<usize>()
                + rel_source_analysis_error_marker_count(body)
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => 0,
        RelExpr::Project { input, exprs, .. } => {
            rel_source_analysis_error_marker_count(input)
                + exprs
                    .iter()
                    .map(scalar_source_analysis_error_marker_count)
                    .sum::<usize>()
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            rel_source_analysis_error_marker_count(input)
                + scalar_source_analysis_error_marker_count(predicate)
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            rel_source_analysis_error_marker_count(left)
                + rel_source_analysis_error_marker_count(right)
                + scalar_source_analysis_error_marker_count(condition)
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            rel_source_analysis_error_marker_count(input)
                + agg_calls
                    .iter()
                    .map(|call| {
                        call.args
                            .iter()
                            .map(scalar_source_analysis_error_marker_count)
                            .sum::<usize>()
                            + call
                                .filter
                                .as_ref()
                                .map_or(0, scalar_source_analysis_error_marker_count)
                    })
                    .sum::<usize>()
        }
        RelExpr::Distinct { input, .. } => rel_source_analysis_error_marker_count(input),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            rel_source_analysis_error_marker_count(input)
                + fetch
                    .as_ref()
                    .map_or(0, scalar_source_analysis_error_marker_count)
                + offset
                    .as_deref()
                    .map_or(0, scalar_source_analysis_error_marker_count)
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .map(rel_source_analysis_error_marker_count)
            .sum(),
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .map(scalar_source_analysis_error_marker_count)
            .sum(),
    }
}

fn scalar_source_analysis_error_marker_count(expr: &ScalarExpr) -> usize {
    expr.source
        .as_ref()
        .and_then(|source| source.clause_ownership.as_ref())
        .map_or(0, |ownership| ownership.analysis_errors.len())
        + scalar_ast_nested_analysis_error_marker_count(&expr.parsed)
}

fn scalar_ast_nested_analysis_error_marker_count(ast: &ScalarAst) -> usize {
    match ast {
        ScalarAst::Call { args, .. } => args
            .iter()
            .map(scalar_ast_nested_analysis_error_marker_count)
            .sum(),
        ScalarAst::TypeAnnotation { expr, .. } => {
            scalar_ast_nested_analysis_error_marker_count(expr)
        }
        ScalarAst::RelSubquery { rel } => rel_source_analysis_error_marker_count(rel),
        ScalarAst::Window { parsed } => {
            parsed
                .args
                .iter()
                .chain(&parsed.partition_by)
                .map(scalar_ast_nested_analysis_error_marker_count)
                .sum::<usize>()
                + parsed
                    .order_by
                    .iter()
                    .map(|key| scalar_ast_nested_analysis_error_marker_count(&key.expr))
                    .sum::<usize>()
                + parsed.frame.as_ref().map_or(0, |frame| {
                    frame
                        .offset_exprs()
                        .map(scalar_ast_nested_analysis_error_marker_count)
                        .sum()
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => 0,
    }
}

fn collect_rel_source_analysis_errors(rel: &RelExpr, errors: &mut Vec<FormalQueryError>) -> usize {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            bindings
                .iter()
                .map(|binding| collect_rel_source_analysis_errors(&binding.rel, errors))
                .sum::<usize>()
                + collect_rel_source_analysis_errors(body, errors)
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => 0,
        RelExpr::Project { input, exprs, .. } => {
            collect_rel_source_analysis_errors(input, errors)
                + exprs
                    .iter()
                    .map(|expr| collect_ast_nested_source_analysis_errors(&expr.parsed, errors))
                    .sum::<usize>()
        }
        RelExpr::Filter {
            input, predicate, ..
        } => {
            collect_filter_source_analysis_errors(input, predicate, errors)
                + collect_ast_nested_source_analysis_errors(&predicate.parsed, errors)
                + collect_rel_source_analysis_errors(input, errors)
        }
        RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            collect_ast_nested_source_analysis_errors(&predicate.parsed, errors)
                + collect_rel_source_analysis_errors(input, errors)
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            collect_ast_nested_source_analysis_errors(&condition.parsed, errors)
                + collect_rel_source_analysis_errors(left, errors)
                + collect_rel_source_analysis_errors(right, errors)
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            collect_rel_source_analysis_errors(input, errors)
                + agg_calls
                    .iter()
                    .map(|call| {
                        call.args
                            .iter()
                            .map(|arg| {
                                collect_ast_nested_source_analysis_errors(&arg.parsed, errors)
                            })
                            .sum::<usize>()
                            + call.filter.as_ref().map_or(0, |filter| {
                                collect_ast_nested_source_analysis_errors(&filter.parsed, errors)
                            })
                    })
                    .sum::<usize>()
        }
        RelExpr::Distinct { input, .. } => collect_rel_source_analysis_errors(input, errors),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            collect_rel_source_analysis_errors(input, errors)
                + fetch.as_ref().map_or(0, |fetch| {
                    collect_ast_nested_source_analysis_errors(&fetch.parsed, errors)
                })
                + offset.as_deref().map_or(0, |offset| {
                    collect_ast_nested_source_analysis_errors(&offset.parsed, errors)
                })
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .map(|input| collect_rel_source_analysis_errors(input, errors))
            .sum(),
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .map(|value| collect_ast_nested_source_analysis_errors(&value.parsed, errors))
            .sum(),
    }
}

fn collect_ast_nested_source_analysis_errors(
    ast: &ScalarAst,
    errors: &mut Vec<FormalQueryError>,
) -> usize {
    match ast {
        ScalarAst::Call { args, .. } => args
            .iter()
            .map(|arg| collect_ast_nested_source_analysis_errors(arg, errors))
            .sum(),
        ScalarAst::TypeAnnotation { expr, .. } => {
            collect_ast_nested_source_analysis_errors(expr, errors)
        }
        ScalarAst::RelSubquery { rel } => collect_rel_source_analysis_errors(rel, errors),
        ScalarAst::Window { parsed } => {
            parsed
                .args
                .iter()
                .chain(&parsed.partition_by)
                .map(|arg| collect_ast_nested_source_analysis_errors(arg, errors))
                .sum::<usize>()
                + parsed
                    .order_by
                    .iter()
                    .map(|key| collect_ast_nested_source_analysis_errors(&key.expr, errors))
                    .sum::<usize>()
                + parsed.frame.as_ref().map_or(0, |frame| {
                    frame
                        .offset_exprs()
                        .map(|offset| collect_ast_nested_source_analysis_errors(offset, errors))
                        .sum()
                })
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => 0,
    }
}

fn collect_filter_source_analysis_errors(
    input: &RelExpr,
    predicate: &ScalarExpr,
    errors: &mut Vec<FormalQueryError>,
) -> usize {
    let Some(ownership) = predicate
        .source
        .as_ref()
        .and_then(|source| source.clause_ownership.as_ref())
    else {
        return 0;
    };
    if !ordinary_source_where_ownership(ownership) {
        return 0;
    }
    let mut paths = BTreeSet::new();
    if ownership.analysis_errors.iter().any(|marker| {
        let SourceAnalysisErrorProvenance::PostgresBooleanIntegerEqualityUndefinedFunction {
            rex_path,
            ..
        } = marker;
        !paths.insert(rex_path.as_str())
    }) {
        return 0;
    }
    ownership
        .analysis_errors
        .iter()
        .filter(|marker| {
            attested_postgres_boolean_integer_equality_undefined_function(input, predicate, marker)
        })
        .map(|_| {
            errors.push(FormalQueryError::UndefinedFunction);
            1usize
        })
        .sum()
}

pub(super) fn ordinary_source_where_ownership(ownership: &ScalarSourceClauseOwnership) -> bool {
    matches!(ownership.kind, SourceClauseKind::Where)
}

fn attested_postgres_boolean_integer_equality_undefined_function(
    input: &RelExpr,
    predicate: &ScalarExpr,
    marker: &SourceAnalysisErrorProvenance,
) -> bool {
    let SourceAnalysisErrorProvenance::PostgresBooleanIntegerEqualityUndefinedFunction {
        rex_path,
        identifier_operand,
        literal_operand,
        generated_comparison_sql,
        input_index,
        base_table,
        table_field_index,
        base_field_name,
        source_literal_canonical_value,
        generated_literal_canonical_value,
    } = marker;
    if [*identifier_operand, *literal_operand].as_slice() != [0, 1]
        && [*identifier_operand, *literal_operand].as_slice() != [1, 0]
    {
        return false;
    }
    let Some(path) = parse_source_analysis_error_rex_path(rex_path) else {
        return false;
    };
    let Some(ast) = scalar_ast_at_rex_path(&predicate.parsed, &path) else {
        return false;
    };
    let Some(source) = predicate
        .source
        .as_ref()
        .and_then(|source| scalar_source_at_rex_path(source, &path))
    else {
        return false;
    };
    let ScalarAst::Call {
        operator,
        op: ScalarOp::Eq,
        args,
    } = ast
    else {
        return false;
    };
    let [_, _] = args.as_slice() else {
        return false;
    };
    if operator != "="
        || !source_binary_operator_matches(Some(source), ScalarOp::Eq)
        || if path.is_empty() {
            source.clause_ownership.is_none()
        } else {
            source.clause_ownership.is_some()
        }
        || source.operands.len() != 2
    {
        return false;
    }
    let Some(ScalarAst::InputRef { index }) = args.get(*identifier_operand) else {
        return false;
    };
    let Some(generated_boolean) = args
        .get(*literal_operand)
        .and_then(exact_typed_boolean_literal)
    else {
        return false;
    };
    let Some(identifier_source) = source_operand(Some(source), *identifier_operand) else {
        return false;
    };
    let Some(literal_source) = source_operand(Some(source), *literal_operand) else {
        return false;
    };
    let expected_boolean = match source_literal_canonical_value.as_str() {
        "0" => false,
        "1" => true,
        _ => return false,
    };
    if *index != *input_index
        || generated_boolean != expected_boolean
        || generated_literal_canonical_value != if expected_boolean { "true" } else { "false" }
        || !source_is_bare_integer_literal(literal_source, source_literal_canonical_value)
        || !source_identifier_matches_analysis_error_binding(
            identifier_source,
            base_table,
            base_field_name,
        )
    {
        return false;
    }
    let RelExpr::TableScan { table, output } = input else {
        return false;
    };
    if table != base_table
        || input_index != table_field_index
        || output.get(*input_index).is_none_or(|column| {
            column.name != *base_field_name || !matches!(column.ty, SqlType::Boolean)
        })
    {
        return false;
    }
    let expected_generated = if *identifier_operand == 0 {
        format!("=(${input_index}, {generated_literal_canonical_value})")
    } else {
        format!("=({generated_literal_canonical_value}, ${input_index})")
    };
    if generated_comparison_sql != &expected_generated {
        return false;
    }
    let Some(parent_tokens) = exact_source_tokens(source) else {
        return false;
    };
    let Some(identifier_tokens) = exact_source_tokens(identifier_source) else {
        return false;
    };
    let Some(literal_tokens) = exact_source_tokens(literal_source) else {
        return false;
    };
    let expected_parent = if *identifier_operand == 0 {
        identifier_tokens
            .into_iter()
            .chain([AttestedSqlToken::Compare("=".to_owned())])
            .chain(literal_tokens)
            .collect::<Vec<_>>()
    } else {
        literal_tokens
            .into_iter()
            .chain([AttestedSqlToken::Compare("=".to_owned())])
            .chain(identifier_tokens)
            .collect::<Vec<_>>()
    };
    parent_tokens == expected_parent
}

fn parse_source_analysis_error_rex_path(path: &str) -> Option<Vec<usize>> {
    let suffix = path.strip_prefix('$')?;
    if suffix.is_empty() {
        return Some(Vec::new());
    }
    if !suffix.starts_with('.') {
        return None;
    }
    suffix
        .split('.')
        .skip(1)
        .map(|part| (!part.is_empty()).then(|| part.parse().ok()).flatten())
        .collect()
}

fn scalar_ast_at_rex_path<'a>(mut ast: &'a ScalarAst, path: &[usize]) -> Option<&'a ScalarAst> {
    for index in path {
        let ScalarAst::Call { args, .. } = ast else {
            return None;
        };
        ast = args.get(*index)?;
    }
    Some(ast)
}

fn scalar_source_at_rex_path<'a>(
    mut source: &'a ScalarSourceProvenance,
    path: &[usize],
) -> Option<&'a ScalarSourceProvenance> {
    for index in path {
        source = source.operands.get(*index)?.as_ref()?;
    }
    Some(source)
}

fn exact_typed_boolean_literal(ast: &ScalarAst) -> Option<bool> {
    let ScalarAst::TypeAnnotation { expr, ty } = ast else {
        return None;
    };
    if !ty.eq_ignore_ascii_case("BOOLEAN") {
        return None;
    }
    let ScalarAst::Literal { raw } = expr.as_ref() else {
        return None;
    };
    match raw.as_str() {
        value if value.eq_ignore_ascii_case("false") => Some(false),
        value if value.eq_ignore_ascii_case("true") => Some(true),
        _ => None,
    }
}

fn source_identifier_matches_analysis_error_binding(
    source: &ScalarSourceProvenance,
    base_table: &[String],
    base_field_name: &str,
) -> bool {
    if !source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("IDENTIFIER"))
        || source.operator.is_some()
        || source.clause_ownership.is_some()
        || !source.operands.is_empty()
    {
        return false;
    }
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    let Some(table_name) = base_table.last() else {
        return false;
    };
    matches!(
        tokens.as_slice(),
        [AttestedSqlToken::Identifier(field)] if field == base_field_name
    ) || matches!(
        tokens.as_slice(),
        [
            AttestedSqlToken::Identifier(table),
            AttestedSqlToken::Dot,
            AttestedSqlToken::Identifier(field),
        ] if table == table_name && field == base_field_name
    )
}

fn collect_rel_analysis_errors(rel: &RelExpr, errors: &mut Vec<FormalQueryError>) {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            for binding in bindings {
                collect_rel_analysis_errors(&binding.rel, errors);
            }
            collect_rel_analysis_errors(body, errors);
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => {}
        RelExpr::Project { input, exprs, .. } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            for expr in exprs {
                collect_scalar_analysis_errors(expr, &scope, errors);
            }
            collect_rel_analysis_errors(input, errors);
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            collect_scalar_analysis_errors(predicate, &scope, errors);
            collect_rel_analysis_errors(input, errors);
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            let scope = left
                .output()
                .iter()
                .chain(right.output())
                .collect::<Vec<_>>();
            collect_scalar_analysis_errors(condition, &scope, errors);
            collect_rel_analysis_errors(left, errors);
            collect_rel_analysis_errors(right, errors);
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            for call in agg_calls {
                if attested_two_argument_count_distinct(call, input) {
                    errors.push(FormalQueryError::UndefinedFunction);
                }
                for arg in &call.args {
                    collect_scalar_analysis_errors(arg, &scope, errors);
                }
                if let Some(filter) = &call.filter {
                    collect_scalar_analysis_errors(filter, &scope, errors);
                }
            }
            collect_rel_analysis_errors(input, errors);
        }
        RelExpr::Distinct { input, .. } => collect_rel_analysis_errors(input, errors),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            if let Some(fetch) = fetch {
                collect_scalar_analysis_errors(fetch, &scope, errors);
            }
            if let Some(offset) = offset {
                collect_scalar_analysis_errors(offset, &scope, errors);
            }
            collect_rel_analysis_errors(input, errors);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_rel_analysis_errors(input, errors);
            }
        }
        RelExpr::Values { rows, output } => {
            let scope = output.iter().collect::<Vec<_>>();
            for row in rows {
                for value in row {
                    collect_scalar_analysis_errors(value, &scope, errors);
                }
            }
        }
    }
}

fn collect_scalar_analysis_errors(
    expr: &ScalarExpr,
    scope: &[&Column],
    errors: &mut Vec<FormalQueryError>,
) {
    collect_scalar_ast_analysis_errors(&expr.parsed, expr.source.as_ref(), scope, errors);
}

fn collect_scalar_ast_analysis_errors(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
    scope: &[&Column],
    errors: &mut Vec<FormalQueryError>,
) {
    match ast {
        ScalarAst::Call { op, args, .. } => {
            if matches!(
                op,
                ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
            ) && args.len() == 2
                && source_invented_numeric_cast_arithmetic_matches(source, op, args, scope)
            {
                errors.push(FormalQueryError::UndefinedFunction);
            }
            if op.is_ordinary_comparison()
                && args.len() == 2
                && let Some(pair) = dynamic_string_integer_pair(args, scope)
                && source_dynamic_string_integer_pair_matches(source, op.clone(), &pair)
            {
                errors.push(FormalQueryError::UndefinedFunction);
            }
            if matches!(op, ScalarOp::In)
                && args.len() == 2
                && source_is_in_operator(source)
                && let Some(string_index) = annotated_integer_cast_input_ref(&args[0])
                && let Some(string_column) = scope.get(string_index)
                && matches!(string_column.ty, SqlType::String(_))
                && source_operand(source, 0)
                    .is_some_and(|source| source_is_direct_identifier(source, &string_column.name))
                && let ScalarAst::RelSubquery { rel } = &args[1]
                && let [integer_column] = rel.output()
                && matches!(integer_column.ty, SqlType::Integer)
                && subquery_has_attested_direct_integer_projection(rel)
            {
                errors.push(FormalQueryError::UndefinedFunction);
            }
            for (index, arg) in args.iter().enumerate() {
                collect_scalar_ast_analysis_errors(
                    arg,
                    source_operand(source, index),
                    scope,
                    errors,
                );
            }
        }
        ScalarAst::TypeAnnotation { expr, .. } => {
            // TypeAnnotation is metadata around the same Rex node, not an
            // additional source or Rex operand.
            collect_scalar_ast_analysis_errors(expr, source, scope, errors)
        }
        ScalarAst::RelSubquery { rel } => collect_rel_analysis_errors(rel, errors),
        ScalarAst::Window { parsed } => {
            for (index, arg) in parsed.args.iter().enumerate() {
                collect_scalar_ast_analysis_errors(
                    arg,
                    source_operand(source, index),
                    scope,
                    errors,
                );
            }
            for arg in &parsed.partition_by {
                collect_scalar_ast_analysis_errors(arg, None, scope, errors);
            }
            for key in &parsed.order_by {
                collect_scalar_ast_analysis_errors(&key.expr, None, scope, errors);
            }
            if let Some(frame) = &parsed.frame {
                for offset in frame.offset_exprs() {
                    collect_scalar_ast_analysis_errors(offset, None, scope, errors);
                }
            }
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. } => {}
    }
}

type ScopedScalarCounter = fn(&ScalarExpr, &[&Column]) -> usize;

fn rel_scoped_scalar_count(rel: &RelExpr, counter: ScopedScalarCounter) -> usize {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            bindings
                .iter()
                .map(|binding| rel_scoped_scalar_count(&binding.rel, counter))
                .sum::<usize>()
                + rel_scoped_scalar_count(body, counter)
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => 0,
        RelExpr::Project { input, exprs, .. } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            rel_scoped_scalar_count(input, counter)
                + exprs
                    .iter()
                    .map(|expr| counter(expr, &scope))
                    .sum::<usize>()
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            rel_scoped_scalar_count(input, counter) + counter(predicate, &scope)
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            let scope = left
                .output()
                .iter()
                .chain(right.output())
                .collect::<Vec<_>>();
            rel_scoped_scalar_count(left, counter)
                + rel_scoped_scalar_count(right, counter)
                + counter(condition, &scope)
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            rel_scoped_scalar_count(input, counter)
                + agg_calls
                    .iter()
                    .map(|call| {
                        call.args
                            .iter()
                            .map(|arg| counter(arg, &scope))
                            .sum::<usize>()
                            + call
                                .filter
                                .as_ref()
                                .map_or(0, |filter| counter(filter, &scope))
                    })
                    .sum::<usize>()
        }
        RelExpr::Distinct { input, .. } => rel_scoped_scalar_count(input, counter),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            rel_scoped_scalar_count(input, counter)
                + fetch.as_ref().map_or(0, |fetch| counter(fetch, &scope))
                + offset
                    .as_deref()
                    .map_or(0, |offset| counter(offset, &scope))
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .map(|input| rel_scoped_scalar_count(input, counter))
            .sum(),
        RelExpr::Values { rows, output } => {
            let scope = output.iter().collect::<Vec<_>>();
            rows.iter()
                .flatten()
                .map(|value| counter(value, &scope))
                .sum()
        }
    }
}

fn query_source_invented_numeric_cast_count(query: &Query) -> usize {
    rel_scoped_scalar_count(&query.rel, scalar_source_invented_numeric_cast_count)
}

fn query_attested_source_invented_numeric_operator_error_count(query: &Query) -> usize {
    rel_scoped_scalar_count(
        &query.rel,
        scalar_attested_source_invented_numeric_operator_error_count,
    )
}

fn scalar_source_invented_numeric_cast_count(expr: &ScalarExpr, scope: &[&Column]) -> usize {
    scalar_ast_source_invented_numeric_cast_count(&expr.parsed, expr.source.as_ref(), scope)
}

fn scalar_ast_source_invented_numeric_cast_count(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
    scope: &[&Column],
) -> usize {
    let current = annotated_numeric_cast_input_ref(ast)
        .and_then(|index| scope.get(index))
        .is_some_and(|column| {
            matches!(column.ty, SqlType::String(_) | SqlType::Null)
                && source
                    .is_some_and(|source| source_is_direct_identifier_chain(source, &column.name))
        });
    usize::from(current)
        + match ast {
            ScalarAst::Call { args, .. } => args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    scalar_ast_source_invented_numeric_cast_count(
                        arg,
                        source_operand(source, index),
                        scope,
                    )
                })
                .sum(),
            ScalarAst::TypeAnnotation { expr, .. } => {
                scalar_ast_source_invented_numeric_cast_count(expr, source, scope)
            }
            ScalarAst::RelSubquery { rel } => {
                rel_scoped_scalar_count(rel, scalar_source_invented_numeric_cast_count)
            }
            ScalarAst::Window { parsed } => {
                parsed
                    .args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        scalar_ast_source_invented_numeric_cast_count(
                            arg,
                            source_operand(source, index),
                            scope,
                        )
                    })
                    .chain(
                        parsed.partition_by.iter().map(|arg| {
                            scalar_ast_source_invented_numeric_cast_count(arg, None, scope)
                        }),
                    )
                    .chain(parsed.order_by.iter().map(|key| {
                        scalar_ast_source_invented_numeric_cast_count(&key.expr, None, scope)
                    }))
                    .sum::<usize>()
                    + parsed.frame.as_ref().map_or(0, |frame| {
                        frame
                            .offset_exprs()
                            .map(|offset| {
                                scalar_ast_source_invented_numeric_cast_count(offset, None, scope)
                            })
                            .sum()
                    })
            }
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. } => 0,
        }
}

fn scalar_attested_source_invented_numeric_operator_error_count(
    expr: &ScalarExpr,
    scope: &[&Column],
) -> usize {
    scalar_ast_attested_source_invented_numeric_operator_error_count(
        &expr.parsed,
        expr.source.as_ref(),
        scope,
    )
}

fn scalar_ast_attested_source_invented_numeric_operator_error_count(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
    scope: &[&Column],
) -> usize {
    let current = match ast {
        ScalarAst::Call { op, args, .. }
            if matches!(
                op,
                ScalarOp::Plus | ScalarOp::Minus | ScalarOp::Multiply | ScalarOp::Divide
            ) && args.len() == 2
                && source_invented_numeric_cast_arithmetic_matches(source, op, args, scope) =>
        {
            1
        }
        ScalarAst::Call { op, args, .. }
            if op.is_ordinary_comparison()
                && args.len() == 2
                && dynamic_string_integer_pair(args, scope).is_some_and(|pair| {
                    source_dynamic_string_integer_pair_matches(source, op.clone(), &pair)
                }) =>
        {
            1
        }
        ScalarAst::Call {
            op: ScalarOp::In,
            args,
            ..
        } if args.len() == 2
            && source_is_in_operator(source)
            && annotated_integer_cast_input_ref(&args[0])
                .and_then(|index| scope.get(index))
                .is_some_and(|column| {
                    matches!(column.ty, SqlType::String(_) | SqlType::Null)
                        && source_operand(source, 0)
                            .is_some_and(|source| source_is_direct_identifier(source, &column.name))
                })
            && matches!(&args[1], ScalarAst::RelSubquery { rel }
                    if matches!(rel.output(), [column] if matches!(column.ty, SqlType::Integer))
                        && subquery_has_attested_direct_integer_projection(rel)) =>
        {
            1
        }
        _ => 0,
    };
    current
        + match ast {
            ScalarAst::Call { args, .. } => args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    scalar_ast_attested_source_invented_numeric_operator_error_count(
                        arg,
                        source_operand(source, index),
                        scope,
                    )
                })
                .sum(),
            ScalarAst::TypeAnnotation { expr, .. } => {
                scalar_ast_attested_source_invented_numeric_operator_error_count(
                    expr, source, scope,
                )
            }
            ScalarAst::RelSubquery { rel } => rel_scoped_scalar_count(
                rel,
                scalar_attested_source_invented_numeric_operator_error_count,
            ),
            ScalarAst::Window { parsed } => {
                parsed
                    .args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        scalar_ast_attested_source_invented_numeric_operator_error_count(
                            arg,
                            source_operand(source, index),
                            scope,
                        )
                    })
                    .chain(parsed.partition_by.iter().map(|arg| {
                        scalar_ast_attested_source_invented_numeric_operator_error_count(
                            arg, None, scope,
                        )
                    }))
                    .chain(parsed.order_by.iter().map(|key| {
                        scalar_ast_attested_source_invented_numeric_operator_error_count(
                            &key.expr, None, scope,
                        )
                    }))
                    .sum::<usize>()
                    + parsed.frame.as_ref().map_or(0, |frame| {
                        frame
                            .offset_exprs()
                            .map(|offset| {
                                scalar_ast_attested_source_invented_numeric_operator_error_count(
                                    offset, None, scope,
                                )
                            })
                            .sum()
                    })
            }
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. } => 0,
        }
}

struct PositionedColumn<'a> {
    position: usize,
    name: &'a str,
}

struct PositionedLiteral<'a> {
    position: usize,
    raw: &'a str,
}

/// Count every typed-IR INTEGER cast around a string spelling which
/// PostgreSQL cannot even begin to parse as int4. This generated-tree count
/// is paired with an independently source-bound count below; neither is
/// sufficient on its own.
fn rel_generated_invalid_int4_unknown_literal_count(rel: &RelExpr) -> usize {
    rel_string_literal_cast_count(rel, invalid_int4_string_literal_cast, false)
}

fn rel_source_attested_invalid_int4_unknown_literal_count(rel: &RelExpr) -> usize {
    rel_source_attested_invalid_int4_comparison_count(rel)
}

fn rel_source_attested_invalid_int4_comparison_count(rel: &RelExpr) -> usize {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            bindings
                .iter()
                .map(|binding| rel_source_attested_invalid_int4_comparison_count(&binding.rel))
                .sum::<usize>()
                + rel_source_attested_invalid_int4_comparison_count(body)
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => 0,
        RelExpr::Project { input, exprs, .. } => {
            rel_source_attested_invalid_int4_comparison_count(input)
                + exprs
                    .iter()
                    .map(|expr| {
                        scalar_source_attested_invalid_int4_comparison_count(
                            expr,
                            &input.output().iter().collect::<Vec<_>>(),
                        )
                    })
                    .sum::<usize>()
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            rel_source_attested_invalid_int4_comparison_count(input)
                + scalar_source_attested_invalid_int4_comparison_count(
                    predicate,
                    &input.output().iter().collect::<Vec<_>>(),
                )
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            let scope = left
                .output()
                .iter()
                .chain(right.output())
                .collect::<Vec<_>>();
            rel_source_attested_invalid_int4_comparison_count(left)
                + rel_source_attested_invalid_int4_comparison_count(right)
                + scalar_source_attested_invalid_int4_comparison_count(condition, &scope)
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            rel_source_attested_invalid_int4_comparison_count(input)
                + agg_calls
                    .iter()
                    .map(|call| {
                        call.args
                            .iter()
                            .map(|arg| {
                                scalar_source_attested_invalid_int4_comparison_count(arg, &scope)
                            })
                            .sum::<usize>()
                            + call.filter.as_ref().map_or(0, |filter| {
                                scalar_source_attested_invalid_int4_comparison_count(filter, &scope)
                            })
                    })
                    .sum::<usize>()
        }
        RelExpr::Distinct { input, .. } => rel_source_attested_invalid_int4_comparison_count(input),
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            let scope = input.output().iter().collect::<Vec<_>>();
            rel_source_attested_invalid_int4_comparison_count(input)
                + fetch.as_ref().map_or(0, |expr| {
                    scalar_source_attested_invalid_int4_comparison_count(expr, &scope)
                })
                + offset.as_deref().map_or(0, |expr| {
                    scalar_source_attested_invalid_int4_comparison_count(expr, &scope)
                })
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .map(rel_source_attested_invalid_int4_comparison_count)
            .sum(),
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .map(|expr| scalar_source_attested_invalid_int4_comparison_count(expr, &[]))
            .sum(),
    }
}

fn scalar_source_attested_invalid_int4_comparison_count(
    expr: &ScalarExpr,
    scope: &[&Column],
) -> usize {
    let ownership = expr
        .source
        .as_ref()
        .and_then(|source| source.clause_ownership.as_ref())
        .filter(|ownership| ordinary_source_where_ownership(ownership));
    scalar_ast_source_attested_invalid_int4_comparison_count(
        &expr.parsed,
        expr.source.as_ref(),
        ownership,
        scope,
    )
}

fn scalar_ast_source_attested_invalid_int4_comparison_count(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
    ownership: Option<&ScalarSourceClauseOwnership>,
    scope: &[&Column],
) -> usize {
    let current = match ast {
        ScalarAst::Call { op, args, .. } if op.is_ordinary_comparison() && args.len() == 2 => (0
            ..2)
            .filter(|cast_position| {
                let other_position = 1 - *cast_position;
                let Some((ty, raw)) = annotated_cast_string_literal(&args[*cast_position]) else {
                    return false;
                };
                if !invalid_int4_string_literal_cast(ty, raw) {
                    return false;
                }
                let Some(input_index) = direct_input_ref(&args[other_position]) else {
                    return false;
                };
                let Some(column) = scope.get(input_index) else {
                    return false;
                };
                exact_source_invalid_int4_comparison(
                    source,
                    ownership,
                    op.clone(),
                    *cast_position,
                    raw,
                    &column.name,
                )
            })
            .count(),
        _ => 0,
    };
    current
        + match ast {
            ScalarAst::Call { args, .. } => args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    scalar_ast_source_attested_invalid_int4_comparison_count(
                        arg,
                        source_operand(source, index),
                        ownership,
                        scope,
                    )
                })
                .sum(),
            ScalarAst::TypeAnnotation { expr, .. } => {
                scalar_ast_source_attested_invalid_int4_comparison_count(
                    expr, source, ownership, scope,
                )
            }
            ScalarAst::RelSubquery { rel } => {
                rel_source_attested_invalid_int4_comparison_count(rel)
            }
            ScalarAst::Window { parsed } => parsed
                .args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    scalar_ast_source_attested_invalid_int4_comparison_count(
                        arg,
                        source_operand(source, index),
                        ownership,
                        scope,
                    )
                })
                .sum(),
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. } => 0,
        }
}

fn exact_source_invalid_int4_comparison(
    source: Option<&ScalarSourceProvenance>,
    ownership: Option<&ScalarSourceClauseOwnership>,
    op: ScalarOp,
    literal_position: usize,
    raw: &str,
    column_name: &str,
) -> bool {
    let Some(source) = source else {
        return false;
    };
    if ownership.is_none()
        || !source_has_exact_binding(source)
        || !source_binary_operator_matches(Some(source), op)
        || source.operands.len() != 2
    {
        return false;
    }
    let column_position = 1 - literal_position;
    let Some(column) = source_operand(Some(source), column_position) else {
        return false;
    };
    let Some(literal) = source_operand(Some(source), literal_position) else {
        return false;
    };
    if !exact_source_direct_identifier_chain(column, column_name)
        || !source_attests_implicit_unknown_string_literal(literal, raw)
    {
        return false;
    }
    let Some(parent_tokens) = exact_source_tokens(source) else {
        return false;
    };
    let Some(column_tokens) = exact_source_tokens(column) else {
        return false;
    };
    let Some(literal_tokens) = exact_source_tokens(literal) else {
        return false;
    };
    let (left, right) = if literal_position == 0 {
        (literal_tokens, column_tokens)
    } else {
        (column_tokens, literal_tokens)
    };
    let mut expected = left;
    expected.push(AttestedSqlToken::Compare(
        source.operator.clone().unwrap_or_default(),
    ));
    expected.extend(right);
    parent_tokens == expected
}

/// A generic query-wide analysis error cannot be selected while Calcite IR
/// contains any independently unaccounted conversion of a string literal.
/// PostgreSQL invokes the selected target type's input routine during parse
/// analysis, and its SQLSTATE and source-order position are observable.  The
fn rel_unaccounted_string_literal_cast_count(rel: &RelExpr) -> usize {
    rel_string_literal_cast_count(rel, |_, _| true, false)
}

type StringLiteralCastPredicate = fn(&str, &str) -> bool;

fn invalid_int4_string_literal_cast(ty: &str, raw: &str) -> bool {
    ty.eq_ignore_ascii_case("INTEGER")
        && sql_string_literal_content(raw)
            .is_some_and(|content| int32_text_is_definitely_invalid(&content))
}

fn rel_string_literal_cast_count(
    rel: &RelExpr,
    matches_cast: StringLiteralCastPredicate,
    require_source_attestation: bool,
) -> usize {
    match rel {
        RelExpr::Bindings { bindings, body, .. } => {
            bindings
                .iter()
                .map(|binding| {
                    rel_string_literal_cast_count(
                        &binding.rel,
                        matches_cast,
                        require_source_attestation,
                    )
                })
                .sum::<usize>()
                + rel_string_literal_cast_count(body, matches_cast, require_source_attestation)
        }
        RelExpr::TableScan { .. } | RelExpr::QueryRef { .. } => 0,
        RelExpr::Project { input, exprs, .. } => {
            rel_string_literal_cast_count(input, matches_cast, require_source_attestation)
                + exprs
                    .iter()
                    .map(|expr| {
                        scalar_string_literal_cast_count(
                            expr,
                            matches_cast,
                            require_source_attestation,
                        )
                    })
                    .sum::<usize>()
        }
        RelExpr::Filter {
            input, predicate, ..
        }
        | RelExpr::NativeHaving {
            input, predicate, ..
        } => {
            rel_string_literal_cast_count(input, matches_cast, require_source_attestation)
                + scalar_string_literal_cast_count(
                    predicate,
                    matches_cast,
                    require_source_attestation,
                )
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            rel_string_literal_cast_count(left, matches_cast, require_source_attestation)
                + rel_string_literal_cast_count(right, matches_cast, require_source_attestation)
                + scalar_string_literal_cast_count(
                    condition,
                    matches_cast,
                    require_source_attestation,
                )
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            rel_string_literal_cast_count(input, matches_cast, require_source_attestation)
                + agg_calls
                    .iter()
                    .map(|call| {
                        call.args
                            .iter()
                            .map(|arg| {
                                scalar_string_literal_cast_count(
                                    arg,
                                    matches_cast,
                                    require_source_attestation,
                                )
                            })
                            .sum::<usize>()
                            + call.filter.as_ref().map_or(0, |filter| {
                                scalar_string_literal_cast_count(
                                    filter,
                                    matches_cast,
                                    require_source_attestation,
                                )
                            })
                    })
                    .sum::<usize>()
        }
        RelExpr::Distinct { input, .. } => {
            rel_string_literal_cast_count(input, matches_cast, require_source_attestation)
        }
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            rel_string_literal_cast_count(input, matches_cast, require_source_attestation)
                + fetch.as_ref().map_or(0, |fetch| {
                    scalar_string_literal_cast_count(
                        fetch,
                        matches_cast,
                        require_source_attestation,
                    )
                })
                + offset.as_deref().map_or(0, |offset| {
                    scalar_string_literal_cast_count(
                        offset,
                        matches_cast,
                        require_source_attestation,
                    )
                })
        }
        RelExpr::Set { inputs, .. } => inputs
            .iter()
            .map(|input| {
                rel_string_literal_cast_count(input, matches_cast, require_source_attestation)
            })
            .sum(),
        RelExpr::Values { rows, .. } => rows
            .iter()
            .flatten()
            .map(|value| {
                scalar_string_literal_cast_count(value, matches_cast, require_source_attestation)
            })
            .sum(),
    }
}

fn scalar_string_literal_cast_count(
    expr: &ScalarExpr,
    matches_cast: StringLiteralCastPredicate,
    require_source_attestation: bool,
) -> usize {
    scalar_ast_string_literal_cast_count(
        &expr.parsed,
        expr.source.as_ref(),
        matches_cast,
        require_source_attestation,
    )
}

fn scalar_ast_string_literal_cast_count(
    ast: &ScalarAst,
    source: Option<&ScalarSourceProvenance>,
    matches_cast: StringLiteralCastPredicate,
    require_source_attestation: bool,
) -> usize {
    let current = usize::from(annotated_cast_string_literal(ast).is_some_and(|(ty, raw)| {
        matches_cast(ty, raw)
            && (!require_source_attestation
                || source.is_some_and(|source| {
                    source_attests_implicit_unknown_string_literal(source, raw)
                }))
    }));
    current
        + match ast {
            ScalarAst::Call { args, .. } => args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    scalar_ast_string_literal_cast_count(
                        arg,
                        source_operand(source, index),
                        matches_cast,
                        require_source_attestation,
                    )
                })
                .sum(),
            ScalarAst::TypeAnnotation { expr, .. } => scalar_ast_string_literal_cast_count(
                expr,
                source,
                matches_cast,
                require_source_attestation,
            ),
            ScalarAst::RelSubquery { rel } => {
                rel_string_literal_cast_count(rel, matches_cast, require_source_attestation)
            }
            ScalarAst::Window { parsed } => {
                parsed
                    .args
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        scalar_ast_string_literal_cast_count(
                            arg,
                            source_operand(source, index),
                            matches_cast,
                            require_source_attestation,
                        )
                    })
                    .chain(parsed.partition_by.iter().map(|arg| {
                        scalar_ast_string_literal_cast_count(
                            arg,
                            None,
                            matches_cast,
                            require_source_attestation,
                        )
                    }))
                    .sum::<usize>()
                    + parsed
                        .order_by
                        .iter()
                        .map(|key| {
                            scalar_ast_string_literal_cast_count(
                                &key.expr,
                                None,
                                matches_cast,
                                require_source_attestation,
                            )
                        })
                        .sum::<usize>()
                    + parsed.frame.as_ref().map_or(0, |frame| {
                        frame
                            .offset_exprs()
                            .map(|offset| {
                                scalar_ast_string_literal_cast_count(
                                    offset,
                                    None,
                                    matches_cast,
                                    require_source_attestation,
                                )
                            })
                            .sum()
                    })
            }
            ScalarAst::InputRef { .. }
            | ScalarAst::CorrelatedRef { .. }
            | ScalarAst::Literal { .. }
            | ScalarAst::Flag { .. } => 0,
        }
}

fn source_attests_implicit_unknown_string_literal(
    source: &ScalarSourceProvenance,
    raw: &str,
) -> bool {
    let Some(expected) = sql_string_literal_content(raw) else {
        return false;
    };
    if !source_has_exact_binding(source)
        || source.text.as_deref() != Some(raw)
        || source.kind.as_deref() != Some("LITERAL")
        || source.operator.is_some()
        || source.clause_ownership.is_some()
        || !exact_source_tokens(source).is_some_and(|tokens| {
            matches!(tokens.as_slice(), [AttestedSqlToken::StringLiteral(value)] if value == &expected)
        })
    {
        return false;
    }
    match source.operands.as_slice() {
        [] => true,
        [Some(child)] => {
            exact_source_nodes_identical(source, child)
                && child.text.as_deref() == Some(raw)
                && child.kind.as_deref() == Some("LITERAL")
                && child.operator.is_none()
                && child.clause_ownership.is_none()
                && child.operands.is_empty()
                && exact_source_tokens(child).is_some_and(|tokens| {
                    matches!(tokens.as_slice(), [AttestedSqlToken::StringLiteral(value)] if value == &expected)
                })
        }
        _ => false,
    }
}

fn int32_text_is_definitely_invalid(value: &str) -> bool {
    let trimmed = value.trim_matches(|ch: char| ch.is_ascii_whitespace());
    let unsigned = trimmed
        .strip_prefix('+')
        .or_else(|| trimmed.strip_prefix('-'))
        .unwrap_or(trimmed);
    // PostgreSQL 17's pg_strtoint32_safe also accepts 0x/0o/0b prefixes and
    // underscores between digits, and distinguishes syntax errors from
    // numeric overflow.  Only classify the closed subset for which its slow
    // path cannot consume even a first digit; everything beginning with a
    // digit remains conservatively unsupported by this analysis-error path.
    !unsigned.as_bytes().first().is_some_and(u8::is_ascii_digit)
}

enum PositionedIntegerOperand<'a> {
    Column(PositionedColumn<'a>),
    Literal(PositionedLiteral<'a>),
}

struct DynamicStringIntegerPair<'a> {
    string_column: PositionedColumn<'a>,
    integer_operand: PositionedIntegerOperand<'a>,
}

fn dynamic_string_integer_pair<'a>(
    args: &'a [ScalarAst],
    scope: &'a [&Column],
) -> Option<DynamicStringIntegerPair<'a>> {
    for (cast_position, other_position) in [(0, 1), (1, 0)] {
        let cast = &args[cast_position];
        let other = &args[other_position];
        let Some(string_index) = annotated_integer_cast_input_ref(cast) else {
            continue;
        };
        let Some(string_column) = scope.get(string_index) else {
            continue;
        };
        if !matches!(string_column.ty, SqlType::String(_) | SqlType::Null) {
            continue;
        }
        if let Some(integer_index) = direct_input_ref(other)
            && let Some(integer_column) = scope.get(integer_index)
            && matches!(integer_column.ty, SqlType::Integer)
        {
            return Some(DynamicStringIntegerPair {
                string_column: PositionedColumn {
                    position: cast_position,
                    name: &string_column.name,
                },
                integer_operand: PositionedIntegerOperand::Column(PositionedColumn {
                    position: other_position,
                    name: &integer_column.name,
                }),
            });
        }
        if let Some(integer_literal) = annotated_integer_literal(other) {
            return Some(DynamicStringIntegerPair {
                string_column: PositionedColumn {
                    position: cast_position,
                    name: &string_column.name,
                },
                integer_operand: PositionedIntegerOperand::Literal(PositionedLiteral {
                    position: other_position,
                    raw: integer_literal,
                }),
            });
        }
    }
    None
}

fn direct_input_ref(ast: &ScalarAst) -> Option<usize> {
    match ast {
        ScalarAst::InputRef { index } => Some(*index),
        ScalarAst::TypeAnnotation { expr, .. } => direct_input_ref(expr),
        _ => None,
    }
}

fn annotated_integer_cast_input_ref(ast: &ScalarAst) -> Option<usize> {
    let ScalarAst::TypeAnnotation { expr, ty } = ast else {
        return None;
    };
    if !ty.eq_ignore_ascii_case("INTEGER") {
        return None;
    }
    let ScalarAst::Call {
        op: ScalarOp::Cast,
        args,
        ..
    } = expr.as_ref()
    else {
        return None;
    };
    let [ScalarAst::InputRef { index }] = args.as_slice() else {
        return None;
    };
    Some(*index)
}

fn annotated_numeric_cast_input_ref(ast: &ScalarAst) -> Option<usize> {
    let ScalarAst::TypeAnnotation { expr, ty } = ast else {
        return None;
    };
    if !generated_numeric_type_annotation(ty) {
        return None;
    }
    let ScalarAst::Call {
        operator,
        op: ScalarOp::Cast,
        args,
    } = expr.as_ref()
    else {
        return None;
    };
    let [ScalarAst::InputRef { index }] = args.as_slice() else {
        return None;
    };
    operator.eq_ignore_ascii_case("CAST").then_some(*index)
}

fn generated_numeric_type_annotation(ty: &str) -> bool {
    let compact = ty
        .chars()
        .filter(|ch| !ch.is_ascii_whitespace())
        .flat_map(char::to_uppercase)
        .collect::<String>();
    let Some(annotation) = classify_type_annotation(ty) else {
        return false;
    };
    match compact.as_str() {
        "INTEGER" => annotation == SqlTypeAnnotation::Integer,
        "BIGINT" => annotation == SqlTypeAnnotation::BigInt,
        "REAL" => annotation == SqlTypeAnnotation::Real,
        "FLOAT" => annotation == SqlTypeAnnotation::Float { precision: None },
        "DOUBLE" | "DOUBLEPRECISION" => annotation == SqlTypeAnnotation::Double,
        "NUMERIC" => {
            annotation
                == SqlTypeAnnotation::Decimal {
                    precision: None,
                    scale: None,
                }
        }
        _ if (compact.starts_with("DECIMAL(") || compact.starts_with("NUMERIC("))
            && compact.contains(',') =>
        {
            matches!(
                annotation,
                SqlTypeAnnotation::Decimal {
                    precision: Some(_),
                    scale: Some(_)
                }
            )
        }
        _ => false,
    }
}

fn annotated_cast_string_literal(ast: &ScalarAst) -> Option<(&str, &str)> {
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
    let [ScalarAst::Literal { raw }] = args.as_slice() else {
        return None;
    };
    sql_string_literal_content(raw)?;
    Some((ty, raw))
}

fn annotated_integer_literal(ast: &ScalarAst) -> Option<&str> {
    match ast {
        ScalarAst::TypeAnnotation { expr, ty } if ty.eq_ignore_ascii_case("INTEGER") => {
            match expr.as_ref() {
                ScalarAst::Literal { raw } if is_integer_literal(raw) => Some(raw),
                _ => None,
            }
        }
        ScalarAst::Literal { raw } if is_integer_literal(raw) => Some(raw),
        _ => None,
    }
}

/// Calcite can make an otherwise unresolved PostgreSQL arithmetic operator
/// executable by inserting a numeric cast around a string-typed input.  The
/// source operand must still be the direct identifier: an explicit source
/// cast selects runtime cast semantics and is deliberately not an
/// always-error query.
fn source_invented_numeric_cast_arithmetic_matches(
    source: Option<&ScalarSourceProvenance>,
    op: &ScalarOp,
    args: &[ScalarAst],
    scope: &[&Column],
) -> bool {
    for (cast_position, numeric_position) in [(0, 1), (1, 0)] {
        let Some(string_index) = annotated_numeric_cast_input_ref(&args[cast_position]) else {
            continue;
        };
        let ScalarAst::InputRef {
            index: numeric_index,
        } = &args[numeric_position]
        else {
            continue;
        };
        let Some(string_column) = scope.get(string_index) else {
            continue;
        };
        let Some(numeric_column) = scope.get(*numeric_index) else {
            continue;
        };
        if !matches!(string_column.ty, SqlType::String(_) | SqlType::Null)
            || !matches!(
                numeric_column.ty,
                SqlType::Integer
                    | SqlType::BigInt
                    | SqlType::Float
                    | SqlType::Double
                    | SqlType::Decimal { .. }
            )
        {
            continue;
        }
        let (left_name, right_name) = if cast_position == 0 {
            (string_column.name.as_str(), numeric_column.name.as_str())
        } else {
            (numeric_column.name.as_str(), string_column.name.as_str())
        };
        if source_arithmetic_identifiers_match(source, op, left_name, right_name) {
            return true;
        }
    }
    false
}

fn source_operand(
    source: Option<&ScalarSourceProvenance>,
    index: usize,
) -> Option<&ScalarSourceProvenance> {
    source?.operands.get(index)?.as_ref()
}

fn source_binary_operator_matches(source: Option<&ScalarSourceProvenance>, op: ScalarOp) -> bool {
    let Some(source) = source else {
        return false;
    };
    let expected_kind = match op {
        ScalarOp::Eq => "EQUALS",
        ScalarOp::NotEq => "NOT_EQUALS",
        ScalarOp::Lt => "LESS_THAN",
        ScalarOp::Lte => "LESS_THAN_OR_EQUAL",
        ScalarOp::Gt => "GREATER_THAN",
        ScalarOp::Gte => "GREATER_THAN_OR_EQUAL",
        _ => return false,
    };
    let expected_operators: &[&str] = match op {
        ScalarOp::Eq => &["="],
        ScalarOp::NotEq => &["<>", "!="],
        ScalarOp::Lt => &["<"],
        ScalarOp::Lte => &["<="],
        ScalarOp::Gt => &[">"],
        ScalarOp::Gte => &[">="],
        _ => return false,
    };
    if !source_has_exact_binding(source)
        || source.operands.len() != 2
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case(expected_kind))
        || !source.operator.as_deref().is_some_and(|operator| {
            expected_operators
                .iter()
                .any(|expected| operator.eq_ignore_ascii_case(expected))
        })
    {
        return false;
    }
    let Some(source_operator) = source.operator.as_deref() else {
        return false;
    };
    exact_source_binary_operands_match(
        source,
        AttestedSqlToken::Compare(source_operator.to_owned()),
    )
}

fn source_is_direct_identifier(source: &ScalarSourceProvenance, expected: &str) -> bool {
    if !source_has_exact_binding(source)
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("IDENTIFIER"))
        || source.operator.is_some()
    {
        return false;
    }
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    direct_column_at(&tokens, 0, expected).is_some_and(|end| end == tokens.len())
}

fn source_is_direct_identifier_chain(source: &ScalarSourceProvenance, expected: &str) -> bool {
    if source.clause_ownership.is_some() || !source_is_direct_identifier(source, expected) {
        return false;
    }
    match source.operands.as_slice() {
        [] => true,
        [Some(child)] => {
            exact_source_nodes_identical(source, child)
                && source_is_direct_identifier_chain(child, expected)
        }
        _ => false,
    }
}

fn source_arithmetic_identifiers_match(
    source: Option<&ScalarSourceProvenance>,
    op: &ScalarOp,
    left_name: &str,
    right_name: &str,
) -> bool {
    let Some(source) = source else {
        return false;
    };
    let (expected_kind, expected_operator, expected_token) = match op {
        ScalarOp::Plus => ("PLUS", "+", AttestedSqlToken::Plus),
        ScalarOp::Minus => ("MINUS", "-", AttestedSqlToken::Minus),
        ScalarOp::Multiply => ("TIMES", "*", AttestedSqlToken::Multiply),
        ScalarOp::Divide => ("DIVIDE", "/", AttestedSqlToken::Divide),
        _ => return false,
    };
    if source
        .kind
        .as_deref()
        .is_none_or(|kind| !kind.eq_ignore_ascii_case(expected_kind))
        || source
            .operator
            .as_deref()
            .is_none_or(|operator| operator != expected_operator)
        || source.clause_ownership.is_some()
        || source.operands.len() != 2
        || source_operand(Some(source), 0)
            .is_none_or(|operand| !source_is_direct_identifier_chain(operand, left_name))
        || source_operand(Some(source), 1)
            .is_none_or(|operand| !source_is_direct_identifier_chain(operand, right_name))
    {
        return false;
    }
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    let Some(left_end) = direct_column_at(&tokens, 0, left_name) else {
        return false;
    };
    tokens.get(left_end) == Some(&expected_token)
        && direct_column_at(&tokens, left_end + 1, right_name)
            .is_some_and(|right_end| right_end == tokens.len())
}

fn source_is_any_direct_identifier(source: &ScalarSourceProvenance) -> bool {
    if !source_has_exact_binding(source)
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("IDENTIFIER"))
        || source.operator.is_some()
    {
        return false;
    }
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    direct_identifier_end(&tokens, 0).is_some_and(|end| end == tokens.len())
}

fn source_is_bare_string_literal(source: &ScalarSourceProvenance, raw: &str) -> bool {
    let Some(expected) = sql_string_literal_content(raw) else {
        return false;
    };
    source_has_exact_binding(source)
        && source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("LITERAL"))
        && source.operator.is_none()
        && source.clause_ownership.is_none()
        && source.operands.is_empty()
        && exact_source_tokens(source)
            .is_some_and(|tokens| {
                matches!(tokens.as_slice(), [AttestedSqlToken::StringLiteral(value)] if value == &expected)
            })
}

fn source_is_bare_integer_literal(source: &ScalarSourceProvenance, raw: &str) -> bool {
    let expected = raw.trim_start_matches('+');
    source_has_exact_binding(source)
        && source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("LITERAL"))
        && source.operator.is_none()
        && exact_source_tokens(source)
            .is_some_and(|tokens| {
                matches!(tokens.as_slice(), [AttestedSqlToken::Number(value)] if value == expected)
            })
}

fn source_dynamic_string_integer_pair_matches(
    source: Option<&ScalarSourceProvenance>,
    op: ScalarOp,
    pair: &DynamicStringIntegerPair<'_>,
) -> bool {
    let Some(string_source) = source_operand(source, pair.string_column.position) else {
        return false;
    };
    if !source_is_direct_identifier(string_source, pair.string_column.name) {
        return false;
    }
    match &pair.integer_operand {
        PositionedIntegerOperand::Column(column) => {
            source_binary_operator_matches(source, op)
                && source_operand(source, column.position)
                    .is_some_and(|source| source_is_direct_identifier(source, column.name))
        }
        PositionedIntegerOperand::Literal(literal) => {
            let Some(integer_source) = source_operand(source, literal.position) else {
                return false;
            };
            if !source_is_bare_integer_literal(integer_source, literal.raw) {
                return false;
            }
            source_binary_operator_matches(source, op)
                || source_is_singleton_integer_in(source, pair.string_column.name, literal.raw)
        }
    }
}

fn source_is_singleton_integer_in(
    source: Option<&ScalarSourceProvenance>,
    column: &str,
    integer: &str,
) -> bool {
    let Some(source) = source else {
        return false;
    };
    if !source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("IN"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("IN"))
    {
        return false;
    }
    let [Some(column_source), Some(integer_source)] = source.operands.as_slice() else {
        return false;
    };
    if !source_is_direct_identifier(column_source, column)
        || !source_is_bare_integer_literal(integer_source, integer)
    {
        return false;
    }
    let Some(mut expected) = exact_source_tokens(column_source) else {
        return false;
    };
    let Some(integer_tokens) = exact_source_tokens(integer_source) else {
        return false;
    };
    expected.extend([AttestedSqlToken::In, AttestedSqlToken::LeftParen]);
    expected.extend(integer_tokens);
    expected.push(AttestedSqlToken::RightParen);
    exact_source_tokens(source).is_some_and(|tokens| tokens == expected)
}

fn source_is_in_operator(source: Option<&ScalarSourceProvenance>) -> bool {
    let Some(source) = source else {
        return false;
    };
    if !source
        .kind
        .as_deref()
        .is_some_and(|kind| kind.eq_ignore_ascii_case("IN"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case("IN"))
    {
        return false;
    }
    let [Some(left)] = source.operands.as_slice() else {
        return false;
    };
    let Some(parent_tokens) = exact_source_tokens(source) else {
        return false;
    };
    let Some(left_tokens) = exact_source_tokens(left) else {
        return false;
    };
    if !parent_tokens.starts_with(&left_tokens)
        || !matches!(
            parent_tokens.get(left_tokens.len()),
            Some(AttestedSqlToken::In)
        )
        || !matches!(
            parent_tokens.get(left_tokens.len() + 1),
            Some(AttestedSqlToken::LeftParen)
        )
        || !matches!(
            parent_tokens.get(left_tokens.len() + 2),
            Some(AttestedSqlToken::Select)
        )
    {
        return false;
    }
    let mut depth = 0usize;
    for (index, token) in parent_tokens[left_tokens.len() + 1..].iter().enumerate() {
        match token {
            AttestedSqlToken::LeftParen => depth += 1,
            AttestedSqlToken::RightParen => {
                let Some(next_depth) = depth.checked_sub(1) else {
                    return false;
                };
                depth = next_depth;
                if depth == 0 {
                    return index + left_tokens.len() + 2 == parent_tokens.len();
                }
            }
            _ => {}
        }
    }
    false
}

fn subquery_has_attested_direct_integer_projection(rel: &RelExpr) -> bool {
    match rel {
        RelExpr::Project {
            input,
            exprs,
            output,
            ..
        } if exprs.len() == 1 && output.len() == 1 && matches!(output[0].ty, SqlType::Integer) => {
            let Some(index) = direct_input_ref(&exprs[0].parsed) else {
                return false;
            };
            let Some(column) = input.output().get(index) else {
                return false;
            };
            exprs[0]
                .source
                .as_ref()
                .is_some_and(|source| source_is_direct_identifier(source, &column.name))
        }
        RelExpr::Sort { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::NativeHaving { input, .. } => {
            subquery_has_attested_direct_integer_projection(input)
        }
        _ => false,
    }
}

fn attested_two_argument_count_distinct(call: &AggregateCall, input: &RelExpr) -> bool {
    if !call.function.eq_ignore_ascii_case("COUNT") || !call.distinct || call.args.len() != 2 {
        return false;
    }
    let Some(source) = call.modifiers.source.as_ref() else {
        return false;
    };
    if !source
        .operator
        .as_deref()
        .is_some_and(|operator| operator.eq_ignore_ascii_case("COUNT"))
        || !source.kind.as_deref().is_some_and(|kind| {
            kind.eq_ignore_ascii_case("OTHER_FUNCTION") || kind.eq_ignore_ascii_case("COUNT")
        })
        || call.modifiers.source_distinct != Some(true)
        || !source_has_exact_binding(source)
        || source.operands.len() != 2
    {
        return false;
    }
    let arguments_match = call.args.iter().enumerate().all(|(position, arg)| {
        let Some(index) = direct_input_ref(&arg.parsed) else {
            return false;
        };
        let Some(source_operand) = source_operand(Some(source), position) else {
            return false;
        };
        if !source_is_any_direct_identifier(source_operand) {
            return false;
        }
        aggregate_input_source(input, index)
            .is_some_and(|input_source| source_nodes_identical(source_operand, input_source))
    });
    if !arguments_match {
        return false;
    }
    let source_operands = source.operands.iter().flatten().collect::<Vec<_>>();
    source_operands.len() == 2
        && exact_source_function_operands_match(source, "COUNT", &source_operands, true)
}

fn aggregate_input_source(input: &RelExpr, index: usize) -> Option<&ScalarSourceProvenance> {
    match input {
        RelExpr::Project { exprs, .. } => exprs.get(index)?.source.as_ref(),
        _ => None,
    }
}

fn source_nodes_identical(left: &ScalarSourceProvenance, right: &ScalarSourceProvenance) -> bool {
    exact_source_nodes_identical(left, right)
}

fn source_has_exact_binding(source: &ScalarSourceProvenance) -> bool {
    source.node_id.as_deref().is_some_and(|id| {
        parse_exact_source_span(id).is_some() || (cfg!(test) && id.starts_with("test:"))
    }) && source.text.as_deref().is_some_and(|text| !text.is_empty())
}

fn exact_source_text(source: &ScalarSourceProvenance) -> Option<&str> {
    source_has_exact_binding(source)
        .then_some(source.text.as_deref())
        .flatten()
}

fn exact_source_tokens(source: &ScalarSourceProvenance) -> Option<Vec<AttestedSqlToken>> {
    tokenize_attested_sql(exact_source_text(source)?)
}

/// Remove only parentheses that enclose the complete token sequence. Source
/// AST nodes can retain redundant expression parentheses even though their
/// binary operands are exposed separately. Parentheses that close before the
/// final token belong to an operand and are deliberately preserved.
fn strip_complete_attested_parentheses(mut tokens: &[AttestedSqlToken]) -> &[AttestedSqlToken] {
    loop {
        if !matches!(tokens.first(), Some(AttestedSqlToken::LeftParen))
            || !matches!(tokens.last(), Some(AttestedSqlToken::RightParen))
        {
            return tokens;
        }
        let mut depth = 0usize;
        let mut complete = true;
        for (index, token) in tokens.iter().enumerate() {
            match token {
                AttestedSqlToken::LeftParen => depth += 1,
                AttestedSqlToken::RightParen => {
                    let Some(next_depth) = depth.checked_sub(1) else {
                        return tokens;
                    };
                    depth = next_depth;
                    if depth == 0 && index + 1 != tokens.len() {
                        complete = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if !complete || depth != 0 {
            return tokens;
        }
        tokens = &tokens[1..tokens.len() - 1];
    }
}

fn exact_source_binary_operands_match(
    source: &ScalarSourceProvenance,
    operator: AttestedSqlToken,
) -> bool {
    let [Some(left), Some(right)] = source.operands.as_slice() else {
        return false;
    };
    let Some(mut expected) = exact_source_tokens(left) else {
        return false;
    };
    let Some(right) = exact_source_tokens(right) else {
        return false;
    };
    expected.push(operator);
    expected.extend(right);
    exact_source_tokens(source)
        .is_some_and(|tokens| strip_complete_attested_parentheses(&tokens) == expected)
}

fn exact_source_nodes_identical(
    left: &ScalarSourceProvenance,
    right: &ScalarSourceProvenance,
) -> bool {
    source_has_exact_binding(left)
        && source_has_exact_binding(right)
        && left.node_id == right.node_id
        && left.text == right.text
}

fn exact_source_function_operands_match(
    source: &ScalarSourceProvenance,
    function: &str,
    operands: &[&ScalarSourceProvenance],
    distinct: bool,
) -> bool {
    let Some(source_tokens) = exact_source_tokens(source) else {
        return false;
    };
    if operands.is_empty() {
        return false;
    }
    let mut expected = vec![
        AttestedSqlToken::Identifier(function.to_ascii_lowercase()),
        AttestedSqlToken::LeftParen,
    ];
    if distinct {
        expected.push(AttestedSqlToken::Distinct);
    }
    for (index, operand) in operands.iter().enumerate() {
        let Some(operand_tokens) = exact_source_tokens(operand) else {
            return false;
        };
        if index != 0 {
            expected.push(AttestedSqlToken::Comma);
        }
        expected.extend(operand_tokens);
    }
    expected.push(AttestedSqlToken::RightParen);
    source_tokens == expected
}

fn exact_source_unary_function_has_direct_identifier(
    source: &ScalarSourceProvenance,
    function: &str,
) -> bool {
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    tokens
        .first()
        .is_some_and(|token| token_is_identifier(token, function))
        && matches!(tokens.get(1), Some(AttestedSqlToken::LeftParen))
        && direct_identifier_end(&tokens, 2).is_some_and(|end| {
            end + 1 == tokens.len() && matches!(tokens.get(end), Some(AttestedSqlToken::RightParen))
        })
}

fn exact_source_direct_identifier_chain(source: &ScalarSourceProvenance, expected: &str) -> bool {
    if source.clause_ownership.is_some() || !source_has_exact_binding(source) {
        return false;
    }
    let Some(tokens) = exact_source_tokens(source) else {
        return false;
    };
    if source
        .kind
        .as_deref()
        .is_none_or(|kind| !kind.eq_ignore_ascii_case("IDENTIFIER"))
        || source.operator.is_some()
        || direct_column_at(&tokens, 0, expected).is_none_or(|end| end != tokens.len())
    {
        return false;
    }
    match source.operands.as_slice() {
        [] => true,
        [Some(child)] => {
            exact_source_nodes_identical(source, child)
                && exact_source_direct_identifier_chain(child, expected)
        }
        _ => false,
    }
}

fn exact_source_unary_function<'a>(
    source: &'a ScalarSourceProvenance,
    function: &str,
) -> Option<&'a ScalarSourceProvenance> {
    if source.clause_ownership.is_some()
        || !source_has_exact_binding(source)
        || !source
            .kind
            .as_deref()
            .is_some_and(|kind| kind.eq_ignore_ascii_case("OTHER_FUNCTION"))
        || !source
            .operator
            .as_deref()
            .is_some_and(|operator| operator.eq_ignore_ascii_case(function))
    {
        return None;
    }
    let [Some(argument)] = source.operands.as_slice() else {
        return None;
    };
    if !source_has_exact_binding(argument) {
        return None;
    }
    exact_source_function_operands_match(source, function, &[argument], false).then_some(argument)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AttestedSqlToken {
    Identifier(String),
    Number(String),
    StringLiteral(String),
    Compare(String),
    In,
    Exists,
    Select,
    Union,
    Intersect,
    Except,
    All,
    Distinct,
    Dot,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    Comma,
    Colon,
    Plus,
    Minus,
    Multiply,
    Divide,
    Other,
}

fn tokenize_attested_sql(sql: &str) -> Option<Vec<AttestedSqlToken>> {
    fn postgres_identifier_start(ch: char) -> bool {
        ch.is_ascii_alphabetic() || ch == '_' || !ch.is_ascii()
    }

    fn postgres_identifier_part(ch: char) -> bool {
        postgres_identifier_start(ch) || ch.is_ascii_digit() || ch == '$'
    }

    fn postgres_dollar_tag_part(ch: char) -> bool {
        postgres_identifier_start(ch) || ch.is_ascii_digit()
    }

    let chars = sql.chars().collect::<Vec<_>>();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < chars.len() {
        let ch = chars[index];
        // PostgreSQL's scanner treats only ASCII space characters as SQL
        // whitespace. Every high-bit byte is an identifier character, even
        // when Unicode classifies the decoded code point as whitespace.
        if ch.is_ascii_whitespace() {
            index += 1;
            continue;
        }
        if ch == '-' && chars.get(index + 1) == Some(&'-') {
            index += 2;
            while index < chars.len() && !matches!(chars[index], '\n' | '\r') {
                index += 1;
            }
            continue;
        }
        if ch == '/' && chars.get(index + 1) == Some(&'*') {
            index += 2;
            let mut depth = 1usize;
            while index < chars.len() {
                if chars.get(index) == Some(&'/') && chars.get(index + 1) == Some(&'*') {
                    depth = depth.checked_add(1)?;
                    index += 2;
                } else if chars.get(index) == Some(&'*') && chars.get(index + 1) == Some(&'/') {
                    depth = depth.checked_sub(1)?;
                    index += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    index += 1;
                }
            }
            if depth != 0 {
                return None;
            }
            continue;
        }
        if matches!(ch, 'e' | 'E')
            && chars.get(index + 1) == Some(&'\'')
            && (index == 0 || !postgres_identifier_part(chars[index - 1]))
        {
            index += 2;
            let mut value = String::new();
            let mut closed = false;
            while index < chars.len() {
                match chars[index] {
                    '\\' => {
                        let escaped = *chars.get(index + 1)?;
                        value.push('\\');
                        value.push(escaped);
                        index += 2;
                    }
                    '\'' if chars.get(index + 1) == Some(&'\'') => {
                        value.push('\'');
                        index += 2;
                    }
                    '\'' => {
                        index += 1;
                        closed = true;
                        break;
                    }
                    ch => {
                        value.push(ch);
                        index += 1;
                    }
                }
            }
            if !closed {
                return None;
            }
            tokens.push(AttestedSqlToken::StringLiteral(value));
            continue;
        }
        if ch == '\'' {
            index += 1;
            let mut value = String::new();
            let mut closed = false;
            while index < chars.len() {
                if chars[index] == '\'' {
                    if chars.get(index + 1) == Some(&'\'') {
                        value.push('\'');
                        index += 2;
                    } else {
                        index += 1;
                        closed = true;
                        break;
                    }
                } else {
                    value.push(chars[index]);
                    index += 1;
                }
            }
            if !closed {
                return None;
            }
            tokens.push(AttestedSqlToken::StringLiteral(value));
            continue;
        }
        if ch == '"' {
            index += 1;
            let mut value = String::new();
            let mut closed = false;
            while index < chars.len() {
                if chars[index] == '"' {
                    if chars.get(index + 1) == Some(&'"') {
                        value.push('"');
                        index += 2;
                    } else {
                        index += 1;
                        closed = true;
                        break;
                    }
                } else {
                    value.push(chars[index]);
                    index += 1;
                }
            }
            if !closed {
                return None;
            }
            // Double quotes carry PostgreSQL's exact case-sensitive
            // identifier identity. Do not fold them together with unquoted
            // names.
            tokens.push(AttestedSqlToken::Identifier(value));
            continue;
        }
        if ch == '`' {
            // Calcite renders identifiers inside parent expressions with
            // backticks even though the independently parsed PostgreSQL leaf
            // may be unquoted or double-quoted. The content is already the
            // parser's canonical identifier identity, so preserve it exactly.
            index += 1;
            let mut value = String::new();
            let mut closed = false;
            while index < chars.len() {
                if chars[index] == '`' {
                    if chars.get(index + 1) == Some(&'`') {
                        value.push('`');
                        index += 2;
                    } else {
                        index += 1;
                        closed = true;
                        break;
                    }
                } else {
                    value.push(chars[index]);
                    index += 1;
                }
            }
            if !closed {
                return None;
            }
            tokens.push(AttestedSqlToken::Identifier(value));
            continue;
        }
        if ch == '$' && (index == 0 || !postgres_identifier_part(chars[index - 1])) {
            let delimiter_end = if chars.get(index + 1) == Some(&'$') {
                Some(index + 2)
            } else if chars
                .get(index + 1)
                .is_some_and(|ch| postgres_identifier_start(*ch))
            {
                let mut cursor = index + 2;
                while chars
                    .get(cursor)
                    .is_some_and(|ch| postgres_dollar_tag_part(*ch))
                {
                    cursor += 1;
                }
                (chars.get(cursor) == Some(&'$')).then_some(cursor + 1)
            } else {
                None
            };
            if let Some(delimiter_end) = delimiter_end {
                let delimiter = &chars[index..delimiter_end];
                let mut closing = delimiter_end;
                while closing + delimiter.len() <= chars.len()
                    && chars[closing..closing + delimiter.len()] != *delimiter
                {
                    closing += 1;
                }
                if closing + delimiter.len() > chars.len() {
                    return None;
                }
                tokens.push(AttestedSqlToken::StringLiteral(
                    chars[delimiter_end..closing].iter().collect(),
                ));
                index = closing + delimiter.len();
                continue;
            }
        }
        if postgres_identifier_start(ch) {
            let start = index;
            index += 1;
            while index < chars.len() && postgres_identifier_part(chars[index]) {
                index += 1;
            }
            let word = chars[start..index].iter().collect::<String>();
            let folded = word.to_ascii_lowercase();
            tokens.push(match folded.as_str() {
                "in" => AttestedSqlToken::In,
                "exists" => AttestedSqlToken::Exists,
                "select" => AttestedSqlToken::Select,
                "union" => AttestedSqlToken::Union,
                "intersect" => AttestedSqlToken::Intersect,
                "except" => AttestedSqlToken::Except,
                "all" => AttestedSqlToken::All,
                "distinct" => AttestedSqlToken::Distinct,
                // PostgreSQL folds every unquoted ASCII identifier to lower
                // case. Double-quoted identifiers and Calcite's canonical
                // backtick rendering are handled above and retain their
                // exact identity.
                _ => AttestedSqlToken::Identifier(folded),
            });
            continue;
        }
        if ch.is_ascii_digit() {
            let start = index;
            index += 1;
            while index < chars.len() && chars[index].is_ascii_digit() {
                index += 1;
            }
            tokens.push(AttestedSqlToken::Number(
                chars[start..index].iter().collect(),
            ));
            continue;
        }
        match ch {
            '.' => tokens.push(AttestedSqlToken::Dot),
            '(' => tokens.push(AttestedSqlToken::LeftParen),
            ')' => tokens.push(AttestedSqlToken::RightParen),
            '[' => tokens.push(AttestedSqlToken::LeftBracket),
            ']' => tokens.push(AttestedSqlToken::RightBracket),
            ',' => tokens.push(AttestedSqlToken::Comma),
            ':' => tokens.push(AttestedSqlToken::Colon),
            '+' => tokens.push(AttestedSqlToken::Plus),
            '-' => tokens.push(AttestedSqlToken::Minus),
            '*' => tokens.push(AttestedSqlToken::Multiply),
            '/' => tokens.push(AttestedSqlToken::Divide),
            '=' | '<' | '>' | '!' => {
                let mut operator = ch.to_string();
                if matches!(chars.get(index + 1), Some('=' | '>')) {
                    operator.push(chars[index + 1]);
                    index += 1;
                }
                tokens.push(AttestedSqlToken::Compare(operator));
            }
            _ => tokens.push(AttestedSqlToken::Other),
        }
        index += 1;
    }
    Some(tokens)
}

fn token_is_identifier(token: &AttestedSqlToken, expected: &str) -> bool {
    matches!(token, AttestedSqlToken::Identifier(value) if value == expected)
}

fn direct_column_at(tokens: &[AttestedSqlToken], start: usize, name: &str) -> Option<usize> {
    if token_is_identifier(tokens.get(start)?, name) {
        return Some(start + 1);
    }
    if matches!(tokens.get(start), Some(AttestedSqlToken::Identifier(_)))
        && matches!(tokens.get(start + 1), Some(AttestedSqlToken::Dot))
        && token_is_identifier(tokens.get(start + 2)?, name)
    {
        return Some(start + 3);
    }
    None
}

fn direct_identifier_end(tokens: &[AttestedSqlToken], start: usize) -> Option<usize> {
    if matches!(tokens.get(start), Some(AttestedSqlToken::Identifier(_))) {
        if matches!(tokens.get(start + 1), Some(AttestedSqlToken::Dot))
            && matches!(tokens.get(start + 2), Some(AttestedSqlToken::Identifier(_)))
        {
            return Some(start + 3);
        }
        return Some(start + 1);
    }
    None
}

#[derive(Debug, Clone)]
pub struct LoweringConfig {
    pub sql_time_zone: SqlTimeZone,
    pub sql_environment: SqlEnvironment,
}

impl Default for LoweringConfig {
    fn default() -> Self {
        Self {
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::default(),
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

    pub(super) fn has_fixed_offset_authority(&self) -> bool {
        matches!(self.kind, SqlTimeZoneKind::FixedOffset { .. })
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
            SqlTimeZoneKind::FixedOffset { offset_micros } => {
                local_micros.checked_sub(offset_micros)
            }
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
    /// Authoritative database schema for proof-producing query lowering.
    /// Calcite relational metadata is validated against this schema at every
    /// table-scan boundary before it can become a typed FormalSQL attribute.
    schema: Option<Schema>,
    correlations: Vec<CorrelationScope>,
    /// Names allocated for capture-avoiding barriers around scalar-subquery
    /// owners.  FormalSQL attributes are nominal, whereas Calcite local
    /// inputs are positional.  A deterministic allocator keeps those two
    /// representations aligned without relying on source spellings.
    next_scope_barrier: usize,
    scope_barrier_names: BTreeSet<String>,
    /// Statement-local CTE identities resolved before any definition or body
    /// is lowered. References become ordinary FormalSQL table leaves using
    /// these fresh internal relation names.
    query_bindings: BTreeMap<String, LoweredQueryBindingSource>,
}

#[derive(Debug, Clone)]
struct LoweredQueryBindingSource {
    relation: String,
    output: Vec<Column>,
    /// Provenance-enriched scope recovered from the already lowered CTE
    /// definition. PostgreSQL aggregate results can be typmodless NUMERIC
    /// while still having a statically known display scale; rebuilding this
    /// scope from Calcite's public row type would discard that distinction.
    lowered_scope: Option<Scope>,
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

pub(crate) use emit::{
    emit_rocq_bound_query_program_module_with_signatures,
    emit_rocq_query_expr_proof_module_for_mode,
};
use emit::{
    emit_rocq_bound_query_proof_module_for_mode, emit_rocq_query_program_module_with_signatures,
};
#[cfg(test)]
use emit::{
    emit_rocq_query_expr_proof_module, emit_rocq_query_module,
    emit_rocq_query_module_with_signatures, emit_trusted_proof_import_block,
    try_emit_rocq_query_module,
};

impl LoweringContext {
    fn new(config: LoweringConfig, schema: Option<&Schema>) -> Self {
        Self {
            diagnostics: Vec::new(),
            config,
            schema: schema.cloned(),
            correlations: Vec::new(),
            next_scope_barrier: 0,
            scope_barrier_names: BTreeSet::new(),
            query_bindings: BTreeMap::new(),
        }
    }

    fn has_authoritative_schema(&self) -> bool {
        self.schema.is_some()
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
            .enumerate()
            .map(|(index, binding)| {
                Some(CorrelationScope {
                    correlation: binding.correlation.clone(),
                    scope: self
                        .lower_scope(&format!("correlations[{index}].output"), &binding.output)?,
                    field_names: binding
                        .output
                        .iter()
                        .map(|column| column.name.clone())
                        .collect(),
                })
            })
            .collect::<Option<Vec<_>>>()?;
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

    fn lower_scope(&mut self, path: &str, columns: &[Column]) -> Option<Scope> {
        let attributes = columns
            .iter()
            .enumerate()
            .map(|(index, column)| {
                let ty = self.lower_attribute_type(
                    &format!("{path}[{index}]"),
                    column,
                    AttributeTypeContext::QueryInput,
                )?;
                Some(ScopeAttribute {
                    name: column.name.clone(),
                    visible_name: column.name.clone(),
                    formal_ty: ty,
                    numeric_dscale: numeric_dscale_for_type(ty),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Scope { attributes })
    }

    pub(super) fn lower_attribute_type(
        &mut self,
        path: &str,
        column: &Column,
        context: AttributeTypeContext,
    ) -> Option<FormalAttributeType> {
        if let Err(error) = column.ty.validate() {
            let (code, message) = match error {
                SqlTypeValidationError::DecimalTypmodPresence => (
                    "incomplete_numeric_typmod",
                    "NUMERIC/DECIMAL must either omit both typmod fields or provide both precision and scale.",
                ),
                SqlTypeValidationError::DecimalPrecision { .. }
                | SqlTypeValidationError::DecimalScale { .. } => (
                    "decimal_typmod_not_supported",
                    "FormalSQL Decimal currently supports PostgreSQL DECIMAL(p,s) for 1 <= p <= 1000 and 0 <= s <= 1000; negative scales are not modeled yet.",
                ),
                SqlTypeValidationError::TimestampPrecision { .. } => (
                    "timestamp_precision_not_supported",
                    "PostgreSQL TIMESTAMP and TIMESTAMPTZ precision must be between 0 and 6.",
                ),
                SqlTypeValidationError::CharacterLength { .. }
                | SqlTypeValidationError::MissingCharacterLength => (
                    "string_typmod_not_supported",
                    "PostgreSQL character type lengths must be present where required and within the supported PostgreSQL range.",
                ),
                SqlTypeValidationError::UnexpectedScale { .. }
                | SqlTypeValidationError::UnexpectedTypmod { .. } => (
                    context.unsupported_type_code(),
                    "The SQL type carries a typmod that its PostgreSQL type family does not accept.",
                ),
            };
            self.error(path, code, message);
            return None;
        }
        match &column.ty {
            SqlType::Null
                if matches!(
                    context,
                    AttributeTypeContext::QueryInput | AttributeTypeContext::QueryOutput
                ) =>
            {
                return Some(self.unresolved_null_postgres_type(path));
            }
            SqlType::Any | SqlType::Null => {
                self.error(
                    path,
                    context.unsupported_type_code(),
                    &context.unsupported_type_message(&column.ty),
                );
                return None;
            }
            _ => {}
        }
        Some(sql_type_to_formal_attribute_type(&column.ty))
    }

    pub(super) fn unresolved_null_postgres_type(&mut self, path: &str) -> FormalAttributeType {
        self.warning(
            path,
            "unresolved_null_resolved_as_text",
            "PostgreSQL resolves a still-unknown NULL in a SELECT or VALUES output to TEXT. Logos uses the FormalSQL string carrier; contextual coercions must already be reflected by Calcite as a concrete type.",
        );
        FormalAttributeType::String {
            typmod: SqlStringType::Text,
        }
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
            .unwrap_or(attribute.visible_name.as_str());
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AttributeTypeContext {
    Schema,
    QueryInput,
    QueryOutput,
}

impl AttributeTypeContext {
    fn unsupported_type_code(self) -> &'static str {
        match self {
            AttributeTypeContext::Schema => "schema_type_not_supported",
            AttributeTypeContext::QueryInput | AttributeTypeContext::QueryOutput => {
                "query_type_not_supported"
            }
        }
    }

    fn unsupported_type_message(self, ty: &SqlType) -> String {
        match self {
            AttributeTypeContext::Schema => {
                format!("FormalSQL proof-of-concept schemas cannot soundly encode {ty:?}.")
            }
            AttributeTypeContext::QueryInput | AttributeTypeContext::QueryOutput => {
                format!("FormalSQL proof-of-concept queries cannot soundly encode {ty:?}.")
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Scope {
    attributes: Vec<ScopeAttribute>,
}

#[derive(Debug, Clone)]
struct ScopeAttribute {
    /// Capture-avoiding FormalSQL binding used in emitted terms and aliases.
    name: String,
    /// SQL-visible name retained across internal alpha-renaming.  This is
    /// metadata for restoring an operator's public output; it never affects
    /// nominal lookup in FormalSQL.
    visible_name: String,
    formal_ty: FormalAttributeType,
    numeric_dscale: Option<NumericDscaleProvenance>,
}

impl Scope {
    fn attribute(&self, index: usize) -> Option<ScopeAttribute> {
        self.attributes.get(index).cloned()
    }
}

fn numeric_dscale_for_type(ty: FormalAttributeType) -> Option<NumericDscaleProvenance> {
    match ty {
        FormalAttributeType::Decimal { scale, .. } => Some(NumericDscaleProvenance::Exact(scale)),
        FormalAttributeType::Z | FormalAttributeType::Int32 | FormalAttributeType::Int64 => {
            Some(NumericDscaleProvenance::Exact(0))
        }
        _ => None,
    }
}

fn sql_type_to_formal_attribute_type(ty: &SqlType) -> FormalAttributeType {
    match ty {
        SqlType::Integer => FormalAttributeType::Int32,
        SqlType::BigInt => FormalAttributeType::Int64,
        SqlType::Float => FormalAttributeType::Float,
        SqlType::Double => FormalAttributeType::Double,
        SqlType::Decimal {
            precision: None,
            scale: None,
        } => FormalAttributeType::Numeric,
        SqlType::Decimal {
            precision: Some(precision),
            scale: Some(scale),
        } => FormalAttributeType::Decimal {
            precision: *precision,
            scale: *scale,
        },
        SqlType::Decimal { .. } => {
            unreachable!("incomplete NUMERIC typmod reached FormalAttributeType conversion")
        }
        SqlType::String(typmod) => FormalAttributeType::String { typmod: *typmod },
        SqlType::Date => FormalAttributeType::Date,
        SqlType::Time => FormalAttributeType::Time,
        SqlType::Timestamp { precision } => FormalAttributeType::Timestamp {
            precision: *precision,
        },
        SqlType::TimestampTz { precision } => FormalAttributeType::Timestamptz {
            precision: *precision,
        },
        SqlType::Boolean => FormalAttributeType::Bool,
        SqlType::Any | SqlType::Null => {
            unreachable!("unsupported SQL type reached FormalAttributeType conversion")
        }
    }
}

fn timestamp_precision(precision: Option<u32>) -> u32 {
    precision.unwrap_or(DEFAULT_TIMESTAMP_PRECISION)
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

fn has_unique_scope_names(scope: &Scope) -> bool {
    scope
        .attributes
        .iter()
        .enumerate()
        .all(|(index, attribute)| {
            scope
                .attributes
                .iter()
                .skip(index + 1)
                .all(|other| other.name != attribute.name)
        })
}

fn scope_has_well_formed_auxiliary_dscales(scope: &Scope, visible_len: usize) -> bool {
    if scope.attributes.len() < visible_len || !has_unique_scope_names(scope) {
        return false;
    }
    let referenced = scope.attributes[..visible_len]
        .iter()
        .filter_map(|attribute| match &attribute.numeric_dscale {
            Some(NumericDscaleProvenance::Attribute(name))
                if attribute.formal_ty == FormalAttributeType::Numeric =>
            {
                Some(name.clone())
            }
            Some(NumericDscaleProvenance::Attribute(_)) => Some(String::new()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    if referenced.contains("") {
        return false;
    }
    let auxiliaries = scope.attributes[visible_len..]
        .iter()
        .filter(|attribute| attribute.formal_ty == FormalAttributeType::Z)
        .map(|attribute| attribute.name.clone())
        .collect::<BTreeSet<_>>();
    auxiliaries.len() == scope.attributes.len() - visible_len && referenced == auxiliaries
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
