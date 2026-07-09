use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::calcite::rel_text_hydrate::{
    hydrate_rel_from_text_plan, rel_contains_unavailable_aggregate_grouping_sets,
    rel_contains_unavailable_values,
};
use crate::calcite::scalar::{
    classify_calcite_scalar, classify_scalar_op, collect_scalar_expr, collect_scalar_exprs,
    parse_calcite_scalar_ast, split_calcite_arg_list, try_calcite_scalar,
};
use crate::calcite::text_plan::parse_calcite_text_plan;
use crate::calcite::ty::parse_calcite_sql_type;
use crate::calcite::{
    CalciteAggregateCall, CalciteFile, CalciteRel, CalciteRex, CalciteSarg, CalciteSargRange,
    CalciteWindow,
};
use crate::error::{Error, Result};
use crate::ir::{
    AggregateCall, AggregateModifiers, Column, CorrelationBinding, Feature, JoinType, LogosIrFile,
    Query, RelExpr, SargAst, SargBound, SargItem, ScalarAst, ScalarClass, ScalarExpr, Schema,
    SetOp, SortDirection, SortKey, SortNullDirection, SqlType, Table, ValuesTuples, WindowAst,
    WindowOrderKey,
};

pub fn convert_file(path: impl AsRef<Path>) -> Result<LogosIrFile> {
    let path = path.as_ref();
    let text = std::fs::read_to_string(path).map_err(|source| Error::Read {
        path: path.to_path_buf(),
        source,
    })?;
    let raw: CalciteFile = serde_json::from_str(&text).map_err(|source| Error::Json {
        path: path.to_path_buf(),
        source,
    })?;
    convert_raw_file(raw)
}

pub fn convert_raw_file(raw: CalciteFile) -> Result<LogosIrFile> {
    let schema = Schema {
        tables: raw
            .schema
            .into_iter()
            .map(|table| {
                let columns = table
                    .columns
                    .into_iter()
                    .map(|column| {
                        Ok(Column {
                            name: column.name,
                            ty: parse_sql_type_with_typmod(
                                column.full_type.as_deref().unwrap_or(&column.ty),
                                column.precision,
                                column.scale,
                            )?,
                            nullable: true,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Table {
                    name: table.name,
                    columns,
                })
            })
            .collect::<Result<Vec<_>>>()?,
    };
    let schema_index = schema_column_index(&schema);

    let mut queries = Vec::with_capacity(raw.queries.len());
    for query in raw.queries {
        if let Some(error) = query.error {
            return Err(Error::CalciteQueryError(error));
        }
        let rel = query.rel.ok_or_else(|| {
            Error::CalciteQueryError("query has neither rel nor error".to_owned())
        })?;
        let mut features = BTreeSet::new();
        let source_sql = query.sql;
        let rel_text = query.rel_text;
        let calcite_rel_plan = rel_text.as_deref().and_then(parse_calcite_text_plan);
        let mut rel = convert_rel(rel, &mut features, &schema_index)?;
        if let Some(plan) = &calcite_rel_plan {
            hydrate_rel_from_text_plan(&mut rel, plan);
            if !rel_contains_unavailable_values(&rel) {
                features.remove(&Feature::ValuesTuplesUnavailable);
            }
            if !rel_contains_unavailable_aggregate_grouping_sets(&rel) {
                features.remove(&Feature::AggregateGroupingSetsUnavailable);
            }
        }
        collect_scalar_features(&rel, &mut features);
        collect_type_features_from_schema(&schema, &mut features);
        collect_type_features(&rel, &mut features);
        detect_query_text_features(source_sql.as_deref(), rel_text.as_deref(), &mut features);
        queries.push(Query {
            source_sql,
            output: rel.output().to_vec(),
            rel,
            features: features.into_iter().collect(),
            calcite_rel_plan,
            calcite_rel_text: rel_text,
        });
    }

    Ok(LogosIrFile { schema, queries })
}

type SchemaColumnIndex = BTreeMap<String, Vec<Column>>;

fn convert_rel(
    raw: CalciteRel,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<RelExpr> {
    match raw.rel_type.as_str() {
        "LogicalTableScan" => {
            features.insert(Feature::TableScan);
            let output = if let Some(columns) = schema_index.get(&table_key(&raw.table)) {
                columns.clone()
            } else {
                convert_row_type(raw.row_type)?
            };
            Ok(RelExpr::TableScan {
                table: raw.table,
                output,
            })
        }
        "LogicalProject" => {
            features.insert(Feature::Projection);
            let correlations = convert_correlation_bindings(&raw.variables_set, &raw.row_type)?;
            let input = one_input("LogicalProject", raw.inputs, features, schema_index)?;
            let exprs =
                convert_project_exprs(raw.projects, raw.project_rex, features, schema_index)?;
            let mut output = convert_row_type(raw.row_type)?;
            inherit_project_input_ref_types(&mut output, &exprs, input.output());
            inherit_project_type_annotation_types(&mut output, &exprs)?;
            Ok(RelExpr::Project {
                input: Box::new(input),
                exprs,
                correlations,
                output,
            })
        }
        "LogicalFilter" => {
            features.insert(Feature::Selection);
            let correlations = convert_correlation_bindings(&raw.variables_set, &raw.row_type)?;
            let input = one_input("LogicalFilter", raw.inputs, features, schema_index)?;
            let condition = required_rex_scalar(
                "LogicalFilter",
                "conditionRex",
                raw.condition_rex,
                features,
                schema_index,
            )?;
            Ok(RelExpr::Filter {
                input: Box::new(input),
                predicate: condition,
                correlations,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalJoin" => {
            let correlations = convert_correlation_bindings(&raw.variables_set, &raw.row_type)?;
            let actual = raw.inputs.len();
            if actual != 2 {
                return Err(Error::Arity {
                    node: "LogicalJoin",
                    expected: "2",
                    actual,
                });
            }
            let mut inputs = raw.inputs.into_iter();
            let left = convert_rel(
                inputs.next().expect("checked arity"),
                features,
                schema_index,
            )?;
            let right = convert_rel(
                inputs.next().expect("checked arity"),
                features,
                schema_index,
            )?;
            let join_type = parse_join_type(required_field(
                "LogicalJoin",
                "joinType",
                raw.join_type.as_deref(),
            )?)?;
            match join_type {
                JoinType::Inner => {
                    features.insert(Feature::InnerJoin);
                }
                JoinType::Left | JoinType::Right | JoinType::Full => {
                    features.insert(Feature::OuterJoin);
                    features.insert(Feature::FormalSqlUnsupported);
                }
                JoinType::Semi => {
                    features.insert(Feature::SemiJoin);
                    features.insert(Feature::FormalSqlUnsupported);
                }
                JoinType::Anti => {
                    features.insert(Feature::AntiJoin);
                    features.insert(Feature::FormalSqlUnsupported);
                }
            }
            let condition = required_rex_scalar(
                "LogicalJoin",
                "conditionRex",
                raw.condition_rex,
                features,
                schema_index,
            )?;
            Ok(RelExpr::Join {
                left: Box::new(left),
                right: Box::new(right),
                join_type,
                condition,
                correlations,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalAggregate" => {
            features.insert(Feature::Aggregation);
            features.insert(Feature::FormalSqlUnsupported);
            let input = one_input("LogicalAggregate", raw.inputs, features, schema_index)?;
            let group_keys = parse_group_set(required_field(
                "LogicalAggregate",
                "groupSet",
                raw.group_set.as_deref(),
            )?)?;
            let grouping_sets = raw
                .group_sets
                .as_ref()
                .map(|sets| parse_group_sets(sets))
                .transpose()?;
            match &grouping_sets {
                Some(sets) if sets.len() == 1 && sets[0] == group_keys => {}
                Some(_) => {
                    features.insert(Feature::GroupingSets);
                    features.insert(Feature::FormalSqlUnsupported);
                }
                None => {
                    features.insert(Feature::AggregateGroupingSetsUnavailable);
                    features.insert(Feature::FormalSqlUnsupported);
                }
            }
            let agg_calls = convert_aggregate_calls(
                raw.agg_call_details,
                raw.agg_calls,
                input.output(),
                features,
                schema_index,
            )?;
            for call in &agg_calls {
                collect_aggregate_features(call, features);
                if call.distinct {
                    features.insert(Feature::DistinctAggregate);
                    features.insert(Feature::FormalSqlUnsupported);
                }
                if call.filter.is_some() {
                    features.insert(Feature::FilteredAggregate);
                    features.insert(Feature::FormalSqlUnsupported);
                }
            }
            Ok(RelExpr::Aggregate {
                input: Box::new(input),
                group_keys,
                grouping_sets,
                agg_calls,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalSort" => {
            features.insert(Feature::Sort);
            if !raw.collation.is_empty() {
                features.insert(Feature::FormalSqlOrderSensitive);
                features.insert(Feature::FormalSqlUnsupported);
            }
            if raw.fetch.is_some() {
                features.insert(Feature::Limit);
                features.insert(Feature::FormalSqlOrderSensitive);
                features.insert(Feature::FormalSqlUnsupported);
            }
            if raw.offset.is_some() {
                features.insert(Feature::Offset);
                features.insert(Feature::FormalSqlOrderSensitive);
                features.insert(Feature::FormalSqlUnsupported);
            }
            let input = one_input("LogicalSort", raw.inputs, features, schema_index)?;
            let collation: Vec<_> = raw
                .collation
                .into_iter()
                .map(|key| {
                    Ok(SortKey {
                        field_index: key.field_index,
                        direction: parse_sort_direction(&key.direction)?,
                        null_direction: key
                            .null_direction
                            .as_deref()
                            .map(parse_sort_null_direction)
                            .transpose()?
                            .flatten(),
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(RelExpr::Sort {
                input: Box::new(input),
                collation,
                fetch: optional_rex_scalar(
                    "LogicalSort",
                    "fetchRex",
                    raw.fetch,
                    raw.fetch_rex,
                    features,
                    schema_index,
                )?,
                offset: optional_rex_scalar(
                    "LogicalSort",
                    "offsetRex",
                    raw.offset,
                    raw.offset_rex,
                    features,
                    schema_index,
                )?,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalUnion" | "LogicalMinus" | "LogicalIntersect" => {
            let op = parse_set_op(raw.set_op.as_deref(), raw.rel_type.as_str())?;
            match op {
                SetOp::Union => {
                    features.insert(Feature::Union);
                    features.insert(Feature::FormalSqlUnsupported);
                }
                SetOp::Intersect => {
                    features.insert(Feature::Intersect);
                    features.insert(Feature::FormalSqlUnsupported);
                }
                SetOp::Except => {
                    features.insert(Feature::Except);
                    features.insert(Feature::FormalSqlUnsupported);
                }
            }
            let all = required_field("LogicalSetOp", "all", raw.all)?;
            if !all {
                features.insert(Feature::SetDistinct);
                features.insert(Feature::FormalSqlUnsupported);
            }
            let inputs = raw
                .inputs
                .into_iter()
                .map(|input| convert_rel(input, features, schema_index))
                .collect::<Result<Vec<_>>>()?;
            Ok(RelExpr::Set {
                op,
                all,
                inputs,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalValues" => {
            features.insert(Feature::Values);
            let tuples = match raw.tuples {
                Some(rows) => ValuesTuples::Rows {
                    rows: rows
                        .into_iter()
                        .map(|row| {
                            row.into_iter()
                                .map(|value| calcite_rex_scalar(value, features, schema_index))
                                .collect::<Result<Vec<_>>>()
                        })
                        .collect::<Result<Vec<_>>>()?,
                },
                None => {
                    features.insert(Feature::ValuesTuplesUnavailable);
                    features.insert(Feature::FormalSqlUnsupported);
                    ValuesTuples::UnavailableFromCalcite
                }
            };
            Ok(RelExpr::Values {
                tuples,
                output: convert_row_type(raw.row_type)?,
            })
        }
        other => Err(Error::UnsupportedRelNode(other.to_owned())),
    }
}

fn convert_project_exprs(
    projects: Vec<String>,
    project_rex: Vec<CalciteRex>,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<Vec<ScalarExpr>> {
    if project_rex.len() != projects.len() {
        return Err(if project_rex.is_empty() {
            Error::MissingField {
                node: "LogicalProject",
                field: "projectRex",
            }
        } else {
            Error::FieldArity {
                node: "LogicalProject",
                field: "projectRex",
                expected: projects.len(),
                actual: project_rex.len(),
            }
        });
    }
    project_rex
        .into_iter()
        .map(|rex| calcite_rex_scalar(rex, features, schema_index))
        .collect()
}

fn required_rex_scalar(
    node: &'static str,
    field: &'static str,
    rex: Option<CalciteRex>,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<ScalarExpr> {
    calcite_rex_scalar(required_field(node, field, rex)?, features, schema_index)
}

fn optional_rex_scalar(
    node: &'static str,
    rex_field: &'static str,
    text: Option<String>,
    rex: Option<CalciteRex>,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<Option<ScalarExpr>> {
    match (text, rex) {
        (_, Some(rex)) => calcite_rex_scalar(rex, features, schema_index).map(Some),
        (Some(_), None) => Err(Error::MissingField {
            node,
            field: rex_field,
        }),
        (None, None) => Ok(None),
    }
}

fn calcite_rex_scalar(
    rex: CalciteRex,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<ScalarExpr> {
    let raw = rex
        .text
        .clone()
        .unwrap_or_else(|| "<structured RexNode>".to_owned());
    let parsed = calcite_rex_ast(&rex, features, schema_index)?;
    let class = classify_calcite_scalar(&raw);
    Ok(ScalarExpr { raw, class, parsed })
}

fn calcite_rex_ast(
    rex: &CalciteRex,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<ScalarAst> {
    if is_rex_subquery(rex) {
        let subquery_rel = rex
            .subquery_rel
            .as_ref()
            .ok_or_else(|| Error::MissingField {
                node: "RexSubQuery",
                field: "subqueryRel",
            })?;
        let operator = rex
            .operator
            .clone()
            .or_else(|| rex.op_kind.clone())
            .ok_or_else(|| Error::InvalidScalar(rex_debug_text(rex)))?;
        let mut args = rex
            .operands
            .iter()
            .map(|operand| calcite_rex_ast(operand, features, schema_index))
            .collect::<Result<Vec<_>>>()?;
        let rel = convert_rel((**subquery_rel).clone(), features, schema_index)?;
        args.push(ScalarAst::RelSubquery { rel: Box::new(rel) });
        let op = classify_scalar_op(&operator);
        return Ok(ScalarAst::Call { operator, op, args });
    }
    if is_rex_field_access(rex) {
        return calcite_rex_field_access_ast(rex);
    }
    if let Some(index) = rex.index {
        return Ok(ScalarAst::InputRef { index });
    }
    if is_rex_literal(rex) {
        return calcite_rex_literal_ast(rex);
    }
    if let Some(window) = &rex.window {
        return calcite_rex_window_ast(rex, window, features, schema_index);
    }
    if is_rex_call(rex) {
        let operator = rex
            .operator
            .clone()
            .or_else(|| rex.op_kind.clone())
            .ok_or_else(|| Error::InvalidScalar(rex_debug_text(rex)))?;
        let args = rex
            .operands
            .iter()
            .map(|operand| calcite_rex_ast(operand, features, schema_index))
            .collect::<Result<Vec<_>>>()?;
        let op = classify_scalar_op(&operator);
        let call = ScalarAst::Call { operator, op, args };
        if is_cast_kind(rex) {
            if let Some(ty) = rex_type_annotation(rex) {
                return Ok(ScalarAst::TypeAnnotation {
                    expr: Box::new(call),
                    ty,
                });
            }
        }
        return Ok(call);
    }
    Err(Error::InvalidScalar(rex_debug_text(rex)))
}

fn calcite_rex_field_access_ast(rex: &CalciteRex) -> Result<ScalarAst> {
    let reference = rex
        .reference_expr
        .as_ref()
        .ok_or_else(|| Error::MissingField {
            node: "RexFieldAccess",
            field: "referenceExpr",
        })?;
    if !is_rex_correl_variable(reference) {
        return Err(Error::InvalidScalar(format!(
            "unsupported RexFieldAccess reference: {}",
            rex_debug_text(rex)
        )));
    }
    let correlation = reference
        .correlation_name
        .clone()
        .or_else(|| reference.text.clone())
        .ok_or_else(|| Error::MissingField {
            node: "RexCorrelVariable",
            field: "correlationName",
        })?;
    let field = rex.field_name.clone().ok_or_else(|| Error::MissingField {
        node: "RexFieldAccess",
        field: "fieldName",
    })?;
    let ty = rex
        .ty
        .as_deref()
        .map(|ty| parse_sql_type_with_typmod(ty, rex.precision, rex.scale))
        .transpose()?
        .ok_or_else(|| Error::MissingField {
            node: "RexFieldAccess",
            field: "type",
        })?;
    Ok(ScalarAst::CorrelatedRef {
        correlation,
        field,
        index: rex.field_index,
        ty,
    })
}

fn calcite_rex_literal_ast(rex: &CalciteRex) -> Result<ScalarAst> {
    if let Some(sarg) = &rex.sarg {
        return Ok(ScalarAst::Sarg {
            raw: sarg.text.clone(),
            parsed: calcite_sarg_ast(sarg),
        });
    }
    if let Some(ty) = rex_interval_annotation(rex) {
        let raw = rex
            .interval_literal
            .as_deref()
            .or(rex.literal_value_as_string.as_deref())
            .or(rex.literal_value2.as_deref())
            .or(rex.literal_value.as_deref())
            .unwrap_or_else(|| rex.text.as_deref().unwrap_or(""));
        return Ok(ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: raw.to_owned(),
            }),
            ty,
        });
    }
    if let Some(ty) = rex_type_annotation(rex) {
        if ty.eq_ignore_ascii_case("DATE") {
            let raw = rex
                .literal_value_as_string
                .as_deref()
                .or(rex.literal_value2.as_deref())
                .or(rex.literal_value.as_deref())
                .unwrap_or_else(|| rex.text.as_deref().unwrap_or(""));
            return Ok(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: raw.to_owned(),
                }),
                ty,
            });
        }
        if type_annotation_is_timestamp_tz(&ty) {
            let precision = parse_type_precision(&ty).unwrap_or(6);
            if let Some(raw) = timestamptz_literal_from_source(rex, precision) {
                return Ok(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal { raw }),
                    ty,
                });
            }
            if let Some(raw) = timestamp_literal_text(rex) {
                if is_null_literal(&raw) || timestamp_literal_has_explicit_offset(&raw) {
                    return Ok(ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal { raw }),
                        ty,
                    });
                }
            }
            return Err(Error::InvalidScalar(format!(
                "TIMESTAMP WITH TIME ZONE literal requires source SQL or an explicit literal offset because Calcite Rex may not preserve the original time-zone semantics: {}",
                rex_debug_text(rex)
            )));
        }
        if type_annotation_is_timestamp(&ty) {
            let precision = parse_type_precision(&ty).unwrap_or(6);
            if precision > 3 {
                // Calcite 1.42 folds CAST(string AS TIMESTAMP(p)) through a millisecond-based
                // runtime path for p > 3, so the structured Rex literal may contain .123000
                // even when the original SQL had .123456.  If the wrapper attached the
                // original source expression, prefer it over every folded Rex representation.
                if let Some(raw) = timestamp_literal_from_source_cast(rex, precision) {
                    return Ok(ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal { raw }),
                        ty,
                    });
                }
                if !timestamp_literal_has_submillisecond_rex_text(rex) {
                    return Err(Error::InvalidScalar(format!(
                        "TIMESTAMP({precision}) literal requires exact sub-millisecond value, but Calcite Rex text does not preserve it: {}",
                        rex_debug_text(rex)
                    )));
                }
            }
            if let Some(raw) = timestamp_literal_text(rex) {
                return Ok(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal { raw }),
                    ty,
                });
            }
        }
        if type_annotation_head(&ty).is_some_and(|head| matches!(head, "DECIMAL" | "NUMERIC"))
            && let Some((raw, source_ty)) = decimal_literal_from_source_cast(rex)
        {
            return Ok(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal { raw }),
                ty: source_ty,
            });
        }
    }
    if is_character_type(rex) {
        if let Some(value) = rex
            .literal_value_as_string
            .as_deref()
            .or(rex.literal_value2.as_deref())
        {
            return Ok(ScalarAst::Literal {
                raw: sql_string_literal(value),
            });
        }
    }
    if let Some(ty) = rex_type_annotation(rex) {
        if let Some(raw) = structured_literal_value(rex) {
            return Ok(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal { raw }),
                ty,
            });
        }
    }
    if let Some(text) = &rex.text {
        if let Ok(ast) = parse_calcite_scalar_ast(text) {
            return Ok(ast);
        }
    }
    Ok(ScalarAst::Literal {
        raw: rex.text.clone().unwrap_or_else(|| {
            rex.literal_value_as_string
                .clone()
                .or_else(|| rex.literal_value2.clone())
                .or_else(|| rex.literal_value.clone())
                .unwrap_or_default()
        }),
    })
}

fn convert_aggregate_calls(
    details: Vec<CalciteAggregateCall>,
    text_calls: Vec<String>,
    input_output: &[Column],
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<Vec<AggregateCall>> {
    if !details.is_empty() {
        return details
            .into_iter()
            .map(|detail| convert_aggregate_call_detail(detail, input_output, features))
            .collect();
    }
    text_calls
        .into_iter()
        .map(|call| parse_aggregate_call_with_context(call, features, schema_index))
        .collect()
}

fn convert_aggregate_call_detail(
    detail: CalciteAggregateCall,
    input_output: &[Column],
    features: &mut BTreeSet<Feature>,
) -> Result<AggregateCall> {
    let collation = detail
        .collation
        .iter()
        .map(|key| {
            Ok(SortKey {
                field_index: key.field_index,
                direction: parse_sort_direction(&key.direction)?,
                null_direction: key
                    .null_direction
                    .as_deref()
                    .map(parse_sort_null_direction)
                    .transpose()?
                    .flatten(),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    if detail.approximate
        || detail.ignore_nulls
        || !detail.distinct_keys.is_empty()
        || !collation.is_empty()
    {
        features.insert(Feature::AdvancedAggregateFunction);
        features.insert(Feature::FormalSqlUnsupported);
    }
    let modifiers = AggregateModifiers {
        approximate: detail.approximate,
        ignore_nulls: detail.ignore_nulls,
        distinct_keys: detail.distinct_keys,
        collation,
    };
    let args = detail
        .arg_list
        .into_iter()
        .map(|index| {
            if index < input_output.len() {
                Ok(input_ref_scalar(index))
            } else {
                Err(Error::InvalidScalar(format!(
                    "invalid aggregate argList index {index}"
                )))
            }
        })
        .collect::<Result<Vec<_>>>()?;
    let filter = detail
        .filter_arg
        .filter(|index| *index >= 0)
        .map(|index| {
            usize::try_from(index)
                .ok()
                .filter(|index| *index < input_output.len())
                .map(input_ref_scalar)
                .ok_or_else(|| Error::InvalidScalar(format!("invalid aggregate filterArg {index}")))
        })
        .transpose()?;
    Ok(AggregateCall {
        raw: detail.text,
        function: detail.function,
        distinct: detail.distinct,
        modifiers,
        args,
        filter,
    })
}

fn input_ref_scalar(index: usize) -> ScalarExpr {
    ScalarExpr {
        raw: format!("${index}"),
        class: ScalarClass::InputRef { index },
        parsed: ScalarAst::InputRef { index },
    }
}

fn calcite_rex_window_ast(
    rex: &CalciteRex,
    window: &CalciteWindow,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<ScalarAst> {
    let function = rex
        .operator
        .clone()
        .or_else(|| rex.op_kind.clone())
        .ok_or_else(|| Error::InvalidScalar(rex_debug_text(rex)))?;
    let args = rex
        .operands
        .iter()
        .map(|operand| calcite_rex_ast(operand, features, schema_index))
        .collect::<Result<Vec<_>>>()?;
    let partition_by = window
        .partition_keys
        .iter()
        .map(|key| calcite_rex_ast(key, features, schema_index))
        .collect::<Result<Vec<_>>>()?;
    let order_by = window
        .order_keys
        .iter()
        .map(|key| {
            Ok(WindowOrderKey {
                expr: calcite_rex_ast(&key.expr, features, schema_index)?,
                direction: Some(parse_sort_direction(&key.direction)?),
                null_direction: parse_sort_null_direction(&key.null_direction)?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let frame = match (&window.lower_bound, &window.upper_bound) {
        (Some(lower), Some(upper)) => Some(format!(
            "{} BETWEEN {} AND {}",
            if window.is_rows { "ROWS" } else { "RANGE" },
            lower.text,
            upper.text
        )),
        (Some(bound), None) | (None, Some(bound)) => Some(format!(
            "{} {}",
            if window.is_rows { "ROWS" } else { "RANGE" },
            bound.text
        )),
        (None, None) => None,
    };
    Ok(ScalarAst::Window {
        raw: rex_debug_text(rex),
        structured: true,
        parsed: WindowAst {
            function,
            args,
            partition_by,
            order_by,
            distinct: rex.distinct.unwrap_or(false),
            ignore_nulls: rex.ignore_nulls.unwrap_or(false),
            exclude: window.exclude.clone(),
            frame,
        },
    })
}

fn calcite_sarg_ast(sarg: &CalciteSarg) -> SargAst {
    SargAst {
        items: sarg.ranges.iter().map(calcite_sarg_item).collect(),
        null_as: sarg.null_as.clone(),
        point_count: sarg.point_count,
        is_all: sarg.is_all,
        is_none: sarg.is_none,
        is_points: sarg.is_points,
        is_complemented_points: sarg.is_complemented_points,
        ty: None,
    }
}

fn calcite_sarg_item(range: &CalciteSargRange) -> SargItem {
    let lower = range
        .lower
        .as_ref()
        .map(|raw| SargBound { raw: raw.clone() });
    let upper = range
        .upper
        .as_ref()
        .map(|raw| SargBound { raw: raw.clone() });
    if range.has_lower_bound
        && range.has_upper_bound
        && range.lower == range.upper
        && range
            .lower_bound_type
            .as_deref()
            .is_some_and(|ty| ty.eq_ignore_ascii_case("CLOSED"))
        && range
            .upper_bound_type
            .as_deref()
            .is_some_and(|ty| ty.eq_ignore_ascii_case("CLOSED"))
    {
        return SargItem::Point {
            raw: range.lower.clone().unwrap_or_else(|| range.text.clone()),
        };
    }
    SargItem::Range {
        raw: range.text.clone(),
        lower,
        upper,
        lower_inclusive: range
            .lower_bound_type
            .as_deref()
            .is_some_and(|ty| ty.eq_ignore_ascii_case("CLOSED")),
        upper_inclusive: range
            .upper_bound_type
            .as_deref()
            .is_some_and(|ty| ty.eq_ignore_ascii_case("CLOSED")),
    }
}

fn rex_interval_annotation(rex: &CalciteRex) -> Option<String> {
    let type_name = rex
        .interval_type_name
        .as_deref()
        .or(rex.literal_type_name.as_deref())
        .or(rex.ty.as_deref())?;
    if !type_name.to_ascii_uppercase().starts_with("INTERVAL") {
        return None;
    }
    let unit = rex
        .interval_unit
        .as_deref()
        .map(|unit| unit.replace('_', " "))
        .or_else(|| {
            type_name
                .to_ascii_uppercase()
                .strip_prefix("INTERVAL_")
                .map(|unit| unit.replace('_', " "))
        })?;
    Some(format!("INTERVAL {unit}"))
}

fn rex_type_annotation(rex: &CalciteRex) -> Option<String> {
    if let Some(ty) = rex
        .source_sql
        .as_deref()
        .and_then(parse_cast_type_annotation_source)
    {
        return Some(ty);
    }
    let ty = rex.ty.as_deref()?.trim();
    let normalized = normalize_type_annotation(ty)?;
    if normalized == "TIMESTAMP" || normalized == "TIMESTAMP_WITH_TIME_ZONE" {
        if let Some(precision) = rex
            .precision
            .and_then(|precision| u32::try_from(precision).ok())
            .or_else(|| parse_type_precision(ty))
        {
            return Some(format!("{normalized}({precision})"));
        }
    }
    if normalized == "DECIMAL" {
        let precision = rex
            .precision
            .and_then(|precision| u32::try_from(precision).ok())
            .or_else(|| parse_type_precision(ty));
        let scale = rex
            .scale
            .and_then(|scale| u32::try_from(scale).ok())
            .or_else(|| parse_type_scale(ty));
        let negative_scale = rex.scale.is_some_and(|scale| scale < 0)
            || parse_type_scale_i32(ty).is_some_and(|scale| scale < 0);
        if let Some(precision) = precision {
            if let Some(scale) = scale {
                return Some(format!("DECIMAL({precision},{scale})"));
            }
            if !negative_scale {
                return Some(format!("DECIMAL({precision},0)"));
            }
        }
    }
    Some(normalized)
}

fn normalize_type_annotation(ty: &str) -> Option<String> {
    let upper = ty.trim().to_ascii_uppercase();
    let head = type_annotation_head(&upper)?;
    match head {
        "DATE" => Some("DATE".to_owned()),
        "INTEGER" | "INT" => Some("INTEGER".to_owned()),
        "BIGINT" => Some("BIGINT".to_owned()),
        "SMALLINT" => Some("SMALLINT".to_owned()),
        "TINYINT" => Some("TINYINT".to_owned()),
        "DECIMAL" | "NUMERIC" => Some("DECIMAL".to_owned()),
        "FLOAT" | "REAL" => Some("FLOAT".to_owned()),
        "DOUBLE" => Some("DOUBLE".to_owned()),
        "VARCHAR" => Some("VARCHAR".to_owned()),
        "CHAR" => Some("CHAR".to_owned()),
        "BOOLEAN" | "BOOL" => Some("BOOLEAN".to_owned()),
        "TIME" => Some("TIME".to_owned()),
        "TIMESTAMP" => {
            if upper.contains("WITH") && upper.contains("TIME ZONE") {
                Some("TIMESTAMP_WITH_TIME_ZONE".to_owned())
            } else {
                Some("TIMESTAMP".to_owned())
            }
        }
        "TIMESTAMPTZ"
        | "TIMESTAMPZ"
        | "TIMESTAMP_TZ"
        | "TIMESTAMP_WITH_TIME_ZONE"
        | "TIMESTAMP_WITH_LOCAL_TIME_ZONE" => Some("TIMESTAMP_WITH_TIME_ZONE".to_owned()),
        _ if upper.starts_with("INTERVAL") => Some(upper.replace('_', " ")),
        _ => None,
    }
}

fn type_annotation_head(ty: &str) -> Option<&str> {
    ty.trim()
        .split(|ch: char| ch.is_ascii_whitespace() || ch == '(')
        .next()
}

fn type_annotation_is_timestamp(ty: &str) -> bool {
    let upper = ty.trim().to_ascii_uppercase();
    let head = upper
        .split(|ch: char| ch.is_ascii_whitespace() || ch == '(')
        .next();
    matches!(head, Some("TIMESTAMP")) && !(upper.contains("WITH") && upper.contains("TIME ZONE"))
}

fn type_annotation_is_timestamp_tz(ty: &str) -> bool {
    let upper = ty.trim().to_ascii_uppercase();
    let head = upper
        .split(|ch: char| ch.is_ascii_whitespace() || ch == '(')
        .next();
    matches!(
        head,
        Some("TIMESTAMPTZ")
            | Some("TIMESTAMPZ")
            | Some("TIMESTAMP_WITH_TIME_ZONE")
            | Some("TIMESTAMP_WITH_LOCAL_TIME_ZONE")
    ) || (matches!(head, Some("TIMESTAMP"))
        && upper.contains("WITH")
        && upper.contains("TIME ZONE"))
}

fn is_character_type(rex: &CalciteRex) -> bool {
    rex.ty
        .as_deref()
        .and_then(normalize_type_annotation)
        .is_some_and(|ty| matches!(ty.as_str(), "CHAR" | "VARCHAR"))
}

fn timestamp_literal_text(rex: &CalciteRex) -> Option<String> {
    if let Some(value) = &rex.timestamp_literal {
        return Some(value.clone());
    }
    if let Some(value) = &rex.literal_value_as_string {
        return Some(value.clone());
    }
    rex.text.as_deref().and_then(|text| {
        text.split_once(":TIMESTAMP")
            .map(|(value, _)| value.to_owned())
    })
}

fn timestamp_literal_has_submillisecond_rex_text(rex: &CalciteRex) -> bool {
    rex.text
        .as_deref()
        .and_then(|text| text.split_once(":TIMESTAMP").map(|(value, _)| value))
        .and_then(|value| value.split_once('.').map(|(_, fraction)| fraction))
        .is_some_and(|fraction| fraction.len() > 3)
}

fn timestamp_literal_from_source_cast(rex: &CalciteRex, precision: u32) -> Option<String> {
    parse_timestamp_cast_source(rex.source_sql.as_deref()?, precision, false)
}

fn timestamptz_literal_from_source(rex: &CalciteRex, precision: u32) -> Option<String> {
    let source = rex.source_sql.as_deref()?;
    parse_timestamp_cast_source(source, precision, true)
        .or_else(|| parse_timestamp_tz_literal_source(source, precision))
}

fn parse_timestamp_cast_source(
    source: &str,
    expected_precision: u32,
    allow_time_zone: bool,
) -> Option<String> {
    let mut parser = SourceParser::new(source);
    parser.consume_keyword("CAST")?;
    parser.consume_char('(')?;
    let value = parser.consume_cast_literal()?;
    parser.consume_keyword("AS")?;
    if allow_time_zone && parser.consume_keyword("TIMESTAMPTZ").is_some() {
        if let Some(precision) = parser.consume_precision()? {
            if precision != expected_precision {
                return None;
            }
        }
        parser.consume_char(')')?;
        parser.finish()?;
        return Some(value);
    }
    parser.consume_keyword("TIMESTAMP")?;
    if let Some(precision) = parser.consume_precision()? {
        if precision != expected_precision {
            return None;
        }
    }
    if parser.consume_optional_keywords(&["WITH", "LOCAL", "TIME", "ZONE"]) && !allow_time_zone {
        return None;
    }
    if parser.consume_optional_keywords(&["WITH", "TIME", "ZONE"]) && !allow_time_zone {
        return None;
    }
    parser.consume_char(')')?;
    parser.finish()?;
    Some(value)
}

fn parse_cast_type_annotation_source(source: &str) -> Option<String> {
    let mut parser = SourceParser::new(source);
    parser.consume_keyword("CAST")?;
    parser.consume_char('(')?;
    parser.consume_until_top_level_as()?;
    parse_cast_target_type_annotation(&mut parser)
}

fn parse_cast_target_type_annotation(parser: &mut SourceParser<'_>) -> Option<String> {
    if parser
        .peek_keyword("DECIMAL")
        .or_else(|| parser.peek_keyword("NUMERIC"))
        .is_some()
    {
        let normalized = if parser.consume_keyword("DECIMAL").is_some() {
            "DECIMAL"
        } else {
            parser.consume_keyword("NUMERIC")?;
            "NUMERIC"
        };
        let precision_scale = parser.consume_precision_scale()?;
        parser.consume_char(')')?;
        parser.finish()?;
        return Some(match precision_scale {
            Some((precision, Some(scale))) => format!("{normalized}({precision},{scale})"),
            Some((precision, None)) => format!("{normalized}({precision})"),
            None => normalized.to_owned(),
        });
    }
    let is_timestamptz = if parser.consume_keyword("TIMESTAMPTZ").is_some() {
        true
    } else {
        parser.consume_keyword("TIMESTAMP")?;
        false
    };
    let precision = parser.consume_precision()?;
    let has_local_time_zone = parser.consume_optional_keywords(&["WITH", "LOCAL", "TIME", "ZONE"]);
    let has_time_zone = parser.consume_optional_keywords(&["WITH", "TIME", "ZONE"]);
    parser.consume_char(')')?;
    parser.finish()?;

    let normalized = if is_timestamptz || has_local_time_zone || has_time_zone {
        "TIMESTAMP_WITH_TIME_ZONE"
    } else {
        "TIMESTAMP"
    };
    Some(match precision {
        Some(precision) => format!("{normalized}({precision})"),
        None => normalized.to_owned(),
    })
}

fn decimal_literal_from_source_cast(rex: &CalciteRex) -> Option<(String, String)> {
    let mut parser = SourceParser::new(rex.source_sql.as_deref()?);
    parser.consume_keyword("CAST")?;
    parser.consume_char('(')?;
    let value = parser.consume_decimal_cast_literal()?;
    parser.consume_keyword("AS")?;
    let normalized = if parser.consume_keyword("DECIMAL").is_some() {
        "DECIMAL"
    } else {
        parser.consume_keyword("NUMERIC")?;
        "NUMERIC"
    };
    let precision_scale = parser.consume_precision_scale()?;
    parser.consume_char(')')?;
    parser.finish()?;
    let ty = match precision_scale {
        Some((precision, Some(scale))) => format!("{normalized}({precision},{scale})"),
        Some((precision, None)) => format!("{normalized}({precision})"),
        None => normalized.to_owned(),
    };
    Some((value, ty))
}

fn parse_timestamp_tz_literal_source(source: &str, expected_precision: u32) -> Option<String> {
    let mut parser = SourceParser::new(source);
    if parser.consume_keyword("TIMESTAMPTZ").is_none() {
        parser.consume_keyword("TIMESTAMP")?;
        if let Some(precision) = parser.consume_precision()? {
            if precision != expected_precision {
                return None;
            }
        }
        if !parser.consume_optional_keywords(&["WITH", "LOCAL", "TIME", "ZONE"])
            && !parser.consume_optional_keywords(&["WITH", "TIME", "ZONE"])
        {
            return None;
        }
    } else if let Some(precision) = parser.consume_precision()? {
        if precision != expected_precision {
            return None;
        }
    }
    let value = parser.consume_sql_string_literal()?;
    parser.finish()?;
    Some(value)
}

fn is_null_literal(raw: &str) -> bool {
    raw.trim().eq_ignore_ascii_case("null")
}

fn timestamp_literal_has_explicit_offset(raw: &str) -> bool {
    let value = raw.trim().trim_matches('\'');
    if value.ends_with('Z') || value.ends_with('z') {
        return true;
    }
    value
        .find(|ch| ch == ' ' || ch == 'T')
        .map(|index| &value[index + 1..])
        .is_some_and(|tail| tail.contains('+') || tail.contains('-'))
}

fn sql_string_literal(value: &str) -> String {
    format!("'{}'", value.replace('\'', "''"))
}

fn structured_literal_value(rex: &CalciteRex) -> Option<String> {
    rex.literal_value_as_string
        .clone()
        .or_else(|| rex.literal_value.clone())
        .or_else(|| rex.literal_value2.clone())
        .or_else(|| rex.text.clone())
}

fn is_rex_literal(rex: &CalciteRex) -> bool {
    matches!(rex.class.as_deref(), Some("RexLiteral")) || rex.literal_type_name.is_some()
}

fn is_rex_call(rex: &CalciteRex) -> bool {
    matches!(rex.class.as_deref(), Some("RexCall"))
        || rex.operator.is_some()
        || !rex.operands.is_empty()
}

fn is_rex_subquery(rex: &CalciteRex) -> bool {
    matches!(rex.class.as_deref(), Some("RexSubQuery"))
}

fn is_rex_field_access(rex: &CalciteRex) -> bool {
    matches!(rex.class.as_deref(), Some("RexFieldAccess"))
}

fn is_rex_correl_variable(rex: &CalciteRex) -> bool {
    matches!(rex.class.as_deref(), Some("RexCorrelVariable")) || rex.correlation_name.is_some()
}

fn is_cast_kind(rex: &CalciteRex) -> bool {
    rex.kind
        .as_deref()
        .or(rex.op_kind.as_deref())
        .is_some_and(|kind| kind.eq_ignore_ascii_case("CAST"))
}

fn rex_debug_text(rex: &CalciteRex) -> String {
    rex.text
        .clone()
        .or_else(|| rex.class.clone())
        .unwrap_or_else(|| "<structured RexNode>".to_owned())
}

struct SourceParser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> SourceParser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn consume_keyword(&mut self, keyword: &str) -> Option<()> {
        self.skip_ws();
        let rest = self.input.get(self.pos..)?;
        if rest.len() < keyword.len() || !rest[..keyword.len()].eq_ignore_ascii_case(keyword) {
            return None;
        }
        self.pos += keyword.len();
        Some(())
    }

    fn consume_optional_keywords(&mut self, keywords: &[&str]) -> bool {
        let saved = self.pos;
        for keyword in keywords {
            if self.consume_keyword(keyword).is_none() {
                self.pos = saved;
                return false;
            }
        }
        true
    }

    fn peek_keyword(&mut self, keyword: &str) -> Option<()> {
        let saved = self.pos;
        let result = self.consume_keyword(keyword);
        self.pos = saved;
        result
    }

    fn consume_char(&mut self, ch: char) -> Option<()> {
        self.skip_ws();
        let rest = self.input.get(self.pos..)?;
        let mut chars = rest.chars();
        if chars.next()? != ch {
            return None;
        }
        self.pos += ch.len_utf8();
        Some(())
    }

    fn consume_precision(&mut self) -> Option<Option<u32>> {
        self.skip_ws();
        if !self.input.get(self.pos..)?.starts_with('(') {
            return Some(None);
        }
        self.pos += 1;
        self.skip_ws();
        let start = self.pos;
        while let Some(ch) = self.input.get(self.pos..)?.chars().next() {
            if !ch.is_ascii_digit() {
                break;
            }
            self.pos += ch.len_utf8();
        }
        if self.pos == start {
            return None;
        }
        let precision = self.input.get(start..self.pos)?.parse().ok()?;
        self.consume_char(')')?;
        Some(Some(precision))
    }

    fn consume_precision_scale(&mut self) -> Option<Option<(u32, Option<u32>)>> {
        self.skip_ws();
        if !self.input.get(self.pos..)?.starts_with('(') {
            return Some(None);
        }
        self.pos += 1;
        let precision = self.consume_unsigned_integer()?;
        self.skip_ws();
        let scale = if self.input.get(self.pos..)?.starts_with(',') {
            self.pos += 1;
            Some(self.consume_unsigned_integer()?)
        } else {
            None
        };
        self.consume_char(')')?;
        Some(Some((precision, scale)))
    }

    fn consume_unsigned_integer(&mut self) -> Option<u32> {
        self.skip_ws();
        let start = self.pos;
        while let Some(ch) = self.input.get(self.pos..)?.chars().next() {
            if !ch.is_ascii_digit() {
                break;
            }
            self.pos += ch.len_utf8();
        }
        (self.pos > start).then(|| self.input.get(start..self.pos)?.parse().ok())?
    }

    fn consume_sql_string_literal(&mut self) -> Option<String> {
        self.skip_ws();
        if !self.input.get(self.pos..)?.starts_with('\'') {
            return None;
        }
        self.pos += 1;
        let mut value = String::new();
        while self.pos < self.input.len() {
            let ch = self.input.get(self.pos..)?.chars().next()?;
            self.pos += ch.len_utf8();
            if ch != '\'' {
                value.push(ch);
                continue;
            }
            if self.input.get(self.pos..)?.starts_with('\'') {
                value.push('\'');
                self.pos += 1;
                continue;
            }
            return Some(value);
        }
        None
    }

    fn consume_decimal_cast_literal(&mut self) -> Option<String> {
        self.consume_sql_string_literal()
            .or_else(|| self.consume_numeric_literal())
            .or_else(|| {
                self.consume_keyword("NULL")?;
                Some("null".to_owned())
            })
    }

    fn consume_numeric_literal(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.pos;
        if self
            .input
            .get(self.pos..)?
            .chars()
            .next()
            .is_some_and(|ch| ch == '+' || ch == '-')
        {
            self.pos += 1;
        }
        let mut saw_digit = false;
        while let Some(ch) = self.input.get(self.pos..)?.chars().next() {
            if !ch.is_ascii_digit() {
                break;
            }
            saw_digit = true;
            self.pos += ch.len_utf8();
        }
        if self.input.get(self.pos..)?.starts_with('.') {
            self.pos += 1;
            while let Some(ch) = self.input.get(self.pos..)?.chars().next() {
                if !ch.is_ascii_digit() {
                    break;
                }
                saw_digit = true;
                self.pos += ch.len_utf8();
            }
        }
        saw_digit.then(|| self.input.get(start..self.pos).map(str::to_owned))?
    }

    fn consume_cast_literal(&mut self) -> Option<String> {
        self.consume_sql_string_literal().or_else(|| {
            self.consume_keyword("NULL")?;
            Some("null".to_owned())
        })
    }

    fn consume_until_top_level_as(&mut self) -> Option<()> {
        let mut depth = 0usize;
        loop {
            self.skip_ws();
            if depth == 0 && self.peek_keyword("AS").is_some() {
                return self.consume_keyword("AS");
            }
            let ch = self.input.get(self.pos..)?.chars().next()?;
            match ch {
                '\'' => {
                    self.consume_sql_string_literal()?;
                }
                '(' => {
                    depth = depth.checked_add(1)?;
                    self.pos += ch.len_utf8();
                }
                ')' => {
                    depth = depth.checked_sub(1)?;
                    self.pos += ch.len_utf8();
                }
                _ => {
                    self.pos += ch.len_utf8();
                }
            }
        }
    }

    fn finish(&mut self) -> Option<()> {
        self.skip_ws();
        (self.pos == self.input.len()).then_some(())
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self
            .input
            .get(self.pos..)
            .and_then(|rest| rest.chars().next())
        {
            if !ch.is_whitespace() {
                break;
            }
            self.pos += ch.len_utf8();
        }
    }
}

fn required_field<T>(node: &'static str, field: &'static str, value: Option<T>) -> Result<T> {
    value.ok_or(Error::MissingField { node, field })
}

fn schema_column_index(schema: &Schema) -> SchemaColumnIndex {
    schema
        .tables
        .iter()
        .map(|table| (table_key(&[table.name.clone()]), table.columns.clone()))
        .collect()
}

fn table_key(table: &[String]) -> String {
    table
        .last()
        .map(|name| name.to_ascii_lowercase())
        .unwrap_or_default()
}

fn inherit_project_input_ref_types(output: &mut [Column], exprs: &[ScalarExpr], input: &[Column]) {
    for (column, expr) in output.iter_mut().zip(exprs) {
        let ScalarAst::InputRef { index } = &expr.parsed else {
            continue;
        };
        if let Some(source) = input.get(*index) {
            inherit_column_type(column, source);
        }
    }
}

fn inherit_project_type_annotation_types(
    output: &mut [Column],
    exprs: &[ScalarExpr],
) -> Result<()> {
    for (column, expr) in output.iter_mut().zip(exprs) {
        let ScalarAst::TypeAnnotation { ty, .. } = &expr.parsed else {
            continue;
        };
        column.ty = parse_sql_type(ty)?;
    }
    Ok(())
}

fn inherit_column_type(column: &mut Column, source: &Column) {
    column.ty = source.ty.clone();
}

fn one_input(
    node: &'static str,
    inputs: Vec<CalciteRel>,
    features: &mut BTreeSet<Feature>,
    schema_index: &SchemaColumnIndex,
) -> Result<RelExpr> {
    let actual = inputs.len();
    if actual != 1 {
        return Err(Error::Arity {
            node,
            expected: "1",
            actual,
        });
    }
    convert_rel(
        inputs.into_iter().next().expect("checked arity"),
        features,
        schema_index,
    )
}

fn convert_row_type(row_type: Vec<crate::calcite::CalciteField>) -> Result<Vec<Column>> {
    row_type
        .into_iter()
        .map(|field| {
            Ok(Column {
                name: field.name,
                ty: parse_sql_type_with_typmod(&field.ty, field.precision, field.scale)?,
                nullable: field.nullable,
            })
        })
        .collect()
}

fn convert_correlation_bindings(
    variables_set: &[String],
    row_type: &[crate::calcite::CalciteField],
) -> Result<Vec<CorrelationBinding>> {
    if variables_set.is_empty() {
        return Ok(Vec::new());
    }
    let output = convert_row_type(row_type.to_vec())?;
    Ok(variables_set
        .iter()
        .map(|correlation| CorrelationBinding {
            correlation: correlation.clone(),
            output: output.clone(),
        })
        .collect())
}

fn parse_sql_type(value: &str) -> Result<SqlType> {
    parse_calcite_sql_type(value)
}

fn parse_sql_type_with_typmod(
    value: &str,
    structured_precision: Option<i32>,
    structured_scale: Option<i32>,
) -> Result<SqlType> {
    Ok(parse_sql_type(value)?.with_typmod(
        type_precision(value, structured_precision),
        type_scale(value, structured_precision, structured_scale),
    ))
}

fn type_precision(ty: &str, structured_precision: Option<i32>) -> Option<u32> {
    structured_precision
        .and_then(|precision| u32::try_from(precision).ok())
        .or_else(|| parse_type_precision(ty))
}

fn parse_type_precision(ty: &str) -> Option<u32> {
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    ty[start..end].split(',').next()?.trim().parse().ok()
}

fn type_scale(
    ty: &str,
    structured_precision: Option<i32>,
    structured_scale: Option<i32>,
) -> Option<u32> {
    if structured_scale.is_some_and(|scale| scale < 0)
        || parse_type_scale_i32(ty).is_some_and(|scale| scale < 0)
    {
        return None;
    }
    structured_scale
        .and_then(|scale| u32::try_from(scale).ok())
        .or_else(|| parse_type_scale(ty))
        .or_else(|| {
            let decimal = type_annotation_head(ty).is_some_and(|head| {
                matches!(head.to_ascii_uppercase().as_str(), "DECIMAL" | "NUMERIC")
            });
            let has_precision =
                structured_precision.is_some() || parse_type_precision(ty).is_some();
            (decimal && has_precision).then_some(0)
        })
}

fn parse_type_scale(ty: &str) -> Option<u32> {
    u32::try_from(parse_type_scale_i32(ty)?).ok()
}

fn parse_type_scale_i32(ty: &str) -> Option<i32> {
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    let mut parts = ty[start..end].split(',');
    parts.next()?;
    parts.next()?.trim().parse().ok()
}

fn parse_join_type(value: &str) -> Result<JoinType> {
    match value.to_ascii_uppercase().as_str() {
        "INNER" => Ok(JoinType::Inner),
        "LEFT" => Ok(JoinType::Left),
        "RIGHT" => Ok(JoinType::Right),
        "FULL" => Ok(JoinType::Full),
        "SEMI" => Ok(JoinType::Semi),
        "ANTI" => Ok(JoinType::Anti),
        _ => Err(Error::UnsupportedJoinType(value.to_owned())),
    }
}

fn parse_set_op(value: Option<&str>, fallback_rel_type: &str) -> Result<SetOp> {
    match value
        .unwrap_or(fallback_rel_type)
        .to_ascii_uppercase()
        .as_str()
    {
        "UNION" | "LOGICALUNION" => Ok(SetOp::Union),
        "INTERSECT" | "LOGICALINTERSECT" => Ok(SetOp::Intersect),
        "EXCEPT" | "MINUS" | "LOGICALMINUS" => Ok(SetOp::Except),
        _ => Err(Error::UnsupportedSetOp(
            value.unwrap_or(fallback_rel_type).to_owned(),
        )),
    }
}

fn parse_sort_direction(value: &str) -> Result<SortDirection> {
    match value.to_ascii_uppercase().as_str() {
        "ASCENDING" => Ok(SortDirection::Ascending),
        "DESCENDING" => Ok(SortDirection::Descending),
        "STRICTLY_ASCENDING" => Ok(SortDirection::StrictlyAscending),
        "STRICTLY_DESCENDING" => Ok(SortDirection::StrictlyDescending),
        "CLUSTERED" => Ok(SortDirection::Clustered),
        _ => Err(Error::UnsupportedSortDirection(value.to_owned())),
    }
}

fn parse_sort_null_direction(value: &str) -> Result<Option<SortNullDirection>> {
    match value.to_ascii_uppercase().as_str() {
        "FIRST" => Ok(Some(SortNullDirection::First)),
        "LAST" => Ok(Some(SortNullDirection::Last)),
        "UNSPECIFIED" => Ok(None),
        _ => Err(Error::UnsupportedSortDirection(value.to_owned())),
    }
}

fn parse_group_set(value: &str) -> Result<Vec<usize>> {
    let trimmed = value.trim();
    let inner = trimmed
        .strip_prefix('{')
        .and_then(|v| v.strip_suffix('}'))
        .ok_or_else(|| Error::InvalidGroupSet(value.to_owned()))?
        .trim();
    if inner.is_empty() {
        return Ok(Vec::new());
    }
    inner
        .split(',')
        .map(|part| {
            part.trim()
                .parse::<usize>()
                .map_err(|_| Error::InvalidGroupSet(value.to_owned()))
        })
        .collect()
}

fn parse_group_sets(values: &[String]) -> Result<Vec<Vec<usize>>> {
    values
        .iter()
        .map(|value| parse_group_set(value))
        .collect::<Result<Vec<_>>>()
}

fn parse_aggregate_call(raw: String) -> Result<AggregateCall> {
    let filter = raw
        .rsplit_once(" FILTER ")
        .map(|(_, filter)| try_calcite_scalar(filter.trim().to_owned()))
        .transpose()?;
    let head = raw
        .rsplit_once(" FILTER ")
        .map(|(head, _)| head)
        .unwrap_or(&raw)
        .trim();
    let (function, args_part) = head
        .split_once('(')
        .map(|(name, rest)| (name.trim().to_owned(), rest.trim_end_matches(')').trim()))
        .ok_or_else(|| Error::InvalidAggregateCall(raw.clone()))?;
    if function.is_empty() || !head.ends_with(')') {
        return Err(Error::InvalidAggregateCall(raw));
    }
    let (distinct, args_part) = args_part
        .strip_prefix("DISTINCT ")
        .map(|rest| (true, rest))
        .unwrap_or((false, args_part));
    let args = if args_part.is_empty() {
        Vec::new()
    } else {
        split_calcite_arg_list(args_part)
            .ok_or_else(|| Error::InvalidAggregateCall(raw.clone()))?
            .into_iter()
            .map(|arg| try_calcite_scalar(arg.trim().to_owned()))
            .collect::<Result<Vec<_>>>()?
    };
    Ok(AggregateCall {
        raw,
        function,
        distinct,
        modifiers: AggregateModifiers::default(),
        args,
        filter,
    })
}

fn parse_aggregate_call_with_context(
    raw: String,
    _features: &mut BTreeSet<Feature>,
    _schema_index: &SchemaColumnIndex,
) -> Result<AggregateCall> {
    parse_aggregate_call(raw)
}

fn collect_aggregate_features(call: &AggregateCall, features: &mut BTreeSet<Feature>) {
    match call.function.to_ascii_uppercase().as_str() {
        "COUNT" | "SUM" | "AVG" | "MIN" | "MAX" => {
            features.insert(Feature::BasicAggregateFunction);
        }
        "GROUPING" => {
            features.insert(Feature::GroupingFunction);
            features.insert(Feature::GroupingSets);
            features.insert(Feature::AdvancedAggregateFunction);
            features.insert(Feature::FormalSqlUnsupported);
        }
        _ => {
            features.insert(Feature::AdvancedAggregateFunction);
            features.insert(Feature::FormalSqlUnsupported);
        }
    }
}

fn detect_query_text_features(
    source_sql: Option<&str>,
    rel_text: Option<&str>,
    features: &mut BTreeSet<Feature>,
) {
    for text in [source_sql, rel_text].into_iter().flatten() {
        let upper = text.to_ascii_uppercase();
        if upper.contains("ROLLUP") {
            features.insert(Feature::Rollup);
            features.insert(Feature::GroupingSets);
            features.insert(Feature::FormalSqlUnsupported);
        }
        if upper.contains("GROUPING SETS") {
            features.insert(Feature::GroupingSets);
            features.insert(Feature::FormalSqlUnsupported);
        }
        if upper.contains("CUBE") {
            features.insert(Feature::Cube);
            features.insert(Feature::GroupingSets);
            features.insert(Feature::FormalSqlUnsupported);
        }
        if upper.contains(" OVER ") || upper.contains("OVER(") {
            features.insert(Feature::WindowFunction);
            features.insert(Feature::FormalSqlUnsupported);
        }
    }
}

fn collect_type_features_from_schema(schema: &Schema, features: &mut BTreeSet<Feature>) {
    for table in &schema.tables {
        collect_column_type_features(&table.columns, features);
    }
}

fn collect_type_features(rel: &RelExpr, features: &mut BTreeSet<Feature>) {
    collect_column_type_features(rel.output(), features);
    match rel {
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
        RelExpr::Project { input, .. }
        | RelExpr::Filter { input, .. }
        | RelExpr::Aggregate { input, .. }
        | RelExpr::Sort { input, .. } => collect_type_features(input, features),
        RelExpr::Join { left, right, .. } => {
            collect_type_features(left, features);
            collect_type_features(right, features);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_type_features(input, features);
            }
        }
    }
}

fn collect_column_type_features(columns: &[Column], features: &mut BTreeSet<Feature>) {
    if columns
        .iter()
        .any(|column| matches!(column.ty, SqlType::Any))
    {
        features.insert(Feature::AnySqlType);
        features.insert(Feature::FormalSqlUnsupported);
    }
    if columns
        .iter()
        .any(|column| matches!(column.ty, SqlType::Null))
    {
        features.insert(Feature::NullSqlType);
    }
}

fn collect_scalar_features(rel: &RelExpr, features: &mut BTreeSet<Feature>) {
    match rel {
        RelExpr::TableScan { .. } | RelExpr::Values { .. } => {}
        RelExpr::Project { input, exprs, .. } => {
            collect_scalar_exprs(exprs.iter(), features);
            collect_scalar_features(input, features);
        }
        RelExpr::Filter {
            input, predicate, ..
        } => {
            collect_scalar_expr(predicate, features);
            collect_scalar_features(input, features);
        }
        RelExpr::Join {
            left,
            right,
            condition,
            ..
        } => {
            collect_scalar_expr(condition, features);
            collect_scalar_features(left, features);
            collect_scalar_features(right, features);
        }
        RelExpr::Aggregate {
            input, agg_calls, ..
        } => {
            for call in agg_calls {
                collect_scalar_exprs(call.args.iter(), features);
                if let Some(filter) = &call.filter {
                    collect_scalar_expr(filter, features);
                }
            }
            collect_scalar_features(input, features);
        }
        RelExpr::Sort {
            input,
            fetch,
            offset,
            ..
        } => {
            if let Some(fetch) = fetch {
                collect_scalar_expr(fetch, features);
            }
            if let Some(offset) = offset {
                collect_scalar_expr(offset, features);
            }
            collect_scalar_features(input, features);
        }
        RelExpr::Set { inputs, .. } => {
            for input in inputs {
                collect_scalar_features(input, features);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::CalciteFile;
    use crate::ir::ScalarOp;

    #[test]
    fn converts_basic_project_filter_scan() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select a from R where a = 1",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                  "projects": ["$0"],
                  "projectRex": [
                    {"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "INTEGER", "index": 0}
                  ],
                  "inputs": [{
                    "type": "LogicalFilter",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "condition": "=($0, 1)",
                    "conditionRex": {
                      "kind": "EQUALS",
                      "class": "RexCall",
                      "text": "=($0, 1)",
                      "type": "BOOLEAN",
                      "operator": "=",
                      "opKind": "EQUALS",
                      "operands": [
                        {"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "INTEGER", "index": 0},
                        {"kind": "LITERAL", "class": "RexLiteral", "text": "1", "type": "INTEGER", "literalTypeName": "INTEGER", "literalValue": "1", "literalValue2": "1"}
                      ]
                    },
                    "inputs": [{
                      "type": "LogicalTableScan",
                      "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                      "table": ["R"],
                      "inputs": []
                    }]
                  }]
                },
                "relText": "LogicalProject(a=[$0])"
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(ir.schema.tables[0].name, "R");
        assert_eq!(ir.queries.len(), 1);
        assert!(ir.queries[0].features.contains(&Feature::TableScan));
        assert!(ir.queries[0].features.contains(&Feature::Selection));
        assert!(ir.queries[0].features.contains(&Feature::Projection));
    }

    #[test]
    fn structured_rex_interval_preserves_sql_literal_unit_value() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [
                {"name": "t", "columns": [
                  {"name": "d", "type": "DATE"},
                  {"name": "x", "type": "INTEGER"}
                ]}
              ],
              "queries": [{
                "sql": "select x from t where d < cast('1993-11-01' as date) + interval '30' day",
                "rel": {
                  "type": "LogicalFilter",
                  "rowType": [
                    {"name": "d", "type": "DATE", "nullable": true},
                    {"name": "x", "type": "INTEGER", "nullable": true}
                  ],
                  "condition": "<($0, +(CAST('1993-11-01'):DATE NOT NULL, 2592000000:INTERVAL DAY))",
                  "conditionRex": {
                    "kind": "LESS_THAN",
                    "class": "RexCall",
                    "text": "<($0, +(CAST('1993-11-01'):DATE NOT NULL, 2592000000:INTERVAL DAY))",
                    "type": "BOOLEAN",
                    "operator": "<",
                    "opKind": "LESS_THAN",
                    "operands": [
                      {"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "DATE", "index": 0},
                      {
                        "kind": "PLUS",
                        "class": "RexCall",
                        "text": "+(CAST('1993-11-01'):DATE NOT NULL, 2592000000:INTERVAL DAY)",
                        "type": "DATE",
                        "operator": "+",
                        "opKind": "PLUS",
                        "operands": [
                          {
                            "kind": "CAST",
                            "class": "RexCall",
                            "text": "CAST('1993-11-01'):DATE NOT NULL",
                            "type": "DATE",
                            "operator": "CAST",
                            "opKind": "CAST",
                            "operands": [
                              {
                                "kind": "LITERAL",
                                "class": "RexLiteral",
                                "text": "'1993-11-01'",
                                "type": "CHAR",
                                "literalTypeName": "CHAR",
                                "literalValueAsString": "1993-11-01"
                              }
                            ]
                          },
                          {
                            "kind": "LITERAL",
                            "class": "RexLiteral",
                            "text": "2592000000:INTERVAL DAY",
                            "type": "INTERVAL_DAY",
                            "literalTypeName": "INTERVAL_DAY",
                            "literalValue": "2592000000",
                            "literalValue2": "2592000000",
                            "literalValueAsString": "30",
                            "intervalTypeName": "INTERVAL_DAY",
                            "intervalLiteral": "30",
                            "intervalInternalValue": "2592000000",
                            "intervalUnit": "DAY"
                          }
                        ]
                      }
                    ]
                  },
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [
                      {"name": "d", "type": "DATE", "nullable": true},
                      {"name": "x", "type": "INTEGER", "nullable": true}
                    ],
                    "table": ["t"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Filter { predicate, .. } = &ir.queries[0].rel else {
            panic!("expected filter");
        };
        let ScalarAst::Call { args, .. } = &predicate.parsed else {
            panic!("expected parsed comparison");
        };
        let ScalarAst::Call {
            args: plus_args, ..
        } = &args[1]
        else {
            panic!("expected date addition");
        };
        let ScalarAst::TypeAnnotation { expr, ty } = &plus_args[1] else {
            panic!("expected interval annotation");
        };
        assert_eq!(ty, "INTERVAL DAY");
        assert_eq!(
            &**expr,
            &ScalarAst::Literal {
                raw: "30".to_owned()
            }
        );
    }

    #[test]
    fn structured_rex_literal_preserves_textual_type_annotation() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select cast(null as integer) as n from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "n", "type": "INTEGER", "nullable": true}],
                  "projects": ["null:INTEGER"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "null:INTEGER",
                    "type": "INTEGER",
                    "nullable": true,
                    "literalTypeName": "NULL",
                    "literalValue": "null",
                    "literalValue2": "null"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        assert_eq!(
            exprs[0].parsed,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "null".to_owned()
                }),
                ty: "INTEGER".to_owned()
            }
        );
    }

    #[test]
    fn structured_rex_timestamp_preserves_precision() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "ts", "type": "TIMESTAMP", "precision": 3}]}],
              "queries": [{
                "sql": "select cast('1970-01-01 00:00:01.001' as timestamp) as ts from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "ts", "type": "TIMESTAMP", "nullable": true, "precision": 3}],
                  "projects": ["1970-01-01 00:00:01.001:TIMESTAMP"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1970-01-01 00:00:01.001:TIMESTAMP",
                    "type": "TIMESTAMP",
                    "nullable": true,
                    "precision": 3,
                    "literalTypeName": "TIMESTAMP",
                    "literalValueAsString": "1970-01-01 00:00:01.001"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "ts", "type": "TIMESTAMP", "nullable": true, "precision": 3}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(
            ir.schema.tables[0].columns[0].ty,
            SqlType::timestamp(Some(3))
        );
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        assert_eq!(
            exprs[0].parsed,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1970-01-01 00:00:01.001".to_owned()
                }),
                ty: "TIMESTAMP(3)".to_owned()
            }
        );
    }

    #[test]
    fn rejects_submillisecond_timestamp_literal_without_exact_rex_value() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "id", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as ts from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "ts", "type": "TIMESTAMP", "nullable": true, "precision": 6}],
                  "projects": ["1970-01-01 00:00:01.123:TIMESTAMP(6)"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1970-01-01 00:00:01.123:TIMESTAMP(6)",
                    "type": "TIMESTAMP",
                    "nullable": true,
                    "precision": 6,
                    "literalTypeName": "TIMESTAMP",
                    "literalValue2": "1123"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "id", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let error = convert_raw_file(raw).expect_err("sub-millisecond timestamp must be rejected");
        assert!(
            error
                .to_string()
                .contains("TIMESTAMP(6) literal requires exact sub-millisecond value"),
            "{error}"
        );
    }

    #[test]
    fn recovers_submillisecond_timestamp_cast_from_source_sql() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "id", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as ts from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "ts", "type": "TIMESTAMP", "nullable": true, "precision": 6}],
                  "projects": ["1970-01-01 00:00:01.123000:TIMESTAMP(6)"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1970-01-01 00:00:01.123000:TIMESTAMP(6)",
                    "type": "TIMESTAMP",
                    "nullable": true,
                    "precision": 6,
                    "sourceSql": "CAST('1970-01-01 00:00:01.123456' AS TIMESTAMP(6))",
                    "literalTypeName": "TIMESTAMP",
                    "literalValue2": "1123",
                    "timestampLiteral": "1970-01-01 00:00:01.123000"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "id", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        assert_eq!(
            exprs[0].parsed,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1970-01-01 00:00:01.123456".to_owned()
                }),
                ty: "TIMESTAMP(6)".to_owned()
            }
        );
    }

    #[test]
    fn structured_rex_timestamp_uses_exact_timestamp_literal() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "id", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select cast('1970-01-01 00:00:01.123456' as timestamp(6)) as ts from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "ts", "type": "TIMESTAMP", "nullable": true, "precision": 6}],
                  "projects": ["1970-01-01 00:00:01.123456:TIMESTAMP(6)"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1970-01-01 00:00:01.123456:TIMESTAMP(6)",
                    "type": "TIMESTAMP",
                    "nullable": true,
                    "precision": 6,
                    "literalTypeName": "TIMESTAMP",
                    "literalValue2": "1123",
                    "timestampLiteral": "1970-01-01 00:00:01.123456"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "id", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        assert_eq!(
            exprs[0].parsed,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1970-01-01 00:00:01.123456".to_owned()
                }),
                ty: "TIMESTAMP(6)".to_owned()
            }
        );
    }

    #[test]
    fn timestamptz_literal_recovers_source_offset() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "id", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select cast('1970-01-01 08:00:00+08:00' as timestamptz(6)) as ts from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "ts", "type": "TIMESTAMP_WITH_TIME_ZONE", "nullable": true, "precision": 6}],
                  "projects": ["1970-01-01 00:00:00:TIMESTAMP_WITH_LOCAL_TIME_ZONE(6)"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1970-01-01 00:00:00:TIMESTAMP_WITH_LOCAL_TIME_ZONE(6)",
                    "type": "TIMESTAMP_WITH_LOCAL_TIME_ZONE",
                    "nullable": true,
                    "precision": 6,
                    "sourceSql": "CAST('1970-01-01 08:00:00+08:00' AS TIMESTAMPTZ(6))",
                    "literalTypeName": "TIMESTAMP_WITH_LOCAL_TIME_ZONE",
                    "timestampLiteral": "1970-01-01 00:00:00"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "id", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        assert_eq!(
            exprs[0].parsed,
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1970-01-01 08:00:00+08:00".to_owned()
                }),
                ty: "TIMESTAMP_WITH_TIME_ZONE(6)".to_owned()
            }
        );
    }

    #[test]
    fn timestamptz_literal_without_source_or_offset_is_rejected() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "id", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select cast('1970-01-01 08:00:00+08:00' as timestamptz(6)) as ts from R",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "ts", "type": "TIMESTAMP_WITH_TIME_ZONE", "nullable": true, "precision": 6}],
                  "projects": ["1970-01-01 00:00:00:TIMESTAMP_WITH_LOCAL_TIME_ZONE(6)"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1970-01-01 00:00:00:TIMESTAMP_WITH_LOCAL_TIME_ZONE(6)",
                    "type": "TIMESTAMP_WITH_LOCAL_TIME_ZONE",
                    "nullable": true,
                    "precision": 6,
                    "literalTypeName": "TIMESTAMP_WITH_LOCAL_TIME_ZONE",
                    "timestampLiteral": "1970-01-01 00:00:00"
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "id", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let error = convert_raw_file(raw).unwrap_err().to_string();
        assert!(
            error.contains("TIMESTAMP WITH TIME ZONE literal requires source SQL"),
            "{error}"
        );
    }

    #[test]
    fn structured_collation_preserves_null_direction() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select a from R order by a desc nulls last",
                "rel": {
                  "type": "LogicalSort",
                  "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                  "collation": [{"fieldIndex": 0, "direction": "DESCENDING", "nullDirection": "LAST"}],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Sort { collation, .. } = &ir.queries[0].rel else {
            panic!("expected sort");
        };
        assert_eq!(collation[0].null_direction, Some(SortNullDirection::Last));
    }

    #[test]
    fn parses_group_set_and_aggregate_call() {
        assert_eq!(parse_group_set("{0, 2, 3}").unwrap(), vec![0, 2, 3]);
        assert_eq!(
            parse_group_sets(&["{0}".to_owned(), "{1, 2}".to_owned()]).unwrap(),
            vec![vec![0], vec![1, 2]]
        );
        let call = parse_aggregate_call("COUNT(DISTINCT $1) FILTER $2".to_owned()).unwrap();
        assert_eq!(call.function, "COUNT");
        assert!(call.distinct);
        assert_eq!(call.args.len(), 1);
        assert!(call.filter.is_some());
    }

    #[test]
    fn values_tuples_are_hydrated_from_text_plan() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [],
              "queries": [{
                "sql": "values (1)",
                "rel": {
                  "type": "LogicalValues",
                  "rowType": [{"name": "EXPR$0", "type": "INTEGER", "nullable": false}],
                  "inputs": []
                },
                "relText": "LogicalValues(tuples=[[{ 1 }]])"
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Values {
            tuples: ValuesTuples::Rows { rows },
            ..
        } = &ir.queries[0].rel
        else {
            panic!("expected hydrated values rows");
        };
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].len(), 1);
        assert_eq!(rows[0][0].raw, "1");
        assert!(!matches!(
            &ir.queries[0].rel,
            RelExpr::Values {
                tuples: ValuesTuples::UnavailableFromCalcite,
                ..
            }
        ));
        assert!(
            !ir.queries[0]
                .features
                .contains(&Feature::ValuesTuplesUnavailable)
        );
        assert!(ir.queries[0].features.contains(&Feature::Values));
        assert!(
            ir.queries[0]
                .features
                .contains(&Feature::FormalSqlUnsupported)
        );
    }

    #[test]
    fn filter_without_condition_is_rejected() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalFilter",
                  "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        assert!(matches!(
            convert_raw_file(raw),
            Err(Error::MissingField {
                node: "LogicalFilter",
                field: "conditionRex"
            })
        ));
    }

    #[test]
    fn project_without_project_rex_is_rejected() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                  "projects": ["$0"],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        assert!(matches!(
            convert_raw_file(raw),
            Err(Error::MissingField {
                node: "LogicalProject",
                field: "projectRex"
            })
        ));
    }

    #[test]
    fn sort_fetch_without_fetch_rex_is_rejected() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalSort",
                  "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                  "collation": [],
                  "fetch": "10",
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        assert!(matches!(
            convert_raw_file(raw),
            Err(Error::MissingField {
                node: "LogicalSort",
                field: "fetchRex"
            })
        ));
    }

    #[test]
    fn rollup_and_grouping_are_marked_unsupported() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select a, grouping(a), count(*) from R group by rollup(a)",
                "rel": {
                  "type": "LogicalAggregate",
                  "rowType": [
                    {"name": "a", "type": "INTEGER", "nullable": true},
                    {"name": "g", "type": "INTEGER", "nullable": false},
                    {"name": "c", "type": "BIGINT", "nullable": false}
	                  ],
	                  "groupSet": "{0}",
	                  "groupSets": ["{0}", "{}"],
	                  "aggCalls": ["GROUPING($0)", "COUNT()"],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert!(ir.queries[0].features.contains(&Feature::Rollup));
        assert!(ir.queries[0].features.contains(&Feature::GroupingFunction));
        assert!(ir.queries[0].features.contains(&Feature::GroupingSets));
        assert!(
            ir.queries[0]
                .features
                .contains(&Feature::FormalSqlUnsupported)
        );
    }

    #[test]
    fn ordinary_group_by_keeps_single_grouping_set() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "sql": "select count(*) from R",
                "rel": {
                  "type": "LogicalAggregate",
                  "rowType": [{"name": "c", "type": "BIGINT", "nullable": false}],
                  "groupSet": "{}",
                  "groupSets": ["{}"],
                  "aggCalls": ["COUNT()"],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert!(!ir.queries[0].features.contains(&Feature::GroupingSets));
        assert!(
            !ir.queries[0]
                .features
                .contains(&Feature::AggregateGroupingSetsUnavailable)
        );
        if let RelExpr::Aggregate { grouping_sets, .. } = &ir.queries[0].rel {
            assert_eq!(grouping_sets, &Some(vec![Vec::new()]));
        } else {
            panic!("expected aggregate");
        }
    }

    #[test]
    fn missing_group_sets_is_marked_unavailable() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalAggregate",
                  "rowType": [{"name": "c", "type": "BIGINT", "nullable": false}],
                  "groupSet": "{}",
                  "aggCalls": ["COUNT()"],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert!(
            ir.queries[0]
                .features
                .contains(&Feature::AggregateGroupingSetsUnavailable)
        );
        assert!(
            ir.queries[0]
                .features
                .contains(&Feature::FormalSqlUnsupported)
        );
    }

    #[test]
    fn missing_group_sets_are_hydrated_from_text_plan() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "R", "columns": [{"name": "a", "type": "INTEGER"}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalAggregate",
                  "rowType": [{"name": "c", "type": "BIGINT", "nullable": false}],
                  "groupSet": "{}",
                  "aggCalls": ["COUNT()"],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
                    "table": ["R"],
                    "inputs": []
                  }]
                },
                "relText": "LogicalAggregate(group=[{}], agg#0=[COUNT()])\n  LogicalTableScan(table=[[R]])"
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert!(
            !ir.queries[0]
                .features
                .contains(&Feature::AggregateGroupingSetsUnavailable)
        );
        if let RelExpr::Aggregate { grouping_sets, .. } = &ir.queries[0].rel {
            assert_eq!(grouping_sets, &Some(vec![Vec::new()]));
        } else {
            panic!("expected aggregate");
        }
    }

    #[test]
    fn time_zone_types_are_preserved() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{
                "name": "R",
                "columns": [{"name": "t", "type": "TIMESTAMP WITH LOCAL TIME ZONE"}]
              }],
              "queries": [{
                "rel": {
                  "type": "LogicalTableScan",
                  "rowType": [{"name": "t", "type": "TIMESTAMP WITH LOCAL TIME ZONE", "nullable": true}],
                  "table": ["R"],
                  "inputs": [{
                    "type": "LogicalValues",
                    "rowType": [],
                    "tuples": [],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert!(matches!(
            ir.schema.tables[0].columns[0].ty,
            SqlType::TimestampTz { .. }
        ));
        assert!(matches!(
            ir.queries[0].output[0].ty,
            SqlType::TimestampTz { .. }
        ));
    }

    #[test]
    fn timezone_schema_type_is_hydrated_through_calcite_timestamp_row_type() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{
                "name": "R",
                "columns": [{"name": "t", "type": "TIMESTAMP_WITH_TIME_ZONE", "fullType": "TIMESTAMP_WITH_TIME_ZONE(6)", "precision": 6}]
              }],
              "queries": [{
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "t", "type": "TIMESTAMP", "nullable": true, "precision": 6}],
                  "projects": ["$0"],
                  "projectRex": [{"kind": "INPUT_REF", "text": "$0", "type": "TIMESTAMP", "index": 0, "precision": 6}],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "t", "type": "TIMESTAMP", "nullable": true, "precision": 6}],
                    "table": ["R"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(ir.queries[0].output[0].ty, SqlType::timestamptz(Some(6)));
        if let RelExpr::Project { input, .. } = &ir.queries[0].rel {
            assert_eq!(input.output()[0].ty, SqlType::timestamptz(Some(6)));
        } else {
            panic!("expected project");
        }
    }

    #[test]
    fn structured_rex_subquery_preserves_rel_tree() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [
                {"name": "EMP", "columns": [{"name": "DEPTNO", "type": "INTEGER"}]},
                {"name": "DEPT", "columns": [{"name": "DEPTNO", "type": "INTEGER"}]}
              ],
              "queries": [{
                "rel": {
                  "type": "LogicalFilter",
                  "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                  "condition": "IN($0, { LogicalProject(DEPTNO=[$0]) })",
                  "conditionRex": {
                    "kind": "IN",
                    "class": "RexSubQuery",
                    "text": "IN($0, { LogicalProject(DEPTNO=[$0]) })",
                    "type": "BOOLEAN",
                    "nullable": true,
                    "operator": "IN",
                    "opKind": "IN",
                    "operands": [{"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "INTEGER", "index": 0}],
                    "subqueryRel": {
                      "type": "LogicalProject",
                      "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                      "projects": ["$0"],
                      "projectRex": [{"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "INTEGER", "index": 0}],
                      "inputs": [{
                        "type": "LogicalTableScan",
                        "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                        "table": ["DEPT"],
                        "inputs": []
                      }]
                    }
                  },
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                    "table": ["EMP"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Filter { predicate, .. } = &ir.queries[0].rel else {
            panic!("expected filter");
        };
        let ScalarAst::Call { op, args, .. } = &predicate.parsed else {
            panic!("expected IN call");
        };
        assert_eq!(op, &ScalarOp::In);
        assert!(matches!(args.last(), Some(ScalarAst::RelSubquery { .. })));
    }

    #[test]
    fn structured_rex_field_access_preserves_correlated_ref() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [
                {"name": "EMP", "columns": [{"name": "DEPTNO", "type": "INTEGER"}]},
                {"name": "DEPT", "columns": [{"name": "DEPTNO", "type": "INTEGER"}]}
              ],
              "queries": [{
                "rel": {
                  "type": "LogicalFilter",
                  "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                  "condition": "EXISTS({ LogicalFilter(condition=[=($0, $cor0.DEPTNO)]) })",
                  "conditionRex": {
                    "kind": "EXISTS",
                    "class": "RexSubQuery",
                    "text": "EXISTS({ LogicalFilter(condition=[=($0, $cor0.DEPTNO)]) })",
                    "type": "BOOLEAN",
                    "nullable": true,
                    "operator": "EXISTS",
                    "opKind": "EXISTS",
                    "operands": [],
                    "subqueryRel": {
                      "type": "LogicalFilter",
                      "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                      "condition": "=($0, $cor0.DEPTNO)",
                      "conditionRex": {
                        "kind": "EQUALS",
                        "class": "RexCall",
                        "text": "=($0, $cor0.DEPTNO)",
                        "type": "BOOLEAN",
                        "nullable": true,
                        "operator": "=",
                        "opKind": "EQUALS",
                        "operands": [
                          {"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "INTEGER", "index": 0},
                          {
                            "kind": "FIELD_ACCESS",
                            "class": "RexFieldAccess",
                            "text": "$cor0.DEPTNO",
                            "type": "INTEGER",
                            "precision": 10,
                            "nullable": true,
                            "fieldName": "DEPTNO",
                            "fieldIndex": 0,
                            "referenceExpr": {
                              "kind": "CORREL_VARIABLE",
                              "class": "RexCorrelVariable",
                              "text": "$cor0",
                              "type": "RecordType(INTEGER DEPTNO)",
                              "correlationId": 0,
                              "correlationName": "$cor0"
                            }
                          }
                        ]
                      },
                      "inputs": [{
                        "type": "LogicalTableScan",
                        "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                        "table": ["DEPT"],
                        "inputs": []
                      }]
                    }
                  },
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": true}],
                    "table": ["EMP"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Filter { predicate, .. } = &ir.queries[0].rel else {
            panic!("expected outer filter");
        };
        let ScalarAst::Call { args, .. } = &predicate.parsed else {
            panic!("expected EXISTS call");
        };
        let Some(ScalarAst::RelSubquery { rel }) = args.last() else {
            panic!("expected structured subquery");
        };
        let RelExpr::Filter {
            predicate: inner_predicate,
            ..
        } = rel.as_ref()
        else {
            panic!("expected inner filter");
        };
        let ScalarAst::Call { args, .. } = &inner_predicate.parsed else {
            panic!("expected inner predicate call");
        };
        assert!(matches!(
            &args[1],
            ScalarAst::CorrelatedRef {
                correlation,
                field,
                index: Some(0),
                ty: SqlType::Integer,
            } if correlation == "$cor0" && field == "DEPTNO"
        ));
    }

    #[test]
    fn structured_values_tuples_do_not_require_text_hydration() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "queries": [{
                "rel": {
                  "type": "LogicalValues",
                  "rowType": [{"name": "EXPR$0", "type": "INTEGER", "nullable": false}],
                  "tuples": [[{"kind": "LITERAL", "class": "RexLiteral", "text": "1", "type": "INTEGER", "nullable": false, "literalTypeName": "DECIMAL", "literalValue": "1"}]],
                  "inputs": []
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert!(
            !ir.queries[0]
                .features
                .contains(&Feature::ValuesTuplesUnavailable)
        );
        let RelExpr::Values { tuples, .. } = &ir.queries[0].rel else {
            panic!("expected values");
        };
        assert!(matches!(tuples, ValuesTuples::Rows { rows } if rows.len() == 1));
    }

    #[test]
    fn decimal_precision_and_scale_survive_project_conversion() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "T", "columns": [{"name": "amount", "type": "DECIMAL", "precision": 10, "scale": 2}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "amount_out", "type": "DECIMAL", "nullable": true, "precision": 10, "scale": 2}],
                  "projects": ["CAST($0):DECIMAL(10, 2)"],
                  "projectRex": [{
                    "kind": "CAST",
                    "class": "RexCall",
                    "text": "CAST($0):DECIMAL(10, 2)",
                    "type": "DECIMAL",
                    "precision": 10,
                    "scale": 2,
                    "operator": "CAST",
                    "opKind": "CAST",
                    "operands": [{"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "DECIMAL", "index": 0, "precision": 10, "scale": 2}]
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "amount", "type": "DECIMAL", "nullable": true, "precision": 10, "scale": 2}],
                    "table": ["T"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(
            ir.schema.tables[0].columns[0].ty,
            SqlType::decimal(Some(10), Some(2))
        );
        assert_eq!(
            ir.queries[0].output[0].ty,
            SqlType::decimal(Some(10), Some(2))
        );
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        let ScalarAst::TypeAnnotation { ty, .. } = &exprs[0].parsed else {
            panic!("expected decimal type annotation");
        };
        assert_eq!(ty, "DECIMAL(10,2)");
    }

    #[test]
    fn decimal_rex_call_result_keeps_operator_ast() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "T", "columns": [
                {"name": "a", "type": "DECIMAL", "precision": 10, "scale": 2},
                {"name": "b", "type": "DECIMAL", "precision": 10, "scale": 2}
              ]}],
              "queries": [{
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "sum_ab", "type": "DECIMAL", "nullable": true, "precision": 11, "scale": 2}],
                  "projects": ["+($0, $1)"],
                  "projectRex": [{
                    "kind": "PLUS",
                    "class": "RexCall",
                    "text": "+($0, $1)",
                    "type": "DECIMAL",
                    "precision": 11,
                    "scale": 2,
                    "operator": "+",
                    "opKind": "PLUS",
                    "operands": [
                      {"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "DECIMAL", "index": 0, "precision": 10, "scale": 2},
                      {"kind": "INPUT_REF", "class": "RexInputRef", "text": "$1", "type": "DECIMAL", "index": 1, "precision": 10, "scale": 2}
                    ]
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [
                      {"name": "a", "type": "DECIMAL", "nullable": true, "precision": 10, "scale": 2},
                      {"name": "b", "type": "DECIMAL", "nullable": true, "precision": 10, "scale": 2}
                    ],
                    "table": ["T"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        assert!(matches!(
            &exprs[0].parsed,
            ScalarAst::Call {
                op: ScalarOp::Plus,
                ..
            }
        ));
    }

    #[test]
    fn decimal_without_explicit_scale_defaults_to_zero() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "T", "columns": [{"name": "amount", "type": "DECIMAL", "precision": 10}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "amount_out", "type": "DECIMAL", "nullable": true, "precision": 10}],
                  "projects": ["CAST($0):DECIMAL(10)"],
                  "projectRex": [{
                    "kind": "CAST",
                    "class": "RexCall",
                    "text": "CAST($0):DECIMAL(10)",
                    "type": "DECIMAL",
                    "precision": 10,
                    "operator": "CAST",
                    "opKind": "CAST",
                    "operands": [{"kind": "INPUT_REF", "class": "RexInputRef", "text": "$0", "type": "DECIMAL", "index": 0, "precision": 10}]
                  }],
                  "inputs": [{
                    "type": "LogicalTableScan",
                    "rowType": [{"name": "amount", "type": "DECIMAL", "nullable": true, "precision": 10}],
                    "table": ["T"],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(
            ir.schema.tables[0].columns[0].ty,
            SqlType::decimal(Some(10), Some(0))
        );
        assert_eq!(
            ir.queries[0].output[0].ty,
            SqlType::decimal(Some(10), Some(0))
        );
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        let ScalarAst::TypeAnnotation { ty, .. } = &exprs[0].parsed else {
            panic!("expected decimal type annotation");
        };
        assert_eq!(ty, "DECIMAL(10,0)");
    }

    #[test]
    fn unconstrained_decimal_preserves_missing_scale() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "T", "columns": [{"name": "amount", "type": "DECIMAL"}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalTableScan",
                  "rowType": [{"name": "amount", "type": "DECIMAL", "nullable": true}],
                  "table": ["T"],
                  "inputs": []
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(
            ir.schema.tables[0].columns[0].ty,
            SqlType::decimal(None, None)
        );
        assert_eq!(ir.queries[0].output[0].ty, SqlType::decimal(None, None));
    }

    #[test]
    fn negative_decimal_scale_is_not_defaulted_to_zero() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [{"name": "T", "columns": [{"name": "amount", "type": "DECIMAL", "precision": 2, "scale": -3}]}],
              "queries": [{
                "rel": {
                  "type": "LogicalTableScan",
                  "rowType": [{"name": "amount", "type": "DECIMAL", "nullable": true, "precision": 2, "scale": -3}],
                  "table": ["T"],
                  "inputs": []
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        assert_eq!(
            ir.schema.tables[0].columns[0].ty,
            SqlType::decimal(Some(2), None)
        );
        assert_eq!(ir.queries[0].output[0].ty, SqlType::decimal(Some(2), None));
    }

    #[test]
    fn decimal_cast_literal_uses_source_sql_before_calcite_rounding() {
        let raw: CalciteFile = serde_json::from_str(
            r#"
            {
              "schema": [],
              "queries": [{
                "sourceSql": "SELECT CAST('1.235' AS DECIMAL(4, 2))",
                "rel": {
                  "type": "LogicalProject",
                  "rowType": [{"name": "amount", "type": "DECIMAL", "nullable": false, "precision": 4, "scale": 2}],
                  "projects": ["1.23:DECIMAL(4, 2)"],
                  "projectRex": [{
                    "kind": "LITERAL",
                    "class": "RexLiteral",
                    "text": "1.23:DECIMAL(4, 2)",
                    "type": "DECIMAL",
                    "precision": 4,
                    "scale": 2,
                    "literalTypeName": "DECIMAL",
                    "literalValue": "1.23",
                    "sourceSql": "CAST('1.235' AS DECIMAL(4, 2))"
                  }],
                  "inputs": [{
                    "type": "LogicalValues",
                    "rowType": [],
                    "tuples": [],
                    "inputs": []
                  }]
                }
              }]
            }
            "#,
        )
        .unwrap();

        let ir = convert_raw_file(raw).unwrap();
        let RelExpr::Project { exprs, .. } = &ir.queries[0].rel else {
            panic!("expected project");
        };
        let ScalarAst::TypeAnnotation { expr, ty } = &exprs[0].parsed else {
            panic!("expected decimal type annotation");
        };
        assert_eq!(ty, "DECIMAL(4,2)");
        assert!(matches!(
            expr.as_ref(),
            ScalarAst::Literal { raw } if raw == "1.235"
        ));
    }
}
