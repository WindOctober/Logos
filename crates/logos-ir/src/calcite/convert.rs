use std::collections::BTreeSet;
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
use crate::calcite::{CalciteFile, CalciteRel, CalciteRex};
use crate::error::{Error, Result};
use crate::ir::{
    AggregateCall, Column, Feature, JoinType, LogosIrFile, Query, RelExpr, ScalarAst, ScalarExpr,
    Schema, SetOp, SortDirection, SortKey, SortNullDirection, SqlType, Table, ValuesTuples,
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
                            ty: parse_sql_type(&column.ty)?,
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
        let mut rel = convert_rel(rel, &mut features)?;
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

fn convert_rel(raw: CalciteRel, features: &mut BTreeSet<Feature>) -> Result<RelExpr> {
    match raw.rel_type.as_str() {
        "LogicalTableScan" => {
            features.insert(Feature::TableScan);
            Ok(RelExpr::TableScan {
                table: raw.table,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalProject" => {
            features.insert(Feature::Projection);
            let input = one_input("LogicalProject", raw.inputs, features)?;
            let exprs = convert_project_exprs(raw.projects, raw.project_rex)?;
            Ok(RelExpr::Project {
                input: Box::new(input),
                exprs,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalFilter" => {
            features.insert(Feature::Selection);
            let input = one_input("LogicalFilter", raw.inputs, features)?;
            let condition =
                required_rex_scalar("LogicalFilter", "conditionRex", raw.condition_rex)?;
            Ok(RelExpr::Filter {
                input: Box::new(input),
                predicate: condition,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalJoin" => {
            let actual = raw.inputs.len();
            if actual != 2 {
                return Err(Error::Arity {
                    node: "LogicalJoin",
                    expected: "2",
                    actual,
                });
            }
            let mut inputs = raw.inputs.into_iter();
            let left = convert_rel(inputs.next().expect("checked arity"), features)?;
            let right = convert_rel(inputs.next().expect("checked arity"), features)?;
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
            let condition = required_rex_scalar("LogicalJoin", "conditionRex", raw.condition_rex)?;
            Ok(RelExpr::Join {
                left: Box::new(left),
                right: Box::new(right),
                join_type,
                condition,
                output: convert_row_type(raw.row_type)?,
            })
        }
        "LogicalAggregate" => {
            features.insert(Feature::Aggregation);
            features.insert(Feature::FormalSqlUnsupported);
            let input = one_input("LogicalAggregate", raw.inputs, features)?;
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
            let agg_calls: Vec<_> = raw
                .agg_calls
                .into_iter()
                .map(parse_aggregate_call)
                .collect::<Result<Vec<_>>>()?;
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
            let input = one_input("LogicalSort", raw.inputs, features)?;
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
                fetch: optional_rex_scalar("LogicalSort", "fetchRex", raw.fetch, raw.fetch_rex)?,
                offset: optional_rex_scalar(
                    "LogicalSort",
                    "offsetRex",
                    raw.offset,
                    raw.offset_rex,
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
                .map(|input| convert_rel(input, features))
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
            features.insert(Feature::ValuesTuplesUnavailable);
            features.insert(Feature::FormalSqlUnsupported);
            Ok(RelExpr::Values {
                tuples: ValuesTuples::UnavailableFromCalcite,
                output: convert_row_type(raw.row_type)?,
            })
        }
        other => Err(Error::UnsupportedRelNode(other.to_owned())),
    }
}

fn convert_project_exprs(
    projects: Vec<String>,
    project_rex: Vec<CalciteRex>,
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
    project_rex.into_iter().map(calcite_rex_scalar).collect()
}

fn required_rex_scalar(
    node: &'static str,
    field: &'static str,
    rex: Option<CalciteRex>,
) -> Result<ScalarExpr> {
    calcite_rex_scalar(required_field(node, field, rex)?)
}

fn optional_rex_scalar(
    node: &'static str,
    rex_field: &'static str,
    text: Option<String>,
    rex: Option<CalciteRex>,
) -> Result<Option<ScalarExpr>> {
    match (text, rex) {
        (_, Some(rex)) => calcite_rex_scalar(rex).map(Some),
        (Some(_), None) => Err(Error::MissingField {
            node,
            field: rex_field,
        }),
        (None, None) => Ok(None),
    }
}

fn calcite_rex_scalar(rex: CalciteRex) -> Result<ScalarExpr> {
    let raw = rex
        .text
        .clone()
        .unwrap_or_else(|| "<structured RexNode>".to_owned());
    let parsed = calcite_rex_ast(&rex)?;
    let class = classify_calcite_scalar(&raw);
    Ok(ScalarExpr { raw, class, parsed })
}

fn calcite_rex_ast(rex: &CalciteRex) -> Result<ScalarAst> {
    if is_rex_subquery(rex) {
        let text = rex
            .text
            .as_deref()
            .ok_or_else(|| Error::InvalidScalar(rex_debug_text(rex)))?;
        return parse_calcite_scalar_ast(text);
    }
    if let Some(index) = rex.index {
        return Ok(ScalarAst::InputRef { index });
    }
    if is_rex_literal(rex) {
        return Ok(calcite_rex_literal_ast(rex));
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
            .map(calcite_rex_ast)
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

fn calcite_rex_literal_ast(rex: &CalciteRex) -> ScalarAst {
    if let Some(ty) = rex_interval_annotation(rex) {
        let raw = rex
            .interval_literal
            .as_deref()
            .or(rex.literal_value_as_string.as_deref())
            .or(rex.literal_value2.as_deref())
            .or(rex.literal_value.as_deref())
            .unwrap_or_else(|| rex.text.as_deref().unwrap_or(""));
        return ScalarAst::TypeAnnotation {
            expr: Box::new(ScalarAst::Literal {
                raw: raw.to_owned(),
            }),
            ty,
        };
    }
    if let Some(ty) = rex_type_annotation(rex) {
        if ty.eq_ignore_ascii_case("DATE") {
            let raw = rex
                .literal_value_as_string
                .as_deref()
                .or(rex.literal_value2.as_deref())
                .or(rex.literal_value.as_deref())
                .unwrap_or_else(|| rex.text.as_deref().unwrap_or(""));
            return ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: raw.to_owned(),
                }),
                ty,
            };
        }
    }
    if is_character_type(rex) {
        if let Some(value) = rex
            .literal_value_as_string
            .as_deref()
            .or(rex.literal_value2.as_deref())
        {
            return ScalarAst::Literal {
                raw: sql_string_literal(value),
            };
        }
    }
    if let Some(ty) = rex_type_annotation(rex) {
        if let Some(raw) = structured_literal_value(rex) {
            return ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal { raw }),
                ty,
            };
        }
    }
    if let Some(text) = &rex.text {
        if let Ok(ast) = parse_calcite_scalar_ast(text) {
            return ast;
        }
    }
    ScalarAst::Literal {
        raw: rex.text.clone().unwrap_or_else(|| {
            rex.literal_value_as_string
                .clone()
                .or_else(|| rex.literal_value2.clone())
                .or_else(|| rex.literal_value.clone())
                .unwrap_or_default()
        }),
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
    let ty = rex.ty.as_deref()?.trim();
    normalize_type_annotation(ty)
}

fn normalize_type_annotation(ty: &str) -> Option<String> {
    match ty.trim().to_ascii_uppercase().as_str() {
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
        "TIMESTAMP" => Some("TIMESTAMP".to_owned()),
        value if value.starts_with("INTERVAL") => Some(value.replace('_', " ")),
        _ => None,
    }
}

fn is_character_type(rex: &CalciteRex) -> bool {
    rex.ty
        .as_deref()
        .and_then(normalize_type_annotation)
        .is_some_and(|ty| matches!(ty.as_str(), "CHAR" | "VARCHAR"))
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

fn required_field<T>(node: &'static str, field: &'static str, value: Option<T>) -> Result<T> {
    value.ok_or(Error::MissingField { node, field })
}

fn one_input(
    node: &'static str,
    inputs: Vec<CalciteRel>,
    features: &mut BTreeSet<Feature>,
) -> Result<RelExpr> {
    let actual = inputs.len();
    if actual != 1 {
        return Err(Error::Arity {
            node,
            expected: "1",
            actual,
        });
    }
    convert_rel(inputs.into_iter().next().expect("checked arity"), features)
}

fn convert_row_type(row_type: Vec<crate::calcite::CalciteField>) -> Result<Vec<Column>> {
    row_type
        .into_iter()
        .map(|field| {
            Ok(Column {
                name: field.name,
                ty: parse_sql_type(&field.ty)?,
                nullable: field.nullable,
            })
        })
        .collect()
}

fn parse_sql_type(value: &str) -> Result<SqlType> {
    parse_calcite_sql_type(value)
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
        args,
        filter,
    })
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
    fn time_zone_types_are_rejected() {
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
                  "inputs": []
                }
              }]
            }
            "#,
        )
        .unwrap();

        assert!(matches!(
            convert_raw_file(raw),
            Err(Error::UnsupportedSqlType(value))
            if value == "TIMESTAMP WITH LOCAL TIME ZONE"
        ));
    }
}
