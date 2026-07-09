use std::collections::BTreeSet;

use crate::error::{Error, Result};
use crate::ir::{
    Feature, SargAst, SargBound, SargItem, ScalarAst, ScalarClass, ScalarExpr, ScalarOp,
    SortDirection, SortNullDirection, WindowAst, WindowOrderKey,
};
use crate::semantic::core_scalar::lower_core_scalar;

pub fn calcite_scalar(raw: impl Into<String>) -> ScalarExpr {
    try_calcite_scalar(raw).expect("valid Calcite scalar expression")
}

pub fn try_calcite_scalar(raw: impl Into<String>) -> Result<ScalarExpr> {
    let raw = raw.into();
    let class = classify_calcite_scalar(&raw);
    let parsed = parse_calcite_scalar_ast(&raw)?;
    Ok(ScalarExpr { raw, class, parsed })
}

pub fn classify_calcite_scalar(raw: &str) -> ScalarClass {
    let trimmed = raw.trim();
    if let Some(index) = parse_input_ref(trimmed) {
        ScalarClass::InputRef { index }
    } else if trimmed.contains("Logical") && trimmed.contains('{') {
        ScalarClass::Subquery
    } else if trimmed.contains("$cor") {
        ScalarClass::CorrelatedRef
    } else if trimmed.starts_with("Logical") {
        ScalarClass::Opaque
    } else if is_literal_like(trimmed) {
        ScalarClass::Literal
    } else if trimmed.contains('(') {
        ScalarClass::Call
    } else {
        ScalarClass::Opaque
    }
}

pub fn parse_calcite_scalar_ast(raw: &str) -> Result<ScalarAst> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Err(Error::InvalidScalar(raw.to_owned()));
    }
    if is_window_scalar(trimmed) {
        return Ok(ScalarAst::Window {
            raw: trimmed.to_owned(),
            structured: false,
            parsed: parse_window_ast(trimmed)?,
        });
    }
    if parse_braced_rel_text(trimmed).is_some() {
        return Err(Error::InvalidScalar(trimmed.to_owned()));
    }
    if is_sarg_literal(trimmed) {
        return Ok(ScalarAst::Sarg {
            raw: trimmed.to_owned(),
            parsed: parse_sarg_ast(trimmed)?,
        });
    }
    if let Some(index) = parse_input_ref(trimmed) {
        return Ok(ScalarAst::InputRef { index });
    }
    if is_atomic_literal_like(trimmed) {
        return Ok(ScalarAst::Literal {
            raw: trimmed.to_owned(),
        });
    }
    if let Some((expr, ty)) = split_top_level_type_annotation(trimmed) {
        let expr = parse_calcite_scalar_ast(expr)?;
        return Ok(ScalarAst::TypeAnnotation {
            expr: Box::new(expr),
            ty: ty.trim().to_owned(),
        });
    }
    if let Some(name) = parse_flag(trimmed) {
        return Ok(ScalarAst::Flag {
            name: name.to_owned(),
        });
    }
    if let Some((operator, args)) = parse_call(trimmed)? {
        let op = classify_scalar_op(&operator);
        return Ok(ScalarAst::Call { operator, op, args });
    }
    Err(Error::InvalidScalar(raw.to_owned()))
}

pub fn classify_scalar_op(operator: &str) -> ScalarOp {
    match operator.trim().to_ascii_uppercase().as_str() {
        "=" => ScalarOp::Eq,
        "<>" | "!=" => ScalarOp::NotEq,
        "<" => ScalarOp::Lt,
        "<=" => ScalarOp::Lte,
        ">" => ScalarOp::Gt,
        ">=" => ScalarOp::Gte,
        "AND" => ScalarOp::And,
        "OR" => ScalarOp::Or,
        "NOT" => ScalarOp::Not,
        "IS NULL" => ScalarOp::IsNull,
        "IS NOT NULL" => ScalarOp::IsNotNull,
        "IS TRUE" => ScalarOp::IsTrue,
        "IS NOT TRUE" => ScalarOp::IsNotTrue,
        "IS FALSE" => ScalarOp::IsFalse,
        "IS NOT FALSE" => ScalarOp::IsNotFalse,
        "IS NOT DISTINCT FROM" => ScalarOp::IsNotDistinctFrom,
        "LIKE" => ScalarOp::Like,
        "+" => ScalarOp::Plus,
        "-" => ScalarOp::Minus,
        "*" => ScalarOp::Multiply,
        "/" => ScalarOp::Divide,
        "||" => ScalarOp::StringConcat,
        "CAST" => ScalarOp::Cast,
        "CASE" => ScalarOp::Case,
        "LOWER" => ScalarOp::Lower,
        "UPPER" => ScalarOp::Upper,
        "SUBSTRING" => ScalarOp::Substring,
        "EXP" => ScalarOp::Exp,
        "POWER" => ScalarOp::Power,
        "EXTRACT" => ScalarOp::Extract,
        "IN" => ScalarOp::In,
        "EXISTS" => ScalarOp::Exists,
        "$SCALAR_QUERY" => ScalarOp::ScalarQuery,
        "SEARCH" => ScalarOp::Search,
        _ => ScalarOp::Other(operator.trim().to_owned()),
    }
}

pub fn split_calcite_arg_list(value: &str) -> Option<Vec<String>> {
    let mut args = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let mut brace_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut in_string = false;
    let mut chars = value.char_indices().peekable();

    while let Some((index, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if in_string {
            continue;
        }
        match ch {
            '(' if brace_depth == 0 && bracket_depth == 0 => depth += 1,
            ')' if brace_depth == 0 && bracket_depth == 0 => depth = depth.checked_sub(1)?,
            '{' => brace_depth += 1,
            '}' => brace_depth = brace_depth.checked_sub(1)?,
            '[' if brace_depth == 0 => bracket_depth += 1,
            ']' if brace_depth == 0 => bracket_depth = bracket_depth.saturating_sub(1),
            ',' if depth == 0 && brace_depth == 0 && bracket_depth == 0 => {
                args.push(value[start..index].trim().to_owned());
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }

    if depth != 0 || brace_depth != 0 || bracket_depth != 0 || in_string {
        return None;
    }

    let tail = value[start..].trim();
    if !tail.is_empty() {
        args.push(tail.to_owned());
    }
    Some(args)
}

pub fn collect_scalar_exprs<'a>(
    exprs: impl Iterator<Item = &'a ScalarExpr>,
    features: &mut BTreeSet<Feature>,
) {
    for expr in exprs {
        collect_scalar_expr(expr, features);
    }
}

pub fn collect_scalar_expr(expr: &ScalarExpr, features: &mut BTreeSet<Feature>) {
    let core_scalar_supported = lower_core_scalar(&expr.parsed).is_ok();
    let core_lowerable_case = core_scalar_supported
        && contains_any_scalar_op(&expr.parsed, &[ScalarOp::Case])
        && !contains_any_scalar_op(
            &expr.parsed,
            &[
                ScalarOp::StringConcat,
                ScalarOp::Lower,
                ScalarOp::Upper,
                ScalarOp::Substring,
                ScalarOp::Like,
                ScalarOp::Exp,
                ScalarOp::Power,
                ScalarOp::Divide,
                ScalarOp::Extract,
                ScalarOp::In,
                ScalarOp::Exists,
                ScalarOp::ScalarQuery,
                ScalarOp::Search,
            ],
        );
    if !core_scalar_supported {
        features.insert(Feature::OpaqueScalar);
        features.insert(Feature::FormalSqlUnsupported);
    }
    if contains_any_scalar_op(
        &expr.parsed,
        &[
            ScalarOp::Cast,
            ScalarOp::StringConcat,
            ScalarOp::Lower,
            ScalarOp::Upper,
            ScalarOp::Substring,
            ScalarOp::Like,
            ScalarOp::Exp,
            ScalarOp::Power,
            ScalarOp::In,
            ScalarOp::Exists,
            ScalarOp::ScalarQuery,
            ScalarOp::Search,
        ],
    ) {
        features.insert(Feature::OpaqueScalar);
        features.insert(Feature::FormalSqlUnsupported);
    }

    if expr.raw.contains("Logical") && expr.raw.contains('{') {
        features.insert(Feature::SubqueryPredicate);
        features.insert(Feature::OpaqueScalar);
        features.insert(Feature::FormalSqlUnsupported);
    }
    if contains_correlated_ref(&expr.parsed) {
        features.insert(Feature::CorrelatedPredicate);
    } else if expr.raw.contains("$cor") {
        features.insert(Feature::CorrelatedPredicate);
        features.insert(Feature::OpaqueScalar);
        features.insert(Feature::FormalSqlUnsupported);
    }

    match expr.class {
        ScalarClass::InputRef { .. } | ScalarClass::Literal => {}
        ScalarClass::Subquery => {
            features.insert(Feature::SubqueryPredicate);
            features.insert(Feature::OpaqueScalar);
            features.insert(Feature::FormalSqlUnsupported);
        }
        ScalarClass::CorrelatedRef if contains_correlated_ref(&expr.parsed) => {
            features.insert(Feature::CorrelatedPredicate);
        }
        ScalarClass::CorrelatedRef => {
            features.insert(Feature::CorrelatedPredicate);
            features.insert(Feature::OpaqueScalar);
            features.insert(Feature::FormalSqlUnsupported);
        }
        ScalarClass::Call if core_lowerable_case => {}
        ScalarClass::Call | ScalarClass::Opaque => {
            features.insert(Feature::OpaqueScalar);
            features.insert(Feature::FormalSqlUnsupported);
        }
    }
}

fn parse_input_ref(value: &str) -> Option<usize> {
    let rest = value.strip_prefix('$')?;
    if rest.chars().all(|ch| ch.is_ascii_digit()) {
        rest.parse().ok()
    } else {
        None
    }
}

fn is_literal_like(value: &str) -> bool {
    is_atomic_literal_like(value) || value.starts_with("CAST('")
}

fn is_atomic_literal_like(value: &str) -> bool {
    value == "true"
        || value == "false"
        || value == "null"
        || value.parse::<i128>().is_ok()
        || value.parse::<f64>().is_ok()
        || is_calcite_bare_date_literal(value)
        || (value.starts_with('\'') && value.ends_with('\''))
}

fn is_calcite_bare_date_literal(value: &str) -> bool {
    let bytes = value.as_bytes();
    bytes.len() == 10
        && bytes[0..4].iter().all(u8::is_ascii_digit)
        && bytes[4] == b'-'
        && bytes[5..7].iter().all(u8::is_ascii_digit)
        && bytes[7] == b'-'
        && bytes[8..10].iter().all(u8::is_ascii_digit)
}

fn is_sarg_literal(value: &str) -> bool {
    value.starts_with("Sarg[")
        && (value.ends_with(']')
            || value
                .char_indices()
                .any(|(index, ch)| ch == ':' && value[..index].ends_with(']')))
}

fn parse_sarg_ast(value: &str) -> Result<SargAst> {
    let (inner, ty) =
        split_sarg_literal(value).ok_or_else(|| Error::InvalidScalar(value.to_owned()))?;
    let items = if inner.trim().is_empty() {
        Vec::new()
    } else {
        split_sarg_item_list(inner)
            .ok_or_else(|| Error::InvalidScalar(value.to_owned()))?
            .into_iter()
            .map(|item| parse_sarg_item(item.trim()))
            .collect()
    };
    Ok(SargAst {
        items,
        null_as: None,
        point_count: None,
        is_all: false,
        is_none: false,
        is_points: false,
        is_complemented_points: false,
        ty: ty.map(ToOwned::to_owned),
    })
}

fn split_sarg_literal(value: &str) -> Option<(&str, Option<&str>)> {
    let rest = value.strip_prefix("Sarg[")?;
    let close = find_sarg_close(value)?;
    let inner = &rest[..close - "Sarg[".len()];
    let suffix = value[close + 1..].trim();
    let ty = suffix
        .strip_prefix(':')
        .map(str::trim)
        .filter(|ty| !ty.is_empty());
    Some((inner, ty))
}

fn find_sarg_close(value: &str) -> Option<usize> {
    let mut in_string = false;
    let mut chars = value["Sarg[".len()..].char_indices().peekable();
    while let Some((relative, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if in_string || ch != ']' {
            continue;
        }
        let close = "Sarg[".len() + relative;
        let suffix = value[close + ch.len_utf8()..].trim();
        if suffix.is_empty() || suffix.starts_with(':') {
            return Some(close);
        }
    }
    None
}

fn parse_sarg_item(value: &str) -> SargItem {
    let trimmed = value.trim();
    let first = trimmed.chars().next();
    let last = trimmed.chars().last();
    if matches!(first, Some('(' | '[')) && matches!(last, Some(')' | ']')) && trimmed.contains("..")
    {
        let body = &trimmed[1..trimmed.len() - 1];
        if let Some((lower, upper)) = body.split_once("..") {
            return SargItem::Range {
                raw: trimmed.to_owned(),
                lower: parse_sarg_bound(lower.trim()),
                upper: parse_sarg_bound(upper.trim()),
                lower_inclusive: first == Some('['),
                upper_inclusive: last == Some(']'),
            };
        }
    }
    SargItem::Point {
        raw: trimmed.to_owned(),
    }
}

fn split_sarg_item_list(value: &str) -> Option<Vec<String>> {
    let mut items = Vec::new();
    let mut start = 0usize;
    let mut range_depth = 0usize;
    let mut in_string = false;
    let mut chars = value.char_indices().peekable();

    while let Some((index, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if in_string {
            continue;
        }
        match ch {
            '(' | '[' => range_depth += 1,
            ')' | ']' => range_depth = range_depth.checked_sub(1)?,
            ',' if range_depth == 0 => {
                items.push(value[start..index].trim().to_owned());
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }

    if range_depth != 0 || in_string {
        return None;
    }

    let tail = value[start..].trim();
    if !tail.is_empty() {
        items.push(tail.to_owned());
    }
    Some(items)
}

fn parse_sarg_bound(value: &str) -> Option<SargBound> {
    let trimmed = value.trim();
    if trimmed.is_empty()
        || trimmed == "-\u{221e}"
        || trimmed == "+\u{221e}"
        || trimmed.eq_ignore_ascii_case("-inf")
        || trimmed.eq_ignore_ascii_case("+inf")
    {
        None
    } else {
        Some(SargBound {
            raw: trimmed.to_owned(),
        })
    }
}

fn parse_braced_rel_text(value: &str) -> Option<&str> {
    let inner = value.strip_prefix('{')?.strip_suffix('}')?.trim();
    if inner.contains("Logical") {
        Some(inner)
    } else {
        None
    }
}

fn parse_flag(value: &str) -> Option<&str> {
    let inner = value.strip_prefix("FLAG(")?.strip_suffix(')')?.trim();
    if !inner.is_empty()
        && inner
            .chars()
            .all(|ch| ch.is_ascii_uppercase() || ch == '_' || ch.is_ascii_digit())
    {
        Some(inner)
    } else {
        None
    }
}

fn is_window_scalar(value: &str) -> bool {
    value.ends_with(')') && find_top_level_keyword(value, "OVER").is_some()
}

fn parse_window_ast(value: &str) -> Result<WindowAst> {
    let over_index = find_top_level_keyword(value, "OVER")
        .ok_or_else(|| Error::InvalidScalar(value.to_owned()))?;
    let function_expr = value[..over_index].trim();
    let window_spec = value[over_index + "OVER".len()..].trim();
    let spec_inner = window_spec
        .strip_prefix('(')
        .and_then(|spec| spec.strip_suffix(')'))
        .ok_or_else(|| Error::InvalidScalar(value.to_owned()))?
        .trim();
    let (function, args) =
        parse_call(function_expr)?.ok_or_else(|| Error::InvalidScalar(value.to_owned()))?;
    let parsed_spec = parse_window_spec(spec_inner)?;
    Ok(WindowAst {
        function,
        args,
        partition_by: parsed_spec.partition_by,
        order_by: parsed_spec.order_by,
        distinct: false,
        ignore_nulls: false,
        exclude: None,
        frame: parsed_spec.frame,
    })
}

struct ParsedWindowSpec {
    partition_by: Vec<ScalarAst>,
    order_by: Vec<WindowOrderKey>,
    frame: Option<String>,
}

fn parse_window_spec(value: &str) -> Result<ParsedWindowSpec> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Ok(ParsedWindowSpec {
            partition_by: Vec::new(),
            order_by: Vec::new(),
            frame: None,
        });
    }

    let partition_index = find_top_level_keyword(trimmed, "PARTITION BY");
    let order_index = find_top_level_keyword(trimmed, "ORDER BY");
    let frame_index = ["ROWS", "RANGE"]
        .into_iter()
        .filter_map(|keyword| find_top_level_keyword(trimmed, keyword))
        .min();

    if partition_index.is_none() && order_index.is_none() && frame_index.is_none() {
        return Err(Error::InvalidScalar(value.to_owned()));
    }

    let partition_by = if let Some(start) = partition_index {
        let body_start = start + "PARTITION BY".len();
        let body_end = [order_index, frame_index]
            .into_iter()
            .flatten()
            .filter(|index| *index > body_start)
            .min()
            .unwrap_or(trimmed.len());
        parse_scalar_list(&trimmed[body_start..body_end])?
    } else {
        Vec::new()
    };

    let order_by = if let Some(start) = order_index {
        let body_start = start + "ORDER BY".len();
        let body_end = frame_index
            .filter(|index| *index > body_start)
            .unwrap_or(trimmed.len());
        parse_window_order_key_list(&trimmed[body_start..body_end])?
    } else {
        Vec::new()
    };

    let frame = frame_index
        .map(|start| trimmed[start..].trim().to_owned())
        .filter(|frame| !frame.is_empty());

    Ok(ParsedWindowSpec {
        partition_by,
        order_by,
        frame,
    })
}

fn parse_scalar_list(value: &str) -> Result<Vec<ScalarAst>> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Ok(Vec::new());
    }
    split_calcite_arg_list(trimmed)
        .ok_or_else(|| Error::InvalidScalar(value.to_owned()))?
        .into_iter()
        .map(|expr| parse_calcite_scalar_ast(&expr))
        .collect()
}

fn parse_window_order_key_list(value: &str) -> Result<Vec<WindowOrderKey>> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Ok(Vec::new());
    }
    split_calcite_arg_list(trimmed)
        .ok_or_else(|| Error::InvalidScalar(value.to_owned()))?
        .into_iter()
        .map(|key| parse_window_order_key(&key))
        .collect()
}

fn parse_window_order_key(value: &str) -> Result<WindowOrderKey> {
    let (without_nulls, null_direction) = strip_trailing_null_direction(value.trim());
    let (expr_raw, direction) = strip_trailing_sort_direction(without_nulls.trim());
    let expr = parse_calcite_scalar_ast(expr_raw.trim())?;
    Ok(WindowOrderKey {
        expr,
        direction,
        null_direction,
    })
}

fn strip_trailing_null_direction(value: &str) -> (&str, Option<SortNullDirection>) {
    if let Some(prefix) = strip_trailing_ascii_phrase(value, "NULLS FIRST") {
        (prefix, Some(SortNullDirection::First))
    } else if let Some(prefix) = strip_trailing_ascii_phrase(value, "NULLS LAST") {
        (prefix, Some(SortNullDirection::Last))
    } else {
        (value, None)
    }
}

fn strip_trailing_sort_direction(value: &str) -> (&str, Option<SortDirection>) {
    if let Some(prefix) = strip_trailing_ascii_phrase(value, "ASC") {
        (prefix, Some(SortDirection::Ascending))
    } else if let Some(prefix) = strip_trailing_ascii_phrase(value, "DESC") {
        (prefix, Some(SortDirection::Descending))
    } else {
        (value, None)
    }
}

fn strip_trailing_ascii_phrase<'a>(value: &'a str, phrase: &str) -> Option<&'a str> {
    let trimmed = value.trim_end();
    if trimmed.len() < phrase.len() {
        return None;
    }
    let start = trimmed.len() - phrase.len();
    if !trimmed[start..].eq_ignore_ascii_case(phrase) {
        return None;
    }
    if start > 0
        && trimmed[..start]
            .chars()
            .next_back()
            .is_some_and(|ch| !ch.is_ascii_whitespace())
    {
        return None;
    }
    Some(trimmed[..start].trim_end())
}

fn split_top_level_type_annotation(value: &str) -> Option<(&str, &str)> {
    let mut depth = 0usize;
    let mut brace_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut in_string = false;
    let mut chars = value.char_indices().peekable();

    while let Some((index, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if in_string {
            continue;
        }
        match ch {
            '(' if brace_depth == 0 && bracket_depth == 0 => depth += 1,
            ')' if brace_depth == 0 && bracket_depth == 0 => depth = depth.checked_sub(1)?,
            '{' => brace_depth += 1,
            '}' => brace_depth = brace_depth.checked_sub(1)?,
            '[' if brace_depth == 0 => bracket_depth += 1,
            ']' if brace_depth == 0 => bracket_depth = bracket_depth.saturating_sub(1),
            ':' if depth == 0 && brace_depth == 0 && bracket_depth == 0 => {
                let expr = value[..index].trim();
                let ty = value[index + ch.len_utf8()..].trim();
                if !expr.is_empty() && !ty.is_empty() {
                    return Some((expr, ty));
                }
            }
            _ => {}
        }
    }
    None
}

fn parse_call(value: &str) -> Result<Option<(String, Vec<ScalarAst>)>> {
    let Some(open) = first_top_level_open_paren(value) else {
        return Ok(None);
    };
    if !value.ends_with(')') {
        return Err(Error::InvalidScalar(value.to_owned()));
    }
    let operator = value[..open].trim();
    if operator.is_empty() {
        return Err(Error::InvalidScalar(value.to_owned()));
    }
    let args_part = &value[open + 1..value.len() - 1];
    let args = split_calcite_arg_list(args_part)
        .ok_or_else(|| Error::InvalidScalar(value.to_owned()))?
        .into_iter()
        .map(|arg| parse_calcite_scalar_ast(&arg))
        .collect::<Result<Vec<_>>>()?;
    Ok(Some((operator.to_owned(), args)))
}

fn find_top_level_keyword(value: &str, keyword: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut brace_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut in_string = false;
    let mut chars = value.char_indices().peekable();

    while let Some((index, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if in_string {
            continue;
        }
        match ch {
            '(' if brace_depth == 0 && bracket_depth == 0 => depth += 1,
            ')' if brace_depth == 0 && bracket_depth == 0 => depth = depth.checked_sub(1)?,
            '{' => brace_depth += 1,
            '}' => brace_depth = brace_depth.checked_sub(1)?,
            '[' if brace_depth == 0 => bracket_depth += 1,
            ']' if brace_depth == 0 => bracket_depth = bracket_depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0
            && brace_depth == 0
            && bracket_depth == 0
            && keyword_matches_at(value, keyword, index)
        {
            return Some(index);
        }
    }
    None
}

fn keyword_matches_at(value: &str, keyword: &str, index: usize) -> bool {
    let Some(candidate) = value.get(index..index + keyword.len()) else {
        return false;
    };
    if !candidate.eq_ignore_ascii_case(keyword) {
        return false;
    }
    let before_ok = value[..index]
        .chars()
        .next_back()
        .is_none_or(|ch| !is_identifier_char(ch));
    let after_ok = value[index + keyword.len()..]
        .chars()
        .next()
        .is_none_or(|ch| !is_identifier_char(ch));
    before_ok && after_ok
}

fn is_identifier_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn first_top_level_open_paren(value: &str) -> Option<usize> {
    let mut in_string = false;
    let mut chars = value.char_indices().peekable();

    while let Some((index, ch)) = chars.next() {
        if ch == '\'' {
            if in_string && matches!(chars.peek(), Some((_, '\''))) {
                chars.next();
            } else {
                in_string = !in_string;
            }
            continue;
        }
        if !in_string && ch == '(' {
            return Some(index);
        }
    }
    None
}

fn contains_scalar_op(ast: &ScalarAst, target: &ScalarOp) -> bool {
    match ast {
        ScalarAst::InputRef { .. }
        | ScalarAst::CorrelatedRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::Window { .. }
        | ScalarAst::RelSubquery { .. }
        | ScalarAst::Sarg { .. } => false,
        ScalarAst::Call { op, args, .. } => {
            op == target || args.iter().any(|arg| contains_scalar_op(arg, target))
        }
        ScalarAst::TypeAnnotation { expr, .. } => contains_scalar_op(expr, target),
    }
}

fn contains_correlated_ref(ast: &ScalarAst) -> bool {
    match ast {
        ScalarAst::CorrelatedRef { .. } => true,
        ScalarAst::Call { args, .. } => args.iter().any(contains_correlated_ref),
        ScalarAst::TypeAnnotation { expr, .. } => contains_correlated_ref(expr),
        ScalarAst::Window { parsed, .. } => {
            parsed.args.iter().any(contains_correlated_ref)
                || parsed.partition_by.iter().any(contains_correlated_ref)
                || parsed
                    .order_by
                    .iter()
                    .any(|key| contains_correlated_ref(&key.expr))
        }
        ScalarAst::InputRef { .. }
        | ScalarAst::Literal { .. }
        | ScalarAst::Flag { .. }
        | ScalarAst::RelSubquery { .. }
        | ScalarAst::Sarg { .. } => false,
    }
}

fn contains_any_scalar_op(ast: &ScalarAst, targets: &[ScalarOp]) -> bool {
    targets.iter().any(|target| contains_scalar_op(ast, target))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_basic_calcite_scalars() {
        assert_eq!(
            classify_calcite_scalar("$12"),
            ScalarClass::InputRef { index: 12 }
        );
        assert_eq!(classify_calcite_scalar("'abc'"), ScalarClass::Literal);
        assert_eq!(classify_calcite_scalar("=($0, 1)"), ScalarClass::Call);
        assert_eq!(
            classify_calcite_scalar("LogicalProject(a=[$0])"),
            ScalarClass::Opaque
        );
    }

    #[test]
    fn rejects_legacy_text_subquery_scalars() {
        assert!(try_calcite_scalar("EXISTS({\nLogicalFilter(condition=[=($0, 1)])\n})").is_err());
    }

    #[test]
    fn leaves_input_refs_and_literals_non_opaque() {
        let mut features = BTreeSet::new();
        collect_scalar_expr(&calcite_scalar("$0"), &mut features);
        collect_scalar_expr(&calcite_scalar("42"), &mut features);
        assert!(!features.contains(&Feature::OpaqueScalar));
        assert!(!features.contains(&Feature::FormalSqlUnsupported));
    }

    #[test]
    fn tags_scalar_with_unsupported_core_lowering() {
        let expr = calcite_scalar("CAST('f'):BOOLEAN NOT NULL");
        assert_eq!(expr.class, ScalarClass::Literal);

        let mut features = BTreeSet::new();
        collect_scalar_expr(&expr, &mut features);

        assert!(features.contains(&Feature::OpaqueScalar));
        assert!(features.contains(&Feature::FormalSqlUnsupported));
    }

    #[test]
    fn does_not_tag_core_lowerable_case_as_formal_sql_unsupported() {
        let expr = calcite_scalar("CASE(IS NOT NULL($0), $0, 0)");

        let mut features = BTreeSet::new();
        collect_scalar_expr(&expr, &mut features);

        assert!(!features.contains(&Feature::OpaqueScalar));
        assert!(!features.contains(&Feature::FormalSqlUnsupported));
    }

    #[test]
    fn tags_string_concat_as_formal_sql_unsupported_even_when_core_lowerable() {
        let expr = calcite_scalar("||('store', $0)");

        let mut features = BTreeSet::new();
        collect_scalar_expr(&expr, &mut features);

        assert!(features.contains(&Feature::OpaqueScalar));
        assert!(features.contains(&Feature::FormalSqlUnsupported));
    }

    #[test]
    fn tags_string_functions_as_formal_sql_unsupported_even_when_core_lowerable() {
        for raw in ["LOWER($0)", "UPPER($0)", "SUBSTRING($0, 1, 2)"] {
            let expr = calcite_scalar(raw);

            let mut features = BTreeSet::new();
            collect_scalar_expr(&expr, &mut features);

            assert!(
                features.contains(&Feature::OpaqueScalar),
                "expected opaqueScalar for {raw}"
            );
            assert!(
                features.contains(&Feature::FormalSqlUnsupported),
                "expected formalSqlUnsupported for {raw}"
            );
        }
    }

    #[test]
    fn tags_like_and_numeric_functions_as_formal_sql_unsupported_even_when_core_lowerable() {
        for raw in ["LIKE($0, 'abc%')", "EXP($0)", "POWER($0, 2)"] {
            let expr = calcite_scalar(raw);

            let mut features = BTreeSet::new();
            collect_scalar_expr(&expr, &mut features);

            assert!(
                features.contains(&Feature::OpaqueScalar),
                "expected opaqueScalar for {raw}"
            );
            assert!(
                features.contains(&Feature::FormalSqlUnsupported),
                "expected formalSqlUnsupported for {raw}"
            );
        }
    }

    #[test]
    fn parses_nested_calcite_call_shape() {
        let expr = calcite_scalar(
            "AND(=($0, $23), >=($25, CAST('1998-08-04'):DATE NOT NULL), <=($25, +(CAST('1998-08-04'):DATE NOT NULL, 2592000000:INTERVAL DAY)))",
        );

        let ScalarAst::Call { operator, op, args } = expr.parsed else {
            panic!("expected parsed call");
        };
        assert_eq!(operator, "AND");
        assert_eq!(op, ScalarOp::And);
        assert_eq!(args.len(), 3);
        assert!(matches!(
            &args[1],
            ScalarAst::Call {
                operator,
                op: ScalarOp::Gte,
                args
            } if operator == ">=" && args.len() == 2
        ));
    }

    #[test]
    fn parses_window_scalar_shape() {
        let Ok(ScalarAst::Window { parsed: window, .. }) = parse_calcite_scalar_ast(
            "SUM(SUM($2)) OVER (PARTITION BY $0 ORDER BY $1 DESC NULLS LAST ROWS UNBOUNDED PRECEDING)",
        ) else {
            panic!("expected parsed window");
        };

        assert_eq!(window.function, "SUM");
        assert_eq!(window.args.len(), 1);
        assert!(matches!(
            &window.args[0],
            ScalarAst::Call {
                operator,
                args,
                ..
            } if operator == "SUM" && args.len() == 1
        ));
        assert_eq!(window.partition_by, vec![ScalarAst::InputRef { index: 0 }]);
        assert_eq!(window.order_by.len(), 1);
        assert_eq!(window.order_by[0].expr, ScalarAst::InputRef { index: 1 });
        assert_eq!(
            window.order_by[0].direction,
            Some(SortDirection::Descending)
        );
        assert_eq!(
            window.order_by[0].null_direction,
            Some(SortNullDirection::Last)
        );
        assert_eq!(window.frame.as_deref(), Some("ROWS UNBOUNDED PRECEDING"));
    }

    #[test]
    fn parses_window_inside_case_as_nested_calls() {
        let Ok(ScalarAst::Call { operator, args, .. }) = parse_calcite_scalar_ast(
            "CASE(>(COUNT($2) OVER (PARTITION BY $0 ORDER BY $1 NULLS FIRST ROWS UNBOUNDED PRECEDING), 0), CAST(SUM($2) OVER (PARTITION BY $0 ORDER BY $1 NULLS FIRST ROWS UNBOUNDED PRECEDING)):DECIMAL(19, 0), null:DECIMAL(19, 0))",
        ) else {
            panic!("expected parsed CASE call");
        };

        assert_eq!(operator, "CASE");
        assert_eq!(args.len(), 3);
        assert!(matches!(
            &args[0],
            ScalarAst::Call { args, .. }
                if matches!(&args[0], ScalarAst::Window { .. })
        ));
        assert!(matches!(
            &args[1],
            ScalarAst::TypeAnnotation { expr, .. }
                if matches!(&**expr, ScalarAst::Call { args, .. }
                    if matches!(&args[0], ScalarAst::Window { .. }))
        ));
    }

    #[test]
    fn splits_nested_argument_lists() {
        assert_eq!(
            split_calcite_arg_list("=($0, 1), +(2, 3), 'a,b'").unwrap(),
            vec!["=($0, 1)", "+(2, 3)", "'a,b'"]
        );
    }

    #[test]
    fn splits_argument_lists_with_braced_text_and_sarg() {
        assert_eq!(
            split_calcite_arg_list("$0, {\nLogicalProject(a=[$0])\n}, Sarg[(30..60]]").unwrap(),
            vec!["$0", "{\nLogicalProject(a=[$0])\n}", "Sarg[(30..60]]"]
        );
        assert_eq!(
            split_calcite_arg_list("$5, Sarg['1-URGENT':VARCHAR, '2-HIGH':VARCHAR]:VARCHAR")
                .unwrap(),
            vec!["$5", "Sarg['1-URGENT':VARCHAR, '2-HIGH':VARCHAR]:VARCHAR"]
        );
    }

    #[test]
    fn parses_sarg_and_bare_date_literals() {
        assert!(parse_calcite_scalar_ast("{\nLogicalProject(a=[$0])\n}").is_err());
        assert!(matches!(
            parse_calcite_scalar_ast("Sarg[(30..60]]"),
            Ok(ScalarAst::Sarg { .. })
        ));
        assert!(matches!(
            parse_calcite_scalar_ast("Sarg['1-URGENT':VARCHAR, '2-HIGH':VARCHAR]:VARCHAR"),
            Ok(ScalarAst::Sarg { .. })
        ));
        assert_eq!(
            parse_calcite_scalar_ast("1999-04-19").unwrap(),
            ScalarAst::Literal {
                raw: "1999-04-19".to_owned()
            }
        );
    }

    #[test]
    fn parses_sarg_shapes() {
        let Ok(ScalarAst::Sarg { parsed, .. }) = parse_calcite_scalar_ast("Sarg[(30..60]]") else {
            panic!("expected parsed sarg");
        };
        assert_eq!(parsed.ty, None);
        assert_eq!(parsed.items.len(), 1);
        assert_eq!(
            parsed.items[0],
            SargItem::Range {
                raw: "(30..60]".to_owned(),
                lower: Some(SargBound {
                    raw: "30".to_owned()
                }),
                upper: Some(SargBound {
                    raw: "60".to_owned()
                }),
                lower_inclusive: false,
                upper_inclusive: true,
            }
        );

        let Ok(ScalarAst::Sarg { parsed, .. }) =
            parse_calcite_scalar_ast("Sarg['1-URGENT':VARCHAR, '2-HIGH':VARCHAR]:VARCHAR")
        else {
            panic!("expected typed sarg");
        };
        assert_eq!(parsed.ty.as_deref(), Some("VARCHAR"));
        assert_eq!(parsed.items.len(), 2);
        assert_eq!(
            parsed.items[0],
            SargItem::Point {
                raw: "'1-URGENT':VARCHAR".to_owned(),
            }
        );

        let Ok(ScalarAst::Sarg { parsed, .. }) =
            parse_calcite_scalar_ast("Sarg[(-\u{221e}..4), (4..6), (6..+\u{221e})]")
        else {
            panic!("expected range-list sarg");
        };
        assert_eq!(parsed.items.len(), 3);
        assert_eq!(
            parsed.items[0],
            SargItem::Range {
                raw: "(-\u{221e}..4)".to_owned(),
                lower: None,
                upper: Some(SargBound {
                    raw: "4".to_owned()
                }),
                lower_inclusive: false,
                upper_inclusive: false,
            }
        );

        let Ok(ScalarAst::Sarg { parsed, .. }) = parse_calcite_scalar_ast("Sarg[-10, 2, 1995]")
        else {
            panic!("expected point-list sarg");
        };
        assert_eq!(parsed.items.len(), 3);
        assert_eq!(
            parsed.items[0],
            SargItem::Point {
                raw: "-10".to_owned(),
            }
        );
    }

    #[test]
    fn classifies_known_and_other_scalar_ops() {
        assert_eq!(classify_scalar_op("="), ScalarOp::Eq);
        assert_eq!(classify_scalar_op("<>"), ScalarOp::NotEq);
        assert_eq!(classify_scalar_op("is not null"), ScalarOp::IsNotNull);
        assert_eq!(
            classify_scalar_op("is not distinct from"),
            ScalarOp::IsNotDistinctFrom
        );
        assert_eq!(classify_scalar_op("LIKE"), ScalarOp::Like);
        assert_eq!(classify_scalar_op("||"), ScalarOp::StringConcat);
        assert_eq!(classify_scalar_op("substring"), ScalarOp::Substring);
        assert_eq!(classify_scalar_op("IN"), ScalarOp::In);
        assert_eq!(classify_scalar_op("EXISTS"), ScalarOp::Exists);
        assert_eq!(classify_scalar_op("$SCALAR_QUERY"), ScalarOp::ScalarQuery);
        assert_eq!(classify_scalar_op("SEARCH"), ScalarOp::Search);
        assert_eq!(classify_scalar_op("IS FALSE"), ScalarOp::IsFalse);
        assert_eq!(classify_scalar_op("IS NOT FALSE"), ScalarOp::IsNotFalse);
        assert_eq!(classify_scalar_op("+"), ScalarOp::Plus);
        assert_eq!(
            classify_scalar_op("ITEM"),
            ScalarOp::Other("ITEM".to_owned())
        );
    }
}
