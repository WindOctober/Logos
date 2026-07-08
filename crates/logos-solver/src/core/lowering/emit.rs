use std::collections::HashMap;

use super::*;

pub(super) fn emit_rocq_create_schema(tables: &[FormalTable]) -> String {
    let mut expr = "init_db".to_owned();
    for table in tables {
        expr = format!(
            "create_table\n  ({})\n  (Rel {})\n  ({})",
            indent_rocq_nested_expr(&expr, 3),
            rocq_string_literal(&table.relation),
            emit_rocq_attribute_list(&table.attributes)
        );
    }
    expr
}

pub(super) fn emit_rocq_schema_module(schema_expr: &str) -> String {
    format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance.
From Stdlib Require Import String ZArith.
Open Scope string_scope.
Open Scope Z_scope.

{}

Check generated_schema.
",
        emit_rocq_schema_definition("generated_schema", schema_expr)
    )
}

pub(super) fn emit_rocq_query_module(
    source: &FormalQuery,
    target: &FormalQuery,
) -> FormalQueryModule {
    let readable = RocqQueryDefinitions::from_query_pair(source, target);
    let shared_definitions = readable.emit_definitions();
    let source_definition = readable.emit_query_definition("source_query", source);
    let target_definition = readable.emit_query_definition("target_query", target);
    let rocq_module = format!(
        "\
From Logos Require Import FormalSQL.TNullSyntax.
From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

{}

{}

{}

Check source_query.
Check target_query.
",
        shared_definitions, source_definition, target_definition
    );
    FormalQueryModule {
        source_definition,
        target_definition,
        rocq_module,
    }
}

pub(super) fn emit_rocq_proof_module() -> FormalProofModule {
    let rocq_module = format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance SqlAlgebra FiniteBag FiniteSet Bool3.
From Logos Require Import FormalSQL.OccFacts FormalSQL.PiFacts FormalSQL.RewriteSpec.
From LogosGenerated Require Import Schema Queries.
From Stdlib Require Import String ZArith NArith List Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition generated_schema_conforms (db : db_state) : Prop :=
  @_relnames TNull db = @_relnames TNull generated_schema /\\
  forall r, @_basesort TNull db r =S= @_basesort TNull generated_schema r.

Definition eval_generated_query (db : db_state) (q : @query TNull relname) :=
  @eval_query TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    nil
    q.

Definition generated_equivalence_input :=
  (generated_schema, source_query, target_query).

Theorem generated_queries_equivalent :
  forall db : db_state,
    generated_schema_conforms db ->
    eval_generated_query db source_query =BE= eval_generated_query db target_query.
Proof.
  (* LOGOS_PROOF_HOLE: replace this proof with a complete proof ending in Qed. *)
Abort.

Check generated_schema_conforms.
Check eval_generated_query.
Check generated_schema.
Check source_query.
Check target_query.
Check generated_equivalence_input.
"
    );
    FormalProofModule { rocq_module }
}

fn emit_rocq_schema_definition(name: &str, schema_expr: &str) -> String {
    format!(
        "Definition {name} :=\n{}.",
        indent_rocq_expr(schema_expr, 2)
    )
}

#[derive(Debug, Default)]
struct RocqQueryDefinitions {
    select_lists: Vec<Vec<FormalSelectItem>>,
    predicates: Vec<FormalFormula>,
    shared_queries: Vec<FormalQuery>,
}

impl RocqQueryDefinitions {
    fn from_query_pair(source: &FormalQuery, target: &FormalQuery) -> Self {
        let mut definitions = Self::default();
        definitions.collect_select_lists(source);
        definitions.collect_select_lists(target);
        definitions.collect_predicates(source);
        definitions.collect_predicates(target);

        let mut query_counts = HashMap::new();
        let mut query_order = Vec::new();
        collect_query_counts(source, &mut query_counts, &mut query_order);
        collect_query_counts(target, &mut query_counts, &mut query_order);
        definitions.shared_queries = select_shared_queries(query_order, &query_counts);
        definitions
    }

    fn collect_select_lists(&mut self, query: &FormalQuery) {
        match query {
            FormalQuery::Projection { select, input } => {
                push_unique(&mut self.select_lists, select.clone());
                self.collect_select_lists(input);
            }
            FormalQuery::Group { select, input, .. } => {
                push_unique(&mut self.select_lists, select.clone());
                self.collect_select_lists(input);
            }
            FormalQuery::Set { left, right, .. }
            | FormalQuery::NaturalJoin { left, right }
            | FormalQuery::CrossJoin { left, right } => {
                self.collect_select_lists(left);
                self.collect_select_lists(right);
            }
            FormalQuery::Selection { input, .. } => self.collect_select_lists(input),
            FormalQuery::Table { .. } => {}
        }
    }

    fn collect_predicates(&mut self, query: &FormalQuery) {
        match query {
            FormalQuery::Selection { predicate, input } => {
                push_unique(&mut self.predicates, predicate.clone());
                self.collect_predicates(input);
            }
            FormalQuery::Group { having, input, .. } => {
                if !matches!(having, FormalFormula::True) {
                    push_unique(&mut self.predicates, having.clone());
                }
                self.collect_predicates(input);
            }
            FormalQuery::Set { left, right, .. }
            | FormalQuery::NaturalJoin { left, right }
            | FormalQuery::CrossJoin { left, right } => {
                self.collect_predicates(left);
                self.collect_predicates(right);
            }
            FormalQuery::Projection { input, .. } => self.collect_predicates(input),
            FormalQuery::Table { .. } => {}
        }
    }

    fn emit_definitions(&self) -> String {
        let mut definitions = Vec::new();
        for (index, select) in self.select_lists.iter().enumerate() {
            definitions.push(format!(
                "Definition select_list_{index} : SelectListT :=\n{}.",
                indent_rocq_expr(&emit_rocq_select_list(select), 2)
            ));
        }
        for (index, predicate) in self.predicates.iter().enumerate() {
            definitions.push(format!(
                "Definition predicate_{index} : Formula :=\n{}.",
                indent_rocq_expr(&emit_rocq_formula(predicate), 2)
            ));
        }
        for (index, query) in self.shared_queries.iter().enumerate() {
            definitions.push(format!(
                "Definition shared_query_{index} : Query :=\n{}.",
                indent_rocq_expr(&self.emit_query(query, false), 2)
            ));
        }
        definitions.join("\n\n")
    }

    fn emit_query_definition(&self, name: &str, query: &FormalQuery) -> String {
        format!(
            "Definition {name} : Query :=\n{}.",
            indent_rocq_expr(&self.emit_query(query, true), 2)
        )
    }

    fn emit_query(&self, query: &FormalQuery, allow_query_refs: bool) -> String {
        if allow_query_refs {
            if let Some(index) = self
                .shared_queries
                .iter()
                .position(|candidate| candidate == query)
            {
                return format!("shared_query_{index}");
            }
        }

        match query {
            FormalQuery::Table { relation } => {
                format!("Table {}", rocq_string_literal(relation))
            }
            FormalQuery::Set { op, left, right } => format!(
                "SetQuery {} ({}) ({})",
                emit_rocq_set_op(*op),
                self.emit_query(left, allow_query_refs),
                self.emit_query(right, allow_query_refs)
            ),
            FormalQuery::NaturalJoin { left, right } => format!(
                "NaturalJoin ({}) ({})",
                self.emit_query(left, allow_query_refs),
                self.emit_query(right, allow_query_refs)
            ),
            FormalQuery::CrossJoin { left, right } => format!(
                "CrossJoin ({}) ({})",
                self.emit_query(left, allow_query_refs),
                self.emit_query(right, allow_query_refs)
            ),
            FormalQuery::Projection { select, input } => format!(
                "Pi ({}) ({})",
                self.emit_select_list(select),
                self.emit_query(input, allow_query_refs)
            ),
            FormalQuery::Selection { predicate, input } => format!(
                "Sigma ({}) ({})",
                self.emit_formula(predicate),
                self.emit_query(input, allow_query_refs)
            ),
            FormalQuery::Group {
                select,
                group_by,
                having,
                input,
            } => format!(
                "Gamma ({}) ({}) ({}) ({})",
                self.emit_select_list(select),
                emit_rocq_list(group_by, emit_rocq_aggregate_term),
                self.emit_formula(having),
                self.emit_query(input, allow_query_refs)
            ),
        }
    }

    fn emit_select_list(&self, select: &[FormalSelectItem]) -> String {
        self.select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("select_list_{index}"))
            .unwrap_or_else(|| emit_rocq_select_list(select))
    }

    fn emit_formula(&self, formula: &FormalFormula) -> String {
        self.predicates
            .iter()
            .position(|candidate| candidate == formula)
            .map(|index| format!("predicate_{index}"))
            .unwrap_or_else(|| emit_rocq_formula(formula))
    }
}

fn push_unique<T: PartialEq>(items: &mut Vec<T>, item: T) {
    if !items.iter().any(|candidate| candidate == &item) {
        items.push(item);
    }
}

fn collect_query_counts(
    query: &FormalQuery,
    counts: &mut HashMap<FormalQuery, usize>,
    order: &mut Vec<FormalQuery>,
) {
    let count = counts.entry(query.clone()).or_insert_with(|| {
        order.push(query.clone());
        0
    });
    *count += 1;

    match query {
        FormalQuery::Set { left, right, .. }
        | FormalQuery::NaturalJoin { left, right }
        | FormalQuery::CrossJoin { left, right } => {
            collect_query_counts(left, counts, order);
            collect_query_counts(right, counts, order);
        }
        FormalQuery::Projection { input, .. }
        | FormalQuery::Selection { input, .. }
        | FormalQuery::Group { input, .. } => collect_query_counts(input, counts, order),
        FormalQuery::Table { .. } => {}
    }
}

fn select_shared_queries(
    query_order: Vec<FormalQuery>,
    query_counts: &HashMap<FormalQuery, usize>,
) -> Vec<FormalQuery> {
    let candidates = query_order
        .into_iter()
        .filter(|query| {
            query_counts.get(query).copied().unwrap_or_default() > 1
                && !matches!(query, FormalQuery::Table { .. })
        })
        .collect::<Vec<_>>();

    candidates
        .iter()
        .filter(|query| {
            let total = query_counts.get(*query).copied().unwrap_or_default();
            let covered_by_larger_shared_queries = candidates
                .iter()
                .filter(|container| *container != *query)
                .map(|container| {
                    query_counts.get(container).copied().unwrap_or_default()
                        * proper_subquery_occurrences(container, query)
                })
                .sum::<usize>();
            total > covered_by_larger_shared_queries
        })
        .cloned()
        .collect()
}

fn proper_subquery_occurrences(container: &FormalQuery, needle: &FormalQuery) -> usize {
    query_children(container)
        .into_iter()
        .map(|child| query_occurrences(child, needle))
        .sum()
}

fn query_occurrences(query: &FormalQuery, needle: &FormalQuery) -> usize {
    let root = usize::from(query == needle);
    root + query_children(query)
        .into_iter()
        .map(|child| query_occurrences(child, needle))
        .sum::<usize>()
}

fn query_children(query: &FormalQuery) -> Vec<&FormalQuery> {
    match query {
        FormalQuery::Set { left, right, .. }
        | FormalQuery::NaturalJoin { left, right }
        | FormalQuery::CrossJoin { left, right } => vec![left, right],
        FormalQuery::Projection { input, .. }
        | FormalQuery::Selection { input, .. }
        | FormalQuery::Group { input, .. } => vec![input],
        FormalQuery::Table { .. } => Vec::new(),
    }
}

fn emit_rocq_set_op(op: FormalSetOp) -> &'static str {
    match op {
        FormalSetOp::Union => "SetUnion",
        FormalSetOp::UnionMax => "SetUnionMax",
        FormalSetOp::Inter => "SetInter",
        FormalSetOp::Diff => "SetDiff",
    }
}

fn emit_rocq_select_list(select: &[FormalSelectItem]) -> String {
    let columns = select
        .iter()
        .map(identity_select_column)
        .collect::<Option<Vec<_>>>();
    if let Some(columns) = columns {
        return format!("SelectColumns {}", emit_rocq_list_expr(&columns));
    }
    format!(
        "SelectList {}",
        emit_rocq_list(select, emit_rocq_select_item)
    )
}

fn emit_rocq_select_item(item: &FormalSelectItem) -> String {
    if let FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::Attribute { name, constructor },
    } = &item.expr
    {
        if name == &item.alias && constructor == &item.alias_constructor {
            if let Some(select_constructor) = identity_select_constructor(constructor) {
                return emit_rocq_named_helper(select_constructor, name, constructor);
            }
        }
    }
    format!(
        "SelectAs ({}) ({})",
        emit_rocq_aggregate_term(&item.expr),
        emit_rocq_attribute(&item.alias_constructor, &item.alias)
    )
}

fn emit_rocq_aggregate_term(term: &FormalAggregateTerm) -> String {
    match term {
        FormalAggregateTerm::Expr { term } => match term {
            FormalFunctionTerm::Attribute { name, constructor } => {
                if let Some(dot_constructor) = dot_constructor(constructor) {
                    emit_rocq_named_helper(dot_constructor, name, constructor)
                } else {
                    format!("AExpr ({})", emit_rocq_function_term(term))
                }
            }
            FormalFunctionTerm::Constant { raw, ty } => emit_rocq_constant_aggregate(raw, *ty),
            _ => format!("AExpr ({})", emit_rocq_function_term(term)),
        },
        FormalAggregateTerm::Aggregate { function, arg } => format!(
            "AAggregate {} ({})",
            rocq_string_literal(function),
            emit_rocq_function_term(arg)
        ),
        FormalAggregateTerm::Function { symbol, args } => format!(
            "AFunction {} ({})",
            rocq_string_literal(symbol),
            emit_rocq_list(args, emit_rocq_aggregate_term)
        ),
    }
}

fn emit_rocq_function_term(term: &FormalFunctionTerm) -> String {
    match term {
        FormalFunctionTerm::Constant { raw, ty } => emit_rocq_constant_function(raw, *ty),
        FormalFunctionTerm::Attribute { name, constructor } => {
            format!("Dot ({})", emit_rocq_attribute(constructor, name))
        }
        FormalFunctionTerm::Function { symbol, args } => format!(
            "Function {} ({})",
            rocq_string_literal(symbol),
            emit_rocq_list(args, emit_rocq_function_term)
        ),
    }
}

fn emit_rocq_formula(formula: &FormalFormula) -> String {
    match formula {
        FormalFormula::True => "TrueFormula".to_owned(),
        FormalFormula::False => "Not (TrueFormula)".to_owned(),
        FormalFormula::Predicate { predicate, args } => format!(
            "Pred {} ({})",
            rocq_string_literal(predicate),
            emit_rocq_list(args, emit_rocq_aggregate_term)
        ),
        FormalFormula::And { left, right } => {
            emit_rocq_call("And", &[emit_rocq_formula(left), emit_rocq_formula(right)])
        }
        FormalFormula::Or { left, right } => {
            emit_rocq_call("Or", &[emit_rocq_formula(left), emit_rocq_formula(right)])
        }
        FormalFormula::Not { formula } => format!("Not ({})", emit_rocq_formula(formula)),
        FormalFormula::Exists { query } => format!("ExistsQuery ({})", emit_rocq_query(query)),
    }
}

fn emit_rocq_query(query: &FormalQuery) -> String {
    RocqQueryDefinitions::default().emit_query(query, false)
}

fn emit_rocq_call(function: &str, args: &[String]) -> String {
    let single_line = format!(
        "{} {}",
        function,
        args.iter()
            .map(|arg| format!("({arg})"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    if single_line.len() <= 72 && !args.iter().any(|arg| arg.contains('\n')) {
        return single_line;
    }

    let mut lines = vec![function.to_owned()];
    for arg in args {
        lines.push(format!("  ({})", indent_rocq_expr(arg, 2).trim_start()));
    }
    lines.join("\n")
}

fn emit_rocq_attribute(constructor: &str, name: &str) -> String {
    let helper = match constructor {
        "Attr_Z" => "AttrZ",
        "Attr_string" => "AttrString",
        "Attr_bool" => "AttrBool",
        "Attr_float" => "AttrFloat",
        "Attr_date" => "AttrDate",
        _ if timestamp_constructor_precision(constructor).is_some() => "AttrTimestamp",
        other => other,
    };
    emit_rocq_named_helper(helper, name, constructor)
}

fn emit_rocq_schema_attribute(constructor: &str, name: &str) -> String {
    if let Some(precision) = timestamp_constructor_precision(constructor) {
        return format!("Attr_timestamp {} {precision}", rocq_string_literal(name));
    }
    format!("{constructor} {}", rocq_string_literal(name))
}

fn emit_rocq_named_helper(helper: &str, name: &str, constructor: &str) -> String {
    if let Some(precision) = timestamp_constructor_precision(constructor) {
        format!("{helper} {} {precision}", rocq_string_literal(name))
    } else {
        format!("{helper} {}", rocq_string_literal(name))
    }
}

fn timestamp_constructor_precision(constructor: &str) -> Option<u32> {
    constructor.strip_prefix("Attr_timestamp#")?.parse().ok()
}

fn identity_select_constructor(attribute_constructor: &str) -> Option<&'static str> {
    match attribute_constructor {
        "Attr_Z" => Some("SelectZ"),
        "Attr_string" => Some("SelectString"),
        "Attr_bool" => Some("SelectBool"),
        "Attr_float" => Some("SelectFloat"),
        "Attr_date" => Some("SelectDate"),
        _ if timestamp_constructor_precision(attribute_constructor).is_some() => {
            Some("SelectTimestamp")
        }
        _ => None,
    }
}

fn identity_select_column(item: &FormalSelectItem) -> Option<String> {
    let FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::Attribute { name, constructor },
    } = &item.expr
    else {
        return None;
    };
    if name != &item.alias || constructor != &item.alias_constructor {
        return None;
    }
    let column_constructor = match constructor.as_str() {
        "Attr_Z" => "ZColumn",
        "Attr_string" => "StringColumn",
        "Attr_bool" => "BoolColumn",
        "Attr_float" => "FloatColumn",
        "Attr_date" => "DateColumn",
        _ if timestamp_constructor_precision(constructor).is_some() => "TimestampColumn",
        _ => return None,
    };
    Some(emit_rocq_named_helper(
        column_constructor,
        name,
        constructor,
    ))
}

fn dot_constructor(attribute_constructor: &str) -> Option<&'static str> {
    match attribute_constructor {
        "Attr_Z" => Some("DotZ"),
        "Attr_string" => Some("DotString"),
        "Attr_bool" => Some("DotBool"),
        "Attr_float" => Some("DotFloat"),
        "Attr_date" => Some("DotDate"),
        _ if timestamp_constructor_precision(attribute_constructor).is_some() => {
            Some("DotTimestamp")
        }
        _ => None,
    }
}

fn emit_rocq_constant_aggregate(raw: &str, ty: Option<FormalAttributeType>) -> String {
    let trimmed = raw.trim();
    if trimmed.eq_ignore_ascii_case("null") {
        return match ty {
            Some(FormalAttributeType::Z) => "NullZ".to_owned(),
            Some(FormalAttributeType::String) | None => "NullString".to_owned(),
            Some(FormalAttributeType::Bool) => "NullBool".to_owned(),
            Some(FormalAttributeType::Float) => "NullFloat".to_owned(),
            Some(FormalAttributeType::Date) => "NullDate".to_owned(),
            Some(FormalAttributeType::Timestamp { .. }) => "NullTimestamp".to_owned(),
        };
    }
    if trimmed.eq_ignore_ascii_case("true") {
        return "CstBool true".to_owned();
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return "CstBool false".to_owned();
    }
    if matches!(ty, Some(FormalAttributeType::Date)) {
        if let Some(days) = parse_date_literal(trimmed) {
            return format!("CstDate ({days})");
        }
    }
    if let Some(FormalAttributeType::Timestamp { precision }) = ty {
        if let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision)) {
            return format!("CstTimestamp ({micros})");
        }
    }
    if let Some(unquoted) = sql_string_literal_content(trimmed) {
        return format!("CstString {}", rocq_string_literal(&unquoted));
    }
    if is_integer_literal(trimmed) {
        return format!("CstZ ({trimmed})");
    }
    format!("CstString {}", rocq_string_literal(trimmed))
}

fn emit_rocq_constant_function(raw: &str, ty: Option<FormalAttributeType>) -> String {
    format!("Constant ({})", emit_rocq_value(raw, ty))
}

fn emit_rocq_value(raw: &str, ty: Option<FormalAttributeType>) -> String {
    let trimmed = raw.trim();
    if trimmed.eq_ignore_ascii_case("null") {
        return match ty {
            Some(FormalAttributeType::Z) => "Value_Z None".to_owned(),
            Some(FormalAttributeType::String) | None => "Value_string None".to_owned(),
            Some(FormalAttributeType::Bool) => "Value_bool None".to_owned(),
            Some(FormalAttributeType::Float) => "Value_float None".to_owned(),
            Some(FormalAttributeType::Date) => "Value_date None".to_owned(),
            Some(FormalAttributeType::Timestamp { .. }) => "Value_timestamp None".to_owned(),
        };
    }
    if trimmed.eq_ignore_ascii_case("true") {
        return "Value_bool (Some true)".to_owned();
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return "Value_bool (Some false)".to_owned();
    }
    if matches!(ty, Some(FormalAttributeType::Date)) {
        if let Some(days) = parse_date_literal(trimmed) {
            return format!("Value_date (Some ({days})%Z)");
        }
    }
    if let Some(FormalAttributeType::Timestamp { precision }) = ty {
        if let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision)) {
            return format!("Value_timestamp (Some ({micros})%Z)");
        }
    }
    if let Some(unquoted) = sql_string_literal_content(trimmed) {
        return format!("Value_string (Some {})", rocq_string_literal(&unquoted));
    }
    if is_integer_literal(trimmed) {
        return format!("Value_Z (Some ({trimmed})%Z)");
    }
    format!("Value_string (Some {})", rocq_string_literal(trimmed))
}

fn emit_rocq_list<T>(items: &[T], emit: fn(&T) -> String) -> String {
    let rendered = items.iter().map(emit).collect::<Vec<_>>();
    emit_rocq_list_expr(&rendered)
}

fn emit_rocq_list_expr(items: &[String]) -> String {
    if items.is_empty() {
        return "[]".to_owned();
    }
    let single_line = format!("[{}]", items.join("; "));
    if items.len() <= 3 && single_line.len() <= 88 && !items.iter().any(|item| item.contains('\n'))
    {
        return single_line;
    }

    let mut lines = Vec::with_capacity(items.len() + 2);
    lines.push("[".to_owned());
    for (index, item) in items.iter().enumerate() {
        let suffix = if index + 1 == items.len() { "" } else { ";" };
        let item = indent_rocq_expr(item, 2);
        lines.push(format!("{item}{suffix}"));
    }
    lines.push("]".to_owned());
    lines.join("\n")
}

fn emit_rocq_attribute_list(attributes: &[FormalAttribute]) -> String {
    if attributes.is_empty() {
        return "nil".to_owned();
    }
    let mut rendered = attributes
        .iter()
        .map(|attribute| emit_rocq_schema_attribute(&attribute.constructor, &attribute.name))
        .collect::<Vec<_>>();
    rendered.push("nil".to_owned());
    rendered.join(" :: ")
}

fn indent_rocq_expr(expr: &str, spaces: usize) -> String {
    let padding = " ".repeat(spaces);
    expr.lines()
        .map(|line| format!("{padding}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
        .to_owned()
}

fn indent_rocq_nested_expr(expr: &str, spaces: usize) -> String {
    indent_rocq_expr(expr, spaces).trim_start().to_owned()
}

fn rocq_string_literal(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

fn parse_date_literal(raw: &str) -> Option<i64> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    if let Ok(days) = value.parse::<i64>() {
        return Some(days);
    }
    let (year, month, day) = parse_ymd(&value)?;
    Some(days_from_civil(year, month, day))
}

pub(super) fn timestamp_literal_conforms_to_precision(raw: &str, precision: u32) -> bool {
    parse_timestamp_literal(raw, precision).is_some()
}

fn parse_timestamp_literal(raw: &str, precision: u32) -> Option<i64> {
    if precision > 6 {
        return None;
    }
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    if let Ok(micros) = value.parse::<i64>() {
        return timestamp_micros_with_precision(micros, precision);
    }
    let (date_part, time_part) = value
        .split_once(' ')
        .or_else(|| value.split_once('T'))
        .unwrap_or((value.as_str(), "00:00:00"));
    let (year, month, day) = parse_ymd(date_part)?;
    let (hour, minute, second, micros) = parse_hms(time_part)?;
    if !valid_time(hour, minute, second, micros) {
        return None;
    }
    timestamp_micros_with_precision(
        days_from_civil(year, month, day) * MICROS_PER_DAY
            + hour * MICROS_PER_HOUR
            + minute * MICROS_PER_MINUTE
            + second * MICROS_PER_SECOND
            + micros,
        precision,
    )
}

fn timestamp_micros_with_precision(micros: i64, precision: u32) -> Option<i64> {
    let factor = 10_i64.pow(6 - precision);
    if micros.rem_euclid(factor) == 0 {
        Some(micros)
    } else {
        None
    }
}

fn parse_ymd(value: &str) -> Option<(i64, i64, i64)> {
    let mut parts = value.split('-');
    let year = parts.next()?.parse::<i64>().ok()?;
    let month = parts.next()?.parse::<i64>().ok()?;
    let day = parts.next()?.parse::<i64>().ok()?;
    if parts.next().is_some() || !valid_ymd(year, month, day) {
        return None;
    }
    Some((year, month, day))
}

fn parse_hms(value: &str) -> Option<(i64, i64, i64, i64)> {
    let mut parts = value.split(':');
    let hour = parts.next()?.parse::<i64>().ok()?;
    let minute = parts.next()?.parse::<i64>().ok()?;
    let second_part = parts.next()?;
    if parts.next().is_some() {
        return None;
    }
    let (second_text, fraction_text) = second_part.split_once('.').unwrap_or((second_part, ""));
    let second = second_text.parse::<i64>().ok()?;
    let micros = if fraction_text.is_empty() {
        0
    } else if fraction_text.len() <= 6 && fraction_text.chars().all(|ch| ch.is_ascii_digit()) {
        let padded = format!("{fraction_text:0<6}");
        padded.parse::<i64>().ok()?
    } else {
        return None;
    };
    Some((hour, minute, second, micros))
}

fn valid_time(hour: i64, minute: i64, second: i64, micros: i64) -> bool {
    (0..=23).contains(&hour)
        && (0..=59).contains(&minute)
        && (0..=59).contains(&second)
        && (0..=999_999).contains(&micros)
}

const MICROS_PER_SECOND: i64 = 1_000_000;
const MICROS_PER_MINUTE: i64 = 60 * MICROS_PER_SECOND;
const MICROS_PER_HOUR: i64 = 60 * MICROS_PER_MINUTE;
const MICROS_PER_DAY: i64 = 24 * MICROS_PER_HOUR;

fn valid_ymd(year: i64, month: i64, day: i64) -> bool {
    (1..=12).contains(&month) && (1..=days_in_month(year, month)).contains(&day)
}

fn is_leap_year(year: i64) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

fn days_in_month(year: i64, month: i64) -> i64 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => 0,
    }
}

fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let yoe = year - era * 400;
    let mp = if month > 2 { month - 3 } else { month + 9 };
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}
