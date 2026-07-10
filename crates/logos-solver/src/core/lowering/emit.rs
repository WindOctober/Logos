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
    source: &FormalListQuery,
    target: &FormalListQuery,
) -> FormalQueryModule {
    let readable = RocqQueryDefinitions::from_list_query_pair(source, target);
    let shared_definitions = readable.emit_definitions();
    let source_bag_definition = source
        .as_bag_query()
        .map(|query| readable.emit_query_definition("source_query", query));
    let target_bag_definition = target
        .as_bag_query()
        .map(|query| readable.emit_query_definition("target_query", query));
    let source_definition = readable.emit_list_query_definition("source_list_query", source);
    let target_definition = readable.emit_list_query_definition("target_list_query", target);
    let mut query_definitions = Vec::new();
    if let Some(definition) = source_bag_definition {
        query_definitions.push(definition);
    }
    if let Some(definition) = target_bag_definition {
        query_definitions.push(definition);
    }
    query_definitions.push(source_definition.clone());
    query_definitions.push(target_definition.clone());
    let rocq_module = format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance SqlOrder SqlListAlgebra.
From Logos Require Import FormalSQL.TNullSyntax.
From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

{}

{}

Check source_list_query.
Check target_list_query.
",
        shared_definitions,
        query_definitions.join("\n\n")
    );
    FormalQueryModule {
        source_definition,
        target_definition,
        rocq_module,
    }
}

pub(super) fn can_emit_bag_bridge_proof(
    source: &FormalListQuery,
    target: &FormalListQuery,
) -> bool {
    source.as_bag_query().is_some() && target.as_bag_query().is_some()
}

pub(super) fn emit_rocq_bag_bridge_proof_module() -> FormalProofModule {
    let rocq_module = format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance Values SqlAlgebra SqlListAlgebra SqlListFacts FiniteBag FiniteSet Bool3.
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

Definition generated_value_is_null (v : value) : bool :=
  NullValues.is_null_value v.

Definition generated_list_query_equiv
    (db : db_state)
    (q1 q2 : @list_query TNull relname) : Prop :=
  @list_query_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    generated_value_is_null
    nil
    q1
    q2.

Definition generated_equivalence_input :=
  (generated_schema, source_list_query, target_list_query).

Theorem generated_queries_equivalent :
  forall db : db_state,
    generated_schema_conforms db ->
    generated_list_query_equiv db source_list_query target_list_query.
Proof.
  intros db Hschema.
  unfold generated_list_query_equiv, source_list_query, target_list_query.
  apply list_equiv_l_bag_of_bag_query_equiv.
  unfold bag_query_equiv.
  (* LOGOS_PROOF_HOLE: prove the remaining bag equality and end with Qed. *)
Abort.

Check generated_schema_conforms.
Check eval_generated_query.
Check generated_list_query_equiv.
Check generated_schema.
Check source_query.
Check target_query.
Check source_list_query.
Check target_list_query.
Check generated_equivalence_input.
"
    );
    FormalProofModule { rocq_module }
}

pub(super) fn emit_rocq_list_proof_module() -> FormalProofModule {
    let rocq_module = format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance Values SqlAlgebra SqlListAlgebra SqlListFacts FiniteBag FiniteSet Bool3.
From Logos Require Import FormalSQL.OccFacts FormalSQL.PiFacts FormalSQL.RewriteSpec.
From LogosGenerated Require Import Schema Queries.
From Stdlib Require Import String ZArith NArith List Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition generated_schema_conforms (db : db_state) : Prop :=
  @_relnames TNull db = @_relnames TNull generated_schema /\\
  forall r, @_basesort TNull db r =S= @_basesort TNull generated_schema r.

Definition generated_value_is_null (v : value) : bool :=
  NullValues.is_null_value v.

Definition generated_list_query_equiv
    (db : db_state)
    (q1 q2 : @list_query TNull relname) : Prop :=
  @list_query_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    generated_value_is_null
    nil
    q1
    q2.

Definition generated_equivalence_input :=
  (generated_schema, source_list_query, target_list_query).

Theorem generated_queries_equivalent :
  forall db : db_state,
    generated_schema_conforms db ->
    generated_list_query_equiv db source_list_query target_list_query.
Proof.
  intros db Hschema.
  (* LOGOS_PROOF_HOLE: prove the list-observation equivalence and end with Qed. *)
Abort.

Check generated_schema_conforms.
Check generated_list_query_equiv.
Check generated_schema.
Check source_list_query.
Check target_list_query.
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
    fn from_list_query_pair(source: &FormalListQuery, target: &FormalListQuery) -> Self {
        let mut definitions = Self::default();
        definitions.collect_list_query(source);
        definitions.collect_list_query(target);

        let mut query_counts = HashMap::new();
        let mut query_order = Vec::new();
        collect_list_query_counts(source, &mut query_counts, &mut query_order);
        collect_list_query_counts(target, &mut query_counts, &mut query_order);
        definitions.shared_queries = select_shared_queries(query_order, &query_counts);
        definitions
    }

    fn collect_list_query(&mut self, query: &FormalListQuery) {
        match query {
            FormalListQuery::Empty { .. } => {}
            FormalListQuery::Bag { input } => {
                self.collect_select_lists(input);
                self.collect_predicates(input);
            }
            FormalListQuery::OrderBy { input, .. }
            | FormalListQuery::Offset { input, .. }
            | FormalListQuery::Fetch { input, .. } => self.collect_list_query(input),
        }
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
            FormalQuery::Empty { .. } | FormalQuery::EmptyTuple | FormalQuery::Table { .. } => {}
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
            FormalQuery::Empty { .. } | FormalQuery::EmptyTuple | FormalQuery::Table { .. } => {}
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

    fn emit_list_query_definition(&self, name: &str, query: &FormalListQuery) -> String {
        format!(
            "Definition {name} : ListQuery :=\n{}.",
            indent_rocq_expr(&self.emit_list_query(query), 2)
        )
    }

    fn emit_list_query(&self, query: &FormalListQuery) -> String {
        match query {
            FormalListQuery::Empty { columns } => {
                format!("EmptyRelation {}", emit_rocq_query_attribute_list(columns))
            }
            FormalListQuery::Bag { input } => format!("Bag ({})", self.emit_query(input, true)),
            FormalListQuery::OrderBy { keys, input } => format!(
                "OrderBy ({}) ({})",
                emit_rocq_list(keys, emit_rocq_sort_key),
                self.emit_list_query(input)
            ),
            FormalListQuery::Offset { count, input } => {
                format!("Offset ({}%nat) ({})", count, self.emit_list_query(input))
            }
            FormalListQuery::Fetch { count, input } => {
                format!("Fetch ({}%nat) ({})", count, self.emit_list_query(input))
            }
        }
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
            FormalQuery::Empty { columns } => {
                format!(
                    "EmptyBagRelation {}",
                    emit_rocq_query_attribute_list(columns)
                )
            }
            FormalQuery::EmptyTuple => "EmptyTuple".to_owned(),
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
        FormalQuery::Empty { .. } | FormalQuery::EmptyTuple | FormalQuery::Table { .. } => {}
    }
}

fn collect_list_query_counts(
    query: &FormalListQuery,
    counts: &mut HashMap<FormalQuery, usize>,
    order: &mut Vec<FormalQuery>,
) {
    match query {
        FormalListQuery::Empty { .. } => {}
        FormalListQuery::Bag { input } => collect_query_counts(input, counts, order),
        FormalListQuery::OrderBy { input, .. }
        | FormalListQuery::Offset { input, .. }
        | FormalListQuery::Fetch { input, .. } => collect_list_query_counts(input, counts, order),
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
                && !matches!(
                    query,
                    FormalQuery::Empty { .. } | FormalQuery::EmptyTuple | FormalQuery::Table { .. }
                )
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
        FormalQuery::Empty { .. } | FormalQuery::EmptyTuple | FormalQuery::Table { .. } => {
            Vec::new()
        }
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

fn emit_rocq_sort_key(key: &FormalSortKey) -> String {
    format!(
        "{} ({})",
        emit_rocq_sort_key_constructor(key.direction, key.null_direction),
        emit_rocq_attribute(key.attribute_ty, &key.attribute_name)
    )
}

fn emit_rocq_sort_key_constructor(
    direction: FormalSortDirection,
    null_direction: FormalNullDirection,
) -> &'static str {
    match (direction, null_direction) {
        (FormalSortDirection::Asc, FormalNullDirection::First) => "SortAscNullsFirst",
        (FormalSortDirection::Asc, FormalNullDirection::Last) => "SortAscNullsLast",
        (FormalSortDirection::Desc, FormalNullDirection::First) => "SortDescNullsFirst",
        (FormalSortDirection::Desc, FormalNullDirection::Last) => "SortDescNullsLast",
    }
}

fn column_ref_constructor(attribute_ty: FormalAttributeType) -> &'static str {
    match attribute_ty {
        FormalAttributeType::Z => "ZColumn",
        FormalAttributeType::String => "StringColumn",
        FormalAttributeType::Bool => "BoolColumn",
        FormalAttributeType::Float => "FloatColumn",
        FormalAttributeType::Double => "DoubleColumn",
        FormalAttributeType::Decimal { .. } => "DecimalColumn",
        FormalAttributeType::Date => "DateColumn",
        FormalAttributeType::Time => "TimeColumn",
        FormalAttributeType::Timestamp { .. } => "TimestampColumn",
        FormalAttributeType::Timestamptz { .. } => "TimestamptzColumn",
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
        term: FormalFunctionTerm::Attribute { name, ty },
    } = &item.expr
    {
        if name == &item.alias && attribute_types_emit_equivalent(*ty, item.alias_ty) {
            if let Some(select_constructor) = identity_select_constructor(*ty) {
                return emit_rocq_named_helper(select_constructor, name, *ty);
            }
        }
    }
    format!(
        "SelectAs ({}) ({})",
        emit_rocq_aggregate_term(&item.expr),
        emit_rocq_attribute(item.alias_ty, &item.alias)
    )
}

fn emit_rocq_aggregate_term(term: &FormalAggregateTerm) -> String {
    match term {
        FormalAggregateTerm::Expr { term } => match term {
            FormalFunctionTerm::Attribute { name, ty } => {
                if let Some(dot_constructor) = dot_constructor(*ty) {
                    emit_rocq_named_helper(dot_constructor, name, *ty)
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
        FormalAggregateTerm::DistinctAggregate { function, arg } => format!(
            "ADistinctAggregate {} ({})",
            rocq_string_literal(function),
            emit_rocq_function_term(arg)
        ),
        FormalAggregateTerm::CountStar => "ACountStar".to_owned(),
        FormalAggregateTerm::Function { symbol, args } => format!(
            "AFunction {} ({})",
            rocq_string_literal(symbol),
            emit_rocq_list(args, emit_rocq_aggregate_term)
        ),
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => format!(
            "AFunction \"case\" ({})",
            emit_rocq_list(
                &case_function_args(branches, else_expr),
                emit_rocq_aggregate_term
            )
        ),
    }
}

fn case_function_args(
    branches: &[FormalCaseBranch],
    else_expr: &FormalAggregateTerm,
) -> Vec<FormalAggregateTerm> {
    let mut args = Vec::with_capacity(branches.len() * 2 + 1);
    for branch in branches {
        args.push(branch.when.clone());
        args.push(branch.then_expr.clone());
    }
    args.push(else_expr.clone());
    args
}

fn emit_rocq_function_term(term: &FormalFunctionTerm) -> String {
    match term {
        FormalFunctionTerm::Constant { raw, ty } => emit_rocq_constant_function(raw, *ty),
        FormalFunctionTerm::Attribute { name, ty } => {
            format!("Dot ({})", emit_rocq_attribute(*ty, name))
        }
        FormalFunctionTerm::Cast { function, arg, .. } => format!(
            "Function {} ({})",
            rocq_string_literal(function),
            emit_rocq_list(&[*arg.clone()], emit_rocq_function_term)
        ),
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

fn emit_rocq_attribute(ty: FormalAttributeType, name: &str) -> String {
    let helper = match ty {
        FormalAttributeType::Z => "AttrZ",
        FormalAttributeType::String => "AttrString",
        FormalAttributeType::Bool => "AttrBool",
        FormalAttributeType::Float => "AttrFloat",
        FormalAttributeType::Double => "AttrDouble",
        FormalAttributeType::Decimal { .. } => "AttrDecimal",
        FormalAttributeType::Date => "AttrDate",
        FormalAttributeType::Time => "AttrTime",
        FormalAttributeType::Timestamp { .. } => "AttrTimestamp",
        FormalAttributeType::Timestamptz { .. } => "AttrTimestamptz",
    };
    emit_rocq_named_helper(helper, name, ty)
}

fn emit_rocq_query_attribute_list(attributes: &[FormalAttribute]) -> String {
    let rendered = attributes
        .iter()
        .map(|attribute| emit_rocq_attribute(attribute.ty, &attribute.name))
        .collect::<Vec<_>>();
    emit_rocq_list_expr(&rendered)
}

fn emit_rocq_schema_attribute(ty: FormalAttributeType, name: &str) -> String {
    match ty {
        FormalAttributeType::Z => format!("Attr_Z {}", rocq_string_literal(name)),
        FormalAttributeType::String => format!("Attr_string {}", rocq_string_literal(name)),
        FormalAttributeType::Bool => format!("Attr_bool {}", rocq_string_literal(name)),
        FormalAttributeType::Float => format!("Attr_float {}", rocq_string_literal(name)),
        FormalAttributeType::Double => format!("Attr_double {}", rocq_string_literal(name)),
        FormalAttributeType::Decimal { precision, scale } => {
            let (precision, scale) = checked_decimal_typmod(precision, scale);
            format!(
                "Attr_decimal {} {precision} {scale}",
                rocq_string_literal(name)
            )
        }
        FormalAttributeType::Date => format!("Attr_date {}", rocq_string_literal(name)),
        FormalAttributeType::Time => format!("Attr_time {}", rocq_string_literal(name)),
        FormalAttributeType::Timestamp { precision } => format!(
            "Attr_timestamp {} {}",
            rocq_string_literal(name),
            timestamp_precision(precision)
        ),
        FormalAttributeType::Timestamptz { precision } => format!(
            "Attr_timestamptz {} {}",
            rocq_string_literal(name),
            timestamp_precision(precision)
        ),
    }
}

fn emit_rocq_named_helper(helper: &str, name: &str, ty: FormalAttributeType) -> String {
    match ty {
        FormalAttributeType::Decimal { precision, scale } => {
            let (precision, scale) = checked_decimal_typmod(precision, scale);
            format!("{helper} {} {precision} {scale}", rocq_string_literal(name))
        }
        FormalAttributeType::Timestamp { precision }
        | FormalAttributeType::Timestamptz { precision } => {
            format!(
                "{helper} {} {}",
                rocq_string_literal(name),
                timestamp_precision(precision)
            )
        }
        _ => format!("{helper} {}", rocq_string_literal(name)),
    }
}

fn checked_decimal_typmod(precision: Option<u32>, scale: Option<u32>) -> (u32, u32) {
    match (precision, scale) {
        (Some(precision), Some(scale)) => (precision, scale),
        _ => panic!("unchecked DECIMAL typmod reached Rocq emitter"),
    }
}

fn identity_select_constructor(attribute_ty: FormalAttributeType) -> Option<&'static str> {
    match attribute_ty {
        FormalAttributeType::Z => Some("SelectZ"),
        FormalAttributeType::String => Some("SelectString"),
        FormalAttributeType::Bool => Some("SelectBool"),
        FormalAttributeType::Float => Some("SelectFloat"),
        FormalAttributeType::Double => Some("SelectDouble"),
        FormalAttributeType::Decimal { .. } => Some("SelectDecimal"),
        FormalAttributeType::Date => Some("SelectDate"),
        FormalAttributeType::Time => Some("SelectTime"),
        FormalAttributeType::Timestamp { .. } => Some("SelectTimestamp"),
        FormalAttributeType::Timestamptz { .. } => Some("SelectTimestamptz"),
    }
}

fn attribute_types_emit_equivalent(left: FormalAttributeType, right: FormalAttributeType) -> bool {
    match (left, right) {
        (
            FormalAttributeType::Timestamp { precision: left },
            FormalAttributeType::Timestamp { precision: right },
        ) => timestamp_precision(left) == timestamp_precision(right),
        (
            FormalAttributeType::Timestamptz { precision: left },
            FormalAttributeType::Timestamptz { precision: right },
        ) => timestamp_precision(left) == timestamp_precision(right),
        _ => left == right,
    }
}

fn identity_select_column(item: &FormalSelectItem) -> Option<String> {
    let FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::Attribute { name, ty },
    } = &item.expr
    else {
        return None;
    };
    if name != &item.alias || !attribute_types_emit_equivalent(*ty, item.alias_ty) {
        return None;
    }
    Some(emit_rocq_named_helper(
        column_ref_constructor(*ty),
        name,
        *ty,
    ))
}

fn dot_constructor(attribute_ty: FormalAttributeType) -> Option<&'static str> {
    match attribute_ty {
        FormalAttributeType::Z => Some("DotZ"),
        FormalAttributeType::String => Some("DotString"),
        FormalAttributeType::Bool => Some("DotBool"),
        FormalAttributeType::Float => Some("DotFloat"),
        FormalAttributeType::Double => Some("DotDouble"),
        FormalAttributeType::Decimal { .. } => Some("DotDecimal"),
        FormalAttributeType::Date => Some("DotDate"),
        FormalAttributeType::Time => Some("DotTime"),
        FormalAttributeType::Timestamp { .. } => Some("DotTimestamp"),
        FormalAttributeType::Timestamptz { .. } => Some("DotTimestamptz"),
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
            Some(FormalAttributeType::Double) => "NullDouble".to_owned(),
            Some(FormalAttributeType::Decimal { .. }) => "NullDecimal".to_owned(),
            Some(FormalAttributeType::Date) => "NullDate".to_owned(),
            Some(FormalAttributeType::Time) => "NullTime".to_owned(),
            Some(FormalAttributeType::Timestamp { .. }) => "NullTimestamp".to_owned(),
            Some(FormalAttributeType::Timestamptz { .. }) => "NullTimestamptz".to_owned(),
        };
    }
    if trimmed.eq_ignore_ascii_case("true") {
        return "CstBool true".to_owned();
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return "CstBool false".to_owned();
    }
    if let Some(bits) = float_literal_bits_for_type(trimmed, ty.as_ref()) {
        return match ty {
            Some(FormalAttributeType::Float) => format!("CstFloatBits ({bits})"),
            Some(FormalAttributeType::Double) => format!("CstDoubleBits ({bits})"),
            _ => unreachable!("float_literal_bits_for_type only accepts FLOAT/DOUBLE"),
        };
    }
    if matches!(ty, Some(FormalAttributeType::Date)) {
        if let Some(days) = parse_date_literal(trimmed) {
            return format!("CstDate ({days})");
        }
    }
    if matches!(ty, Some(FormalAttributeType::Time)) {
        if let Some(micros) = parse_time_literal(trimmed) {
            return format!("CstTime ({micros})");
        }
    }
    if let Some(FormalAttributeType::Timestamp { precision }) = ty {
        if let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision)) {
            return format!("CstTimestamp ({micros})");
        }
    }
    if let Some(FormalAttributeType::Timestamptz { precision }) = ty {
        if let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision)) {
            return format!("CstTimestamptz ({micros})");
        }
    }
    if matches!(ty, Some(FormalAttributeType::Decimal { .. })) {
        if let Some((coeff, precision, scale)) = decimal_literal_for_type(trimmed, ty.as_ref()) {
            return format!("CstDecimal ({precision}) ({scale}) ({coeff})");
        }
        panic!("unsupported DECIMAL aggregate literal reached Rocq emitter: {trimmed}");
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
            Some(FormalAttributeType::Double) => "Value_double None".to_owned(),
            Some(FormalAttributeType::Decimal { .. }) => "Value_decimal None".to_owned(),
            Some(FormalAttributeType::Date) => "Value_date None".to_owned(),
            Some(FormalAttributeType::Time) => "Value_time None".to_owned(),
            Some(FormalAttributeType::Timestamp { .. }) => "Value_timestamp None".to_owned(),
            Some(FormalAttributeType::Timestamptz { .. }) => "Value_timestamptz None".to_owned(),
        };
    }
    if trimmed.eq_ignore_ascii_case("true") {
        return "Value_bool (Some true)".to_owned();
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return "Value_bool (Some false)".to_owned();
    }
    if let Some(bits) = float_literal_bits_for_type(trimmed, ty.as_ref()) {
        return match ty {
            Some(FormalAttributeType::Float) => {
                format!("Value_float (Some (Float32OfBits ({bits})))")
            }
            Some(FormalAttributeType::Double) => {
                format!("Value_double (Some (Float64OfBits ({bits})))")
            }
            _ => unreachable!("float_literal_bits_for_type only accepts FLOAT/DOUBLE"),
        };
    }
    if matches!(ty, Some(FormalAttributeType::Date)) {
        if let Some(days) = parse_date_literal(trimmed) {
            return format!("Value_date (Some ({days})%Z)");
        }
    }
    if matches!(ty, Some(FormalAttributeType::Time)) {
        if let Some(micros) = parse_time_literal(trimmed) {
            return format!("Value_time (Some ({micros})%Z)");
        }
    }
    if let Some(FormalAttributeType::Timestamp { precision }) = ty {
        if let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision)) {
            return format!("Value_timestamp (Some ({micros})%Z)");
        }
    }
    if let Some(FormalAttributeType::Timestamptz { precision }) = ty {
        if let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision)) {
            return format!("Value_timestamptz (Some ({micros})%Z)");
        }
    }
    if matches!(ty, Some(FormalAttributeType::Decimal { .. })) {
        if let Some((coeff, precision, scale)) = decimal_literal_for_type(trimmed, ty.as_ref()) {
            return format!("Value_decimal (decimal_checked ({precision}) ({scale}) ({coeff}))");
        }
        panic!("unsupported DECIMAL value literal reached Rocq emitter: {trimmed}");
    }
    if let Some(unquoted) = sql_string_literal_content(trimmed) {
        return format!("Value_string (Some {})", rocq_string_literal(&unquoted));
    }
    if is_integer_literal(trimmed) {
        return format!("Value_Z (Some ({trimmed})%Z)");
    }
    format!("Value_string (Some {})", rocq_string_literal(trimmed))
}

pub(super) fn parse_decimal_literal(raw: &str) -> Option<(String, u32)> {
    let trimmed = raw.trim();
    if trimmed.is_empty() || trimmed.contains(['e', 'E']) {
        return None;
    }
    let (negative, body) = match trimmed.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, trimmed.strip_prefix('+').unwrap_or(trimmed)),
    };
    let (whole, fractional) = body.split_once('.').unwrap_or((body, ""));
    if whole.is_empty() && fractional.is_empty() {
        return None;
    }
    if !whole.chars().all(|c| c.is_ascii_digit()) || !fractional.chars().all(|c| c.is_ascii_digit())
    {
        return None;
    }
    let mut digits = format!("{whole}{fractional}");
    if digits.is_empty() {
        return None;
    }
    while digits.len() > 1 && digits.starts_with('0') {
        digits.remove(0);
    }
    if negative && digits != "0" {
        digits.insert(0, '-');
    }
    Some((digits, fractional.len().try_into().ok()?))
}

pub(super) fn float_literal_bits_for_type(
    raw: &str,
    ty: Option<&FormalAttributeType>,
) -> Option<u64> {
    let value = finite_sql_float_literal_text(raw)?;
    match ty {
        Some(FormalAttributeType::Float) => {
            let parsed = value.parse::<f32>().ok()?;
            parsed.is_finite().then_some(parsed.to_bits() as u64)
        }
        Some(FormalAttributeType::Double) => {
            let parsed = value.parse::<f64>().ok()?;
            parsed.is_finite().then_some(parsed.to_bits())
        }
        _ => None,
    }
}

fn finite_sql_float_literal_text(raw: &str) -> Option<String> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    let value = value.trim();
    if !is_sql_finite_float_literal(value) {
        return None;
    }
    Some(value.to_owned())
}

fn is_sql_finite_float_literal(value: &str) -> bool {
    let mut chars = value.chars().peekable();
    if matches!(chars.peek(), Some('+') | Some('-')) {
        chars.next();
    }

    let mut saw_digit = false;
    while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
        saw_digit = true;
        chars.next();
    }

    if matches!(chars.peek(), Some('.')) {
        chars.next();
        while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            saw_digit = true;
            chars.next();
        }
    }

    if !saw_digit {
        return false;
    }

    if matches!(chars.peek(), Some('e') | Some('E')) {
        chars.next();
        if matches!(chars.peek(), Some('+') | Some('-')) {
            chars.next();
        }
        let mut saw_exponent_digit = false;
        while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            saw_exponent_digit = true;
            chars.next();
        }
        if !saw_exponent_digit {
            return false;
        }
    }

    chars.next().is_none()
}

pub(super) fn decimal_literal_for_type(
    raw: &str,
    ty: Option<&FormalAttributeType>,
) -> Option<(String, u32, u32)> {
    let (coeff, literal_scale) = parse_decimal_literal(raw)?;
    let Some(FormalAttributeType::Decimal {
        precision: Some(precision),
        scale: Some(target_scale),
        ..
    }) = ty
    else {
        return None;
    };
    let coerced = if literal_scale > *target_scale {
        round_decimal_coeff_to_scale(&coeff, literal_scale, *target_scale)?
    } else {
        let padding = target_scale - literal_scale;
        if padding == 0 {
            coeff
        } else {
            format!("{coeff}{}", "0".repeat(padding as usize))
        }
    };
    if !decimal_literal_fits_precision(&coerced, *target_scale, Some(*precision)) {
        return None;
    }
    Some((coerced, *precision, *target_scale))
}

fn decimal_literal_fits_precision(coeff: &str, scale: u32, precision: Option<u32>) -> bool {
    let Some(precision) = precision else {
        return false;
    };
    if precision == 0 || precision > 1000 || scale > 1000 {
        return false;
    }
    let digits = coeff.trim_start_matches('-').trim_start_matches('0');
    digits.len() <= precision as usize
}

fn round_decimal_coeff_to_scale(
    coeff: &str,
    literal_scale: u32,
    target_scale: u32,
) -> Option<String> {
    let drop_digits = literal_scale.checked_sub(target_scale)?;
    let divisor = 10_i128.checked_pow(drop_digits)?;
    let value = coeff.parse::<i128>().ok()?;
    let quotient = value / divisor;
    let remainder = value % divisor;
    let rounded = if remainder.abs().checked_mul(2)? >= divisor {
        quotient + if value.is_negative() { -1 } else { 1 }
    } else {
        quotient
    };
    Some(rounded.to_string())
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
        .map(|attribute| emit_rocq_schema_attribute(attribute.ty, &attribute.name))
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

pub(super) fn date_literal_conforms_to_day(raw: &str) -> bool {
    parse_date_literal(raw).is_some()
}

fn parse_time_literal(raw: &str) -> Option<i64> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    if let Ok(micros) = value.parse::<i64>() {
        return valid_day_time_micros(micros).then_some(micros);
    }
    let (hour, minute, second, micros) = parse_hms(&value)?;
    if !valid_sql_time(hour, minute, second, micros) {
        return None;
    }
    Some(hour * MICROS_PER_HOUR + minute * MICROS_PER_MINUTE + second * MICROS_PER_SECOND + micros)
}

pub(super) fn time_literal_conforms_to_day(raw: &str) -> bool {
    parse_time_literal(raw).is_some()
}

pub(super) fn timestamp_literal_conforms_to_precision(raw: &str, precision: u32) -> bool {
    parse_timestamp_literal(raw, precision).is_some()
}

pub(super) fn timestamptz_literal_to_utc_micros(
    raw: &str,
    precision: u32,
    sql_time_zone: &SqlTimeZone,
) -> Option<i64> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    let (timestamp_text, literal_offset) = split_timestamp_offset(&value)?;
    let local_micros = parse_timestamp_literal(timestamp_text, precision)?;
    let utc_micros = if let Some(literal_offset) = literal_offset {
        local_micros - literal_offset
    } else {
        sql_time_zone.local_timestamp_micros_to_utc_instant(local_micros)?
    };
    timestamp_micros_with_precision(utc_micros, precision)
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

fn split_timestamp_offset(value: &str) -> Option<(&str, Option<i64>)> {
    let value = value.trim();
    if let Some(timestamp) = value.strip_suffix('Z').or_else(|| value.strip_suffix('z')) {
        return Some((timestamp.trim_end(), Some(0)));
    }
    let search_start = value
        .find(|ch| ch == ' ' || ch == 'T')
        .map(|index| index + 1)
        .unwrap_or(value.len());
    let offset_start = value[search_start..]
        .rfind(|ch| ch == '+' || ch == '-')
        .map(|index| search_start + index);
    match offset_start {
        Some(index) => {
            let timestamp = value[..index].trim_end();
            let offset = parse_timestamp_offset(&value[index..])?;
            Some((timestamp, Some(offset)))
        }
        None => Some((value, None)),
    }
}

fn parse_timestamp_offset(value: &str) -> Option<i64> {
    let value = value.trim();
    let sign = if value.starts_with('+') {
        1
    } else if value.starts_with('-') {
        -1
    } else {
        return None;
    };
    let body = &value[1..];
    let (hour_text, minute_text) = body.split_once(':').unwrap_or((body, "0"));
    let hours = hour_text.parse::<i64>().ok()?;
    let minutes = minute_text.parse::<i64>().ok()?;
    if !(0..=23).contains(&hours) || !(0..=59).contains(&minutes) {
        return None;
    }
    Some(sign * (hours * MICROS_PER_HOUR + minutes * MICROS_PER_MINUTE))
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

fn valid_sql_time(hour: i64, minute: i64, second: i64, micros: i64) -> bool {
    valid_time(hour, minute, second, micros)
        || (hour == 24 && minute == 0 && second == 0 && micros == 0)
}

fn valid_day_time_micros(micros: i64) -> bool {
    (0..=MICROS_PER_DAY).contains(&micros)
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
