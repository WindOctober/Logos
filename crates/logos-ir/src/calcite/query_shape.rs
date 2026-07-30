//! Exact declarative query-shape closure for Calcite's logical Rel tree.
//!
//! Calcite operator metadata is not source authority.  This module derives the
//! relational clause skeleton again from the byte-exact SQL submitted to the
//! wrapper and checks that the generated logical tree contains every
//! observable declarative role exactly once.  Projects used only as Calcite
//! row carriers are deliberately not roles: they may surround a role, but
//! cannot replace or authorize one.

use std::collections::BTreeSet;
use std::ops::Range;

use crate::calcite::{
    CalciteAggregateCall, CalciteProjectedSourceExpansion, CalciteRel, CalciteRex,
    CalciteSourceCteUse,
};
use crate::error::{Error, Result};
use crate::ir::SetOp;

use super::source_lexer::{self, LexemeKind};
use super::ty::calcite_full_type_bases_equal;
use super::{group_set_is_canonical, group_sets_are_canonical};

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Word(String),
    Comma,
    Open,
    Close,
    Semicolon,
    Protected,
    Other,
}

#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
    start: usize,
    end: usize,
    /// Parenthesis depth at which this token occurs.  For `(` this is the
    /// depth before opening; for `)` it is the depth after closing.
    depth: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Position {
    line: u32,
    column: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Span {
    start: Position,
    end: Position,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SuffixShape {
    order: bool,
    fetch: bool,
    offset: bool,
}

#[derive(Clone, Debug, Default)]
struct SuffixRoles {
    shape: SuffixShape,
    order_range: Option<Range<usize>>,
    fetch_range: Option<Range<usize>>,
    offset_range: Option<Range<usize>>,
}

type CteEdgeKey = (String, String);
type CtePath = Vec<CteEdgeKey>;

#[derive(Default)]
struct ClaimedRoles {
    sorts: BTreeSet<usize>,
    sets: BTreeSet<usize>,
    /// Exact generated Set identity to independently parsed source
    /// query-expression range.  `sets` closes node use globally; this map-like
    /// set additionally prevents a Set claimed for one nested expression from
    /// serving as another query-expression block's output carrier.
    set_bindings: BTreeSet<(usize, usize, usize)>,
    /// One exact source Set role may occur once in the original tree and once
    /// per distinct, validated lexical CTE-reference edge.  Keying by the
    /// edge prevents blanket CTE ownership from authorizing an extra copy
    /// inside a single clone.
    set_sources: BTreeSet<(usize, usize, CtePath)>,
    /// Set-expression roles derived independently from each exact CTE
    /// definition.  Every lexical reference path must realize every role in
    /// its own cloned subtree; an intact sibling clone cannot supply evidence
    /// for a damaged one.
    expected_set_sources: BTreeSet<(usize, usize, CtePath)>,
}

#[derive(Clone, Copy)]
struct StatementContext<'a> {
    sql: &'a str,
    tokens: &'a [Token],
}

#[derive(Clone, Copy)]
struct ComponentOptions<'a> {
    allow_exact_erased_order: bool,
    terminal_order_error_block: Option<&'a str>,
}

#[derive(Default)]
struct RelocatedHavingRoles {
    filters: BTreeSet<(usize, String)>,
}

impl RelocatedHavingRoles {
    fn contains_filter(&self, rel: &CalciteRel) -> bool {
        self.filters
            .iter()
            .any(|(identity, _)| *identity == rel_identity(rel))
    }

    fn count_for_block(&self, block: &str) -> usize {
        self.filters
            .iter()
            .filter(|(_, target)| target == block)
            .count()
    }
}

#[derive(Default)]
struct RelocatedBlockRoles {
    owners: BTreeSet<(usize, String)>,
}

struct BlockWalkContext<'a> {
    statement: StatementContext<'a>,
    in_subquery_erased_orders: &'a BTreeSet<String>,
    relocated_having: &'a RelocatedHavingRoles,
    relocated_blocks: &'a RelocatedBlockRoles,
    terminal_order_error_block: Option<&'a str>,
}

struct SelectOutputContext<'a> {
    block_id: &'a str,
    statement: StatementContext<'a>,
    block_range: &'a Range<usize>,
    block_source: &'a str,
    tokens: &'a [Token],
    unobservable_select_output: bool,
    enclosing_project: Option<&'a CalciteRel>,
    relocated_blocks: &'a RelocatedBlockRoles,
    terminal_analysis_error: bool,
}

#[derive(Clone, Copy)]
struct SourceBlockContext<'a> {
    block_id: &'a str,
    statement: StatementContext<'a>,
    block_range: &'a Range<usize>,
    block_source: &'a str,
    tokens: &'a [Token],
    enclosing_project: Option<&'a CalciteRel>,
}

impl<'a> SelectOutputContext<'a> {
    fn source_block(&self) -> SourceBlockContext<'a> {
        SourceBlockContext {
            block_id: self.block_id,
            statement: self.statement,
            block_range: self.block_range,
            block_source: self.block_source,
            tokens: self.tokens,
            enclosing_project: self.enclosing_project,
        }
    }
}

struct CollapsedCompositionContext<'a> {
    block: SourceBlockContext<'a>,
    enclosing_project: &'a CalciteRel,
    inner_items: &'a [Range<usize>],
    outer_block: &'a Range<usize>,
    outer_items: &'a [Range<usize>],
}

struct AggregateOutputContext<'a> {
    block: SourceBlockContext<'a>,
    input: &'a CalciteRel,
    group: &'a [usize],
    items: &'a [Range<usize>],
    repeated_group_items: Option<&'a [Range<usize>]>,
}

impl RelocatedBlockRoles {
    fn effective_block<'a>(&'a self, rel: &'a CalciteRel) -> Option<&'a str> {
        self.owners
            .iter()
            .find(|(identity, _)| *identity == rel_identity(rel))
            .map(|(_, block)| block.as_str())
            .or(rel.source_query_block_id.as_deref())
    }
}

fn cte_edge_key(use_: &CalciteSourceCteUse) -> CteEdgeKey {
    (
        use_.reference_node_id.clone(),
        use_.definition_query_node_id.clone(),
    )
}

fn extend_cte_path(path: &[CteEdgeKey], use_: Option<&CalciteSourceCteUse>) -> CtePath {
    let mut extended = path.to_vec();
    if let Some(use_) = use_ {
        extended.push(cte_edge_key(use_));
    }
    extended
}

fn rel_identity(rel: &CalciteRel) -> usize {
    rel as *const CalciteRel as usize
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SetOperator {
    Union,
    Intersect,
    Except,
}

impl SetOperator {
    fn generated_type(self) -> &'static str {
        match self {
            Self::Union => "LogicalUnion",
            Self::Intersect => "LogicalIntersect",
            Self::Except => "LogicalMinus",
        }
    }

    fn generated_name(self) -> &'static str {
        match self {
            Self::Union => "UNION",
            Self::Intersect => "INTERSECT",
            Self::Except => "EXCEPT",
        }
    }
}

#[derive(Clone, Debug)]
enum QueryShape {
    Leaf(Range<usize>),
    Set {
        op: SetOperator,
        all: bool,
        inputs: Vec<QueryShape>,
        range: Range<usize>,
    },
}

impl QueryShape {
    fn range(&self) -> &Range<usize> {
        match self {
            Self::Leaf(range) | Self::Set { range, .. } => range,
        }
    }
}

fn invalid(message: impl Into<String>) -> Error {
    Error::InvalidRelSourceProvenance(format!(
        "exact declarative query-shape mismatch: {}",
        message.into()
    ))
}

/// Validate one independently submitted SQL statement and every relational
/// subtree rooted from it (including Rex subqueries). Exact nonblank source
/// SQL is mandatory; absence cannot bypass relational/source-shape validation.
pub(super) fn validate_query_shape_bijection_with_terminal_error(
    root: &CalciteRel,
    statement_sql: Option<&str>,
    terminal_order_error_block: Option<&str>,
) -> Result<()> {
    let statement_sql = statement_sql
        .filter(|sql| !sql.trim().is_empty())
        .ok_or_else(|| invalid("the original statement is missing or blank"))?;
    let tokens = lex(statement_sql)
        .ok_or_else(|| invalid("the original statement has unsupported lexical structure"))?;
    let statement_range = trim_range(statement_sql, 0..statement_sql.len())
        .ok_or_else(|| invalid("the original statement is empty"))?;
    validate_independent_query_block_presence(root, statement_sql, &tokens)?;
    let mut claimed = ClaimedRoles::default();
    let statement = StatementContext {
        sql: statement_sql,
        tokens: &tokens,
    };
    validate_component(
        root,
        statement,
        statement_range,
        &[],
        &mut claimed,
        ComponentOptions {
            allow_exact_erased_order: false,
            terminal_order_error_block,
        },
    )?;

    let mut in_subquery_erased_orders = BTreeSet::new();
    collect_exact_in_subquery_order_blocks(root, &mut in_subquery_erased_orders);
    collect_outer_sorted_set_branch_orders(
        root,
        statement_sql,
        &tokens,
        &mut in_subquery_erased_orders,
    )?;
    let mut relocated_having = RelocatedHavingRoles::default();
    collect_exact_relocated_having_roles(root, statement_sql, &tokens, &mut relocated_having)?;
    let mut relocated_blocks = RelocatedBlockRoles::default();
    collect_exact_flattened_derived_group_roles(
        root,
        statement_sql,
        &tokens,
        &mut relocated_blocks,
    )?;
    // Close every nested/CTE-cloned Set before validating source-query block
    // carriers.  A Set-expression block may use only a Set already matched to
    // its exact operator/quantifier/ordered branches below.
    claim_nested_set_roles(root, statement_sql, &tokens, &mut claimed, &[])?;
    let block_context = BlockWalkContext {
        statement,
        in_subquery_erased_orders: &in_subquery_erased_orders,
        relocated_having: &relocated_having,
        relocated_blocks: &relocated_blocks,
        terminal_order_error_block,
    };
    validate_block_roots(root, None, None, None, &block_context, &mut claimed)?;
    validate_expected_set_roles(&claimed)?;
    validate_no_unclaimed_semantic_nodes(root, &claimed, &relocated_having)?;
    Ok(())
}

/// Parser-position fields on surviving nodes cannot establish completeness:
/// deleting a whole nested query would delete its own evidence.  Discover
/// every SELECT/VALUES query start from the protected-token scan first, then
/// require an independently owned relational subtree beginning at that exact
/// byte.  Repeated CTE clones collapse to one source start, as they should;
/// at least one generated clone is still mandatory for the definition.
fn validate_independent_query_block_presence(
    root: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Result<()> {
    #[derive(Default)]
    struct OwnedStarts {
        selects: BTreeSet<usize>,
        values: BTreeSet<usize>,
    }

    fn direct_query_start(
        source: &str,
        tokens: &[Token],
        range: Range<usize>,
        keyword: &str,
    ) -> Option<usize> {
        let range = strip_complete_parentheses(source, tokens, range).ok()?;
        let base_depth = tokens
            .iter()
            .find(|token| token.start >= range.start && token.end <= range.end)?
            .depth;
        tokens
            .iter()
            .find(|token| {
                token.start >= range.start
                    && token.end <= range.end
                    && token.depth == base_depth
                    && matches!(&token.kind, TokenKind::Word(word) if word == keyword)
            })
            .map(|token| token.start)
    }

    fn rex(node: &CalciteRex, source: &str, tokens: &[Token], owned: &mut OwnedStarts) {
        if let Some(subquery) = node.subquery_rel.as_deref() {
            rel(subquery, source, tokens, owned);
        }
        if let Some(reference) = node.reference_expr.as_deref() {
            rex(reference, source, tokens, owned);
        }
        for operand in &node.operands {
            rex(operand, source, tokens, owned);
        }
    }

    fn rel(node: &CalciteRel, source: &str, tokens: &[Token], owned: &mut OwnedStarts) {
        let query_range = node
            .source_query_block_id
            .as_deref()
            .and_then(|id| span_range(source, id));
        let owns_set_expression = query_range.as_ref().is_some_and(|range| {
            matches!(
                parse_query_shape(source, tokens, range.clone()),
                Ok(QueryShape::Set { .. })
            )
        });
        // A Set query expression is not another SELECT block.  Its ordered
        // arms must each be owned by their own Project/subtree; allowing the
        // Set's enclosing range to claim its first SELECT would mask deletion
        // of that first arm's carrier.
        if !owns_set_expression
            && let Some(start) =
                query_range.and_then(|range| direct_query_start(source, tokens, range, "select"))
        {
            owned.selects.insert(start);
        }
        if node.source_kind.as_deref() == Some("VALUES")
            && let Some(start) = exact_rel_range(node, source)
                .and_then(|range| direct_query_start(source, tokens, range, "values"))
        {
            owned.values.insert(start);
        }
        for rex_node in node
            .project_rex
            .iter()
            .chain(node.condition_rex.iter())
            .chain(node.fetch_rex.iter())
            .chain(node.offset_rex.iter())
        {
            rex(rex_node, source, tokens, owned);
        }
        if let Some(rows) = &node.tuples {
            for rex_node in rows.iter().flatten() {
                rex(rex_node, source, tokens, owned);
            }
        }
        for input in &node.inputs {
            rel(input, source, tokens, owned);
        }
    }

    let mut owned = OwnedStarts::default();
    rel(root, statement_sql, tokens, &mut owned);
    for token in tokens {
        match &token.kind {
            TokenKind::Word(word) if word == "select" => {
                if !owned.selects.contains(&token.start) {
                    return Err(invalid(format!(
                        "source SELECT at byte {} has no owned logical query-block subtree",
                        token.start
                    )));
                }
            }
            TokenKind::Word(word) if word == "values" => {
                if !owned.values.contains(&token.start) {
                    return Err(invalid(format!(
                        "source VALUES at byte {} has no owned logical Values subtree",
                        token.start
                    )));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_component(
    root: &CalciteRel,
    statement: StatementContext<'_>,
    component_range: Range<usize>,
    cte_path: &[CteEdgeKey],
    claimed: &mut ClaimedRoles,
    options: ComponentOptions<'_>,
) -> Result<()> {
    let statement_sql = statement.sql;
    let tokens = statement.tokens;
    let suffix = suffix_roles(tokens, component_range.clone())?;
    let exact_erased_order = options.allow_exact_erased_order
        && suffix.shape
            == (SuffixShape {
                order: true,
                fetch: false,
                offset: false,
            });
    let terminal_error_owns_suffix = options.terminal_order_error_block.is_some_and(|block| {
        first_query_block_id(root) == Some(block) && suffix.shape != SuffixShape::default()
    });
    let (after_sort, sort) = generated_component_sort(
        root,
        suffix.shape != SuffixShape::default() && !exact_erased_order,
        terminal_error_owns_suffix,
    )?;
    validate_generated_sort(sort, &suffix, statement_sql)?;
    if let Some(sort) = sort {
        claimed.sorts.insert(rel_identity(sort));
    }

    let core_end = [
        suffix.order_range.as_ref().map(|range| range.start),
        suffix.fetch_range.as_ref().map(|range| range.start),
        suffix.offset_range.as_ref().map(|range| range.start),
    ]
    .into_iter()
    .flatten()
    .min()
    .unwrap_or(component_range.end);
    let core_range = trim_range(statement_sql, component_range.start..core_end)
        .ok_or_else(|| invalid("the source query core is empty"))?;
    let source_shape = parse_query_shape(statement_sql, tokens, core_range)?;
    match_query_shape(
        &source_shape,
        after_sort,
        statement_sql,
        tokens,
        cte_path,
        claimed,
    )?;

    visit_rex_subquery_components(root, statement, cte_path, claimed)
}

fn generated_component_sort(
    root: &CalciteRel,
    expected: bool,
    allow_terminal_absence: bool,
) -> Result<(&CalciteRel, Option<&CalciteRel>)> {
    let candidate = strip_component_projects(root);
    if expected {
        if candidate.rel_type != "LogicalSort" {
            if allow_terminal_absence {
                return Ok((root, None));
            }
            return Err(invalid(
                "source ORDER/LIMIT/OFFSET has no corresponding LogicalSort",
            ));
        }
        let input = candidate
            .inputs
            .as_slice()
            .first()
            .ok_or_else(|| invalid("source-owned LogicalSort has no relational input"))?;
        Ok((input, Some(candidate)))
    } else if candidate.rel_type == "LogicalSort" {
        Err(invalid(
            "LogicalSort is not claimed by source ORDER/LIMIT/OFFSET",
        ))
    } else {
        Ok((root, None))
    }
}

fn strip_component_projects(mut rel: &CalciteRel) -> &CalciteRel {
    while rel.rel_type == "LogicalProject" && rel.inputs.len() == 1 {
        let input = &rel.inputs[0];
        if matches!(
            (
                rel.source_query_block_id.as_deref(),
                input.source_query_block_id.as_deref(),
            ),
            (Some(project_block), Some(input_block)) if project_block != input_block
        ) {
            // An outer SELECT Project and the root of its sole ordered derived
            // input are distinct declarative components even when Calcite
            // connects them directly.  Crossing that exact boundary here
            // would let the inner Sort appear to implement a nonexistent
            // outer ORDER/LIMIT/OFFSET suffix.  Only two present, unequal
            // parser-owned block identities establish the boundary; missing
            // or ambiguous provenance receives no inferred separation and is
            // rejected by the ordinary component/block completeness checks.
            break;
        }
        rel = input;
    }
    rel
}

fn strip_projects(mut rel: &CalciteRel) -> &CalciteRel {
    while rel.rel_type == "LogicalProject" && rel.inputs.len() == 1 {
        rel = &rel.inputs[0];
    }
    rel
}

fn first_query_block_id(rel: &CalciteRel) -> Option<&str> {
    rel.source_query_block_id
        .as_deref()
        .or_else(|| rel.inputs.iter().find_map(first_query_block_id))
}

fn validate_generated_sort(
    sort: Option<&CalciteRel>,
    suffix: &SuffixRoles,
    statement_sql: &str,
) -> Result<()> {
    let Some(sort) = sort else {
        return Ok(());
    };
    if sort.inputs.len() != 1
        || !suffix.shape.order && !sort.collation.is_empty()
        || suffix.shape.order && sort.collation.is_empty()
        || suffix.shape.fetch != sort.fetch_rex.is_some()
        || suffix.shape.offset != sort.offset_rex.is_some()
    {
        return Err(invalid(format!(
            "LogicalSort roles disagree with source suffix: source={:?}, keys={}, fetch={}, offset={}",
            suffix.shape,
            sort.collation.len(),
            sort.fetch_rex.is_some(),
            sort.offset_rex.is_some()
        )));
    }
    if let (Some(rex), Some(role)) = (sort.fetch_rex.as_ref(), suffix.fetch_range.as_ref()) {
        require_rex_inside_role(rex, statement_sql, role, "LIMIT/FETCH")?;
    }
    if let (Some(rex), Some(role)) = (sort.offset_rex.as_ref(), suffix.offset_range.as_ref()) {
        require_rex_inside_role(rex, statement_sql, role, "OFFSET")?;
    }
    Ok(())
}

fn require_rex_inside_role(
    rex: &CalciteRex,
    statement_sql: &str,
    role: &Range<usize>,
    name: &str,
) -> Result<()> {
    let node_id = rex
        .source_node_id
        .as_deref()
        .ok_or_else(|| invalid(format!("LogicalSort {name} Rex has no exact source span")))?;
    let range = span_range(statement_sql, node_id).ok_or_else(|| {
        invalid(format!(
            "LogicalSort {name} Rex has a malformed source span"
        ))
    })?;
    if range.start < role.start || range.end > role.end {
        return Err(invalid(format!(
            "LogicalSort {name} Rex borrows a literal from a different source clause"
        )));
    }
    Ok(())
}

fn rex_subquery_component_range(
    node: &CalciteRex,
    subquery: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Result<Range<usize>> {
    let role = node
        .source_node_id
        .as_deref()
        .and_then(|node_id| span_range(statement_sql, node_id))
        .ok_or_else(|| invalid("Rex subquery has no exact source range"))?;

    let semantic = strip_projects(subquery);
    if matches!(
        semantic.rel_type.as_str(),
        "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
    ) {
        let candidate = generated_set_leaf_range(semantic, statement_sql, tokens)
            .ok_or_else(|| invalid("Rex Set subquery has no exact source query expression"))?;
        if !range_contains(&role, &candidate) {
            return Err(invalid(
                "Rex Set subquery query expression lies outside its exact predicate role",
            ));
        }
        return Ok(candidate);
    }

    let owner = first_query_block_range(subquery, statement_sql)
        .or_else(|| exact_rel_range(subquery, statement_sql))
        .ok_or_else(|| invalid("Rex subquery has no exact query-block range"))?;
    let owner = strip_complete_parentheses(statement_sql, tokens, owner)?;
    if !range_contains(&role, &owner) || owner.start >= role.end {
        return Err(invalid(
            "Rex subquery query block lies outside its exact predicate role",
        ));
    }
    trim_range(statement_sql, owner.start..role.end)
        .ok_or_else(|| invalid("Rex subquery has an empty exact query expression"))
}

fn visit_rex_subquery_components(
    rel: &CalciteRel,
    statement: StatementContext<'_>,
    cte_path: &[CteEdgeKey],
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    fn rex(
        node: &CalciteRex,
        statement: StatementContext<'_>,
        cte_path: &[CteEdgeKey],
        claimed: &mut ClaimedRoles,
    ) -> Result<()> {
        let statement_sql = statement.sql;
        let tokens = statement.tokens;
        if let Some(subquery) = node.subquery_rel.as_deref() {
            let range = rex_subquery_component_range(node, subquery, statement_sql, tokens)?;
            let exact_erased_order = node.source_in_subquery_order.as_ref().is_some_and(|order| {
                order.kind == "POSTGRES_IN_SUBQUERY_LOST_ORDER_BY"
                    && first_query_block_id(subquery) == Some(order.query_block_id.as_str())
                    && span_range(statement_sql, &order.query_block_id)
                        .and_then(|range| statement_sql.get(range))
                        == Some(order.select_text.as_str())
            });
            validate_component(
                subquery,
                statement,
                range,
                cte_path,
                claimed,
                ComponentOptions {
                    allow_exact_erased_order: exact_erased_order,
                    terminal_order_error_block: None,
                },
            )?;
        }
        if let Some(reference) = node.reference_expr.as_deref() {
            rex(reference, statement, cte_path, claimed)?;
        }
        for operand in &node.operands {
            rex(operand, statement, cte_path, claimed)?;
        }
        if let Some(window) = node.window.as_deref() {
            for key in &window.partition_keys {
                rex(key, statement, cte_path, claimed)?;
            }
            for key in &window.order_keys {
                rex(&key.expr, statement, cte_path, claimed)?;
            }
            for bound in [window.lower_bound.as_deref(), window.upper_bound.as_deref()]
                .into_iter()
                .flatten()
            {
                if let Some(offset) = bound.offset.as_deref() {
                    rex(offset, statement, cte_path, claimed)?;
                }
            }
        }
        Ok(())
    }

    for node in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        rex(node, statement, cte_path, claimed)?;
    }
    if let Some(rows) = &rel.tuples {
        for node in rows.iter().flatten() {
            rex(node, statement, cte_path, claimed)?;
        }
    }
    for (index, input) in rel.inputs.iter().enumerate() {
        let input_path = extend_cte_path(cte_path, generated_input_cte_use(rel, index));
        visit_rex_subquery_components(input, statement, &input_path, claimed)?;
    }
    Ok(())
}

fn match_query_shape(
    source: &QueryShape,
    generated: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
    cte_path: &[CteEdgeKey],
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    match source {
        QueryShape::Leaf(expected) => {
            // A Project that owns an exact SELECT block is the declarative
            // leaf itself.  Stripping it would expose a set expression in the
            // SELECT's FROM/CTE input and falsely promote that nested operator
            // to the query-expression root.
            let semantic = source_leaf_root(generated, expected, statement_sql, tokens);
            if semantic.set_op.as_deref() == Some("UNION")
                && semantic.all == Some(true)
                && super::convert::exact_source_values_union_parent(semantic, SetOp::Union, true)
            {
                let values_range = exact_rel_range(semantic, statement_sql).ok_or_else(|| {
                    invalid("source-attested VALUES expansion has no exact source range")
                })?;
                if !range_contains(expected, &values_range) {
                    return Err(invalid(
                        "source-attested VALUES expansion lies outside its source branch",
                    ));
                }
                claim_set_role(claimed, semantic, &values_range, cte_path)?;
                return Ok(());
            }
            let cte_range = cte_path
                .last()
                .and_then(|(reference, _)| span_range(statement_sql, reference));
            if matches!(
                semantic.rel_type.as_str(),
                "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
            ) {
                if cte_range
                    .as_ref()
                    .is_some_and(|actual| range_contains(expected, actual))
                {
                    // The source branch is a CTE reference while Calcite
                    // clones its set-expression definition here. The exact
                    // CTE edge is validated elsewhere; the cloned Set itself
                    // is closed against its definition below.
                    return Ok(());
                }
                return Err(invalid(format!(
                    "Calcite inserted a set operation absent from the exact source branch {:?}: generated node {} source {:?}",
                    expected,
                    strip_projects(generated).rel_type,
                    strip_projects(generated).source_node_id
                )));
            }
            let generated_range = first_query_block_range(generated, statement_sql)
                .or_else(|| exact_rel_range(generated, statement_sql))
                .and_then(|range| strip_complete_parentheses(statement_sql, tokens, range).ok());
            if !generated_range
                .as_ref()
                .is_some_and(|actual| range_contains(expected, actual))
                && !cte_range
                    .as_ref()
                    .is_some_and(|actual| range_contains(expected, actual))
            {
                return Err(invalid(format!(
                    "generated set branch does not come from the corresponding ordered source branch: expected={:?}, generated={:?}, cte={:?}",
                    expected, generated_range, cte_range
                )));
            }
            Ok(())
        }
        QueryShape::Set {
            op, all, inputs, ..
        } => {
            let generated = strip_projects(generated);
            if generated.rel_type != op.generated_type()
                || generated.set_op.as_deref() != Some(op.generated_name())
                || generated.all != Some(*all)
            {
                return Err(invalid(format!(
                    "source {} {} with {} branches disagrees with generated {} {:?} {:?} with {} branches",
                    op.generated_name(),
                    if *all { "ALL" } else { "DISTINCT" },
                    inputs.len(),
                    generated.rel_type,
                    generated.set_op,
                    generated.all,
                    generated.inputs.len()
                )));
            }
            validate_generated_set_output_layout(generated)?;
            if generated.inputs.len() == inputs.len() {
                claim_set_role(claimed, generated, source.range(), cte_path)?;
                for (index, (expected, actual)) in inputs.iter().zip(&generated.inputs).enumerate()
                {
                    let path = extend_cte_path(cte_path, generated_input_cte_use(generated, index));
                    match_query_shape(expected, actual, statement_sql, tokens, &path, claimed)?;
                }
                return Ok(());
            }

            if !matches!(op, SetOperator::Union | SetOperator::Intersect) {
                return Err(invalid(format!(
                    "non-associative source {} has {} branches but generated {}",
                    op.generated_name(),
                    inputs.len(),
                    generated.inputs.len()
                )));
            }
            let mut source_leaves = Vec::new();
            collect_associative_source_leaves(source, *op, *all, &mut source_leaves);
            let mut generated_leaves = Vec::new();
            let mut generated_nodes = Vec::new();
            collect_associative_generated_leaves(
                generated,
                *op,
                *all,
                cte_path,
                &mut generated_leaves,
                &mut generated_nodes,
            );
            for node in &generated_nodes {
                validate_generated_set_output_layout(node)?;
            }
            if source_leaves.len() != generated_leaves.len() {
                return Err(invalid(
                    "associative Set flattening changes branch count or resolved common types",
                ));
            }
            claim_set_component(claimed, &generated_nodes, source.range(), cte_path)?;
            for (expected, (actual, path)) in source_leaves.into_iter().zip(generated_leaves) {
                match_query_shape(expected, actual, statement_sql, tokens, &path, claimed)?;
            }
            Ok(())
        }
    }
}

/// A declarative Set result takes its ordered output labels from its first
/// arm and resolves one common type at every position.  Calcite's Set node is
/// therefore an exact output carrier only when its first input preserves both
/// names and types, and every later input preserves the resolved types.  This
/// is independent of physical Set implementation and closes coherent row-type
/// mutations that leave the operator/branch count unchanged.
fn validate_generated_set_output_layout(generated: &CalciteRel) -> Result<()> {
    let Some(first) = generated.inputs.first() else {
        return Err(invalid("logical Set has no first ordered input"));
    };
    let widths_match = generated
        .inputs
        .iter()
        .all(|input| input.row_type.len() == generated.row_type.len());
    let fields_resolve = widths_match
        && generated
            .row_type
            .iter()
            .enumerate()
            .all(|(index, output)| {
                let inputs = generated
                    .inputs
                    .iter()
                    .map(|input| &input.row_type[index])
                    .collect::<Vec<_>>();
                output.name == first.row_type[index].name
                    && inputs
                        .iter()
                        .all(|input| same_calcite_set_base_type(output, input))
                    && output.nullable == inputs.iter().any(|input| input.nullable)
            });
    if generated.inputs.len() < 2 || !fields_resolve {
        return Err(invalid(
            "logical Set changes first-arm output names or resolved branch types",
        ));
    }
    Ok(())
}

fn same_calcite_set_base_type(
    left: &crate::calcite::CalciteField,
    right: &crate::calcite::CalciteField,
) -> bool {
    left.ty == right.ty
        && calcite_full_type_bases_equal(
            left.full_type.as_deref(),
            left.nullable,
            right.full_type.as_deref(),
            right.nullable,
        )
        && left.precision == right.precision
        && left.scale == right.scale
        && left.charset == right.charset
        && left.type_collation == right.type_collation
}

fn source_leaf_root<'a>(
    mut rel: &'a CalciteRel,
    expected: &Range<usize>,
    statement_sql: &str,
    tokens: &[Token],
) -> &'a CalciteRel {
    while rel.rel_type == "LogicalProject" && rel.inputs.len() == 1 {
        if rel
            .source_query_block_id
            .as_deref()
            .and_then(|id| span_range(statement_sql, id))
            .and_then(|range| strip_complete_parentheses(statement_sql, tokens, range).ok())
            .is_some_and(|range| range_contains(expected, &range))
        {
            break;
        }
        rel = &rel.inputs[0];
    }
    rel
}

fn claim_set_role(
    claimed: &mut ClaimedRoles,
    generated: &CalciteRel,
    source_range: &Range<usize>,
    cte_path: &[CteEdgeKey],
) -> Result<()> {
    claim_set_component(claimed, &[generated], source_range, cte_path)
}

fn claim_set_component(
    claimed: &mut ClaimedRoles,
    generated: &[&CalciteRel],
    source_range: &Range<usize>,
    cte_path: &[CteEdgeKey],
) -> Result<()> {
    let source_key = (source_range.start, source_range.end, cte_path.to_vec());
    let conflicts = claimed.set_sources.iter().any(|(start, end, prior_path)| {
        *start == source_range.start
            && *end == source_range.end
            && (prior_path == cte_path || prior_path.is_empty() || cte_path.is_empty())
    });
    if conflicts || !claimed.set_sources.insert(source_key.clone()) {
        return Err(invalid(format!(
            "one exact source set-expression/CTE-edge role {:?} is reused by unrelated logical Set nodes {:?}",
            source_key,
            generated
                .iter()
                .map(|node| (&node.rel_type, &node.source_node_id))
                .collect::<Vec<_>>()
        )));
    }
    for generated in generated {
        let identity = rel_identity(generated);
        claimed.sets.insert(identity);
        claimed
            .set_bindings
            .insert((identity, source_range.start, source_range.end));
    }
    Ok(())
}

fn source_set_core_range(
    statement_sql: &str,
    tokens: &[Token],
    range: Range<usize>,
) -> Result<(Range<usize>, bool)> {
    let suffix = suffix_roles(tokens, range.clone())?;
    let core_end = [
        suffix.order_range.as_ref().map(|range| range.start),
        suffix.fetch_range.as_ref().map(|range| range.start),
        suffix.offset_range.as_ref().map(|range| range.start),
    ]
    .into_iter()
    .flatten()
    .min()
    .unwrap_or(range.end);
    let core = trim_range(statement_sql, range.start..core_end)
        .ok_or_else(|| invalid("source Set expression has an empty core"))?;
    Ok((core, suffix.shape != SuffixShape::default()))
}

/// Record the maximal semantic Set components represented by one parsed query
/// expression.  Calcite may reassociate or flatten UNION/INTERSECT chains, so
/// a same-operator/same-quantifier child without its own suffix is part of the
/// parent component rather than a separately mandatory generated node.
fn collect_source_set_components(
    shape: &QueryShape,
    statement_sql: &str,
    tokens: &[Token],
    parent: Option<(SetOperator, bool)>,
    roles: &mut BTreeSet<(usize, usize)>,
    covered: &mut BTreeSet<(usize, usize)>,
) -> Result<()> {
    let QueryShape::Set {
        op,
        all,
        inputs,
        range,
    } = shape
    else {
        return Ok(());
    };
    let (core, has_suffix) = source_set_core_range(statement_sql, tokens, range.clone())?;
    let key = (core.start, core.end);
    covered.insert(key);
    let associative_child = !has_suffix
        && matches!(op, SetOperator::Union | SetOperator::Intersect)
        && parent == Some((*op, *all));
    if !associative_child {
        roles.insert(key);
    }
    for input in inputs {
        collect_source_set_components(
            input,
            statement_sql,
            tokens,
            Some((*op, *all)),
            roles,
            covered,
        )?;
    }
    Ok(())
}

/// Derive every Set component inside an exact CTE definition without using
/// generated Rel metadata.  A nested SQL query expression must be either the
/// definition itself or enclosed in parentheses, so inspecting the complete
/// definition plus each balanced parenthesized range discovers derived-table
/// and Rex-subquery Sets as well as a top-level Set definition.
fn source_set_component_ranges(
    statement_sql: &str,
    tokens: &[Token],
    definition_range: Range<usize>,
) -> Result<BTreeSet<(usize, usize)>> {
    let definition_range = trim_range(statement_sql, definition_range)
        .ok_or_else(|| invalid("CTE definition query is empty"))?;
    let mut candidates = vec![definition_range.clone()];
    let mut opens = Vec::new();
    for token in tokens
        .iter()
        .filter(|token| token.start >= definition_range.start && token.end <= definition_range.end)
    {
        match token.kind {
            TokenKind::Open => opens.push(token.end),
            TokenKind::Close => {
                if let Some(start) = opens.pop()
                    && start < token.start
                {
                    candidates.push(start..token.start);
                }
            }
            _ => {}
        }
    }
    candidates.sort_by(|left, right| {
        (right.end - right.start)
            .cmp(&(left.end - left.start))
            .then_with(|| left.start.cmp(&right.start))
    });
    candidates.dedup_by(|left, right| left.start == right.start && left.end == right.end);

    let mut roles = BTreeSet::new();
    let mut covered = BTreeSet::new();
    for candidate in candidates {
        let Some(candidate) = trim_range(statement_sql, candidate) else {
            continue;
        };
        if !tokens
            .iter()
            .any(|token| token.start >= candidate.start && token.end <= candidate.end)
        {
            continue;
        }
        let candidate = strip_complete_parentheses(statement_sql, tokens, candidate)?;
        let Some(first) = tokens
            .iter()
            .find(|token| token.start >= candidate.start && token.end <= candidate.end)
        else {
            continue;
        };
        if !matches!(&first.kind, TokenKind::Word(word)
            if matches!(word.as_str(), "select" | "values" | "with"))
        {
            continue;
        }
        let (core, _) = source_set_core_range(statement_sql, tokens, candidate)?;
        let shape = parse_query_shape(statement_sql, tokens, core)?;
        let QueryShape::Set { range, .. } = &shape else {
            continue;
        };
        let (top_core, _) = source_set_core_range(statement_sql, tokens, range.clone())?;
        if covered.contains(&(top_core.start, top_core.end)) {
            continue;
        }
        let mut local_roles = BTreeSet::new();
        let mut local_covered = BTreeSet::new();
        collect_source_set_components(
            &shape,
            statement_sql,
            tokens,
            None,
            &mut local_roles,
            &mut local_covered,
        )?;
        roles.extend(local_roles);
        covered.extend(local_covered);
    }
    Ok(roles)
}

fn register_expected_cte_set_roles(
    use_: &CalciteSourceCteUse,
    statement_sql: &str,
    tokens: &[Token],
    cte_path: &[CteEdgeKey],
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    let definition_range = span_range(statement_sql, &use_.definition_query_node_id)
        .ok_or_else(|| invalid("CTE edge has a malformed definition-query span"))?;
    for (start, end) in source_set_component_ranges(statement_sql, tokens, definition_range)? {
        claimed
            .expected_set_sources
            .insert((start, end, cte_path.to_vec()));
    }
    Ok(())
}

fn validate_expected_set_roles(claimed: &ClaimedRoles) -> Result<()> {
    if let Some(missing) = claimed
        .expected_set_sources
        .iter()
        .find(|expected| !claimed.set_sources.contains(*expected))
    {
        return Err(invalid(format!(
            "exact CTE reference path is missing source Set-expression role {missing:?}"
        )));
    }
    Ok(())
}

fn generated_input_cte_use(rel: &CalciteRel, index: usize) -> Option<&CalciteSourceCteUse> {
    rel.source_input_cte_uses
        .get(index)
        .and_then(Option::as_ref)
        .or_else(|| {
            rel.source_join.as_ref().and_then(|join| match index {
                0 => join.left_cte_use.as_ref(),
                1 => join.right_cte_use.as_ref(),
                _ => None,
            })
        })
}

fn collect_associative_source_leaves<'a>(
    shape: &'a QueryShape,
    op: SetOperator,
    all: bool,
    leaves: &mut Vec<&'a QueryShape>,
) {
    match shape {
        QueryShape::Set {
            op: nested_op,
            all: nested_all,
            inputs,
            ..
        } if *nested_op == op && *nested_all == all => {
            for input in inputs {
                collect_associative_source_leaves(input, op, all, leaves);
            }
        }
        other => leaves.push(other),
    }
}

fn collect_associative_generated_leaves<'a>(
    rel: &'a CalciteRel,
    op: SetOperator,
    all: bool,
    inherited_cte_path: &[CteEdgeKey],
    leaves: &mut Vec<(&'a CalciteRel, CtePath)>,
    nodes: &mut Vec<&'a CalciteRel>,
) {
    let rel = strip_projects(rel);
    if rel.rel_type == op.generated_type()
        && rel.set_op.as_deref() == Some(op.generated_name())
        && rel.all == Some(all)
    {
        nodes.push(rel);
        for (index, input) in rel.inputs.iter().enumerate() {
            let path = extend_cte_path(inherited_cte_path, generated_input_cte_use(rel, index));
            collect_associative_generated_leaves(input, op, all, &path, leaves, nodes);
        }
    } else {
        leaves.push((rel, inherited_cte_path.to_vec()));
    }
}

fn same_calcite_set_row_types(
    left: &[crate::calcite::CalciteField],
    right: &[crate::calcite::CalciteField],
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.ty == right.ty
                && left.nullable == right.nullable
                && left.full_type == right.full_type
                && left.precision == right.precision
                && left.scale == right.scale
                && left.charset == right.charset
                && left.type_collation == right.type_collation
        })
}

/// Calcite can flatten an associative set expression while attaching the
/// enclosing SELECT identity to the new outer Set node.  Recover only the
/// source range forced by the ordered exact query-block leaves; reparsing that
/// range and matching the complete generated tree below still authenticates
/// the operator, quantifier, branch count, branch order, and common row type.
/// This is also independent of how many transparent Project/Aggregate nodes a
/// validated CTE clone places above the set expression.
fn generated_set_leaf_range(
    rel: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Option<Range<usize>> {
    fn collect(
        rel: &CalciteRel,
        statement_sql: &str,
        leaves: &mut Vec<Range<usize>>,
    ) -> Option<()> {
        if rel.rel_type == "LogicalProject"
            && let Some(range) = rel
                .source_query_block_id
                .as_deref()
                .and_then(|id| span_range(statement_sql, id))
        {
            leaves.push(range);
            return Some(());
        }
        let rel = strip_projects(rel);
        if matches!(
            rel.rel_type.as_str(),
            "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
        ) {
            if rel.inputs.len() < 2 {
                return None;
            }
            for input in &rel.inputs {
                collect(input, statement_sql, leaves)?;
            }
            return Some(());
        }
        leaves.push(
            first_query_block_range(rel, statement_sql)
                .or_else(|| exact_rel_range(rel, statement_sql))?,
        );
        Some(())
    }

    let mut leaves = Vec::new();
    collect(rel, statement_sql, &mut leaves)?;
    if leaves.len() < 2 || leaves.windows(2).any(|pair| pair[0].end > pair[1].start) {
        return None;
    }
    let envelope = leaves.first()?.start..leaves.last()?.end;
    let mut candidates = vec![envelope.clone(), 0..statement_sql.len()];
    let mut opens = Vec::new();
    for token in tokens {
        match token.kind {
            TokenKind::Open => opens.push((token.start, token.end)),
            TokenKind::Close => {
                let (open_start, open_end) = opens.pop()?;
                if open_end < token.start {
                    candidates.push(open_start..token.end);
                    candidates.push(open_end..token.start);
                }
            }
            _ => {}
        }
    }
    if !opens.is_empty() {
        return None;
    }
    candidates.sort_by_key(|candidate| {
        (
            candidate.end.saturating_sub(candidate.start),
            candidate.start,
        )
    });
    candidates.dedup_by(|left, right| left.start == right.start && left.end == right.end);
    candidates.into_iter().find_map(|candidate| {
        range_contains(&candidate, &envelope)
            .then(|| trim_range(statement_sql, candidate))
            .flatten()
            .and_then(|candidate| {
                parse_query_shape(statement_sql, tokens, candidate.clone())
                    .ok()
                    .and_then(|shape| matches!(shape, QueryShape::Set { .. }).then_some(candidate))
            })
    })
}

fn parse_query_shape(source: &str, tokens: &[Token], range: Range<usize>) -> Result<QueryShape> {
    let range = strip_complete_parentheses(source, tokens, range)?;
    let base_depth = tokens
        .iter()
        .find(|token| token.start >= range.start && token.end <= range.end)
        .map(|token| token.depth)
        .ok_or_else(|| invalid("source query expression has no tokens"))?;
    let operators = tokens
        .iter()
        .enumerate()
        .filter_map(|(index, token)| {
            if token.start < range.start || token.end > range.end || token.depth != base_depth {
                return None;
            }
            let op = match token.kind {
                TokenKind::Word(ref word) if word == "union" => SetOperator::Union,
                TokenKind::Word(ref word) if word == "intersect" => SetOperator::Intersect,
                TokenKind::Word(ref word) if word == "except" => SetOperator::Except,
                _ => return None,
            };
            Some((index, op))
        })
        .collect::<Vec<_>>();
    if operators.is_empty() {
        return Ok(QueryShape::Leaf(range));
    }

    let mut operands = Vec::with_capacity(operators.len() + 1);
    let mut ops = Vec::with_capacity(operators.len());
    let mut operand_start = range.start;
    for (position, (token_index, op)) in operators.iter().enumerate() {
        let operator = &tokens[*token_index];
        let operand = trim_range(source, operand_start..operator.start)
            .ok_or_else(|| invalid("set operation has an empty left branch"))?;
        operands.push(parse_query_shape(source, tokens, operand)?);
        let next = tokens.get(*token_index + 1);
        let (all, after_operator) = match next {
            Some(Token {
                kind: TokenKind::Word(word),
                end,
                depth,
                ..
            }) if *depth == base_depth && word == "all" => (true, *end),
            Some(Token {
                kind: TokenKind::Word(word),
                end,
                depth,
                ..
            }) if *depth == base_depth && word == "distinct" => (false, *end),
            _ => (false, operator.end),
        };
        let next_operator_start = operators
            .get(position + 1)
            .map(|(index, _)| tokens[*index].start)
            .unwrap_or(range.end);
        if after_operator >= next_operator_start {
            return Err(invalid("set quantifier consumes the following branch"));
        }
        operand_start = after_operator;
        ops.push((*op, all));
    }
    let last = trim_range(source, operand_start..range.end)
        .ok_or_else(|| invalid("set operation has an empty right branch"))?;
    operands.push(parse_query_shape(source, tokens, last)?);

    // SQL INTERSECT binds more tightly than UNION/EXCEPT.  Reduce those runs
    // first, preserving source order, then reduce UNION/EXCEPT left-to-right.
    let mut reduced_operands = vec![operands.remove(0)];
    let mut reduced_ops = Vec::new();
    for ((op, all), right) in ops.into_iter().zip(operands) {
        if op == SetOperator::Intersect {
            let left = reduced_operands.pop().expect("one left operand");
            reduced_operands.push(combine_set(op, all, left, right));
        } else {
            reduced_ops.push((op, all));
            reduced_operands.push(right);
        }
    }
    let mut result = reduced_operands.remove(0);
    for ((op, all), right) in reduced_ops.into_iter().zip(reduced_operands) {
        result = combine_set(op, all, result, right);
    }
    Ok(result)
}

fn combine_set(op: SetOperator, all: bool, left: QueryShape, right: QueryShape) -> QueryShape {
    let start = left.range().start;
    let end = right.range().end;
    QueryShape::Set {
        op,
        all,
        inputs: vec![left, right],
        range: start..end,
    }
}

fn strip_complete_parentheses(
    source: &str,
    tokens: &[Token],
    mut range: Range<usize>,
) -> Result<Range<usize>> {
    loop {
        range =
            trim_range(source, range).ok_or_else(|| invalid("source query expression is empty"))?;
        let relevant = tokens
            .iter()
            .filter(|token| token.start >= range.start && token.end <= range.end)
            .collect::<Vec<_>>();
        let (Some(first), Some(last)) = (relevant.first(), relevant.last()) else {
            return Err(invalid("source query expression has no lexical tokens"));
        };
        if first.kind != TokenKind::Open || last.kind != TokenKind::Close {
            return Ok(range);
        }
        let open_depth = first.depth;
        let closes_at_end = relevant
            .iter()
            .skip(1)
            .find(|token| token.kind == TokenKind::Close && token.depth == open_depth);
        if closes_at_end.is_none_or(|close| close.end != last.end) {
            return Ok(range);
        }
        range = first.end..last.start;
    }
}

fn suffix_roles(tokens: &[Token], range: Range<usize>) -> Result<SuffixRoles> {
    let relevant = tokens
        .iter()
        .enumerate()
        .filter(|(_, token)| token.start >= range.start && token.end <= range.end)
        .collect::<Vec<_>>();
    let Some((_, first)) = relevant.first().copied() else {
        return Ok(SuffixRoles::default());
    };

    // A parenthesized set expression may be followed by ORDER/LIMIT at the
    // surrounding depth.  Otherwise the suffix is at the SELECT's own depth.
    let suffix_depth = first.depth;
    let mut clause_starts = Vec::new();
    for (position, (global_index, token)) in relevant.iter().enumerate() {
        if token.depth != suffix_depth {
            continue;
        }
        let role = match &token.kind {
            TokenKind::Word(word) if word == "order" => {
                let next = relevant.get(position + 1).map(|(_, token)| *token);
                if next.is_some_and(|next| {
                    next.depth == suffix_depth
                        && matches!(&next.kind, TokenKind::Word(word) if word == "by")
                }) {
                    Some("order")
                } else {
                    None
                }
            }
            TokenKind::Word(word) if word == "limit" || word == "fetch" => Some("fetch"),
            TokenKind::Word(word) if word == "offset" => Some("offset"),
            _ => None,
        };
        if let Some(role) = role {
            clause_starts.push((token.start, *global_index, role));
        }
    }
    clause_starts.sort_by_key(|(start, _, _)| *start);
    if clause_starts.is_empty() {
        return Ok(SuffixRoles::default());
    }
    let mut roles = SuffixRoles::default();
    for (position, (start, token_index, role)) in clause_starts.iter().enumerate() {
        let end = clause_starts
            .get(position + 1)
            .map(|(start, _, _)| *start)
            .unwrap_or(range.end);
        match *role {
            "order" => {
                roles.shape.order = true;
                roles.order_range = Some(*start..end);
            }
            "fetch" => {
                let is_limit_all = matches!(
                    tokens.get(*token_index + 1).map(|token| &token.kind),
                    Some(TokenKind::Word(word)) if word == "all"
                );
                if !is_limit_all {
                    roles.shape.fetch = true;
                    roles.fetch_range = Some(*start..end);
                }
            }
            "offset" => {
                roles.shape.offset = true;
                roles.offset_range = Some(*start..end);
            }
            _ => unreachable!(),
        }
    }
    Ok(roles)
}

fn validate_block_roots(
    rel: &CalciteRel,
    parent_block: Option<&str>,
    enclosing_project: Option<&CalciteRel>,
    unobservable_output_block: Option<&str>,
    context: &BlockWalkContext<'_>,
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    let own_block = context.relocated_blocks.effective_block(rel);
    if let Some(block) = own_block
        && own_block != parent_block
    {
        validate_one_block(
            rel,
            block,
            unobservable_output_block == Some(block),
            enclosing_project,
            context,
            claimed,
        )?;
    }
    let child_enclosing_project = if rel.rel_type == "LogicalProject" {
        Some(rel)
    } else {
        enclosing_project
    };
    for input in &rel.inputs {
        validate_block_roots(
            input,
            own_block,
            child_enclosing_project,
            unobservable_output_block,
            context,
            claimed,
        )?;
    }
    for rex in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        validate_rex_block_roots(rex, context, claimed)?;
    }
    if let Some(rows) = &rel.tuples {
        for rex in rows.iter().flatten() {
            validate_rex_block_roots(rex, context, claimed)?;
        }
    }
    Ok(())
}

fn validate_rex_block_roots(
    rex: &CalciteRex,
    context: &BlockWalkContext<'_>,
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    let statement_sql = context.statement.sql;
    let tokens = context.statement.tokens;
    if let Some(subquery) = rex.subquery_rel.as_deref() {
        let unobservable_output_block =
            exact_exists_subquery(rex, subquery, statement_sql, tokens)?
                .then_some(subquery.source_query_block_id.as_deref())
                .flatten();
        validate_block_roots(
            subquery,
            None,
            None,
            unobservable_output_block,
            context,
            claimed,
        )?;
    }
    if let Some(reference) = rex.reference_expr.as_deref() {
        validate_rex_block_roots(reference, context, claimed)?;
    }
    for operand in &rex.operands {
        validate_rex_block_roots(operand, context, claimed)?;
    }
    Ok(())
}

fn exact_exists_subquery(
    rex: &CalciteRex,
    subquery: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Result<bool> {
    if rex.kind.as_deref() != Some("EXISTS") {
        return Ok(false);
    }
    if rex.class.as_deref() != Some("RexSubQuery") {
        return Err(invalid("EXISTS Rex has no exact RexSubQuery class"));
    }
    let role = rex
        .source_node_id
        .as_deref()
        .and_then(|id| span_range(statement_sql, id))
        .ok_or_else(|| invalid("EXISTS Rex has no exact source span"))?;
    let source_text = rex
        .source_text
        .as_deref()
        .ok_or_else(|| invalid("EXISTS Rex has no exact source text"))?;
    if statement_sql.get(role.clone()) != Some(source_text) {
        return Err(invalid(
            "EXISTS Rex source text differs from its exact span",
        ));
    }
    let first = tokens
        .iter()
        .find(|token| token.start >= role.start && token.end <= role.end)
        .ok_or_else(|| invalid("EXISTS Rex source span has no tokens"))?;
    if first.start != role.start
        || !matches!(&first.kind, TokenKind::Word(word) if word == "exists")
    {
        return Err(invalid("EXISTS Rex source span does not begin with EXISTS"));
    }
    let open = tokens
        .iter()
        .find(|token| {
            token.start >= first.end
                && token.end <= role.end
                && token.depth == first.depth
                && token.kind == TokenKind::Open
        })
        .ok_or_else(|| invalid("EXISTS Rex has no exact subquery parenthesis"))?;
    let owner = first_query_block_range(subquery, statement_sql)
        .or_else(|| exact_rel_range(subquery, statement_sql))
        .ok_or_else(|| invalid("EXISTS subquery has no exact source owner"))?;
    let owner = strip_complete_parentheses(statement_sql, tokens, owner)?;
    if owner.start < open.end || owner.end > role.end {
        return Err(invalid(
            "EXISTS subquery owner lies outside its exact parenthesized role",
        ));
    }
    exists_root_select_targets_are_runtime_total(subquery, statement_sql, tokens)
}

fn exists_root_select_targets_are_runtime_total(
    subquery: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Result<bool> {
    let Some(block) = subquery
        .source_query_block_id
        .as_deref()
        .and_then(|id| span_range(statement_sql, id))
    else {
        return Ok(false);
    };
    let block = strip_complete_parentheses(statement_sql, tokens, block)?;
    let Some(source) = statement_sql.get(block) else {
        return Ok(false);
    };
    let Some(local_tokens) = lex(source) else {
        return Ok(false);
    };
    let Ok(items) = direct_select_item_ranges(source, &local_tokens) else {
        return Ok(false);
    };
    Ok(!items.is_empty()
        && items.iter().all(|item| {
            source.get(item.clone()).is_some_and(|item| {
                select_item_is_wildcard(item)
                    || select_item_is_runtime_total_literal(item)
                    || simple_identifier_select_output_name(item).is_some()
            })
        }))
}

fn select_item_is_runtime_total_literal(source: &str) -> bool {
    let source = source.trim();
    // Keep the source-only totality proof deliberately smaller than SQL's
    // literal grammar.  String and arbitrary-precision NUMERIC literals can
    // still fail during encoding/allocation or numeric input; without the
    // generated Project there is no typed payload with which to prove those
    // boundaries.  NULL, booleans, and one in-range INT4 token are total.
    let prefix_end = ["null", "true", "false"]
        .into_iter()
        .find_map(|literal| {
            source
                .get(..literal.len())
                .filter(|prefix| prefix.eq_ignore_ascii_case(literal))
                .filter(|_| {
                    source
                        .get(literal.len()..)
                        .and_then(|suffix| suffix.chars().next())
                        .is_none_or(|ch| ch.is_whitespace())
                })
                .map(|_| literal.len())
        })
        .or_else(|| exact_int4_literal_prefix_end(source));
    let Some(prefix_end) = prefix_end else {
        return false;
    };
    let Some(suffix) = source.get(prefix_end..) else {
        return false;
    };
    suffix.is_empty()
        || suffix.chars().next().is_some_and(char::is_whitespace)
            && valid_output_alias_suffix(suffix)
}

fn exact_int4_literal_prefix_end(source: &str) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut index = usize::from(matches!(bytes.first(), Some(b'+' | b'-')));
    while bytes.get(index).is_some_and(u8::is_ascii_digit) {
        index += 1;
    }
    (index > usize::from(matches!(bytes.first(), Some(b'+' | b'-')))
        && source.get(..index)?.parse::<i32>().is_ok())
    .then_some(index)
}

#[derive(Default)]
struct BlockCounts<'a> {
    where_filters: usize,
    having_filters: usize,
    other_filters: usize,
    joins: usize,
    sorts: usize,
    aggregates: Vec<&'a CalciteRel>,
}

fn validate_select_output_carrier(
    block_root: &CalciteRel,
    context: &SelectOutputContext<'_>,
) -> Result<()> {
    let block_id = context.block_id;
    let statement_sql = context.statement.sql;
    let block_range = context.block_range;
    let block_source = context.block_source;
    let tokens = context.tokens;
    let unobservable_select_output = context.unobservable_select_output;
    let enclosing_project = context.enclosing_project;
    let relocated_blocks = context.relocated_blocks;
    let terminal_analysis_error = context.terminal_analysis_error;
    let mut carrier = block_root;
    loop {
        if relocated_blocks
            .effective_block(carrier)
            .is_some_and(|owner| owner != block_id)
        {
            break;
        }
        if matches!(carrier.rel_type.as_str(), "LogicalSort" | "LogicalFilter")
            && carrier.inputs.len() == 1
            && same_calcite_set_row_types(&carrier.row_type, &carrier.inputs[0].row_type)
        {
            carrier = &carrier.inputs[0];
            continue;
        }
        break;
    }

    match carrier.rel_type.as_str() {
        "LogicalProject" if relocated_blocks.effective_block(carrier) == Some(block_id) => Ok(()),
        "LogicalAggregate"
            if unobservable_select_output
                && relocated_blocks.effective_block(carrier) == Some(block_id) =>
        {
            // EXISTS observes only whether this logical input produces a row.
            // `exact_exists_subquery` independently proved every erased
            // SELECT target runtime-total, so Calcite's internal grouping
            // keys need not equal the source SELECT-output arity. Grouping,
            // aggregate, WHERE/HAVING, and join roles remain mandatory below.
            Ok(())
        }
        "LogicalAggregate" if relocated_blocks.effective_block(carrier) == Some(block_id) => {
            if super::convert::exact_direct_cte_aggregate_reconstruction_owner(
                carrier,
                statement_sql,
            )
            .as_deref()
                == Some(block_id)
            {
                Ok(())
            } else {
                validate_direct_aggregate_select_output(carrier, context.source_block())
            }
        }
        _ if unobservable_select_output => Ok(()),
        _ if validate_collapsed_direct_cte_select_output(
            block_root,
            block_id,
            statement_sql,
            block_range,
            block_source,
            tokens,
            enclosing_project,
        )? =>
        {
            Ok(())
        }
        _ if validate_collapsed_derived_identity_select(
            block_root,
            carrier,
            context.source_block(),
        )? =>
        {
            Ok(())
        }
        _ if terminal_analysis_error => Ok(()),
        _ => Err(invalid(format!(
            "query block {block_id:?} has no exact SELECT-output Project or closed direct Aggregate carrier"
        ))),
    }
}

fn same_named_calcite_row_types(
    left: &[crate::calcite::CalciteField],
    right: &[crate::calcite::CalciteField],
) -> bool {
    same_calcite_set_row_types(left, right)
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.name == right.name)
}

fn simple_unaliased_identifier_name(source: &str) -> Option<(String, bool)> {
    let source = source.trim();
    let mut offset = 0usize;
    loop {
        let (name, quoted, consumed) = parse_one_identifier(source.get(offset..)?)?;
        offset += consumed;
        let rest = source.get(offset..)?;
        let trimmed = rest.trim_start();
        offset += rest.len() - trimmed.len();
        if trimmed.is_empty() {
            return Some((name, quoted));
        }
        if !trimmed.starts_with('.') {
            return None;
        }
        offset += 1;
        let rest = source.get(offset..)?;
        let trimmed = rest.trim_start();
        offset += rest.len() - trimmed.len();
    }
}

/// Close a direct non-aggregate CTE definition whose output Project Calcite
/// has moved to the consuming query block.  This is the Project analogue of
/// `validate_direct_cte_aggregate_select_output`: the exact CTE edge and the
/// independently parsed public SELECT list, rather than Calcite row names,
/// authorize the cross-block carrier.  Conversion subsequently revalidates
/// each scalar's complete typed lineage and rejects unsafe omitted outputs.
fn validate_collapsed_direct_cte_select_output(
    block_root: &CalciteRel,
    block_id: &str,
    statement_sql: &str,
    block_range: &Range<usize>,
    block_source: &str,
    tokens: &[Token],
    enclosing_project: Option<&CalciteRel>,
) -> Result<bool> {
    let Some(project) = enclosing_project else {
        return Ok(false);
    };
    let ([input], [Some(cte_use)]) = (
        project.inputs.as_slice(),
        project.source_input_cte_uses.as_slice(),
    ) else {
        return Ok(false);
    };
    if cte_use.definition_query_node_id != block_id {
        return Ok(false);
    }
    if project.rel_type != "LogicalProject"
        || !std::ptr::eq(input, block_root)
        || project.source_query_block_id.as_deref() == Some(block_id)
        || project.project_rex.len() != project.row_type.len()
    {
        return Err(invalid(
            "direct CTE Project is not the exact sole-input consumer of its definition clone",
        ));
    }

    validate_direct_cte_shape_edge(cte_use, block_id, block_range, block_source, statement_sql)?;
    let items = direct_select_item_ranges(block_source, tokens)?
        .into_iter()
        .map(|range| block_range.start + range.start..block_range.start + range.end)
        .collect::<Vec<_>>();
    let outputs =
        super::convert::exact_direct_cte_query_shape_outputs(cte_use).ok_or_else(|| {
            invalid(
                "direct CTE Project definition has no exact, unambiguous public output namespace",
            )
        })?;
    if outputs.len() != items.len()
        || outputs.iter().enumerate().any(|(index, output)| {
            span_range(statement_sql, &output.project_item_node_id) != items.get(index).cloned()
                || span_range(statement_sql, &output.definition_node_id).is_none_or(|definition| {
                    !range_contains(&items[index], &definition)
                        || statement_sql.get(definition) != Some(&output.definition_text)
                })
                || span_range(statement_sql, &output.output_alias_node_id).is_none()
        })
    {
        return Err(invalid(
            "direct CTE Project public output descriptors do not exactly cover its SELECT list",
        ));
    }

    let root_expansions = project
        .project_rex
        .iter()
        .filter(|rex| {
            rex.source_expansion
                .as_ref()
                .is_some_and(|expansion| direct_cte_expansion_kind(&expansion.kind))
        })
        .count();
    let all_expansions = project
        .project_rex
        .iter()
        .map(direct_cte_expansion_count)
        .sum::<usize>();
    if root_expansions != all_expansions {
        return Err(invalid(
            "direct CTE Project contains a nested/lazy expansion",
        ));
    }

    let outer_block_id = project
        .source_query_block_id
        .as_deref()
        .ok_or_else(|| invalid("direct CTE Project has no exact consumer query block"))?;
    let outer_block = span_range(statement_sql, outer_block_id)
        .ok_or_else(|| invalid("direct CTE Project consumer query block is malformed"))?;
    let mut realized = BTreeSet::new();
    for (project_index, rex) in project.project_rex.iter().enumerate() {
        let Some(expansion) = rex
            .source_expansion
            .as_ref()
            .filter(|expansion| direct_cte_expansion_kind(&expansion.kind))
        else {
            continue;
        };
        let public_index = expansion
            .public_output_index
            .ok_or_else(|| invalid("direct CTE Project expansion has no public output ordinal"))?;
        let output = outputs.get(public_index).ok_or_else(|| {
            invalid("direct CTE Project expansion public output ordinal is out of range")
        })?;
        let reference = exact_text_range(
            statement_sql,
            &expansion.reference_node_id,
            &expansion.reference_text,
        );
        let outer_from = exact_text_range(
            statement_sql,
            &expansion.outer_from_node_id,
            &expansion.outer_from_text,
        );
        let reference_identity = simple_unaliased_identifier_name(&expansion.reference_text);
        if expansion.cte_use.as_ref() != Some(cte_use)
            || expansion.inner_select_node_id != block_id
            || expansion.inner_select_text != block_source
            || !exact_query_expression_range_matches_block(
                statement_sql,
                &expansion.outer_select_node_id,
                &expansion.outer_select_text,
                &outer_block,
            )
            || expansion.outer_from_node_id != cte_use.relation_node_id
            || expansion.outer_from_text != cte_use.relation_text
            || expansion.project_item_node_id != output.project_item_node_id
            || expansion.definition_node_id != output.definition_node_id
            || expansion.output_alias_node_id != output.output_alias_node_id
            || expansion.definition_text != output.definition_text
            || exact_text_range(
                statement_sql,
                &expansion.project_item_node_id,
                &expansion.project_item_text,
            ) != items.get(public_index).cloned()
            || exact_text_range(
                statement_sql,
                &expansion.definition_node_id,
                &expansion.definition_text,
            ) != span_range(statement_sql, &output.definition_node_id)
            || exact_text_range(
                statement_sql,
                &expansion.output_alias_node_id,
                &expansion.output_alias_text,
            ) != span_range(statement_sql, &output.output_alias_node_id)
            || reference
                .as_ref()
                .is_none_or(|range| !range_contains(&outer_block, range))
            || outer_from
                .as_ref()
                .is_none_or(|range| !range_contains(&outer_block, range))
            || reference_identity
                .as_ref()
                .map(|(name, quoted)| (name, quoted))
                != Some((&output.name, &output.quoted))
            || rex.source_node_id.as_deref() != Some(output.definition_node_id.as_str())
            || rex.source_text.as_deref() != Some(output.definition_text.as_str())
            || !rex_has_exact_field_type(rex, &project.row_type[project_index])
        {
            return Err(invalid(
                "direct CTE Project expansion differs from its containing edge or exact public descriptor",
            ));
        }
        if let Some(index) = rex.index {
            let field = input.row_type.get(index).ok_or_else(|| {
                invalid("direct CTE Project expansion input index is out of range")
            })?;
            if rex.kind.as_deref() != Some("INPUT_REF")
                || rex.class.as_deref() != Some("RexInputRef")
                || !rex.operands.is_empty()
                || rex.reference_expr.is_some()
                || rex.subquery_rel.is_some()
                || rex.window.is_some()
                || !rex_has_exact_field_type(rex, field)
                || !same_calcite_set_row_types(
                    std::slice::from_ref(field),
                    std::slice::from_ref(&project.row_type[project_index]),
                )
            {
                return Err(invalid(
                    "direct CTE Project expansion changes its exact typed input position",
                ));
            }
        }
        realized.insert(public_index);
    }

    for (index, output) in outputs.iter().enumerate() {
        if !realized.contains(&index)
            && !super::convert::exact_cte_project_realizes_public_output(
                project,
                index,
                statement_sql,
            )
            && !super::convert::exact_cte_definition_is_conservatively_runtime_total(
                &output.definition_text,
            )
            && !super::convert::exact_cte_omitted_output_has_declarative_reconstruction(
                project, index,
            )
        {
            return Err(invalid(format!(
                "direct CTE Project omits non-runtime-total public output {index} ({:?})",
                output.name
            )));
        }
    }
    Ok(true)
}

fn validate_collapsed_derived_identity_select(
    block_root: &CalciteRel,
    carrier: &CalciteRel,
    block: SourceBlockContext<'_>,
) -> Result<bool> {
    let block_id = block.block_id;
    let statement_sql = block.statement.sql;
    let block_source = block.block_source;
    let tokens = block.tokens;
    let Some(enclosing_project) = block.enclosing_project else {
        return Ok(false);
    };
    if enclosing_project.rel_type != "LogicalProject"
        || enclosing_project.inputs.len() != 1
        || !std::ptr::eq(&enclosing_project.inputs[0], block_root)
        || enclosing_project.source_query_block_id.as_deref() == Some(block_id)
    {
        return Ok(false);
    }
    let outer_block = enclosing_project
        .source_query_block_id
        .as_deref()
        .and_then(|id| span_range(statement_sql, id))
        .ok_or_else(|| invalid("collapsed derived SELECT has no exact enclosing query block"))?;
    let statement_tokens = lex(statement_sql)
        .ok_or_else(|| invalid("collapsed derived SELECT statement is lexically malformed"))?;
    let outer_block = strip_complete_parentheses(statement_sql, &statement_tokens, outer_block)?;
    let outer_source = statement_sql.get(outer_block.clone()).ok_or_else(|| {
        invalid("collapsed derived SELECT enclosing block is outside its statement")
    })?;
    let outer_tokens = lex(outer_source)
        .ok_or_else(|| invalid("collapsed derived SELECT enclosing block is malformed"))?;
    let outer_items = direct_select_item_ranges(outer_source, &outer_tokens)?;
    let items = direct_select_item_ranges(block_source, tokens)?;
    let outer_wildcard = outer_items.len() == 1
        && outer_source
            .get(outer_items[0].clone())
            .is_some_and(|item| item.trim() == "*");
    if outer_wildcard {
        if carrier.source_query_block_id.as_deref() != Some(block_id)
            || !same_named_calcite_row_types(&block_root.row_type, &carrier.row_type)
            || !same_named_calcite_row_types(&block_root.row_type, &enclosing_project.row_type)
            || items.len() != block_root.row_type.len()
        {
            return Err(invalid(
                "collapsed derived identity SELECT changes its complete named row type",
            ));
        }
        for ((item, output), input) in items
            .iter()
            .zip(&block_root.row_type)
            .zip(&carrier.row_type)
        {
            let Some((name, quoted)) = block_source
                .get(item.clone())
                .and_then(simple_unaliased_identifier_name)
            else {
                return Err(invalid(
                    "collapsed derived identity SELECT item is not an unaliased identifier",
                ));
            };
            let matches = |field: &str| {
                if quoted {
                    name == field
                } else {
                    name.eq_ignore_ascii_case(field)
                }
            };
            if !matches(&output.name) || !matches(&input.name) {
                return Err(invalid(
                    "collapsed derived identity SELECT changes identifier order",
                ));
            }
        }
        return Ok(true);
    }

    let inner_wildcard = items.len() == 1
        && block_source
            .get(items[0].clone())
            .is_some_and(select_item_is_wildcard);
    if inner_wildcard {
        return validate_collapsed_wildcard_composition(
            block_root,
            carrier,
            enclosing_project,
            statement_sql,
            &outer_block,
            &outer_items,
        );
    }
    let composition = CollapsedCompositionContext {
        block,
        enclosing_project,
        inner_items: &items,
        outer_block: &outer_block,
        outer_items: &outer_items,
    };
    validate_collapsed_expansion_composition(block_root, carrier, &composition)
}

fn validate_collapsed_wildcard_composition(
    block_root: &CalciteRel,
    carrier: &CalciteRel,
    enclosing_project: &CalciteRel,
    statement_sql: &str,
    outer_block: &Range<usize>,
    outer_items: &[Range<usize>],
) -> Result<bool> {
    if carrier.rel_type != "LogicalProject"
        || carrier.source_query_block_id == block_root.source_query_block_id
        || !same_named_calcite_row_types(&block_root.row_type, &carrier.row_type)
        || outer_items.len() != enclosing_project.project_rex.len()
        || enclosing_project.project_rex.len() != enclosing_project.row_type.len()
    {
        return Err(invalid(
            "collapsed derived wildcard is not one exact composed Project boundary",
        ));
    }
    for (index, (item, rex)) in outer_items
        .iter()
        .zip(&enclosing_project.project_rex)
        .enumerate()
    {
        let role = rex
            .source_node_id
            .as_deref()
            .and_then(|id| span_range(statement_sql, id))
            .ok_or_else(|| invalid("collapsed wildcard consumer has no exact SELECT-item span"))?;
        let input_index = rex.index.ok_or_else(|| {
            invalid("collapsed wildcard consumer is not a direct positional reference")
        })?;
        let input_field = block_root.row_type.get(input_index).ok_or_else(|| {
            invalid("collapsed wildcard consumer index is outside the derived row")
        })?;
        let output_field = &enclosing_project.row_type[index];
        let global_item = outer_block.start + item.start..outer_block.start + item.end;
        let Some((source_name, source_quoted)) = statement_sql
            .get(role.clone())
            .and_then(simple_unaliased_identifier_name)
        else {
            return Err(invalid(
                "collapsed wildcard consumer is not an exact identifier reference",
            ));
        };
        let source_matches_input = if source_quoted {
            source_name == input_field.name
        } else {
            source_name.eq_ignore_ascii_case(&input_field.name)
        };
        if !range_contains(&global_item, &role)
            || statement_sql.get(role.clone()) != rex.source_text.as_deref()
            || rex.kind.as_deref() != Some("INPUT_REF")
            || rex.class.as_deref() != Some("RexInputRef")
            || rex.source_expansion.is_some()
            || !rex.operands.is_empty()
            || rex.reference_expr.is_some()
            || rex.subquery_rel.is_some()
            || !source_matches_input
            || !same_calcite_set_row_types(
                std::slice::from_ref(input_field),
                std::slice::from_ref(output_field),
            )
        {
            return Err(invalid(
                "collapsed derived wildcard consumer changes an exact ordered output role",
            ));
        }
    }
    Ok(true)
}

fn validate_collapsed_expansion_composition(
    block_root: &CalciteRel,
    carrier: &CalciteRel,
    context: &CollapsedCompositionContext<'_>,
) -> Result<bool> {
    let block_id = context.block.block_id;
    let enclosing_project = context.enclosing_project;
    let statement_sql = context.block.statement.sql;
    let block_range = context.block.block_range;
    let block_source = context.block.block_source;
    let inner_items = context.inner_items;
    let outer_block = context.outer_block;
    let outer_items = context.outer_items;
    if carrier.source_query_block_id.as_deref() != Some(block_id)
        || !same_named_calcite_row_types(&block_root.row_type, &carrier.row_type)
        || enclosing_project.project_rex.len() != enclosing_project.row_type.len()
        || inner_items.is_empty()
        || outer_items.is_empty()
    {
        return Err(invalid(
            "collapsed derived SELECT composition has inconsistent source/generated arity",
        ));
    }

    // Calcite composes the inner projection into the relational carrier used
    // by the outer block.  That carrier is not in general the outer SELECT
    // list: before an Aggregate it contains grouping inputs and aggregate
    // arguments, and one outer scalar can use the same inner output more than
    // once.  Likewise, the wrapper may choose an exact GROUP BY reference as
    // the public alias role instead of the textually earlier SELECT role.
    // Collect every exact expansion in each carrier expression rather than
    // pairing carrier fields positionally with outer SELECT items.
    let mut expansions = Vec::new();
    for (root_index, rex) in enclosing_project.project_rex.iter().enumerate() {
        collect_direct_derived_projected_expansions(rex, root_index, true, &mut expansions);
    }
    let mut claimed = BTreeSet::new();
    for (root_index, root, rex, expansion) in expansions {
        if expansion.inner_select_node_id != block_id {
            // One composed Project can carry expansions from several nested
            // derived boundaries.  Each boundary is closed independently.
            continue;
        }
        if expansion.inner_select_text != block_source
            || exact_text_range(
                statement_sql,
                &expansion.outer_select_node_id,
                &expansion.outer_select_text,
            ) != Some(outer_block.clone())
        {
            return Err(invalid(
                "collapsed derived SELECT expansion has inconsistent query identities",
            ));
        }
        let project_item = exact_text_range(
            statement_sql,
            &expansion.project_item_node_id,
            &expansion.project_item_text,
        )
        .ok_or_else(|| invalid("collapsed derived SELECT expansion has no exact project item"))?;
        let Some(inner_index) = inner_items.iter().position(|item| {
            project_item == (block_range.start + item.start..block_range.start + item.end)
        }) else {
            return Err(invalid(
                "collapsed derived SELECT expansion is not one ordered inner output item",
            ));
        };
        // Reusing one derived output in two exact outer scalar roles is
        // ordinary SQL (for example SUM(volume) and a CASE over volume).
        // Every occurrence is still validated below against the same unique
        // inner SELECT item and its own exact outer reference.
        claimed.insert(inner_index);
        let inner_source = block_source
            .get(inner_items[inner_index].clone())
            .ok_or_else(|| invalid("collapsed derived SELECT inner item is out of bounds"))?;
        let reference = exact_text_range(
            statement_sql,
            &expansion.reference_node_id,
            &expansion.reference_text,
        )
        .ok_or_else(|| invalid("collapsed derived SELECT expansion has no exact outer role"))?;
        let outer_from = exact_text_range(
            statement_sql,
            &expansion.outer_from_node_id,
            &expansion.outer_from_text,
        );
        let definition = exact_text_range(
            statement_sql,
            &expansion.definition_node_id,
            &expansion.definition_text,
        );
        let output_alias = exact_text_range(
            statement_sql,
            &expansion.output_alias_node_id,
            &expansion.output_alias_text,
        );
        let reference_identity = simple_unaliased_identifier_name(&expansion.reference_text);
        let alias_identity = simple_unaliased_identifier_name(&expansion.output_alias_text);
        let expansion_shape_exact = match expansion.kind.as_str() {
            "DIRECT_DERIVED_PASSTHROUGH" => {
                definition.as_ref() == Some(&project_item)
                    && output_alias.as_ref() == Some(&project_item)
                    && simple_unaliased_identifier_name(inner_source) == alias_identity
            }
            "DIRECT_DERIVED_OUTPUT_ALIAS" => definition
                .as_ref()
                .zip(output_alias.as_ref())
                .is_some_and(|(definition, alias)| {
                    range_contains(&project_item, definition)
                        && range_contains(&project_item, alias)
                        && definition.start == project_item.start
                        && definition.end < alias.start
                        && alias.end == project_item.end
                        && statement_sql
                            .get(definition.end..alias.start)
                            .and_then(lex)
                            .is_some_and(|tokens| {
                                matches!(tokens.as_slice(), [Token {
                                    depth: 0,
                                    kind: TokenKind::Word(word),
                                    ..
                                }] if word == "as")
                            })
                }),
            _ => false,
        };
        let generated_input_binding_exact = if let Some(input_index) = rex.index {
            carrier
                .row_type
                .get(input_index)
                .is_some_and(|input_field| {
                    rex.kind.as_deref() == Some("INPUT_REF")
                        && rex.class.as_deref() == Some("RexInputRef")
                        && rex.operands.is_empty()
                        && rex.reference_expr.is_none()
                        && rex.subquery_rel.is_none()
                        && rex_has_exact_field_type(rex, input_field)
                })
        } else {
            rex.class.as_deref() == Some("RexCall")
                && rex.reference_expr.is_none()
                && rex.subquery_rel.is_none()
        };
        let generated_root_binding_exact = !root
            || enclosing_project
                .row_type
                .get(root_index)
                .is_some_and(|output_field| rex_has_exact_field_type(rex, output_field));
        let reference_is_owned_by_outer_select = statement_sql
            .get(outer_block.clone())
            .zip(reference.start.checked_sub(outer_block.start))
            .is_some_and(|(outer_source, offset)| {
                super::convert::aggregate_source_select_owner_is_root(outer_source, offset)
            });
        if !range_contains(outer_block, &reference)
            || !reference_is_owned_by_outer_select
            || outer_from
                .as_ref()
                .is_none_or(|range| !range_contains(range, block_range))
            || definition.is_none()
            || output_alias.is_none()
            || rex
                .source_node_id
                .as_deref()
                .and_then(|id| span_range(statement_sql, id))
                != definition
            || rex.source_text.as_deref() != Some(expansion.definition_text.as_str())
            || reference_identity.is_none()
            || reference_identity != alias_identity
            || !expansion_shape_exact
            || !generated_input_binding_exact
            || !generated_root_binding_exact
        {
            return Err(invalid(
                "collapsed derived SELECT expansion changes an exact ordered identity",
            ));
        }
    }
    if claimed.len() != inner_items.len() {
        return Err(invalid(
            "collapsed derived SELECT composition omits an inner output item",
        ));
    }
    Ok(true)
}

fn collect_direct_derived_projected_expansions<'a>(
    rex: &'a CalciteRex,
    root_index: usize,
    root: bool,
    expansions: &mut Vec<(
        usize,
        bool,
        &'a CalciteRex,
        &'a CalciteProjectedSourceExpansion,
    )>,
) {
    if let Some(expansion) = rex.source_expansion.as_ref()
        && matches!(
            expansion.kind.as_str(),
            "DIRECT_DERIVED_OUTPUT_ALIAS" | "DIRECT_DERIVED_PASSTHROUGH"
        )
    {
        expansions.push((root_index, root, rex, expansion));
    }
    if let Some(reference) = rex.reference_expr.as_deref() {
        collect_direct_derived_projected_expansions(reference, root_index, false, expansions);
    }
    for operand in &rex.operands {
        collect_direct_derived_projected_expansions(operand, root_index, false, expansions);
    }
    if let Some(window) = rex.window.as_deref() {
        for key in &window.partition_keys {
            collect_direct_derived_projected_expansions(key, root_index, false, expansions);
        }
        for key in &window.order_keys {
            collect_direct_derived_projected_expansions(&key.expr, root_index, false, expansions);
        }
        for bound in [window.lower_bound.as_deref(), window.upper_bound.as_deref()]
            .into_iter()
            .flatten()
        {
            if let Some(offset) = bound.offset.as_deref() {
                collect_direct_derived_projected_expansions(offset, root_index, false, expansions);
            }
        }
    }
}

fn direct_select_item_ranges(source: &str, tokens: &[Token]) -> Result<Vec<Range<usize>>> {
    let select = tokens
        .iter()
        .position(|token| {
            token.depth == 0 && matches!(&token.kind, TokenKind::Word(word) if word == "select")
        })
        .ok_or_else(|| invalid("query block has no direct SELECT token"))?;
    let mut start_index = select + 1;
    if matches!(
        tokens.get(start_index).map(|token| &token.kind),
        Some(TokenKind::Word(word)) if matches!(word.as_str(), "all" | "distinct")
    ) {
        start_index += 1;
    }
    if matches!(
        tokens.get(start_index).map(|token| &token.kind),
        Some(TokenKind::Word(word)) if word == "on"
    ) {
        return Err(invalid(
            "PostgreSQL DISTINCT ON output shape is not represented",
        ));
    }
    let start = tokens
        .get(start_index)
        .map(|token| token.start)
        .unwrap_or(source.len());
    let end = tokens
        .iter()
        .skip(start_index)
        .find(|token| {
            token.depth == 0
                && (matches!(token.kind, TokenKind::Semicolon)
                    || matches!(&token.kind, TokenKind::Word(word)
                    if matches!(
                        word.as_str(),
                        "from"
                            | "where"
                            | "group"
                            | "having"
                            | "window"
                            | "order"
                            | "limit"
                            | "offset"
                            | "fetch"
                    )))
        })
        .map(|token| token.start)
        .unwrap_or(source.len());
    if start >= end {
        return Err(invalid("direct SELECT has an empty output list"));
    }

    let commas = tokens
        .iter()
        .filter(|token| {
            token.depth == 0
                && token.start >= start
                && token.end <= end
                && token.kind == TokenKind::Comma
        })
        .map(|token| token.start)
        .collect::<Vec<_>>();
    let mut items = Vec::with_capacity(commas.len() + 1);
    let mut item_start = start;
    for item_end in commas.into_iter().chain(std::iter::once(end)) {
        let item = trim_range(source, item_start..item_end)
            .ok_or_else(|| invalid("direct SELECT contains an empty output item"))?;
        items.push(item);
        item_start = item_end.saturating_add(1);
    }
    Ok(items)
}

fn valid_output_alias_suffix(source: &str) -> bool {
    let mut suffix = source.trim();
    if suffix.is_empty() {
        return true;
    }
    if suffix.len() >= 2
        && suffix
            .get(..2)
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case("as"))
        && suffix
            .get(2..)
            .and_then(|rest| rest.chars().next())
            .is_some_and(char::is_whitespace)
    {
        suffix = suffix[2..].trim_start();
    }
    parse_one_identifier(suffix).is_some_and(|(_, _, consumed)| {
        suffix
            .get(consumed..)
            .is_some_and(|rest| rest.trim().is_empty())
    })
}

fn parse_one_identifier(source: &str) -> Option<(String, bool, usize)> {
    if source.starts_with('"') {
        let mut name = String::new();
        let mut index = 1usize;
        while index < source.len() {
            let rest = source.get(index..)?;
            let ch = rest.chars().next()?;
            index += ch.len_utf8();
            if ch == '"' {
                if source.get(index..)?.starts_with('"') {
                    name.push('"');
                    index += 1;
                    continue;
                }
                return Some((name, true, index));
            }
            name.push(ch);
        }
        return None;
    }
    let mut chars = source.char_indices();
    let (_, first) = chars.next()?;
    if first != '_' && !first.is_alphabetic() {
        return None;
    }
    let mut end = first.len_utf8();
    for (index, ch) in chars {
        if ch == '_' || ch == '$' || ch.is_alphanumeric() {
            end = index + ch.len_utf8();
        } else {
            break;
        }
    }
    Some((source.get(..end)?.to_ascii_lowercase(), false, end))
}

fn simple_identifier_select_output_name(source: &str) -> Option<(String, bool)> {
    let source = source.trim();
    let mut offset = 0usize;
    loop {
        let (name, quoted, consumed) = parse_one_identifier(source.get(offset..)?)?;
        offset += consumed;
        let rest = source.get(offset..)?;
        let trimmed = rest.trim_start();
        offset += rest.len() - trimmed.len();
        if !trimmed.starts_with('.') {
            if trimmed.is_empty() {
                return Some((name, quoted));
            }
            let alias = if trimmed
                .get(..2)
                .is_some_and(|prefix| prefix.eq_ignore_ascii_case("as"))
                && trimmed
                    .get(2..)
                    .and_then(|rest| rest.chars().next())
                    .is_some_and(char::is_whitespace)
            {
                trimmed.get(2..)?.trim_start()
            } else {
                trimmed
            };
            let alias_source = alias;
            let (alias, alias_quoted, consumed) = parse_one_identifier(alias_source)?;
            return alias_source
                .get(consumed..)
                .is_some_and(|rest| rest.trim().is_empty())
                .then_some((alias, alias_quoted));
        }
        offset += 1;
        let rest = source.get(offset..)?;
        let trimmed = rest.trim_start();
        offset += rest.len() - trimmed.len();
    }
}

fn select_item_is_wildcard(source: &str) -> bool {
    let source = source.trim();
    if source == "*" {
        return true;
    }
    let mut offset = 0usize;
    loop {
        let Some((_, _, consumed)) = parse_one_identifier(source.get(offset..).unwrap_or_default())
        else {
            return false;
        };
        offset += consumed;
        let Some(rest) = source.get(offset..) else {
            return false;
        };
        let trimmed = rest.trim_start();
        offset += rest.len() - trimmed.len();
        if !trimmed.starts_with('.') {
            return false;
        }
        offset += 1;
        let Some(rest) = source.get(offset..) else {
            return false;
        };
        let trimmed = rest.trim_start();
        offset += rest.len() - trimmed.len();
        if trimmed == "*" {
            return true;
        }
    }
}

fn aggregate_group_output_matches_input(
    aggregate: &CalciteRel,
    input_index: usize,
    output: &crate::calcite::CalciteField,
    input: &crate::calcite::CalciteField,
) -> bool {
    let may_synthesize_null = aggregate.source_grouping.as_ref().is_some_and(|grouping| {
        grouping
            .grouping_sets
            .iter()
            .any(|set| !set.contains(&input_index))
    }) || aggregate
        .source_grouping_sets
        .as_ref()
        .is_some_and(|sets| sets.iter().any(|set| !set.contains(&input_index)));
    let nullability_matches = if may_synthesize_null {
        output.nullable
    } else {
        output.nullable == input.nullable
    };
    nullability_matches
        && output.ty == input.ty
        && calcite_full_type_bases_equal(
            output.full_type.as_deref(),
            output.nullable,
            input.full_type.as_deref(),
            input.nullable,
        )
        && output.precision == input.precision
        && output.scale == input.scale
        && output.charset == input.charset
        && output.type_collation == input.type_collation
}

fn select_item_matches_exact_role(
    statement_sql: &str,
    item: &Range<usize>,
    role: &Range<usize>,
) -> bool {
    role.start == item.start
        && role.end <= item.end
        && statement_sql
            .get(role.end..item.end)
            .is_some_and(valid_output_alias_suffix)
}

fn valid_filtered_aggregate_suffix(source: &str) -> bool {
    let Some(tokens) = lex(source) else {
        return false;
    };
    if !matches!(
        tokens.as_slice(),
        [
            Token {
                kind: TokenKind::Word(filter),
                depth: 0,
                ..
            },
            Token {
                kind: TokenKind::Open,
                depth: 0,
                ..
            },
            Token {
                kind: TokenKind::Word(where_),
                depth: 1,
                ..
            },
            ..
        ] if filter == "filter" && where_ == "where"
    ) {
        return false;
    }
    let Some((close_index, close)) = tokens
        .iter()
        .enumerate()
        .skip(3)
        .find(|(_, token)| token.kind == TokenKind::Close && token.depth == 0)
    else {
        return false;
    };
    close_index > 3
        && source
            .get(close.end..)
            .is_some_and(valid_output_alias_suffix)
}

fn select_item_matches_exact_aggregate_call(
    statement_sql: &str,
    item: &Range<usize>,
    role: &Range<usize>,
    call: &CalciteAggregateCall,
) -> bool {
    select_item_matches_exact_role(statement_sql, item, role)
        || call.filter_arg.is_some_and(|filter| filter >= 0)
            && role.start == item.start
            && role.end <= item.end
            && statement_sql
                .get(role.end..item.end)
                .is_some_and(valid_filtered_aggregate_suffix)
}

fn exact_query_expression_range_matches_block(
    statement_sql: &str,
    node_id: &str,
    text: &str,
    block: &Range<usize>,
) -> bool {
    let Some(range) = exact_text_range(statement_sql, node_id, text) else {
        return false;
    };
    let Some(tokens) = lex(statement_sql) else {
        return false;
    };
    let (Ok(actual), Ok(expected)) = (
        strip_complete_parentheses(statement_sql, &tokens, range),
        strip_complete_parentheses(statement_sql, &tokens, block.clone()),
    ) else {
        return false;
    };
    actual == expected
}

fn direct_cte_expansion_kind(kind: &str) -> bool {
    matches!(
        kind,
        "DIRECT_CTE_OUTPUT_ALIAS" | "DIRECT_CTE_PASSTHROUGH" | "DIRECT_CTE_EXPLICIT_COLUMN"
    )
}

fn direct_cte_expansion_count(rex: &CalciteRex) -> usize {
    let mut count = usize::from(
        rex.source_expansion
            .as_ref()
            .is_some_and(|expansion| direct_cte_expansion_kind(&expansion.kind)),
    );
    if let Some(reference) = rex.reference_expr.as_deref() {
        count += direct_cte_expansion_count(reference);
    }
    count += rex
        .operands
        .iter()
        .map(direct_cte_expansion_count)
        .sum::<usize>();
    if let Some(window) = rex.window.as_deref() {
        count += window
            .partition_keys
            .iter()
            .map(direct_cte_expansion_count)
            .sum::<usize>();
        count += window
            .order_keys
            .iter()
            .map(|key| direct_cte_expansion_count(&key.expr))
            .sum::<usize>();
        for bound in [window.lower_bound.as_deref(), window.upper_bound.as_deref()]
            .into_iter()
            .flatten()
        {
            if let Some(offset) = bound.offset.as_deref() {
                count += direct_cte_expansion_count(offset);
            }
        }
    }
    count
}

fn rex_has_exact_field_type(rex: &CalciteRex, field: &crate::calcite::CalciteField) -> bool {
    rex.ty.as_deref() == Some(field.ty.as_str())
        && rex.nullable == field.nullable
        && rex.full_type == field.full_type
        && rex.precision == field.precision
        && rex.scale == field.scale
        && rex.charset == field.charset
        && rex.type_collation == field.type_collation
}

fn aggregate_call_has_exact_field_type(
    call: &crate::calcite::CalciteAggregateCall,
    field: &crate::calcite::CalciteField,
) -> bool {
    call.ty.as_deref() == Some(field.ty.as_str())
        && call.full_type == field.full_type
        && call.precision == field.precision
        && call.scale == field.scale
        && call.charset == field.charset
        && call.type_collation == field.type_collation
}

fn claim_unique_direct_cte_public_output(
    candidates: &[usize],
    claimed: &mut BTreeSet<usize>,
    role: &str,
) -> Result<usize> {
    let [public_index] = candidates else {
        return Err(invalid(format!(
            "direct CTE Aggregate {role} does not identify one exact public SELECT item"
        )));
    };
    if !claimed.insert(*public_index) {
        return Err(invalid(
            "direct CTE Aggregate outputs reuse one public SELECT item",
        ));
    }
    Ok(*public_index)
}

fn validate_direct_cte_shape_edge(
    cte_use: &CalciteSourceCteUse,
    block_id: &str,
    block_range: &Range<usize>,
    block_source: &str,
    statement_sql: &str,
) -> Result<()> {
    let exact = |node_id: &str, text: &str, role: &str| {
        exact_text_range(statement_sql, node_id, text).ok_or_else(|| {
            invalid(format!(
                "direct CTE Aggregate {role} is not byte-exact in its submitted statement"
            ))
        })
    };
    if cte_use.kind != "CTE_USE"
        || cte_use.definition_query_node_id != block_id
        || cte_use.definition_query_text != block_source
    {
        return Err(invalid(
            "direct CTE Aggregate edge does not name its exact definition SELECT",
        ));
    }
    let relation = exact(
        &cte_use.relation_node_id,
        &cte_use.relation_text,
        "relation",
    )?;
    let reference = exact(
        &cte_use.reference_node_id,
        &cte_use.reference_text,
        "reference",
    )?;
    let definition_name = exact(
        &cte_use.definition_name_node_id,
        &cte_use.definition_name_text,
        "definition name",
    )?;
    let definition_query = exact(
        &cte_use.definition_query_node_id,
        &cte_use.definition_query_text,
        "definition query",
    )?;
    let definition_item = exact(
        &cte_use.definition_item_node_id,
        &cte_use.definition_item_text,
        "definition item",
    )?;
    let definition_list = exact(
        &cte_use.definition_list_node_id,
        &cte_use.definition_list_text,
        "definition list",
    )?;
    let definition_body = exact(
        &cte_use.definition_body_node_id,
        &cte_use.definition_body_text,
        "WITH body",
    )?;
    let definition_with = exact(
        &cte_use.definition_with_node_id,
        &cte_use.definition_with_text,
        "complete WITH",
    )?;
    let reference_scope = exact(
        &cte_use.reference_scope_node_id,
        &cte_use.reference_scope_text,
        "reference scope",
    )?;
    let definition_identity = simple_unaliased_identifier_name(&cte_use.definition_name_text);
    let reference_identity = simple_unaliased_identifier_name(&cte_use.reference_text);
    if definition_query != *block_range
        || !range_contains(&relation, &reference)
        || !range_contains(&definition_item, &definition_name)
        || !range_contains(&definition_item, &definition_query)
        || !range_contains(&definition_list, &definition_item)
        || !range_contains(&definition_with, &definition_list)
        || !range_contains(&definition_with, &definition_body)
        || !range_contains(&reference_scope, &relation)
        || definition_query.end > relation.start
        || definition_identity.is_none()
        || definition_identity != reference_identity
    {
        return Err(invalid(
            "direct CTE Aggregate edge has inconsistent lexical nesting or identifier identity",
        ));
    }
    Ok(())
}

/// A direct CTE definition with HAVING is rooted at a logical Filter above
/// its Aggregate.  The filter changes rows, but not the Aggregate output
/// positions consumed by the outer CTE Project.  Accept only the exact
/// same-block declarative HAVING chain whose row type is preserved at every
/// edge; arbitrary planner wrappers remain ineligible.
fn exact_direct_cte_aggregate_input_carrier(
    rel: &CalciteRel,
    aggregate: &CalciteRel,
    block_id: &str,
) -> bool {
    if std::ptr::eq(rel, aggregate) {
        return true;
    }
    let [input] = rel.inputs.as_slice() else {
        return false;
    };
    rel.rel_type == "LogicalFilter"
        && rel.source_query_block_id.as_deref() == Some(block_id)
        && rel.source_clause.as_deref() == Some("HAVING")
        && rel.source_native_having.is_some()
        && same_named_calcite_row_types(&rel.row_type, &input.row_type)
        && exact_direct_cte_aggregate_input_carrier(input, aggregate, block_id)
}

fn validate_direct_cte_aggregate_select_output(
    aggregate: &CalciteRel,
    context: &AggregateOutputContext<'_>,
) -> Result<()> {
    let input = context.input;
    let group = context.group;
    let block_id = context.block.block_id;
    let statement_sql = context.block.statement.sql;
    let block_range = context.block.block_range;
    let block_source = context.block.block_source;
    let items = context.items;
    let repeated_group_items = context.repeated_group_items;
    let Some(enclosing_project) = context.block.enclosing_project else {
        return Err(invalid(
            "direct CTE Aggregate has no owning Project context",
        ));
    };
    let ([project_input], [Some(cte_use)]) = (
        enclosing_project.inputs.as_slice(),
        enclosing_project.source_input_cte_uses.as_slice(),
    ) else {
        return Err(invalid(
            "direct CTE Aggregate has no unique owning Project/input edge",
        ));
    };
    if enclosing_project.rel_type != "LogicalProject"
        || !exact_direct_cte_aggregate_input_carrier(project_input, aggregate, block_id)
        || enclosing_project.source_query_block_id.as_deref() == Some(block_id)
        || enclosing_project.project_rex.len() != enclosing_project.row_type.len()
    {
        return Err(invalid(
            "direct CTE Aggregate is not the exact sole input of its owning Project",
        ));
    }
    validate_direct_cte_shape_edge(cte_use, block_id, block_range, block_source, statement_sql)?;
    let outputs =
        super::convert::exact_direct_cte_query_shape_outputs(cte_use).ok_or_else(|| {
            invalid(
                "direct CTE Aggregate definition has no exact, unambiguous public output namespace",
            )
        })?;
    if outputs.len() != items.len()
        || outputs.iter().enumerate().any(|(index, output)| {
            span_range(statement_sql, &output.project_item_node_id) != items.get(index).cloned()
                || span_range(statement_sql, &output.definition_node_id).is_none_or(|definition| {
                    !range_contains(&items[index], &definition)
                        || statement_sql.get(definition) != Some(&output.definition_text)
                })
                || span_range(statement_sql, &output.output_alias_node_id).is_none()
        })
    {
        return Err(invalid(
            "direct CTE Aggregate public output descriptors do not exactly cover its SELECT list",
        ));
    }

    let mut output_to_public = vec![None; aggregate.row_type.len()];
    let mut claimed_public = BTreeSet::new();
    for (output_index, input_index) in group.iter().copied().enumerate() {
        let input_field = input.row_type.get(input_index).ok_or_else(|| {
            invalid("direct CTE Aggregate group index is outside its generated input")
        })?;
        let output_field = &aggregate.row_type[output_index];
        if !aggregate_group_output_matches_input(aggregate, input_index, output_field, input_field)
        {
            return Err(invalid(
                "direct CTE Aggregate group output changes its exact typed input",
            ));
        }
        let group_rex = (input.rel_type == "LogicalProject")
            .then(|| input.project_rex.get(input_index))
            .flatten()
            .ok_or_else(|| {
                invalid("direct CTE Aggregate group output has no exact input Project Rex")
            })?;
        let direct_role = group_rex
            .source_node_id
            .as_deref()
            .and_then(|id| exact_text_range(statement_sql, id, group_rex.source_text.as_deref()?));
        let repeated_role = repeated_group_items
            .and_then(|roles| roles.get(output_index))
            .filter(|role| {
                group_rex
                    .source_node_id
                    .as_deref()
                    .and_then(|id| span_range(statement_sql, id))
                    == Some((*role).clone())
                    && group_rex.source_text.as_deref() == statement_sql.get((*role).clone())
            });
        let candidates = outputs
            .iter()
            .enumerate()
            .filter(|(_, output)| {
                let definition = span_range(statement_sql, &output.definition_node_id);
                direct_role.as_ref() == definition.as_ref()
                    || repeated_role.is_some_and(|role| {
                        statement_sql.get(role.clone()).map(str::trim)
                            == Some(output.definition_text.trim())
                    })
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let public_index = claim_unique_direct_cte_public_output(
            &candidates,
            &mut claimed_public,
            &format!("group output {output_index}"),
        )?;
        output_to_public[output_index] = Some(public_index);
    }

    for (call_index, call) in aggregate.agg_call_details.iter().enumerate() {
        let output_index = group.len() + call_index;
        let output_field = &aggregate.row_type[output_index];
        if !aggregate_call_has_exact_field_type(call, output_field) {
            return Err(invalid(format!(
                "direct CTE Aggregate call output {output_index} changes its exact result type"
            )));
        }
        let role = call
            .source_node_id
            .as_deref()
            .and_then(|id| exact_text_range(statement_sql, id, call.source_text.as_deref()?))
            .ok_or_else(|| invalid("direct CTE Aggregate call has no exact source role"))?;
        let candidates = outputs
            .iter()
            .enumerate()
            .filter(|(_, output)| {
                span_range(statement_sql, &output.definition_node_id) == Some(role.clone())
                    && output.definition_text == call.source_text.as_deref().unwrap_or_default()
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let public_index = claim_unique_direct_cte_public_output(
            &candidates,
            &mut claimed_public,
            &format!("call output {output_index}"),
        )?;
        output_to_public[output_index] = Some(public_index);
    }
    if output_to_public.iter().any(Option::is_none) {
        return Err(invalid(
            "direct CTE Aggregate output/public-item permutation is incomplete",
        ));
    }

    let root_expansion_count = enclosing_project
        .project_rex
        .iter()
        .filter(|rex| {
            rex.source_expansion
                .as_ref()
                .is_some_and(|expansion| direct_cte_expansion_kind(&expansion.kind))
        })
        .count();
    let all_expansion_count = enclosing_project
        .project_rex
        .iter()
        .map(direct_cte_expansion_count)
        .sum::<usize>();
    if root_expansion_count == 0 || all_expansion_count != root_expansion_count {
        return Err(invalid(
            "direct CTE Aggregate Project has no root expansion or contains a nested/lazy expansion",
        ));
    }
    let outer_block_id = enclosing_project
        .source_query_block_id
        .as_deref()
        .ok_or_else(|| invalid("direct CTE Aggregate owning Project has no source block"))?;
    let outer_block = span_range(statement_sql, outer_block_id)
        .ok_or_else(|| invalid("direct CTE Aggregate owning Project block is malformed"))?;
    let mut realized_nonaggregate = BTreeSet::new();
    for (project_index, rex) in enclosing_project.project_rex.iter().enumerate() {
        let Some(expansion) = rex
            .source_expansion
            .as_ref()
            .filter(|expansion| direct_cte_expansion_kind(&expansion.kind))
        else {
            continue;
        };
        let public_index = expansion.public_output_index.ok_or_else(|| {
            invalid("direct CTE Aggregate root expansion has no public output ordinal")
        })?;
        let output = outputs.get(public_index).ok_or_else(|| {
            invalid("direct CTE Aggregate root expansion public ordinal is out of range")
        })?;
        let reference = exact_text_range(
            statement_sql,
            &expansion.reference_node_id,
            &expansion.reference_text,
        );
        let project_item = exact_text_range(
            statement_sql,
            &expansion.project_item_node_id,
            &expansion.project_item_text,
        );
        let definition = exact_text_range(
            statement_sql,
            &expansion.definition_node_id,
            &expansion.definition_text,
        );
        let output_alias = exact_text_range(
            statement_sql,
            &expansion.output_alias_node_id,
            &expansion.output_alias_text,
        );
        let outer_from = exact_text_range(
            statement_sql,
            &expansion.outer_from_node_id,
            &expansion.outer_from_text,
        );
        let expansion_outer = exact_text_range(
            statement_sql,
            &expansion.outer_select_node_id,
            &expansion.outer_select_text,
        );
        let reference_identity = simple_unaliased_identifier_name(&expansion.reference_text);
        if expansion.cte_use.as_ref() != Some(cte_use)
            || expansion.inner_select_node_id != block_id
            || expansion.inner_select_text != block_source
            || !exact_query_expression_range_matches_block(
                statement_sql,
                &expansion.outer_select_node_id,
                &expansion.outer_select_text,
                &outer_block,
            )
            || expansion.outer_from_node_id != cte_use.relation_node_id
            || expansion.outer_from_text != cte_use.relation_text
            || expansion.project_item_node_id != output.project_item_node_id
            || expansion.definition_node_id != output.definition_node_id
            || expansion.output_alias_node_id != output.output_alias_node_id
            || expansion.definition_text != output.definition_text
            || project_item != items.get(public_index).cloned()
            || definition != span_range(statement_sql, &output.definition_node_id)
            || output_alias != span_range(statement_sql, &output.output_alias_node_id)
            || expansion_outer.is_none()
            || reference
                .as_ref()
                .is_none_or(|range| !range_contains(&outer_block, range))
            || outer_from
                .as_ref()
                .is_none_or(|range| !range_contains(&outer_block, range))
            || reference_identity
                .as_ref()
                .map(|(name, quoted)| (name, quoted))
                != Some((&output.name, &output.quoted))
            || rex.source_node_id.as_deref() != Some(output.definition_node_id.as_str())
            || rex.source_text.as_deref() != Some(output.definition_text.as_str())
        {
            return Err(invalid(
                "direct CTE Aggregate root expansion differs from its containing edge or exact public descriptor",
            ));
        }
        let project_field = &enclosing_project.row_type[project_index];
        if !rex_has_exact_field_type(rex, project_field) {
            return Err(invalid(
                "direct CTE Aggregate root expansion changes its owning Project output type",
            ));
        }
        let direct_input_ref = rex.kind.as_deref() == Some("INPUT_REF")
            && rex.class.as_deref() == Some("RexInputRef")
            && rex.index.is_some();
        if direct_input_ref {
            let input_index = rex.index.unwrap();
            let aggregate_field = aggregate.row_type.get(input_index).ok_or_else(|| {
                invalid("direct CTE Aggregate root expansion input index is out of range")
            })?;
            if output_to_public.get(input_index).copied().flatten() != Some(public_index)
                || !rex.operands.is_empty()
                || rex.reference_expr.is_some()
                || rex.subquery_rel.is_some()
                || rex.window.is_some()
                || !rex_has_exact_field_type(rex, aggregate_field)
                || !same_calcite_set_row_types(
                    std::slice::from_ref(aggregate_field),
                    std::slice::from_ref(project_field),
                )
            {
                return Err(invalid(
                    "direct CTE Aggregate input expansion disagrees with its exact output/public permutation",
                ));
            }
        } else {
            if rex.index.is_some() || claimed_public.contains(&public_index) {
                return Err(invalid(
                    "direct CTE Aggregate non-input expansion conflicts with an Aggregate output",
                ));
            }
            realized_nonaggregate.insert(public_index);
        }
    }

    for (index, output) in outputs.iter().enumerate() {
        if !claimed_public.contains(&index)
            && !realized_nonaggregate.contains(&index)
            && !super::convert::exact_cte_definition_is_conservatively_runtime_total(
                &output.definition_text,
            )
            && !super::convert::exact_cte_omitted_output_has_declarative_reconstruction(
                enclosing_project,
                index,
            )
        {
            return Err(invalid(format!(
                "direct CTE Aggregate omits non-runtime-total public output {index} ({:?})",
                output.name
            )));
        }
    }
    Ok(())
}

fn validate_direct_aggregate_select_output(
    aggregate: &CalciteRel,
    block: SourceBlockContext<'_>,
) -> Result<()> {
    let block_id = block.block_id;
    let statement_sql = block.statement.sql;
    let block_range = block.block_range;
    let block_source = block.block_source;
    let tokens = block.tokens;
    let [input] = aggregate.inputs.as_slice() else {
        return Err(invalid(
            "direct SELECT Aggregate has no unique relational input",
        ));
    };
    let (group, _) =
        required_grouping_vectors(aggregate, input.row_type.len(), "direct SELECT Aggregate")?;
    if group.len() + aggregate.agg_call_details.len() != aggregate.row_type.len() {
        return Err(invalid(
            "direct SELECT Aggregate output is not exactly its groups followed by source-bound calls",
        ));
    }
    let local_items = direct_select_item_ranges(block_source, tokens)?;
    let items = local_items
        .into_iter()
        .map(|range| block_range.start + range.start..block_range.start + range.end)
        .collect::<Vec<_>>();
    let repeated_group_items = direct_group_item_ranges(block_source, tokens)?
        .filter(|items| items.len() == group.len())
        .map(|items| {
            items
                .into_iter()
                .map(|range| block_range.start + range.start..block_range.start + range.end)
                .collect::<Vec<_>>()
        });

    if items.len() == 1
        && statement_sql
            .get(items[0].clone())
            .is_some_and(select_item_is_wildcard)
        && aggregate.agg_call_details.is_empty()
        && group == (0..input.row_type.len()).collect::<Vec<_>>().as_slice()
        && aggregate.row_type.len() == input.row_type.len()
        && aggregate
            .row_type
            .iter()
            .zip(&input.row_type)
            .enumerate()
            .all(|(index, (output, input))| {
                aggregate_group_output_matches_input(aggregate, index, output, input)
            })
        && (statement_sql
            .get(items[0].clone())
            .is_some_and(|item| item.trim() == "*")
            || input.rel_type == "LogicalProject")
    {
        return Ok(());
    }
    let ordered_result: Result<()> = (|| {
        if items.len() != aggregate.row_type.len() {
            return Err(invalid(
                "direct SELECT item count differs from its Aggregate output arity",
            ));
        }

        for (output_index, input_index) in group.iter().copied().enumerate() {
            let input_field = input.row_type.get(input_index).ok_or_else(|| {
                invalid("direct SELECT Aggregate group index is outside its input")
            })?;
            let output_field = &aggregate.row_type[output_index];
            if !aggregate_group_output_matches_input(
                aggregate,
                input_index,
                output_field,
                input_field,
            ) {
                return Err(invalid(
                    "direct SELECT Aggregate group output changes its typed input",
                ));
            }
            let item = &items[output_index];
            let simple_matches = statement_sql
                .get(item.clone())
                .and_then(simple_identifier_select_output_name)
                .is_some_and(|(name, quoted)| {
                    if quoted {
                        name == output_field.name
                    } else {
                        name.eq_ignore_ascii_case(&output_field.name)
                    }
                });
            let project_matches = input.rel_type == "LogicalProject"
                && input.project_rex.get(input_index).is_some_and(|rex| {
                    rex.source_node_id
                        .as_deref()
                        .and_then(|id| span_range(statement_sql, id))
                        .is_some_and(|role| {
                            select_item_matches_exact_role(statement_sql, item, &role)
                        })
                });
            let repeated_group_matches = input.rel_type == "LogicalProject"
                && repeated_group_items
                    .as_ref()
                    .and_then(|items| items.get(output_index))
                    .is_some_and(|group_item| {
                        let select_source = statement_sql.get(item.clone()).map(str::trim);
                        let group_source = statement_sql.get(group_item.clone()).map(str::trim);
                        select_source == group_source
                            && input.project_rex.get(input_index).is_some_and(|rex| {
                                rex.source_node_id
                                    .as_deref()
                                    .and_then(|id| span_range(statement_sql, id))
                                    == Some(group_item.clone())
                                    && rex.source_text.as_deref() == group_source
                            })
                    });
            if !simple_matches && !project_matches && !repeated_group_matches {
                return Err(invalid(
                    "direct SELECT Aggregate group output is not its exact ordered SELECT item",
                ));
            }
        }

        for (call_index, call) in aggregate.agg_call_details.iter().enumerate() {
            let item = &items[group.len() + call_index];
            let role = call
                .source_node_id
                .as_deref()
                .and_then(|id| span_range(statement_sql, id))
                .ok_or_else(|| invalid("direct SELECT Aggregate call has no exact source span"))?;
            if !select_item_matches_exact_aggregate_call(statement_sql, item, &role, call) {
                return Err(invalid(
                    "direct SELECT Aggregate call is not its exact ordered SELECT item",
                ));
            }
        }
        Ok(())
    })();
    if ordered_result.is_ok() {
        return ordered_result;
    }
    let output_context = AggregateOutputContext {
        block,
        input,
        group,
        items: &items,
        repeated_group_items: repeated_group_items.as_deref(),
    };
    if validate_direct_derived_aggregate_select_output(aggregate, &output_context)? {
        return Ok(());
    }
    if output_context
        .block
        .enclosing_project
        .is_some_and(|project| {
            matches!(
                project.source_input_cte_uses.as_slice(),
                [Some(cte_use)] if cte_use.definition_query_node_id == block_id
            )
        })
    {
        return validate_direct_cte_aggregate_select_output(aggregate, &output_context);
    }
    ordered_result
}

/// Validate a grouped derived SELECT whose generated Aggregate contains
/// internal outputs in addition to the SELECT's public row.
///
/// PostgreSQL permits a grouping key to be used only by HAVING, while the
/// derived table exposes a smaller SELECT list.  Calcite keeps that key in the
/// Aggregate row and places a Project at the consuming outer query block to
/// select the public derived outputs.  Requiring the Aggregate arity itself to
/// equal the SELECT-item count rejects this declarative shape.  The exact
/// projected-source expansions already bind each outer reference to one
/// public inner item; close that positional boundary here while allowing only
/// unprojected Aggregate outputs to remain internal.
fn validate_direct_derived_aggregate_select_output(
    aggregate: &CalciteRel,
    context: &AggregateOutputContext<'_>,
) -> Result<bool> {
    fn exact_computed_public_output(
        rex: &CalciteRex,
        aggregate: &CalciteRel,
        project_field: &crate::calcite::CalciteField,
    ) -> bool {
        fn collect_inputs(
            rex: &CalciteRex,
            aggregate: &CalciteRel,
            inputs: &mut BTreeSet<usize>,
        ) -> bool {
            if rex.class.as_deref() == Some("RexInputRef") {
                let Some(index) = rex.index else {
                    return false;
                };
                let exact = rex.kind.as_deref() == Some("INPUT_REF")
                    && rex.operands.is_empty()
                    && rex.reference_expr.is_none()
                    && rex.subquery_rel.is_none()
                    && rex.window.is_none()
                    && aggregate
                        .row_type
                        .get(index)
                        .is_some_and(|field| rex_has_exact_field_type(rex, field));
                if exact {
                    inputs.insert(index);
                }
                return exact;
            }
            if rex.class.as_deref() == Some("RexLiteral") {
                return rex.index.is_none()
                    && rex.operands.is_empty()
                    && rex.reference_expr.is_none()
                    && rex.subquery_rel.is_none()
                    && rex.window.is_none();
            }
            rex.class.as_deref() == Some("RexCall")
                && rex.index.is_none()
                && rex.reference_expr.is_none()
                && rex.subquery_rel.is_none()
                && rex.window.is_none()
                && !rex.operands.is_empty()
                && rex
                    .operands
                    .iter()
                    .all(|operand| collect_inputs(operand, aggregate, inputs))
        }

        let mut inputs = BTreeSet::new();
        rex.class.as_deref() == Some("RexCall")
            && rex.source_expansion.is_some()
            && rex_has_exact_field_type(rex, project_field)
            && collect_inputs(rex, aggregate, &mut inputs)
            && !inputs.is_empty()
    }

    let input = context.input;
    let group = context.group;
    let block_id = context.block.block_id;
    let statement_sql = context.block.statement.sql;
    let block_source = context.block.block_source;
    let items = context.items;
    let Some(project) = context.block.enclosing_project else {
        return Ok(false);
    };
    if project.rel_type != "LogicalProject"
        || project.source_query_block_id.as_deref() == Some(block_id)
        || project.inputs.len() != 1
    {
        return Ok(false);
    }

    let mut child = &project.inputs[0];
    while matches!(child.rel_type.as_str(), "LogicalFilter" | "LogicalSort")
        && child.inputs.len() == 1
        && same_calcite_set_row_types(&child.row_type, &child.inputs[0].row_type)
    {
        child = &child.inputs[0];
    }
    if !std::ptr::eq(child, aggregate) {
        return Ok(false);
    }

    let derived_for_block = |rex: &CalciteRex| {
        rex.source_expansion.as_ref().is_some_and(|expansion| {
            matches!(
                expansion.kind.as_str(),
                "DIRECT_DERIVED_OUTPUT_ALIAS" | "DIRECT_DERIVED_PASSTHROUGH"
            ) && expansion.inner_select_node_id == block_id
        })
    };
    if !project.project_rex.iter().any(derived_for_block) {
        return Ok(false);
    }
    if project.project_rex.len() != project.row_type.len()
        || project.project_rex.len() != items.len()
        || group.len() + aggregate.agg_call_details.len() != aggregate.row_type.len()
    {
        return Err(invalid(
            "derived Aggregate public Project does not exactly cover its SELECT items",
        ));
    }

    for (output_index, input_index) in group.iter().copied().enumerate() {
        let (Some(input_field), Some(output_field)) = (
            input.row_type.get(input_index),
            aggregate.row_type.get(output_index),
        ) else {
            return Err(invalid(
                "derived Aggregate group output is outside its generated input",
            ));
        };
        if !aggregate_group_output_matches_input(aggregate, input_index, output_field, input_field)
        {
            return Err(invalid(
                "derived Aggregate group output changes its exact typed input",
            ));
        }
    }
    for (call_index, call) in aggregate.agg_call_details.iter().enumerate() {
        let output_index = group.len() + call_index;
        if aggregate
            .row_type
            .get(output_index)
            .is_none_or(|field| !aggregate_call_has_exact_field_type(call, field))
        {
            return Err(invalid(
                "derived Aggregate call output changes its exact result type",
            ));
        }
    }

    let block_range = span_range(statement_sql, block_id)
        .ok_or_else(|| invalid("derived Aggregate SELECT block has a malformed exact span"))?;
    let mut claimed_items = BTreeSet::new();
    let mut claimed_outputs = BTreeSet::new();
    for (project_index, rex) in project.project_rex.iter().enumerate() {
        let expansion = rex
            .source_expansion
            .as_ref()
            .filter(|_| derived_for_block(rex))
            .ok_or_else(|| {
                invalid("derived Aggregate public Project mixes an unrelated or unattested output")
            })?;
        if expansion.inner_select_text != block_source
            || rex.source_node_id.as_deref() != Some(expansion.definition_node_id.as_str())
            || rex.source_text.as_deref() != Some(expansion.definition_text.as_str())
        {
            return Err(invalid(
                "derived Aggregate public expansion changes its exact inner definition",
            ));
        }
        let item = exact_text_range(
            statement_sql,
            &expansion.project_item_node_id,
            &expansion.project_item_text,
        )
        .ok_or_else(|| invalid("derived Aggregate public item has no exact source role"))?;
        if !range_contains(&block_range, &item) {
            return Err(invalid(
                "derived Aggregate public item lies outside its inner SELECT",
            ));
        }
        let matching_items = items
            .iter()
            .enumerate()
            .filter(|(_, expected)| **expected == item)
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let [item_index] = matching_items.as_slice() else {
            return Err(invalid(
                "derived Aggregate expansion does not name one direct SELECT item",
            ));
        };
        if !claimed_items.insert(*item_index) {
            return Err(invalid(
                "derived Aggregate public Project duplicates a SELECT item",
            ));
        }

        let Some(project_field) = project.row_type.get(project_index) else {
            return Err(invalid(
                "derived Aggregate public Project index is outside its typed output row",
            ));
        };
        let exact_positional_output = rex.index.is_some_and(|output_index| {
            aggregate
                .row_type
                .get(output_index)
                .is_some_and(|aggregate_field| {
                    rex.kind.as_deref() == Some("INPUT_REF")
                        && rex.class.as_deref() == Some("RexInputRef")
                        && rex.operands.is_empty()
                        && rex.reference_expr.is_none()
                        && rex.subquery_rel.is_none()
                        && rex.window.is_none()
                        && rex_has_exact_field_type(rex, aggregate_field)
                        && same_calcite_set_row_types(
                            std::slice::from_ref(aggregate_field),
                            std::slice::from_ref(project_field),
                        )
                        && claimed_outputs.insert(output_index)
                })
        });
        if !exact_positional_output && !exact_computed_public_output(rex, aggregate, project_field)
        {
            return Err(invalid(
                "derived Aggregate public Project is neither one unique typed output position nor one exact source-expanded expression over typed Aggregate outputs",
            ));
        }
    }
    if claimed_items.len() != items.len() {
        return Err(invalid(
            "derived Aggregate public Project omits a direct SELECT item",
        ));
    }
    Ok(true)
}

fn validate_one_block(
    block_root: &CalciteRel,
    block_id: &str,
    unobservable_select_output: bool,
    enclosing_project: Option<&CalciteRel>,
    context: &BlockWalkContext<'_>,
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    let statement_sql = context.statement.sql;
    let tokens = context.statement.tokens;
    let terminal_order_error = context.terminal_order_error_block == Some(block_id);
    let block_range = span_range(statement_sql, block_id)
        .ok_or_else(|| invalid(format!("query block {block_id:?} has a malformed span")))?;
    // Calcite reports a nested SqlSelect's owner at the parser position of
    // the complete parenthesized query in some Rex subqueries.  Parentheses
    // are query-expression syntax, not part of the SELECT block itself: use
    // the same exact, balanced unwrapping as set-shape matching before
    // looking for direct clauses and output items.
    let block_range = strip_complete_parentheses(statement_sql, tokens, block_range)?;
    let block_source = statement_sql.get(block_range.clone()).ok_or_else(|| {
        invalid(format!(
            "query block {block_id:?} lies outside its statement"
        ))
    })?;
    let local_tokens = lex(block_source)
        .ok_or_else(|| invalid(format!("query block {block_id:?} is lexically malformed")))?;
    if validate_exact_set_query_expression_block(
        block_root,
        block_id,
        &block_range,
        context,
        claimed,
    )? {
        return Ok(());
    }
    if local_tokens.first().is_some_and(|token| {
        token.depth == 0 && matches!(&token.kind, TokenKind::Word(word) if word == "values")
    }) {
        return validate_exact_values_block(block_root, block_id, block_source, &local_tokens);
    }
    let obligations = block_obligations(&local_tokens)?;
    let mut counts = BlockCounts::default();
    collect_block_counts(
        block_root,
        block_id,
        context.relocated_having,
        context.relocated_blocks,
        &mut counts,
    );
    counts.having_filters += context.relocated_having.count_for_block(block_id);

    let select_output_context = SelectOutputContext {
        block_id,
        statement: context.statement,
        block_range: &block_range,
        block_source,
        tokens: &local_tokens,
        unobservable_select_output,
        enclosing_project,
        relocated_blocks: context.relocated_blocks,
        terminal_analysis_error: terminal_order_error,
    };
    validate_select_output_carrier(block_root, &select_output_context)?;

    if counts.where_filters != usize::from(obligations.where_clause)
        || counts.having_filters != usize::from(obligations.having_clause)
        || counts.other_filters != 0
        || counts.joins != obligations.joins
        || counts.aggregates.len() != obligations.aggregate_count
    {
        return Err(invalid(format!(
            "query block {block_id:?} roles disagree: source WHERE={}, HAVING={}, joins={}, aggregate={}; generated WHERE={}, HAVING={}, unclaimed filters={}, joins={}, aggregates={}",
            obligations.where_clause,
            obligations.having_clause,
            obligations.joins,
            obligations.aggregate_count,
            counts.where_filters,
            counts.having_filters,
            counts.other_filters,
            counts.joins,
            counts.aggregates.len()
        )));
    }

    let mut aggregate_index = 0usize;
    if obligations.distinct_aggregate {
        validate_distinct_aggregate_role(counts.aggregates[0])?;
        aggregate_index += 1;
    }
    if obligations.base_global_aggregate {
        validate_global_aggregate_role(counts.aggregates[aggregate_index])?;
    }

    validate_block_suffix_roles(
        block_root,
        block_id,
        &block_range,
        counts.sorts,
        context,
        claimed,
    )
}

fn validate_exact_set_query_expression_block(
    block_root: &CalciteRel,
    block_id: &str,
    block_range: &Range<usize>,
    context: &BlockWalkContext<'_>,
    claimed: &mut ClaimedRoles,
) -> Result<bool> {
    let statement_sql = context.statement.sql;
    let tokens = context.statement.tokens;
    let relocated_having = context.relocated_having;
    let relocated_blocks = context.relocated_blocks;
    let Ok(shape) = parse_query_shape(statement_sql, tokens, block_range.clone()) else {
        return Ok(false);
    };
    let QueryShape::Set { .. } = &shape else {
        return Ok(false);
    };

    let mut carrier = block_root;
    loop {
        let [input] = carrier.inputs.as_slice() else {
            break;
        };
        let transparent_sort = carrier.rel_type == "LogicalSort"
            && relocated_blocks.effective_block(carrier) == Some(block_id)
            && same_named_calcite_row_types(&carrier.row_type, &input.row_type);
        let transparent_project = carrier.rel_type == "LogicalProject"
            && relocated_blocks.effective_block(carrier) == Some(block_id)
            && same_named_calcite_row_types(&carrier.row_type, &input.row_type)
            && carrier.project_rex.len() == carrier.row_type.len()
            && carrier.project_rex.iter().enumerate().all(|(index, rex)| {
                rex.kind.as_deref() == Some("INPUT_REF")
                    && rex.class.as_deref() == Some("RexInputRef")
                    && rex.index == Some(index)
                    && rex.operands.is_empty()
                    && rex.reference_expr.is_none()
                    && rex.subquery_rel.is_none()
                    && rex.window.is_none()
            });
        if transparent_sort || transparent_project {
            carrier = input;
            continue;
        }
        break;
    }

    if !matches!(
        carrier.rel_type.as_str(),
        "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
    ) || !claimed.set_bindings.contains(&(
        rel_identity(carrier),
        shape.range().start,
        shape.range().end,
    )) {
        return Err(invalid(format!(
            "query block {block_id:?} is a Set expression without its exactly matched logical Set carrier"
        )));
    }
    validate_generated_set_output_layout(carrier)?;

    // All WHERE/HAVING/JOIN/Aggregate roles belong to the ordered SELECT arms,
    // which are validated as their own query blocks.  The expression-level
    // block may own only transparent row carriers and its declarative suffix.
    let mut counts = BlockCounts::default();
    collect_block_counts(
        block_root,
        block_id,
        relocated_having,
        relocated_blocks,
        &mut counts,
    );
    counts.having_filters += relocated_having.count_for_block(block_id);
    if counts.where_filters != 0
        || counts.having_filters != 0
        || counts.other_filters != 0
        || counts.joins != 0
        || !counts.aggregates.is_empty()
    {
        return Err(invalid(format!(
            "Set-expression block {block_id:?} owns SELECT-arm filter/join/aggregate roles"
        )));
    }
    validate_block_suffix_roles(
        block_root,
        block_id,
        block_range,
        counts.sorts,
        context,
        claimed,
    )?;
    Ok(true)
}

fn validate_block_suffix_roles(
    block_root: &CalciteRel,
    block_id: &str,
    block_range: &Range<usize>,
    sort_count: usize,
    context: &BlockWalkContext<'_>,
    claimed: &mut ClaimedRoles,
) -> Result<()> {
    let statement_sql = context.statement.sql;
    let tokens = context.statement.tokens;
    let erased_in_subquery_order = context.in_subquery_erased_orders.contains(block_id);
    let terminal_order_error = context.terminal_order_error_block == Some(block_id);
    // In `a UNION b ORDER BY ...`, the trailing suffix belongs to the Set
    // query expression, not to its final SELECT arm `b`.  Exact Set bindings
    // were established before block validation, so suppress only this
    // boundary-equal enclosing role; a parenthesized arm's own suffix still
    // lies strictly inside the Set range and remains mandatory.
    let enclosing_set_owns_suffix = claimed
        .set_bindings
        .iter()
        .any(|(_, start, end)| *start < block_range.start && *end == block_range.end);
    let suffix = if enclosing_set_owns_suffix {
        SuffixRoles::default()
    } else {
        suffix_after_block(statement_sql, tokens, block_range)?
    };
    let expected_sorts = usize::from(suffix.shape != SuffixShape::default());
    if sort_count != expected_sorts {
        let erased_order_only = (erased_in_subquery_order
            && suffix.shape.order
            && !suffix.shape.fetch
            && !suffix.shape.offset
            || terminal_order_error)
            && sort_count == 0;
        if !erased_order_only {
            return Err(invalid(format!(
                "query block {block_id:?} source suffix {:?} has {sort_count} generated LogicalSort roles",
                suffix.shape
            )));
        }
    }
    if sort_count == 1 {
        let sort = find_block_sort(block_root, block_id).expect("counted one block sort");
        validate_generated_sort(Some(sort), &suffix, statement_sql)?;
        claimed.sorts.insert(rel_identity(sort));
    }
    Ok(())
}

fn validate_exact_values_block(
    block_root: &CalciteRel,
    block_id: &str,
    block_source: &str,
    tokens: &[Token],
) -> Result<()> {
    let direct_values = tokens
        .iter()
        .filter(|token| token.depth == 0)
        .filter(|token| matches!(&token.kind, TokenKind::Word(word) if word == "values"))
        .count();
    let direct_select = tokens.iter().any(|token| {
        token.depth == 0 && matches!(&token.kind, TokenKind::Word(word) if word == "select")
    });
    let exact_literal_leaf = block_root.rel_type == "LogicalValues"
        && block_root.source_query_block_id.as_deref() == Some(block_id)
        && block_root.source_node_id.as_deref() == Some(block_id)
        && block_root.source_kind.as_deref() == Some("VALUES")
        && block_root.source_operator.as_deref() == Some("VALUES")
        && block_root.source_text.as_deref() == Some(block_source)
        && block_root.inputs.is_empty()
        && !block_root.row_type.is_empty()
        && block_root
            .tuples
            .as_ref()
            .is_some_and(|rows| !rows.is_empty());
    let exact_expression_expansion =
        super::convert::exact_source_values_union_parent(block_root, SetOp::Union, true);
    if direct_values != 1 || direct_select || !exact_literal_leaf && !exact_expression_expansion {
        return Err(invalid(
            "exact VALUES query block is neither one self-identical LogicalValues leaf nor its exact source-attested expression expansion",
        ));
    }
    Ok(())
}

#[derive(Default)]
struct BlockObligations {
    where_clause: bool,
    having_clause: bool,
    joins: usize,
    aggregate_count: usize,
    distinct_aggregate: bool,
    base_global_aggregate: bool,
}

fn block_obligations(tokens: &[Token]) -> Result<BlockObligations> {
    let select_index = tokens.iter().position(|token| {
        token.depth == 0 && matches!(&token.kind, TokenKind::Word(word) if word == "select")
    });
    let Some(select_index) = select_index else {
        return Err(invalid(
            "query-block span does not identify one direct SELECT",
        ));
    };
    let top_word = |word: &str| {
        tokens.iter().position(|token| {
            token.depth == 0
                && matches!(&token.kind, TokenKind::Word(candidate) if candidate == word)
        })
    };
    let from = top_word("from");
    let where_clause = top_word("where").is_some();
    let having_clause = top_word("having").is_some();
    let group = tokens.windows(2).any(|pair| {
        pair[0].depth == 0
            && pair[1].depth == 0
            && matches!(&pair[0].kind, TokenKind::Word(word) if word == "group")
            && matches!(&pair[1].kind, TokenKind::Word(word) if word == "by")
    });
    let modifier = tokens
        .get(select_index + 1)
        .and_then(|token| (token.depth == 0).then_some(&token.kind));
    let distinct = matches!(modifier, Some(TokenKind::Word(word)) if word == "distinct");
    if distinct
        && matches!(tokens.get(select_index + 2).map(|token| &token.kind), Some(TokenKind::Word(word)) if word == "on")
    {
        return Err(invalid(
            "PostgreSQL DISTINCT ON query shape is not yet represented exactly",
        ));
    }
    let has_aggregate_call = contains_source_aggregate_call(tokens);
    let base_aggregate = group || having_clause || has_aggregate_call;
    let distinct_aggregate = distinct && (!base_aggregate || group);
    let aggregate_count = usize::from(base_aggregate) + usize::from(distinct_aggregate);

    let clause_end = tokens
        .iter()
        .enumerate()
        .filter(|(_, token)| token.depth == 0)
        .filter_map(|(index, token)| match &token.kind {
            TokenKind::Word(word)
                if matches!(
                    word.as_str(),
                    "where" | "group" | "having" | "order" | "limit" | "offset" | "fetch"
                ) =>
            {
                Some(index)
            }
            _ => None,
        })
        .filter(|index| from.is_some_and(|from| *index > from))
        .min()
        .unwrap_or(tokens.len());
    let joins = from.map_or(0, |from| count_source_joins(tokens, from + 1, clause_end));
    Ok(BlockObligations {
        where_clause,
        having_clause,
        joins,
        aggregate_count,
        distinct_aggregate,
        base_global_aggregate: base_aggregate && !group,
    })
}

fn contains_source_aggregate_call(tokens: &[Token]) -> bool {
    let names = [
        "any_value",
        "array_agg",
        "avg",
        "bit_and",
        "bit_or",
        "bool_and",
        "bool_or",
        "count",
        "every",
        "grouping",
        "json_agg",
        "jsonb_agg",
        "max",
        "min",
        "single_value",
        "stddev",
        "stddev_pop",
        "stddev_samp",
        "string_agg",
        "sum",
        "variance",
        "var_pop",
        "var_samp",
    ];
    let mut nested_select_depths = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        nested_select_depths.retain(|depth| token.depth >= *depth);
        if token.depth > 0 && matches!(&token.kind, TokenKind::Word(word) if word == "select") {
            nested_select_depths.push(token.depth);
            continue;
        }
        if !nested_select_depths.is_empty() {
            continue;
        }
        if let TokenKind::Word(word) = &token.kind
            && names.contains(&word.as_str())
            && matches!(
                tokens.get(index + 1).map(|next| &next.kind),
                Some(TokenKind::Open)
            )
            && !source_aggregate_call_is_window(tokens, index)
        {
            return true;
        }
    }
    false
}

fn source_aggregate_call_is_window(tokens: &[Token], function_index: usize) -> bool {
    let Some(function) = tokens.get(function_index) else {
        return false;
    };
    let Some(open) = tokens.get(function_index + 1) else {
        return false;
    };
    let Some(close_index) = tokens
        .iter()
        .enumerate()
        .skip(function_index + 2)
        .find(|(_, token)| token.kind == TokenKind::Close && token.depth == open.depth)
        .map(|(index, _)| index)
    else {
        return false;
    };
    for token in tokens.iter().skip(close_index + 1) {
        if token.depth > function.depth {
            continue;
        }
        if token.depth < function.depth {
            return false;
        }
        match &token.kind {
            TokenKind::Word(word) if word == "over" => return true,
            TokenKind::Word(word) if word == "filter" => continue,
            TokenKind::Word(word)
                if matches!(
                    word.as_str(),
                    "from"
                        | "where"
                        | "group"
                        | "having"
                        | "order"
                        | "limit"
                        | "offset"
                        | "fetch"
                        | "as"
                ) =>
            {
                return false;
            }
            TokenKind::Comma | TokenKind::Semicolon | TokenKind::Other => return false,
            _ => {}
        }
    }
    false
}

fn count_source_joins(tokens: &[Token], start: usize, end: usize) -> usize {
    let base_depth = tokens
        .get(start)
        .map(|token| token.depth)
        .unwrap_or_default();
    let mut joins = 0usize;
    let mut nested_select_depths = Vec::new();
    for token in tokens.iter().take(end).skip(start) {
        nested_select_depths.retain(|depth| token.depth >= *depth);
        if token.depth > base_depth
            && matches!(&token.kind, TokenKind::Word(word) if word == "select")
        {
            nested_select_depths.push(token.depth);
            continue;
        }
        if !nested_select_depths.is_empty() {
            continue;
        }
        match &token.kind {
            TokenKind::Word(word) if word == "join" => joins += 1,
            TokenKind::Comma if token.depth == base_depth => joins += 1,
            _ => {}
        }
    }
    joins
}

fn collect_block_counts<'a>(
    rel: &'a CalciteRel,
    block: &str,
    relocated_having: &RelocatedHavingRoles,
    relocated_blocks: &RelocatedBlockRoles,
    counts: &mut BlockCounts<'a>,
) {
    if relocated_blocks.effective_block(rel) == Some(block) {
        match rel.rel_type.as_str() {
            "LogicalFilter" if relocated_having.contains_filter(rel) => {}
            "LogicalFilter" => match rel.source_clause.as_deref() {
                Some("WHERE") => counts.where_filters += 1,
                Some("HAVING") => counts.having_filters += 1,
                _ => counts.other_filters += 1,
            },
            "LogicalJoin" => counts.joins += 1,
            "LogicalSort" => counts.sorts += 1,
            "LogicalAggregate" => counts.aggregates.push(rel),
            _ => {}
        }
    }
    for input in &rel.inputs {
        if relocated_blocks
            .effective_block(input)
            .is_none_or(|id| id == block)
        {
            collect_block_counts(input, block, relocated_having, relocated_blocks, counts);
        }
    }
}

fn find_block_sort<'a>(rel: &'a CalciteRel, block: &str) -> Option<&'a CalciteRel> {
    if rel.rel_type == "LogicalSort" && rel.source_query_block_id.as_deref() == Some(block) {
        return Some(rel);
    }
    rel.inputs
        .iter()
        .filter(|input| {
            input
                .source_query_block_id
                .as_deref()
                .is_none_or(|id| id == block)
        })
        .find_map(|input| find_block_sort(input, block))
}

fn validate_distinct_aggregate_role(aggregate: &CalciteRel) -> Result<()> {
    let [input] = aggregate.inputs.as_slice() else {
        return Err(invalid(
            "SELECT DISTINCT Aggregate has no unique relational input",
        ));
    };
    let (group, sets) =
        required_grouping_vectors(aggregate, input.row_type.len(), "SELECT DISTINCT Aggregate")?;
    let expected = (0..aggregate.row_type.len()).collect::<Vec<_>>();
    if !aggregate.agg_call_details.is_empty() || group != expected || sets != [expected] {
        return Err(invalid(
            "SELECT DISTINCT Aggregate does not group by exactly every ordered output once",
        ));
    }
    Ok(())
}

fn validate_global_aggregate_role(aggregate: &CalciteRel) -> Result<()> {
    let [input] = aggregate.inputs.as_slice() else {
        return Err(invalid(
            "source global Aggregate has no unique relational input",
        ));
    };
    let (group, sets) =
        required_grouping_vectors(aggregate, input.row_type.len(), "source global Aggregate")?;
    if !group.is_empty() || sets != [Vec::<usize>::new()] {
        return Err(invalid(
            "source global aggregate must have groupSet=[] and exactly groupSets=[[]]",
        ));
    }
    Ok(())
}

fn required_grouping_vectors<'a>(
    aggregate: &'a CalciteRel,
    input_width: usize,
    context: &str,
) -> Result<(&'a [usize], &'a [Vec<usize>])> {
    let group = aggregate
        .group_set
        .as_deref()
        .ok_or_else(|| invalid(format!("{context} has no structured group set")))?;
    let group_sets = aggregate
        .group_sets
        .as_deref()
        .ok_or_else(|| invalid(format!("{context} has no structured grouping sets")))?;
    if !group_set_is_canonical(group) || !group_sets_are_canonical(group_sets) {
        return Err(invalid(format!(
            "{context} grouping indexes are not strictly increasing"
        )));
    }
    if group
        .iter()
        .chain(group_sets.iter().flatten())
        .any(|index| *index >= input_width)
    {
        return Err(invalid(format!(
            "{context} has a grouping index outside its input row"
        )));
    }
    Ok((group, group_sets))
}

fn suffix_after_block(source: &str, tokens: &[Token], block: &Range<usize>) -> Result<SuffixRoles> {
    let first = tokens
        .iter()
        .find(|token| token.start >= block.start && token.end <= block.end)
        .ok_or_else(|| invalid("query block has no source tokens"))?;
    let depth = first.depth;
    let boundary = tokens
        .iter()
        .filter(|token| token.start >= block.end)
        .find(|token| {
            token.depth < depth
                || token.depth == depth
                    && (matches!(token.kind, TokenKind::Semicolon)
                        || matches!(&token.kind, TokenKind::Word(word)
                            if matches!(word.as_str(), "union" | "intersect" | "except")))
        })
        .map(|token| token.start)
        .unwrap_or(source.len());
    suffix_roles(tokens, block.end..boundary)
}

fn claim_nested_set_roles(
    rel: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
    claimed: &mut ClaimedRoles,
    cte_path: &[CteEdgeKey],
) -> Result<()> {
    if matches!(
        rel.rel_type.as_str(),
        "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
    ) && !claimed.sets.contains(&rel_identity(rel))
    {
        let direct_range = exact_rel_range(rel, statement_sql).ok_or_else(|| {
            invalid("nested logical Set has no exact source query-expression range")
        })?;
        let direct_shape = parse_query_shape(statement_sql, tokens, direct_range.clone())?;
        let shape = if matches!(direct_shape, QueryShape::Set { .. }) {
            direct_shape
        } else {
            let inferred_range =
                generated_set_leaf_range(rel, statement_sql, tokens).ok_or_else(|| {
                    invalid("nested logical Set is not rooted at an exact source set operation")
                })?;
            let inferred_shape = parse_query_shape(statement_sql, tokens, inferred_range.clone())?;
            if !matches!(inferred_shape, QueryShape::Set { .. }) {
                return Err(invalid(format!(
                    "nested logical Set source {:?} has direct range {:?}, while ordered leaves delimit {:?} without an exact source set operation",
                    rel.source_node_id, direct_range, inferred_range
                )));
            }
            inferred_shape
        };
        match_query_shape(&shape, rel, statement_sql, tokens, cte_path, claimed)?;
    }
    for (index, input) in rel.inputs.iter().enumerate() {
        let input_cte_use = generated_input_cte_use(rel, index);
        let input_path = extend_cte_path(cte_path, input_cte_use);
        if let Some(use_) = input_cte_use {
            register_expected_cte_set_roles(use_, statement_sql, tokens, &input_path, claimed)?;
        }
        claim_nested_set_roles(input, statement_sql, tokens, claimed, &input_path)?;
    }
    for rex in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        claim_rex_nested_set_roles(rex, statement_sql, tokens, claimed, cte_path)?;
    }
    if let Some(rows) = &rel.tuples {
        for rex in rows.iter().flatten() {
            claim_rex_nested_set_roles(rex, statement_sql, tokens, claimed, cte_path)?;
        }
    }
    Ok(())
}

fn claim_rex_nested_set_roles(
    rex: &CalciteRex,
    statement_sql: &str,
    tokens: &[Token],
    claimed: &mut ClaimedRoles,
    cte_path: &[CteEdgeKey],
) -> Result<()> {
    if let Some(subquery) = rex.subquery_rel.as_deref() {
        claim_nested_set_roles(subquery, statement_sql, tokens, claimed, cte_path)?;
    }
    if let Some(reference) = rex.reference_expr.as_deref() {
        claim_rex_nested_set_roles(reference, statement_sql, tokens, claimed, cte_path)?;
    }
    for operand in &rex.operands {
        claim_rex_nested_set_roles(operand, statement_sql, tokens, claimed, cte_path)?;
    }
    if let Some(window) = rex.window.as_deref() {
        for key in &window.partition_keys {
            claim_rex_nested_set_roles(key, statement_sql, tokens, claimed, cte_path)?;
        }
        for key in &window.order_keys {
            claim_rex_nested_set_roles(&key.expr, statement_sql, tokens, claimed, cte_path)?;
        }
        for bound in [window.lower_bound.as_deref(), window.upper_bound.as_deref()]
            .into_iter()
            .flatten()
        {
            if let Some(offset) = bound.offset.as_deref() {
                claim_rex_nested_set_roles(offset, statement_sql, tokens, claimed, cte_path)?;
            }
        }
    }
    Ok(())
}

fn validate_no_unclaimed_semantic_nodes(
    rel: &CalciteRel,
    claimed: &ClaimedRoles,
    relocated_having: &RelocatedHavingRoles,
) -> Result<()> {
    match rel.rel_type.as_str() {
        "LogicalFilter" if relocated_having.contains_filter(rel) => {}
        "LogicalFilter"
            if rel.source_query_block_id.is_none()
                || !matches!(rel.source_clause.as_deref(), Some("WHERE" | "HAVING")) =>
        {
            return Err(invalid(
                "LogicalFilter is not claimed by one exact source WHERE/HAVING role",
            ));
        }
        "LogicalJoin" if rel.source_join.is_none() => {
            return Err(invalid(
                "LogicalJoin is not claimed by one exact source join role",
            ));
        }
        "LogicalAggregate" if rel.source_query_block_id.is_none() => {
            return Err(invalid(
                "LogicalAggregate is not claimed by one exact source SELECT block",
            ));
        }
        "LogicalSort" if !claimed.sorts.contains(&rel_identity(rel)) => {
            return Err(invalid(
                "LogicalSort is not claimed by one exact declarative suffix role",
            ));
        }
        "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
            if !claimed.sets.contains(&rel_identity(rel)) =>
        {
            return Err(invalid(
                "logical Set is not claimed by one exact source set-expression role",
            ));
        }
        _ => {}
    }
    for input in &rel.inputs {
        validate_no_unclaimed_semantic_nodes(input, claimed, relocated_having)?;
    }
    for rex in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        validate_rex_no_unclaimed(rex, claimed, relocated_having)?;
    }
    Ok(())
}

fn validate_rex_no_unclaimed(
    rex: &CalciteRex,
    claimed: &ClaimedRoles,
    relocated_having: &RelocatedHavingRoles,
) -> Result<()> {
    if let Some(subquery) = rex.subquery_rel.as_deref() {
        validate_no_unclaimed_semantic_nodes(subquery, claimed, relocated_having)?;
    }
    if let Some(reference) = rex.reference_expr.as_deref() {
        validate_rex_no_unclaimed(reference, claimed, relocated_having)?;
    }
    for operand in &rex.operands {
        validate_rex_no_unclaimed(operand, claimed, relocated_having)?;
    }
    Ok(())
}

fn collect_exact_in_subquery_order_blocks(rel: &CalciteRel, blocks: &mut BTreeSet<String>) {
    fn rex(node: &CalciteRex, blocks: &mut BTreeSet<String>) {
        if let Some(order) = node.source_in_subquery_order.as_ref() {
            blocks.insert(order.query_block_id.clone());
        }
        if let Some(reference) = node.reference_expr.as_deref() {
            rex(reference, blocks);
        }
        for operand in &node.operands {
            rex(operand, blocks);
        }
        if let Some(subquery) = node.subquery_rel.as_deref() {
            collect_exact_in_subquery_order_blocks(subquery, blocks);
        }
    }
    for node in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        rex(node, blocks);
    }
    for input in &rel.inputs {
        collect_exact_in_subquery_order_blocks(input, blocks);
    }
}

fn collect_exact_relocated_having_roles(
    rel: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
    roles: &mut RelocatedHavingRoles,
) -> Result<()> {
    fn rex(
        node: &CalciteRex,
        statement_sql: &str,
        tokens: &[Token],
        roles: &mut RelocatedHavingRoles,
    ) -> Result<()> {
        if let Some(subquery) = node.subquery_rel.as_deref() {
            collect_exact_relocated_having_roles(subquery, statement_sql, tokens, roles)?;
        }
        if let Some(reference) = node.reference_expr.as_deref() {
            rex(reference, statement_sql, tokens, roles)?;
        }
        for operand in &node.operands {
            rex(operand, statement_sql, tokens, roles)?;
        }
        Ok(())
    }

    if let Some(target) = exact_relocated_having_target(rel, statement_sql, tokens)?
        && !roles.filters.insert((rel_identity(rel), target))
    {
        return Err(invalid(
            "one generated Filter is reused by multiple relocated HAVING roles",
        ));
    }
    for input in &rel.inputs {
        collect_exact_relocated_having_roles(input, statement_sql, tokens, roles)?;
    }
    for node in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        rex(node, statement_sql, tokens, roles)?;
    }
    Ok(())
}

fn collect_exact_flattened_derived_group_roles(
    rel: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
    roles: &mut RelocatedBlockRoles,
) -> Result<()> {
    fn rex(
        node: &CalciteRex,
        statement_sql: &str,
        tokens: &[Token],
        roles: &mut RelocatedBlockRoles,
    ) -> Result<()> {
        if let Some(subquery) = node.subquery_rel.as_deref() {
            collect_exact_flattened_derived_group_roles(subquery, statement_sql, tokens, roles)?;
        }
        if let Some(reference) = node.reference_expr.as_deref() {
            rex(reference, statement_sql, tokens, roles)?;
        }
        for operand in &node.operands {
            rex(operand, statement_sql, tokens, roles)?;
        }
        Ok(())
    }

    if let Some((target, project)) =
        exact_flattened_derived_group_target(rel, statement_sql, tokens)?
    {
        for node in [rel, project] {
            if roles
                .owners
                .iter()
                .any(|(identity, prior)| *identity == rel_identity(node) && prior != &target)
                || !roles.owners.insert((rel_identity(node), target.clone()))
            {
                return Err(invalid(
                    "one generated group/project node is reused by flattened derived query blocks",
                ));
            }
        }
    }
    // A direct scalar CTE can consume a grouped CTE whose public aggregate
    // result Calcite rebuilds above the latter CTE's input carrier Project.
    // The Aggregate and that carrier belong to the grouped definition, while
    // the enclosing Project remains the exact output carrier of the scalar
    // CTE. Validate the intervening scalar block eagerly, then relocate only
    // the two generated grouping nodes to the independently recovered owner.
    if rel.rel_type == "LogicalProject"
        && let ([aggregate], [Some(cte_use)]) =
            (rel.inputs.as_slice(), rel.source_input_cte_uses.as_slice())
        && aggregate.rel_type == "LogicalAggregate"
        && let Some(target) = super::convert::exact_direct_cte_aggregate_reconstruction_owner(
            aggregate,
            statement_sql,
        )
        && aggregate.source_query_block_id.as_deref()
            == Some(cte_use.definition_query_node_id.as_str())
        && target != cte_use.definition_query_node_id
    {
        let block_range = span_range(statement_sql, &cte_use.definition_query_node_id)
            .ok_or_else(|| invalid("collapsed scalar CTE block has a malformed exact span"))?;
        let block_range = strip_complete_parentheses(statement_sql, tokens, block_range)?;
        let block_source = statement_sql
            .get(block_range.clone())
            .ok_or_else(|| invalid("collapsed scalar CTE block is outside its statement"))?;
        let local_tokens =
            lex(block_source).ok_or_else(|| invalid("collapsed scalar CTE block is malformed"))?;
        let obligations = block_obligations(&local_tokens)?;
        let has_other_clause = local_tokens.iter().any(|token| {
            token.depth == 0
                && matches!(&token.kind, TokenKind::Word(word)
                    if matches!(word.as_str(),
                        "where" | "group" | "having" | "window" | "order" | "limit"
                            | "offset" | "fetch"))
        });
        if has_other_clause
            || obligations.where_clause
            || obligations.having_clause
            || obligations.joins != 0
            || obligations.aggregate_count != 0
            || !validate_collapsed_direct_cte_select_output(
                aggregate,
                &cte_use.definition_query_node_id,
                statement_sql,
                &block_range,
                block_source,
                &local_tokens,
                Some(rel),
            )?
        {
            return Err(invalid(
                "collapsed scalar CTE above a reconstructed Aggregate is not one exact clause-free direct projection",
            ));
        }
        let [carrier] = aggregate.inputs.as_slice() else {
            unreachable!("exact CTE Aggregate reconstruction has one carrier")
        };
        for node in [aggregate, carrier] {
            if roles
                .owners
                .iter()
                .any(|(identity, prior)| *identity == rel_identity(node) && prior != &target)
                || !roles.owners.insert((rel_identity(node), target.clone()))
            {
                return Err(invalid(
                    "one generated Aggregate/carrier is reused by reconstructed CTE blocks",
                ));
            }
        }
    }
    for input in &rel.inputs {
        collect_exact_flattened_derived_group_roles(input, statement_sql, tokens, roles)?;
    }
    for node in rel
        .project_rex
        .iter()
        .chain(rel.condition_rex.iter())
        .chain(rel.fetch_rex.iter())
        .chain(rel.offset_rex.iter())
    {
        rex(node, statement_sql, tokens, roles)?;
    }
    Ok(())
}

fn exact_flattened_derived_group_target<'a>(
    aggregate: &'a CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Result<Option<(String, &'a CalciteRel)>> {
    let [project] = aggregate.inputs.as_slice() else {
        return Ok(None);
    };
    if aggregate.rel_type != "LogicalAggregate"
        || project.rel_type != "LogicalProject"
        || project.inputs.len() != 1
        || project.project_rex.is_empty()
        // A native sourceGrouping payload already closes this Aggregate's
        // declarative GROUP BY in its current query block. Derived-column
        // expansions on its input Project bind names; they do not relocate
        // the Aggregate to the nested definition block.
        || aggregate.source_grouping.as_ref().is_some_and(|grouping| {
            aggregate.source_query_block_id.as_deref() == Some(grouping.query_block_id.as_str())
        })
        || !aggregate.agg_call_details.is_empty()
        || project
            .project_rex
            .iter()
            .all(|rex| rex.source_expansion.is_none())
    {
        return Ok(None);
    }
    let outer = aggregate
        .source_query_block_id
        .as_deref()
        .ok_or_else(|| invalid("flattened derived group has no generated outer query block"))?;
    if project.source_query_block_id.as_deref() != Some(outer)
        || aggregate.row_type.len() != project.row_type.len()
        || !same_named_calcite_row_types(&aggregate.row_type, &project.row_type)
        || project.project_rex.len() != project.row_type.len()
    {
        return Err(invalid(
            "flattened derived group/project changes its ordered named row type",
        ));
    }
    let expected_group = (0..project.row_type.len()).collect::<Vec<_>>();
    let (group, group_sets) =
        required_grouping_vectors(aggregate, project.row_type.len(), "flattened derived group")?;
    if group != expected_group || group_sets != [expected_group] {
        return Err(invalid(
            "flattened derived group is not exactly one grouping of every projected field",
        ));
    }

    let first_expansion = project.project_rex[0]
        .source_expansion
        .as_ref()
        .ok_or_else(|| invalid("flattened derived group Project has a missing source expansion"))?;
    let target = first_expansion.inner_select_node_id.as_str();
    if target == outer
        || first_query_block_id(&project.inputs[0]) != Some(target)
        || exact_text_range(statement_sql, target, &first_expansion.inner_select_text).is_none()
    {
        return Err(invalid(
            "flattened derived group is not rooted in one exact inner SELECT",
        ));
    }
    let target_range = span_range(statement_sql, target)
        .ok_or_else(|| invalid("flattened derived group inner SELECT has a malformed span"))?;
    let target_range = strip_complete_parentheses(statement_sql, tokens, target_range)?;
    let source = statement_sql
        .get(target_range.clone())
        .ok_or_else(|| invalid("flattened derived group inner SELECT is out of bounds"))?;
    let local_tokens =
        lex(source).ok_or_else(|| invalid("flattened derived group inner SELECT is malformed"))?;
    let select_items = direct_select_item_ranges(source, &local_tokens)?;
    let group_items = direct_group_item_ranges(source, &local_tokens)?
        .ok_or_else(|| invalid("flattened derived group inner SELECT has no direct GROUP BY"))?;
    if select_items.len() != project.project_rex.len() || group_items.len() != select_items.len() {
        return Err(invalid(
            "flattened derived group SELECT/GROUP BY arity disagrees with its Project",
        ));
    }

    for (index, ((select_item, group_item), rex)) in select_items
        .iter()
        .zip(&group_items)
        .zip(&project.project_rex)
        .enumerate()
    {
        let select_source = source
            .get(select_item.clone())
            .ok_or_else(|| invalid("flattened derived group SELECT item is out of bounds"))?;
        let group_source = source
            .get(group_item.clone())
            .ok_or_else(|| invalid("flattened derived group item is out of bounds"))?;
        let Some((select_name, select_quoted)) = simple_unaliased_identifier_name(select_source)
        else {
            return Err(invalid(
                "flattened derived group SELECT item is not an unaliased identifier",
            ));
        };
        let Some((group_name, group_quoted)) = simple_unaliased_identifier_name(group_source)
        else {
            return Err(invalid(
                "flattened derived GROUP BY item is not an identifier",
            ));
        };
        if select_name != group_name || select_quoted != group_quoted {
            return Err(invalid(
                "flattened derived SELECT and GROUP BY item order differs",
            ));
        }
        let expansion = rex.source_expansion.as_ref().ok_or_else(|| {
            invalid("flattened derived group Project has an incomplete source expansion")
        })?;
        let global_item =
            target_range.start + select_item.start..target_range.start + select_item.end;
        let input_index = rex.index.ok_or_else(|| {
            invalid("flattened derived group Project Rex has no exact input index")
        })?;
        let input_field = project.inputs[0]
            .row_type
            .get(input_index)
            .ok_or_else(|| invalid("flattened derived group Project index is outside its input"))?;
        let output_field = &project.row_type[index];
        let outer_range = exact_text_range(statement_sql, outer, &expansion.outer_select_text);
        let outer_from_range = exact_text_range(
            statement_sql,
            &expansion.outer_from_node_id,
            &expansion.outer_from_text,
        );
        let reference_range = exact_text_range(
            statement_sql,
            &expansion.reference_node_id,
            &expansion.reference_text,
        );
        let name_matches = |field: &str| {
            if select_quoted {
                select_name == field
            } else {
                select_name.eq_ignore_ascii_case(field)
            }
        };
        if !matches!(
            expansion.kind.as_str(),
            "DIRECT_DERIVED_PASSTHROUGH" | "DIRECT_DERIVED_OUTPUT_ALIAS"
        ) || expansion.inner_select_node_id != target
            || expansion.inner_select_text != source
            || expansion.outer_select_node_id != outer
            || outer_range.is_none()
            || outer_from_range
                .as_ref()
                .is_none_or(|range| !range_contains(range, &target_range))
            || reference_range.as_ref().is_none_or(|range| {
                outer_range
                    .as_ref()
                    .is_none_or(|outer| !range_contains(outer, range))
            })
            || exact_text_range(
                statement_sql,
                &expansion.project_item_node_id,
                &expansion.project_item_text,
            ) != Some(global_item.clone())
            || exact_text_range(
                statement_sql,
                &expansion.definition_node_id,
                &expansion.definition_text,
            ) != Some(global_item.clone())
            || exact_text_range(
                statement_sql,
                &expansion.output_alias_node_id,
                &expansion.output_alias_text,
            ) != Some(global_item.clone())
            || rex
                .source_node_id
                .as_deref()
                .and_then(|id| span_range(statement_sql, id))
                != Some(global_item.clone())
            || rex.source_text.as_deref() != Some(select_source)
            || rex.kind.as_deref() != Some("INPUT_REF")
            || rex.class.as_deref() != Some("RexInputRef")
            || !rex.operands.is_empty()
            || rex.reference_expr.is_some()
            || rex.subquery_rel.is_some()
            || !name_matches(&input_field.name)
            || !name_matches(&output_field.name)
            || !same_calcite_set_row_types(
                std::slice::from_ref(output_field),
                std::slice::from_ref(input_field),
            )
        {
            return Err(invalid(
                "flattened derived group Project does not preserve one exact ordered identity item",
            ));
        }
    }
    Ok(Some((target.to_owned(), project)))
}

fn exact_text_range(statement_sql: &str, node_id: &str, text: &str) -> Option<Range<usize>> {
    let range = span_range(statement_sql, node_id)?;
    (statement_sql.get(range.clone()) == Some(text)).then_some(range)
}

fn direct_group_item_ranges(source: &str, tokens: &[Token]) -> Result<Option<Vec<Range<usize>>>> {
    let groups = tokens
        .windows(2)
        .filter(|pair| {
            pair[0].depth == 0
                && pair[1].depth == 0
                && matches!(&pair[0].kind, TokenKind::Word(word) if word == "group")
                && matches!(&pair[1].kind, TokenKind::Word(word) if word == "by")
        })
        .collect::<Vec<_>>();
    let [group] = groups.as_slice() else {
        return Ok(None);
    };
    let start = group[1].end;
    let end = tokens
        .iter()
        .filter(|token| token.depth == 0 && token.start >= start)
        .find(|token| {
            matches!(token.kind, TokenKind::Semicolon)
                || matches!(&token.kind, TokenKind::Word(word)
                    if matches!(word.as_str(), "having" | "window" | "order" | "limit" | "offset" | "fetch"))
        })
        .map(|token| token.start)
        .unwrap_or(source.len());
    let range = trim_range(source, start..end)
        .ok_or_else(|| invalid("direct GROUP BY has an empty item list"))?;
    let commas = tokens
        .iter()
        .filter(|token| {
            token.depth == 0
                && token.start >= range.start
                && token.end <= range.end
                && token.kind == TokenKind::Comma
        })
        .map(|token| token.start)
        .collect::<Vec<_>>();
    let mut items = Vec::with_capacity(commas.len() + 1);
    let mut item_start = range.start;
    for item_end in commas.into_iter().chain(std::iter::once(range.end)) {
        items.push(
            trim_range(source, item_start..item_end)
                .ok_or_else(|| invalid("direct GROUP BY contains an empty item"))?,
        );
        item_start = item_end.saturating_add(1);
    }
    Ok(Some(items))
}

fn exact_relocated_having_target(
    filter: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
) -> Result<Option<String>> {
    let [aggregate] = filter.inputs.as_slice() else {
        return Ok(None);
    };
    if filter.rel_type != "LogicalFilter"
        || filter.source_clause.is_some()
        || aggregate.rel_type != "LogicalAggregate"
    {
        return Ok(None);
    }
    let Some(grouping) = aggregate
        .source_grouping
        .as_ref()
        .filter(|grouping| grouping.source_has_having)
    else {
        return Ok(None);
    };
    let target = grouping.query_block_id.as_str();
    if aggregate.source_query_block_id.as_deref() != Some(target)
        || grouping.source_select_node_id != target
        || filter
            .source_query_block_id
            .as_deref()
            .is_none_or(|owner| owner == target)
        || filter.source_native_having.is_some()
        || filter.source_where.is_some()
        || !same_named_calcite_row_types(&filter.row_type, &aggregate.row_type)
    {
        return Err(invalid(
            "relocated HAVING Filter has inconsistent generated ownership or row type",
        ));
    }
    let target_range = span_range(statement_sql, target)
        .ok_or_else(|| invalid("relocated HAVING query block has a malformed span"))?;
    let target_range = strip_complete_parentheses(statement_sql, tokens, target_range)?;
    let owner_range = filter
        .source_query_block_id
        .as_deref()
        .and_then(|owner| span_range(statement_sql, owner))
        .ok_or_else(|| invalid("relocated HAVING Filter has no exact outer owner"))?;
    if !range_contains(&owner_range, &target_range)
        || statement_sql.get(target_range.clone()) != Some(grouping.source_select_text.as_str())
    {
        return Err(invalid(
            "relocated HAVING source query is not nested exactly in its generated owner",
        ));
    }
    let condition_range = direct_having_condition_range(statement_sql, tokens, &target_range)?;
    let condition = filter
        .condition_rex
        .as_ref()
        .ok_or_else(|| invalid("relocated HAVING Filter has no generated condition"))?;
    let generated_range = condition
        .source_node_id
        .as_deref()
        .and_then(|id| span_range(statement_sql, id))
        .ok_or_else(|| invalid("relocated HAVING condition has no exact source span"))?;
    if generated_range != condition_range
        || condition.source_text.as_deref() != statement_sql.get(condition_range)
    {
        return Err(invalid(
            "relocated HAVING condition differs from the exact direct HAVING role",
        ));
    }
    Ok(Some(target.to_owned()))
}

fn direct_having_condition_range(
    statement_sql: &str,
    tokens: &[Token],
    block: &Range<usize>,
) -> Result<Range<usize>> {
    let first = tokens
        .iter()
        .find(|token| token.start >= block.start && token.end <= block.end)
        .ok_or_else(|| invalid("relocated HAVING query block has no tokens"))?;
    let candidates = tokens
        .iter()
        .filter(|token| {
            token.start >= block.start
                && token.end <= block.end
                && token.depth == first.depth
                && matches!(&token.kind, TokenKind::Word(word) if word == "having")
        })
        .collect::<Vec<_>>();
    let [having] = candidates.as_slice() else {
        return Err(invalid(
            "relocated HAVING query block does not contain one direct HAVING role",
        ));
    };
    let end = tokens
        .iter()
        .filter(|token| {
            token.start >= having.end && token.end <= block.end && token.depth == first.depth
        })
        .find(|token| {
            matches!(&token.kind, TokenKind::Word(word)
                if matches!(word.as_str(), "order" | "limit" | "offset" | "fetch"))
        })
        .map(|token| token.start)
        .unwrap_or(block.end);
    trim_range(statement_sql, having.end..end)
        .ok_or_else(|| invalid("relocated HAVING has an empty direct condition"))
}

fn collect_outer_sorted_set_branch_orders(
    rel: &CalciteRel,
    statement_sql: &str,
    tokens: &[Token],
    blocks: &mut BTreeSet<String>,
) -> Result<()> {
    if rel.rel_type == "LogicalSort" && !rel.collation.is_empty() && rel.inputs.len() == 1 {
        if rel.inputs[0].rel_type == "LogicalProject" && rel.inputs[0].inputs.len() == 1 {
            let project = &rel.inputs[0];
            let derived = &project.inputs[0];
            if let Some(block) = first_query_block_id(derived)
                && project.source_query_block_id.as_deref() != Some(block)
                && find_block_sort(derived, block).is_none()
            {
                let range = span_range(statement_sql, block).ok_or_else(|| {
                    invalid("outer-sorted derived SELECT has a malformed query-block span")
                })?;
                let range = strip_complete_parentheses(statement_sql, tokens, range)?;
                let suffix = suffix_after_block(statement_sql, tokens, &range)?;
                if suffix.shape
                    == (SuffixShape {
                        order: true,
                        fetch: false,
                        offset: false,
                    })
                    && suffix.order_range.as_ref().is_some_and(|range| {
                        order_role_has_only_total_identifier_keys(
                            statement_sql,
                            range,
                            &derived.row_type,
                        )
                    })
                {
                    blocks.insert(block.to_owned());
                }
            }
        }
        let set = strip_projects(&rel.inputs[0]);
        if matches!(
            set.rel_type.as_str(),
            "LogicalUnion" | "LogicalIntersect" | "LogicalMinus"
        ) {
            for branch in &set.inputs {
                let Some(block) = first_query_block_id(branch) else {
                    continue;
                };
                if rel.source_query_block_id.as_deref() == Some(block)
                    || find_block_sort(branch, block).is_some()
                {
                    continue;
                }
                let range = span_range(statement_sql, block).ok_or_else(|| {
                    invalid("outer-sorted Set branch has a malformed query-block span")
                })?;
                let range = strip_complete_parentheses(statement_sql, tokens, range)?;
                let suffix = suffix_after_block(statement_sql, tokens, &range)?;
                if suffix.shape
                    == (SuffixShape {
                        order: true,
                        fetch: false,
                        offset: false,
                    })
                    && suffix.order_range.as_ref().is_some_and(|range| {
                        order_role_has_only_total_identifier_keys(
                            statement_sql,
                            range,
                            &branch.row_type,
                        )
                    })
                {
                    blocks.insert(block.to_owned());
                }
            }
        }

        // A logical join consumes relations, not an operand's presentation
        // order.  PostgreSQL consequently does not promise that ORDER BY in
        // a derived join operand survives the join.  When Calcite removes
        // that inner Sort, close only an order-only suffix whose key
        // expressions are exact total identifiers, and only below a
        // surviving outer Sort that establishes the observable result order.
        // Row-selecting inner FETCH/OFFSET remains mandatory.
        let join = strip_projects(&rel.inputs[0]);
        if join.rel_type == "LogicalJoin" && join.inputs.len() == 2 {
            for operand in &join.inputs {
                let Some(block) = first_query_block_id(operand) else {
                    continue;
                };
                if join.source_query_block_id.as_deref() == Some(block)
                    || find_block_sort(operand, block).is_some()
                {
                    continue;
                }
                let range = span_range(statement_sql, block).ok_or_else(|| {
                    invalid("outer-sorted join operand has a malformed query-block span")
                })?;
                let range = strip_complete_parentheses(statement_sql, tokens, range)?;
                let suffix = suffix_after_block(statement_sql, tokens, &range)?;
                if suffix.shape
                    == (SuffixShape {
                        order: true,
                        fetch: false,
                        offset: false,
                    })
                    && suffix.order_range.as_ref().is_some_and(|range| {
                        order_role_has_only_total_identifier_keys(
                            statement_sql,
                            range,
                            &operand.row_type,
                        )
                    })
                {
                    blocks.insert(block.to_owned());
                }
            }
        }
    }
    for input in &rel.inputs {
        collect_outer_sorted_set_branch_orders(input, statement_sql, tokens, blocks)?;
    }
    Ok(())
}

fn order_role_has_only_total_identifier_keys(
    statement_sql: &str,
    range: &Range<usize>,
    fields: &[crate::calcite::CalciteField],
) -> bool {
    let Some(source) = statement_sql.get(range.clone()) else {
        return false;
    };
    let Some(tokens) = lex(source) else {
        return false;
    };
    let Some(order) = tokens.first() else {
        return false;
    };
    let Some(by) = tokens.get(1) else {
        return false;
    };
    if order.depth != 0
        || by.depth != 0
        || !matches!(&order.kind, TokenKind::Word(word) if word == "order")
        || !matches!(&by.kind, TokenKind::Word(word) if word == "by")
    {
        return false;
    }
    let start = by.end;
    let mut item_start = start;
    let commas = tokens
        .iter()
        .filter(|token| token.depth == 0 && token.kind == TokenKind::Comma)
        .map(|token| token.start)
        .chain(std::iter::once(source.len()));
    for item_end in commas {
        let Some(item) = source.get(item_start..item_end).map(str::trim) else {
            return false;
        };
        let Some(item_tokens) = lex(item) else {
            return false;
        };
        let mut keep = item_tokens.len();
        if keep >= 2
            && matches!(&item_tokens[keep - 2].kind, TokenKind::Word(word) if word == "nulls")
            && matches!(&item_tokens[keep - 1].kind, TokenKind::Word(word) if matches!(word.as_str(), "first" | "last"))
        {
            keep -= 2;
        }
        if keep >= 1
            && matches!(&item_tokens[keep - 1].kind, TokenKind::Word(word) if matches!(word.as_str(), "asc" | "desc"))
        {
            keep -= 1;
        }
        if keep == 0 {
            return false;
        }
        let Some(expression) = item.get(..item_tokens[keep - 1].end).map(str::trim) else {
            return false;
        };
        let Some((name, quoted)) = simple_unaliased_identifier_name(expression) else {
            return false;
        };
        if !fields.iter().any(|field| {
            if quoted {
                name == field.name
            } else {
                name.eq_ignore_ascii_case(&field.name)
            }
        }) {
            return false;
        }
        item_start = item_end.saturating_add(1);
    }
    true
}

fn first_query_block_range(rel: &CalciteRel, source: &str) -> Option<Range<usize>> {
    if let Some(id) = rel.source_query_block_id.as_deref() {
        return span_range(source, id);
    }
    rel.inputs
        .iter()
        .find_map(|input| first_query_block_range(input, source))
}

fn exact_rel_range(rel: &CalciteRel, source: &str) -> Option<Range<usize>> {
    rel.source_node_id
        .as_deref()
        .and_then(|id| span_range(source, id))
}

fn range_contains(outer: &Range<usize>, inner: &Range<usize>) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

fn trim_range(source: &str, mut range: Range<usize>) -> Option<Range<usize>> {
    if range.start > range.end
        || range.end > source.len()
        || !source.is_char_boundary(range.start)
        || !source.is_char_boundary(range.end)
    {
        return None;
    }
    while range.start < range.end {
        let ch = source.get(range.start..range.end)?.chars().next()?;
        if !ch.is_whitespace() {
            break;
        }
        range.start += ch.len_utf8();
    }
    while range.start < range.end {
        let ch = source.get(range.start..range.end)?.chars().next_back()?;
        if !ch.is_whitespace() && ch != ';' {
            break;
        }
        range.end -= ch.len_utf8();
    }
    (range.start < range.end).then_some(range)
}

fn parse_span(raw: &str) -> Option<Span> {
    fn position(raw: &str) -> Option<Position> {
        let (line, column) = raw.split_once(':')?;
        Some(Position {
            line: line.parse().ok()?,
            column: column.parse().ok()?,
        })
    }
    let (start, end) = raw.split_once('-')?;
    let span = Span {
        start: position(start)?,
        end: position(end)?,
    };
    (span.start <= span.end
        && span.start.line > 0
        && span.start.column > 0
        && span.end.line > 0
        && span.end.column > 0)
        .then_some(span)
}

fn span_range(source: &str, raw: &str) -> Option<Range<usize>> {
    let span = parse_span(raw)?;
    let offset = |target: Position| {
        let mut position = Position { line: 1, column: 1 };
        for (index, ch) in source.char_indices() {
            if position == target {
                return Some(index);
            }
            if ch == '\n' {
                position.line = position.line.checked_add(1)?;
                position.column = 1;
            } else {
                position.column = position.column.checked_add(1)?;
            }
        }
        None
    };
    let start = offset(span.start)?;
    let last = offset(span.end)?;
    let end = last.checked_add(source.get(last..)?.chars().next()?.len_utf8())?;
    (start <= end).then_some(start..end)
}

fn lex(source: &str) -> Option<Vec<Token>> {
    let lexemes = source_lexer::lex(source)?;
    let depths = source_lexer::parenthesis_depths(source, &lexemes)?;
    let mut tokens = Vec::new();
    for (lexeme, depth) in lexemes.into_iter().zip(depths) {
        let text = lexeme.text(source)?;
        let kind = match lexeme.kind {
            LexemeKind::Whitespace | LexemeKind::LineComment => continue,
            LexemeKind::BlockComment
            | LexemeKind::QuotedIdentifier { .. }
            | LexemeKind::StandardString
            | LexemeKind::EscapeString
            | LexemeKind::DollarString => TokenKind::Protected,
            LexemeKind::Word => TokenKind::Word(text.to_ascii_lowercase()),
            LexemeKind::Operator | LexemeKind::Symbol => match text {
                "(" => TokenKind::Open,
                ")" => TokenKind::Close,
                "," => TokenKind::Comma,
                ";" => TokenKind::Semicolon,
                _ => TokenKind::Other,
            },
            LexemeKind::Number => TokenKind::Other,
        };
        tokens.push(Token {
            kind,
            start: lexeme.start,
            end: lexeme.end,
            depth,
        });
    }
    Some(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn rel(value: serde_json::Value) -> CalciteRel {
        serde_json::from_value(value).unwrap()
    }

    fn span(start: usize, end: usize) -> String {
        format!("1:{}-1:{}", start + 1, end)
    }

    #[test]
    fn simple_identifier_output_name_preserves_quoted_alias_boundaries() {
        assert_eq!(
            simple_identifier_select_output_name(r#""s_store_id" AS "store_id""#),
            Some(("store_id".to_owned(), true))
        );
        assert_eq!(
            simple_identifier_select_output_name(r#""schema"."column" "output""#),
            Some(("output".to_owned(), true))
        );
        assert_eq!(
            simple_identifier_select_output_name(r#""s_store_id" AS "store_id" trailing"#),
            None
        );
    }

    #[test]
    fn filtered_aggregate_suffix_requires_one_complete_filter_role() {
        assert!(valid_filtered_aggregate_suffix(" FILTER (WHERE c = 1)"));
        assert!(valid_filtered_aggregate_suffix(
            " FILTER (WHERE f(a, b) AND c = 1) AS total"
        ));
        assert!(valid_filtered_aggregate_suffix(
            r#" FILTER (WHERE c = 1) AS "Total""#
        ));
        for malformed in [
            " FILTER (c = 1)",
            " FILTER (WHERE)",
            " FILTER (WHERE c = 1",
            " FILTER WHERE c = 1",
            " FILTER (WHERE c = 1) first second",
            " FILTER (WHERE c = 1);",
        ] {
            assert!(
                !valid_filtered_aggregate_suffix(malformed),
                "accepted malformed aggregate suffix {malformed:?}"
            );
        }
    }

    fn cte_use() -> CalciteSourceCteUse {
        CalciteSourceCteUse {
            kind: "DIRECT_CTE_USE".to_owned(),
            relation_node_id: "1:1-1:1".to_owned(),
            relation_text: "x".to_owned(),
            reference_node_id: "1:1-1:1".to_owned(),
            reference_text: "x".to_owned(),
            definition_name_node_id: "1:1-1:1".to_owned(),
            definition_name_text: "x".to_owned(),
            definition_query_node_id: "1:1-1:1".to_owned(),
            definition_query_text: "x".to_owned(),
            definition_item_node_id: "1:1-1:1".to_owned(),
            definition_item_text: "x".to_owned(),
            definition_list_node_id: "1:1-1:1".to_owned(),
            definition_list_text: "x".to_owned(),
            definition_body_node_id: "1:1-1:1".to_owned(),
            definition_body_text: "x".to_owned(),
            definition_with_node_id: "1:1-1:1".to_owned(),
            definition_with_text: "x".to_owned(),
            reference_scope_kind: "WITH_BODY".to_owned(),
            reference_scope_node_id: "1:1-1:1".to_owned(),
            reference_scope_text: "x".to_owned(),
        }
    }

    fn validate_query_shape_bijection(
        root: &CalciteRel,
        statement_sql: Option<&str>,
    ) -> Result<()> {
        validate_query_shape_bijection_with_terminal_error(root, statement_sql, None)
    }

    fn direct_where() -> (String, CalciteRel) {
        let sql = "select a from t where a > 0".to_owned();
        let block = "1:1-1:27";
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": block,
            "inputs": [{
                "type": "LogicalFilter",
                "sourceQueryBlockId": block,
                "sourceClause": "WHERE",
                "inputs": [{"type": "LogicalTableScan", "sourceQueryBlockId": block}]
            }]
        }));
        (sql, tree)
    }

    fn erased_exists_target(target: &str) -> (String, CalciteRel) {
        let sql = format!("select a from t where exists (select {target} from u)");
        let exists = sql.find("exists").unwrap();
        let close = sql.rfind(')').unwrap() + 1;
        let inner = sql.rfind("select").unwrap();
        let inner_end = close - 1;
        let outer_block = span(0, sql.len());
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "inputs": [{
                "type": "LogicalFilter",
                "sourceQueryBlockId": outer_block,
                "sourceClause": "WHERE",
                "conditionRex": {
                    "kind": "EXISTS",
                    "class": "RexSubQuery",
                    "sourceNodeId": span(exists, close),
                    "sourceText": &sql[exists..close],
                    "subqueryRel": {
                        "type": "LogicalTableScan",
                        "sourceQueryBlockId": span(inner, inner_end),
                        "rowType": [{"name": "a", "type": "INTEGER"}]
                    }
                }
            }]
        }));
        (sql, tree)
    }

    #[test]
    fn exact_query_shape_rejects_deleted_and_unclaimed_where_filters() {
        let (sql, pristine) = direct_where();
        validate_query_shape_bijection(&pristine, Some(&sql)).unwrap();

        let deleted_output = pristine.inputs[0].clone();
        assert!(
            validate_query_shape_bijection(&deleted_output, Some(&sql)).is_err(),
            "a surviving WHERE role cannot stand in for the SELECT output"
        );

        let mut deleted = pristine.clone();
        let scan = deleted.inputs[0].inputs.remove(0);
        deleted.inputs[0] = scan;
        assert!(validate_query_shape_bijection(&deleted, Some(&sql)).is_err());

        let mut inserted = pristine.clone();
        inserted = rel(json!({
            "type": "LogicalFilter",
            "inputs": [inserted]
        }));
        assert!(validate_query_shape_bijection(&inserted, Some(&sql)).is_err());
    }

    #[test]
    fn shared_source_lexer_keeps_protected_keywords_out_of_query_shape() {
        let sql = "select E'not \\' ORDER BY JOIN' as x /* outer /* UNION */ WHERE */ from t";
        let tokens = lex(sql).unwrap();
        let words = tokens
            .iter()
            .filter_map(|token| match &token.kind {
                TokenKind::Word(word) => Some(word.as_str()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(words, ["select", "as", "x", "from", "t"]);
        assert_eq!(
            tokens
                .iter()
                .filter(|token| token.kind == TokenKind::Protected)
                .count(),
            2
        );
        assert!(lex("select $tag$ unterminated").is_none());
        assert!(lex("select $é$x$é$").is_none());
    }

    #[test]
    fn exact_query_shape_closes_keyless_limit_and_offset_roles() {
        let sql = "select a from t limit 2 offset 1";
        let block = "1:1-1:15";
        let pristine = rel(json!({
            "type": "LogicalSort",
            "sourceQueryBlockId": block,
            "fetchRex": {"sourceNodeId": "1:23-1:23"},
            "offsetRex": {"sourceNodeId": "1:32-1:32"},
            "inputs": [{"type": "LogicalProject", "sourceQueryBlockId": block,
                "inputs": [{"type": "LogicalTableScan", "sourceQueryBlockId": block}]}]
        }));
        validate_query_shape_bijection(&pristine, Some(sql)).unwrap();

        let mut swapped = pristine.clone();
        std::mem::swap(&mut swapped.fetch_rex, &mut swapped.offset_rex);
        assert!(validate_query_shape_bijection(&swapped, Some(sql)).is_err());
        let mut deleted = pristine;
        deleted.fetch_rex = None;
        assert!(validate_query_shape_bijection(&deleted, Some(sql)).is_err());
    }

    #[test]
    fn exact_query_shape_closes_order_and_offset_as_distinct_suffix_roles() {
        let sql = "SELECT DEPTNO, CAST(DEPTNO AS DOUBLE PRECISION) FROM DEPT ORDER BY CAST(DEPTNO AS DOUBLE PRECISION) OFFSET 1 ROWS";
        let block_end = sql.find(" ORDER BY").unwrap();
        let offset_literal = sql.rfind("1 ROWS").unwrap();
        let tree = rel(json!({
            "type": "LogicalSort",
            "sourceQueryBlockId": span(0, block_end),
            "collation": [{"fieldIndex": 1, "direction": "ASCENDING"}],
            "offsetRex": {"sourceNodeId": span(offset_literal, offset_literal + 1)},
            "inputs": [{
                "type": "LogicalProject",
                "sourceQueryBlockId": span(0, block_end)
            }]
        }));
        let tokens = lex(sql).unwrap();
        assert_eq!(
            suffix_roles(&tokens, 0..sql.len()).unwrap().shape,
            SuffixShape {
                order: true,
                fetch: false,
                offset: true,
            }
        );
        assert_eq!(
            suffix_after_block(sql, &tokens, &(0..block_end))
                .unwrap()
                .shape,
            SuffixShape {
                order: true,
                fetch: false,
                offset: true,
            }
        );
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut deleted = tree;
        deleted.offset_rex = None;
        assert!(validate_query_shape_bijection(&deleted, Some(sql)).is_err());
    }

    #[test]
    fn exact_ordered_derived_sort_stays_in_its_own_query_block() {
        let sql = "select ranked.a from (select a, b from t order by b desc nulls first offset 1 rows fetch next 2 rows only) as ranked";
        let inner_start = sql.find("select a, b from t").unwrap();
        let inner_end = inner_start + "select a, b from t".len();
        let offset = sql.find("offset 1").unwrap() + "offset ".len();
        let fetch = sql.find("fetch next 2").unwrap() + "fetch next ".len();
        let outer_block = span(0, sql.len());
        let inner_block = span(inner_start, inner_end);
        let fields = json!([
            {"name": "a", "type": "INTEGER", "nullable": true},
            {"name": "b", "type": "INTEGER", "nullable": true}
        ]);
        let pristine = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
            "inputs": [{
                "type": "LogicalSort",
                "sourceQueryBlockId": inner_block,
                "rowType": fields,
                "collation": [{
                    "fieldIndex": 1,
                    "direction": "DESCENDING",
                    "nullDirection": "FIRST"
                }],
                "offsetRex": {"sourceNodeId": span(offset, offset + 1)},
                "fetchRex": {"sourceNodeId": span(fetch, fetch + 1)},
                "inputs": [{
                    "type": "LogicalProject",
                    "sourceQueryBlockId": inner_block,
                    "rowType": fields,
                    "inputs": [{
                        "type": "LogicalTableScan",
                        "sourceQueryBlockId": inner_block,
                        "rowType": fields
                    }]
                }]
            }]
        }));

        validate_query_shape_bijection(&pristine, Some(sql)).unwrap();

        let mut missing_inner_fetch = pristine.clone();
        missing_inner_fetch.inputs[0].fetch_rex = None;
        assert!(validate_query_shape_bijection(&missing_inner_fetch, Some(sql)).is_err());

        let mut missing_outer_boundary = pristine;
        missing_outer_boundary.source_query_block_id = None;
        assert!(validate_query_shape_bijection(&missing_outer_boundary, Some(sql)).is_err());
    }

    #[test]
    fn exact_restored_in_subquery_order_allows_only_order_without_slicing() {
        let sql = "select a from t order by a";
        let core_end = sql.find(" order by").unwrap();
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": span(0, core_end)
        }));
        let tokens = lex(sql).unwrap();
        let statement = StatementContext {
            sql,
            tokens: &tokens,
        };
        let mut restored = ClaimedRoles::default();
        validate_component(
            &tree,
            statement,
            0..sql.len(),
            &[],
            &mut restored,
            ComponentOptions {
                allow_exact_erased_order: true,
                terminal_order_error_block: None,
            },
        )
        .unwrap();

        let mut unattested = ClaimedRoles::default();
        assert!(
            validate_component(
                &tree,
                statement,
                0..sql.len(),
                &[],
                &mut unattested,
                ComponentOptions {
                    allow_exact_erased_order: false,
                    terminal_order_error_block: None,
                },
            )
            .is_err()
        );

        let sliced = "select a from t order by a limit 1";
        let sliced_tokens = lex(sliced).unwrap();
        let mut sliced_claims = ClaimedRoles::default();
        assert!(
            validate_component(
                &tree,
                StatementContext {
                    sql: sliced,
                    tokens: &sliced_tokens,
                },
                0..sliced.len(),
                &[],
                &mut sliced_claims,
                ComponentOptions {
                    allow_exact_erased_order: true,
                    terminal_order_error_block: None,
                },
            )
            .is_err(),
            "restoring ORDER must not authorize erased LIMIT/FETCH semantics"
        );
    }

    #[test]
    fn exact_query_shape_closes_set_operator_quantifier_and_branch_order() {
        let sql = "select a from t union all select a from u";
        let pristine = rel(json!({
            "type": "LogicalUnion", "setOp": "UNION", "all": true,
            "inputs": [
                {"type": "LogicalProject", "sourceQueryBlockId": "1:1-1:15"},
                {"type": "LogicalProject", "sourceQueryBlockId": "1:27-1:41"}
            ]
        }));
        validate_query_shape_bijection(&pristine, Some(sql)).unwrap();

        let mut wrong_op = pristine.clone();
        wrong_op.rel_type = "LogicalIntersect".to_owned();
        wrong_op.set_op = Some("INTERSECT".to_owned());
        assert!(validate_query_shape_bijection(&wrong_op, Some(sql)).is_err());
        let mut wrong_all = pristine.clone();
        wrong_all.all = Some(false);
        assert!(validate_query_shape_bijection(&wrong_all, Some(sql)).is_err());
        let mut swapped = pristine;
        swapped.inputs.swap(0, 1);
        assert!(validate_query_shape_bijection(&swapped, Some(sql)).is_err());
    }

    #[test]
    fn exact_set_query_expression_is_a_carrier_without_becoming_a_select_block() {
        let sql = "select a from t union all select a from u order by a offset 1 rows fetch next 2 rows only";
        let core_end = sql.find(" order by").unwrap();
        let second = sql.find("select a from u").unwrap();
        let offset = sql.find("1 rows").unwrap();
        let fetch = sql.find("2 rows").unwrap();
        let block = span(0, core_end);
        let field = json!([{
            "name": "a", "type": "INTEGER", "nullable": true, "fullType": "INTEGER"
        }]);
        let tree = rel(json!({
            "type": "LogicalSort",
            "sourceQueryBlockId": block,
            "rowType": field,
            "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
            "offsetRex": {"sourceNodeId": span(offset, offset + 1)},
            "fetchRex": {"sourceNodeId": span(fetch, fetch + 1)},
            "inputs": [{
                "type": "LogicalUnion",
                "setOp": "UNION",
                "all": true,
                // Calcite may attach the complete Set query expression as a
                // query-block identity. It is not an extra SELECT role.
                "sourceQueryBlockId": block,
                "rowType": field,
                "inputs": [{
                    "type": "LogicalProject",
                    "sourceQueryBlockId": span(0, "select a from t".len()),
                    "rowType": field,
                    "inputs": [{
                        "type": "LogicalTableScan",
                        "sourceQueryBlockId": span(0, "select a from t".len()),
                        "rowType": field
                    }]
                }, {
                    "type": "LogicalProject",
                    "sourceQueryBlockId": span(second, core_end),
                    "rowType": field,
                    "inputs": [{
                        "type": "LogicalTableScan",
                        "sourceQueryBlockId": span(second, core_end),
                        "rowType": field
                    }]
                }]
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut mixed_nullability = tree.clone();
        {
            let field = &mut mixed_nullability.inputs[0].inputs[1].row_type[0];
            field.nullable = false;
            field.full_type = Some("INTEGER NOT NULL".to_owned());
        }
        {
            let field = &mut mixed_nullability.inputs[0].inputs[1].inputs[0].row_type[0];
            field.nullable = false;
            field.full_type = Some("INTEGER NOT NULL".to_owned());
        }
        validate_query_shape_bijection(&mixed_nullability, Some(sql)).unwrap();

        let mut incoherent_branch_full_type = tree.clone();
        {
            let field = &mut incoherent_branch_full_type.inputs[0].inputs[1].row_type[0];
            field.nullable = false;
            field.full_type = Some("INTEGER".to_owned());
        }
        {
            let field = &mut incoherent_branch_full_type.inputs[0].inputs[1].inputs[0].row_type[0];
            field.nullable = false;
            field.full_type = Some("INTEGER".to_owned());
        }
        assert!(
            validate_query_shape_bijection(&incoherent_branch_full_type, Some(sql)).is_err(),
            "Set branch fullType must agree with its structured nullability"
        );

        let mut wrong_resolved_nullability = mixed_nullability;
        wrong_resolved_nullability.inputs[0].row_type[0].nullable = false;
        wrong_resolved_nullability.inputs[0].row_type[0].full_type =
            Some("INTEGER NOT NULL".to_owned());
        assert!(validate_query_shape_bijection(&wrong_resolved_nullability, Some(sql)).is_err());

        let mut deleted_branch = tree.clone();
        deleted_branch.inputs[0].inputs.pop();
        assert!(validate_query_shape_bijection(&deleted_branch, Some(sql)).is_err());

        let mut deleted_arm_project = tree.clone();
        deleted_arm_project.inputs[0].inputs[0] =
            deleted_arm_project.inputs[0].inputs[0].inputs.remove(0);
        assert!(validate_query_shape_bijection(&deleted_arm_project, Some(sql)).is_err());

        let mut reordered = tree.clone();
        reordered.inputs[0].inputs.swap(0, 1);
        assert!(validate_query_shape_bijection(&reordered, Some(sql)).is_err());

        let mut wrong_op = tree.clone();
        wrong_op.inputs[0].rel_type = "LogicalIntersect".to_owned();
        wrong_op.inputs[0].set_op = Some("INTERSECT".to_owned());
        assert!(validate_query_shape_bijection(&wrong_op, Some(sql)).is_err());

        let mut wrong_all = tree.clone();
        wrong_all.inputs[0].all = Some(false);
        assert!(validate_query_shape_bijection(&wrong_all, Some(sql)).is_err());

        let mut output_name_drift = tree.clone();
        output_name_drift.inputs[0].row_type[0].name = "forged".to_owned();
        assert!(validate_query_shape_bijection(&output_name_drift, Some(sql)).is_err());

        let mut branch_type_drift = tree.clone();
        branch_type_drift.inputs[0].inputs[1].row_type[0].ty = "VARCHAR".to_owned();
        assert!(validate_query_shape_bijection(&branch_type_drift, Some(sql)).is_err());

        let mut lost_fetch = tree.clone();
        lost_fetch.fetch_rex = None;
        assert!(validate_query_shape_bijection(&lost_fetch, Some(sql)).is_err());

        let lost_whole_suffix = tree.inputs[0].clone();
        assert!(validate_query_shape_bijection(&lost_whole_suffix, Some(sql)).is_err());
    }

    #[test]
    fn exact_values_query_block_requires_one_self_identical_values_leaf() {
        let sql = "VALUES (TRUE)";
        let block = span(0, sql.len());
        let tree = rel(json!({
            "type": "LogicalValues",
            "sourceQueryBlockId": block,
            "sourceNodeId": block,
            "sourceText": sql,
            "sourceKind": "VALUES",
            "sourceOperator": "VALUES",
            "rowType": [{"name": "i", "type": "BOOLEAN", "nullable": false}],
            "tuples": [[{"kind": "LITERAL", "type": "BOOLEAN", "nullable": false}]]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut wrong_operator = tree.clone();
        wrong_operator.source_operator = Some("SELECT".to_owned());
        assert!(validate_query_shape_bijection(&wrong_operator, Some(sql)).is_err());

        let mut borrowed_span = tree.clone();
        borrowed_span.source_node_id = Some(span("VALUES ".len(), sql.len()));
        assert!(validate_query_shape_bijection(&borrowed_span, Some(sql)).is_err());

        let mut inserted_project = tree;
        inserted_project.rel_type = "LogicalProject".to_owned();
        assert!(validate_query_shape_bijection(&inserted_project, Some(sql)).is_err());
    }

    #[test]
    fn exact_query_shape_binds_set_branch_projects_to_their_relational_children() {
        let sql = "select * from t where a = 1 except select * from t where a = 2";
        let second = sql.find("select * from t where a = 2").unwrap();
        let first_end = sql[..second].trim_end().len() - "except".len();
        let first_end = sql[..first_end].trim_end().len();
        let first_block = span(0, first_end);
        let second_block = span(second, sql.len());
        let pristine = rel(json!({
            "type": "LogicalMinus", "setOp": "EXCEPT", "all": false,
            "sourceNodeId": span(0, sql.len()),
            "inputs": [{
                "type": "LogicalProject", "sourceQueryBlockId": first_block,
                "inputs": [{
                    "type": "LogicalFilter", "sourceQueryBlockId": first_block,
                    "sourceClause": "WHERE",
                    "inputs": [{"type": "LogicalTableScan",
                                "sourceQueryBlockId": first_block}]
                }]
            }, {
                "type": "LogicalProject", "sourceQueryBlockId": second_block,
                "inputs": [{
                    "type": "LogicalFilter", "sourceQueryBlockId": second_block,
                    "sourceClause": "WHERE",
                    "inputs": [{"type": "LogicalTableScan",
                                "sourceQueryBlockId": second_block}]
                }]
            }]
        }));
        validate_query_shape_bijection(&pristine, Some(sql)).unwrap();

        let mut swapped_children = pristine;
        let [left, right] = swapped_children.inputs.as_mut_slice() else {
            unreachable!()
        };
        std::mem::swap(&mut left.inputs[0], &mut right.inputs[0]);
        assert!(
            validate_query_shape_bijection(&swapped_children, Some(sql)).is_err(),
            "ordered SELECT carriers must not borrow the opposite branch subtree"
        );
    }

    #[test]
    fn exact_query_shape_closes_distinct_and_global_aggregate_group_vectors() {
        let distinct_sql = "select distinct a, b from t";
        let distinct = rel(json!({
            "type": "LogicalAggregate", "sourceQueryBlockId": "1:1-1:27",
            "rowType": [{"name": "a", "type": "INTEGER"}, {"name": "b", "type": "INTEGER"}],
            "groupSet": [0, 1], "groupSets": [[0, 1]],
            "inputs": [{"type": "LogicalProject", "sourceQueryBlockId": "1:1-1:27",
                "rowType": [{"name": "a", "type": "INTEGER"}, {"name": "b", "type": "INTEGER"}]}]
        }));
        validate_query_shape_bijection(&distinct, Some(distinct_sql)).unwrap();
        for invalid_group in [vec![0, 0], vec![1, 0], vec![0, 2]] {
            let mut malformed = distinct.clone();
            malformed.group_set = Some(invalid_group);
            assert!(validate_query_shape_bijection(&malformed, Some(distinct_sql)).is_err());
        }
        let mut malformed_set = distinct.clone();
        malformed_set.group_sets = Some(vec![vec![0, 0]]);
        assert!(validate_query_shape_bijection(&malformed_set, Some(distinct_sql)).is_err());
        let mut missing_group = distinct.clone();
        missing_group.group_set = None;
        assert!(validate_query_shape_bijection(&missing_group, Some(distinct_sql)).is_err());
        let mut missing_sets = distinct.clone();
        missing_sets.group_sets = None;
        assert!(validate_query_shape_bijection(&missing_sets, Some(distinct_sql)).is_err());
        let mut forged_distinct = distinct;
        forged_distinct.group_set = Some(vec![0]);
        assert!(validate_query_shape_bijection(&forged_distinct, Some(distinct_sql)).is_err());

        let aggregate_sql = "select count(*) from t";
        let aggregate = rel(json!({
            "type": "LogicalAggregate", "sourceQueryBlockId": "1:1-1:22",
            "rowType": [{"name": "EXPR$0", "type": "BIGINT"}],
            "groupSet": [], "groupSets": [[]],
            "aggCallDetails": [{
                "text": "COUNT()", "function": "COUNT", "kind": "COUNT",
                "filterArg": null, "sourceNodeId": "1:8-1:15",
                "sourceText": "count(*)", "sourceSql": "COUNT(*)"
            }],
            "inputs": [{"type": "LogicalTableScan", "sourceQueryBlockId": "1:1-1:22"}]
        }));
        validate_query_shape_bijection(&aggregate, Some(aggregate_sql)).unwrap();
        let mut forged_global = aggregate;
        forged_global.group_set = Some(vec![0]);
        assert!(validate_query_shape_bijection(&forged_global, Some(aggregate_sql)).is_err());

        let mut forged_global_sets = rel(json!({
            "type": "LogicalAggregate", "sourceQueryBlockId": "1:1-1:22",
            "rowType": [{"name": "EXPR$0", "type": "BIGINT"}],
            "groupSet": [], "groupSets": [[], []],
            "aggCallDetails": [{
                "text": "COUNT()", "function": "COUNT", "kind": "COUNT",
                "filterArg": null, "sourceNodeId": "1:8-1:15",
                "sourceText": "count(*)", "sourceSql": "COUNT(*)"
            }],
            "inputs": [{"type": "LogicalTableScan", "sourceQueryBlockId": "1:1-1:22"}]
        }));
        assert!(validate_query_shape_bijection(&forged_global_sets, Some(aggregate_sql)).is_err());
        forged_global_sets.group_sets = Some(vec![vec![0]]);
        assert!(validate_query_shape_bijection(&forged_global_sets, Some(aggregate_sql)).is_err());
    }

    #[test]
    fn exact_query_shape_distinguishes_window_calls_and_distinct_group_layers() {
        let window_sql = "select sum(a) over (partition by b) from t";
        let window_block = format!("1:1-1:{}", window_sql.chars().count());
        let window = rel(json!({
            "type": "LogicalProject", "sourceQueryBlockId": window_block,
            "inputs": [{"type": "LogicalTableScan", "sourceQueryBlockId": window_block}]
        }));
        validate_query_shape_bijection(&window, Some(window_sql)).unwrap();

        let distinct_group_sql = "select distinct count(*) from t group by a";
        let block = format!("1:1-1:{}", distinct_group_sql.chars().count());
        let count_start = distinct_group_sql.find("count(*)").unwrap();
        let count_end = count_start + "count(*)".len();
        let distinct_group = rel(json!({
            "type": "LogicalAggregate", "sourceQueryBlockId": block,
            "rowType": [{"name": "EXPR$0", "type": "BIGINT"}],
            "groupSet": [0], "groupSets": [[0]],
            "inputs": [{
                "type": "LogicalProject", "sourceQueryBlockId": block,
                "rowType": [{"name": "EXPR$0", "type": "BIGINT"}],
                "projectRex": [{"sourceNodeId": span(count_start, count_end)}],
                "inputs": [{
                    "type": "LogicalAggregate", "sourceQueryBlockId": block,
                    "rowType": [
                        {"name": "a", "type": "INTEGER"},
                        {"name": "EXPR$0", "type": "BIGINT"}
                    ],
                    "groupSet": [0], "groupSets": [[0]],
                    "inputs": [{"type": "LogicalTableScan", "sourceQueryBlockId": block}]
                }]
            }]
        }));
        validate_query_shape_bijection(&distinct_group, Some(distinct_group_sql)).unwrap();
        let mut deleted_distinct = distinct_group.clone();
        deleted_distinct = deleted_distinct.inputs.remove(0);
        assert!(
            validate_query_shape_bijection(&deleted_distinct, Some(distinct_group_sql)).is_err()
        );
        let mut forged_distinct = distinct_group;
        forged_distinct.group_set = Some(vec![]);
        assert!(
            validate_query_shape_bijection(&forged_distinct, Some(distinct_group_sql)).is_err()
        );
    }

    #[test]
    fn exact_query_shape_rejects_nested_unclaimed_sort_and_set_nodes() {
        let (sql, pristine) = direct_where();

        let mut inserted_sort = pristine.clone();
        let filter = &mut inserted_sort.inputs[0];
        let scan = filter.inputs.remove(0);
        filter.inputs.push(rel(json!({
            "type": "LogicalSort",
            "inputs": [scan]
        })));
        assert!(validate_query_shape_bijection(&inserted_sort, Some(&sql)).is_err());

        let mut inserted_set = pristine;
        let filter = &mut inserted_set.inputs[0];
        let scan = filter.inputs.remove(0);
        filter.inputs.push(rel(json!({
            "type": "LogicalUnion", "setOp": "UNION", "all": true,
            "inputs": [scan.clone(), scan]
        })));
        assert!(validate_query_shape_bijection(&inserted_set, Some(&sql)).is_err());
    }

    #[test]
    fn exact_query_shape_keeps_a_select_leaf_above_its_nested_set_input() {
        let sql = "select a from (select a from t union all select a from u) s";
        let first = sql.find("select a from t").unwrap();
        let second = sql.find("select a from u").unwrap();
        let second_end = second + "select a from u".len();
        let pristine = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": span(0, sql.len()),
            "inputs": [{
                "type": "LogicalUnion", "setOp": "UNION", "all": true,
                "sourceNodeId": span(first, second_end),
                "inputs": [
                    {"type": "LogicalProject",
                     "sourceQueryBlockId": span(first, first + "select a from t".len())},
                    {"type": "LogicalProject",
                     "sourceQueryBlockId": span(second, second_end)}
                ]
            }]
        }));
        validate_query_shape_bijection(&pristine, Some(sql)).unwrap();

        let promoted_nested_set = pristine.inputs[0].clone();
        assert!(validate_query_shape_bijection(&promoted_nested_set, Some(sql)).is_err());
    }

    #[test]
    fn exact_query_shape_recovers_flattened_associative_sets_inside_cte_clones() {
        let sql = "select count(*) from (select a from t union all select a from u union all select a from v) s";
        let first = sql.find("select a from t").unwrap();
        let second = sql.find("select a from u").unwrap();
        let third = sql.find("select a from v").unwrap();
        let first_end = first + "select a from t".len();
        let second_end = second + "select a from u".len();
        let third_end = third + "select a from v".len();
        let clone = rel(json!({
            "type": "LogicalUnion", "setOp": "UNION", "all": true,
            "sourceNodeId": span(0, sql.len()),
            "inputs": [{
                "type": "LogicalUnion", "setOp": "UNION", "all": true,
                "sourceNodeId": span(first, second_end),
                "inputs": [
                    {"type": "LogicalProject",
                     "sourceQueryBlockId": span(first, first_end)},
                    {"type": "LogicalProject",
                     "sourceQueryBlockId": span(second, second_end)}
                ]
            }, {
                "type": "LogicalProject",
                "sourceQueryBlockId": span(third, third_end)
            }]
        }));
        let wrapper = |clone: CalciteRel, use_: Option<CalciteSourceCteUse>| {
            let mut project = rel(json!({
                "type": "LogicalProject",
                "inputs": [{"type": "LogicalAggregate", "inputs": [clone]}]
            }));
            project.source_input_cte_uses = vec![use_];
            project
        };
        let tokens = lex(sql).unwrap();
        let mut claimed = ClaimedRoles::default();
        let first_use = cte_use();
        let mut second_use = cte_use();
        second_use.reference_node_id = "1:2-1:2".to_owned();
        let two_clones = rel(json!({
            "type": "LogicalJoin",
            "inputs": [
                serde_json::to_value(wrapper(clone.clone(), Some(first_use.clone()))).unwrap(),
                serde_json::to_value(wrapper(clone.clone(), Some(second_use))).unwrap()
            ]
        }));
        claim_nested_set_roles(&two_clones, sql, &tokens, &mut claimed, &[]).unwrap();
        assert_eq!(claimed.sets.len(), 4);

        let mut unowned = ClaimedRoles::default();
        let unrelated_duplicate = rel(json!({
            "type": "LogicalJoin",
            "inputs": [
                serde_json::to_value(wrapper(clone.clone(), Some(first_use))).unwrap(),
                serde_json::to_value(wrapper(clone, None)).unwrap()
            ]
        }));
        assert!(
            claim_nested_set_roles(&unrelated_duplicate, sql, &tokens, &mut unowned, &[]).is_err()
        );

        // One lexical CTE reference authorizes one clone of each exact source
        // Set role, not an arbitrary number of copies inside that clone.
        let binary_sql = "select a from t union all select a from u";
        let split = binary_sql.find("select a from u").unwrap();
        let mut binary_clone = rel(json!({
            "type": "LogicalUnion", "setOp": "UNION", "all": true,
            "sourceNodeId": span(0, binary_sql.len()),
            "inputs": [
                {"type": "LogicalProject",
                 "sourceQueryBlockId": span(0, "select a from t".len())},
                {"type": "LogicalProject",
                 "sourceQueryBlockId": span(split, binary_sql.len())}
            ]
        }));
        let extra_copy = binary_clone.clone();
        binary_clone.inputs[0] = extra_copy;
        let same_edge_duplicate = wrapper(binary_clone, Some(cte_use()));
        let mut duplicate_claims = ClaimedRoles::default();
        assert!(
            claim_nested_set_roles(
                &same_edge_duplicate,
                binary_sql,
                &lex(binary_sql).unwrap(),
                &mut duplicate_claims,
                &[],
            )
            .is_err()
        );
    }

    fn exact_set_cte_use(sql: &str, reference_start: usize) -> CalciteSourceCteUse {
        let mut use_ = cte_use();
        use_.reference_node_id = span(reference_start, reference_start + 1);
        use_.definition_query_node_id = span(0, sql.len());
        use_.definition_query_text = sql.to_owned();
        use_
    }

    fn binary_union_clone(sql: &str) -> CalciteRel {
        let second = sql.find("select a from u").unwrap();
        rel(json!({
            "type": "LogicalUnion", "setOp": "UNION", "all": true,
            "sourceNodeId": span(0, sql.len()),
            "inputs": [
                {"type": "LogicalProject",
                 "sourceQueryBlockId": span(0, "select a from t".len())},
                {"type": "LogicalProject",
                 "sourceQueryBlockId": span(second, sql.len())}
            ]
        }))
    }

    #[test]
    fn exact_query_shape_preserves_outer_cte_paths_through_rex_subqueries() {
        let sql = "select a from t union all select a from u";
        let clone = binary_union_clone(sql);
        let rex_holder = |clone: CalciteRel| {
            rel(json!({
                "type": "LogicalProject",
                "projectRex": [{
                    "sourceNodeId": span(0, sql.len()),
                    "subqueryRel": serde_json::to_value(clone).unwrap()
                }]
            }))
        };
        let mut two_clones = rel(json!({
            "type": "LogicalJoin",
            "inputs": [
                serde_json::to_value(rex_holder(clone.clone())).unwrap(),
                serde_json::to_value(rex_holder(clone)).unwrap()
            ]
        }));
        two_clones.source_input_cte_uses = vec![
            Some(exact_set_cte_use(sql, 0)),
            Some(exact_set_cte_use(sql, 1)),
        ];
        let tokens = lex(sql).unwrap();

        let mut component_claims = ClaimedRoles::default();
        visit_rex_subquery_components(
            &two_clones,
            StatementContext {
                sql,
                tokens: &tokens,
            },
            &[],
            &mut component_claims,
        )
        .unwrap();
        assert_eq!(component_claims.sets.len(), 2);

        let mut nested_claims = ClaimedRoles::default();
        claim_nested_set_roles(&two_clones, sql, &tokens, &mut nested_claims, &[]).unwrap();
        validate_expected_set_roles(&nested_claims).unwrap();
        assert_eq!(nested_claims.sets.len(), 2);
        assert_eq!(nested_claims.expected_set_sources.len(), 2);
    }

    #[test]
    fn exact_query_shape_requires_every_cte_clone_to_realize_its_set_roles() {
        let sql = "select a from t union all select a from u";
        let intact = binary_union_clone(sql);
        let damaged = intact.inputs[0].clone();
        let mut two_clones = rel(json!({
            "type": "LogicalJoin",
            "inputs": [
                serde_json::to_value(intact).unwrap(),
                serde_json::to_value(damaged).unwrap()
            ]
        }));
        two_clones.source_input_cte_uses = vec![
            Some(exact_set_cte_use(sql, 0)),
            Some(exact_set_cte_use(sql, 1)),
        ];
        let tokens = lex(sql).unwrap();
        let mut claimed = ClaimedRoles::default();
        claim_nested_set_roles(&two_clones, sql, &tokens, &mut claimed, &[]).unwrap();
        assert!(
            validate_expected_set_roles(&claimed).is_err(),
            "an intact CTE clone must not mask a missing Set in another reference path"
        );
    }

    #[test]
    fn exact_query_shape_recovers_parenthesized_set_branches_with_suffixes() {
        let sql = "select * from ((select a from t order by a limit 1) union all (select a from u order by a limit 1)) s";
        let first = sql.find("select a from t").unwrap();
        let first_end = first + "select a from t".len();
        let second = sql.find("select a from u").unwrap();
        let second_end = second + "select a from u".len();
        let second_close = sql[second..].find(')').unwrap() + second;
        let misleading_start = sql[..second].rfind('1').unwrap();
        let union = rel(json!({
            "type": "LogicalUnion",
            "setOp": "UNION",
            "all": true,
            // Calcite can attach only the tail of the first ordered branch
            // through the end of the second branch to the Set node.
            "sourceNodeId": span(misleading_start, second_close),
            "inputs": [{
                "type": "LogicalSort",
                "sourceQueryBlockId": span(first, first_end),
                "inputs": [{
                    "type": "LogicalProject",
                    "sourceQueryBlockId": span(first, first_end)
                }]
            }, {
                "type": "LogicalSort",
                "sourceQueryBlockId": span(second, second_end),
                "inputs": [{
                    "type": "LogicalProject",
                    "sourceQueryBlockId": span(second, second_end)
                }]
            }]
        }));
        let tokens = lex(sql).unwrap();
        let mut claimed = ClaimedRoles::default();
        claim_nested_set_roles(&union, sql, &tokens, &mut claimed, &[]).unwrap();
        assert!(claimed.sets.contains(&rel_identity(&union)));

        let mut swapped = union;
        swapped.inputs.swap(0, 1);
        let mut invalid_claims = ClaimedRoles::default();
        assert!(
            claim_nested_set_roles(&swapped, sql, &tokens, &mut invalid_claims, &[]).is_err(),
            "source range recovery must retain exact branch order"
        );
    }

    #[test]
    fn exact_outer_sort_may_erase_only_total_set_branch_orders() {
        let sql = "select * from ((select a from t order by a) union all (select a from u order by a)) s order by a";
        let first = sql.find("select a from t").unwrap();
        let first_end = first + "select a from t".len();
        let second = sql.find("select a from u").unwrap();
        let second_end = second + "select a from u".len();
        let set_start = sql.find("(select").unwrap();
        let set_end = sql.find(") s").unwrap();
        let outer_order = sql.rfind(" order by a").unwrap();
        let field = json!([{"name": "a", "type": "INTEGER"}]);
        let tree = rel(json!({
            "type": "LogicalSort",
            "sourceQueryBlockId": span(0, outer_order),
            "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
            "rowType": field,
            "inputs": [{
                "type": "LogicalProject",
                "sourceQueryBlockId": span(0, outer_order),
                "rowType": field,
                "inputs": [{
                    "type": "LogicalUnion",
                    "setOp": "UNION",
                    "all": true,
                    "sourceNodeId": span(set_start, set_end),
                    "rowType": field,
                    "inputs": [{
                        "type": "LogicalProject",
                        "sourceQueryBlockId": span(first, first_end),
                        "rowType": field
                    }, {
                        "type": "LogicalProject",
                        "sourceQueryBlockId": span(second, second_end),
                        "rowType": field
                    }]
                }]
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let deleted_outer_sort = tree.inputs[0].clone();
        assert!(validate_query_shape_bijection(&deleted_outer_sort, Some(sql)).is_err());

        let dangerous = "order by 1 / 0";
        assert!(!order_role_has_only_total_identifier_keys(
            dangerous,
            &(0..dangerous.len()),
            &tree.row_type,
        ));
    }

    #[test]
    fn exact_outer_sort_may_erase_only_order_only_join_operand_order() {
        let sql = "select * from (select a from t order by a) x join u on x.a = u.a order by x.a";
        let inner = sql.find("select a from t").unwrap();
        let inner_end = inner + "select a from t".len();
        let outer_order = sql.rfind(" order by x.a").unwrap();
        let inner_block = span(inner, inner_end);
        let outer_block = span(0, outer_order);
        let field = json!([{"name": "a", "type": "INTEGER"}]);
        let tree = rel(json!({
            "type": "LogicalSort",
            "sourceQueryBlockId": outer_block,
            "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
            "rowType": field,
            "inputs": [{
                "type": "LogicalProject",
                "sourceQueryBlockId": outer_block,
                "rowType": field,
                "inputs": [{
                    "type": "LogicalJoin",
                    "sourceQueryBlockId": outer_block,
                    "joinType": "INNER",
                    "sourceJoin": {
                        "kind": "DIRECT_JOIN", "queryBlockId": outer_block,
                        "joinNodeId": span(sql.find("join").unwrap(), sql.find("join").unwrap() + 4),
                        "joinText": "join",
                        "leftNodeId": span(sql.find('(').unwrap(), sql.find(") x").unwrap() + 3),
                        "leftText": &sql[sql.find('(').unwrap()..sql.find(") x").unwrap() + 3],
                        "rightNodeId": span(sql.find("join u").unwrap() + 5, sql.find("join u").unwrap() + 6),
                        "rightText": "u",
                        "conditionType": "ON",
                        "conditionNodeId": span(sql.find("x.a = u.a").unwrap(), sql.find("x.a = u.a").unwrap() + "x.a = u.a".len()),
                        "conditionText": "x.a = u.a"
                    },
                    "rowType": [
                        {"name": "a", "type": "INTEGER"},
                        {"name": "a0", "type": "INTEGER"}
                    ],
                    "inputs": [{
                        "type": "LogicalProject",
                        "sourceQueryBlockId": inner_block,
                        "rowType": field,
                        "inputs": [{
                            "type": "LogicalTableScan",
                            "sourceQueryBlockId": inner_block,
                            "rowType": field
                        }]
                    }, {
                        "type": "LogicalTableScan",
                        "sourceQueryBlockId": outer_block,
                        "rowType": field
                    }]
                }]
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut erased = BTreeSet::new();
        collect_outer_sorted_set_branch_orders(&tree, sql, &lex(sql).unwrap(), &mut erased)
            .unwrap();
        assert_eq!(erased, BTreeSet::from([inner_block.clone()]));

        let without_outer_sort = tree.inputs[0].clone();
        assert!(validate_query_shape_bijection(&without_outer_sort, Some(sql)).is_err());
        let mut unowned = BTreeSet::new();
        collect_outer_sorted_set_branch_orders(
            &without_outer_sort,
            sql,
            &lex(sql).unwrap(),
            &mut unowned,
        )
        .unwrap();
        assert!(!unowned.contains(&inner_block));

        let sliced_sql = sql.replacen(") x", " fetch first 1 row only) x", 1);
        let mut sliced = BTreeSet::new();
        collect_outer_sorted_set_branch_orders(
            &tree,
            &sliced_sql,
            &lex(&sliced_sql).unwrap(),
            &mut sliced,
        )
        .unwrap();
        assert!(
            !sliced.contains(&inner_block),
            "row-selecting inner FETCH must retain a real LogicalSort"
        );
    }

    #[test]
    fn exact_query_shape_finds_parenthesized_rex_subquery_blocks() {
        let sql = "select a from t where exists (select b from u)";
        let open = sql.find('(').unwrap();
        let close = sql.rfind(')').unwrap() + 1;
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": span(0, sql.len()),
            "inputs": [{
                "type": "LogicalFilter",
                "sourceQueryBlockId": span(0, sql.len()),
                "sourceClause": "WHERE",
                "conditionRex": {
                    "sourceNodeId": span(open, close),
                    "subqueryRel": {
                        "type": "LogicalProject",
                        // Calcite's query-block owner includes the complete
                        // parenthesized subquery, while the independently
                        // scanned SELECT starts one byte later.
                        "sourceQueryBlockId": span(open, close)
                    }
                }
            }]
        }));
        let tokens = lex(sql).unwrap();
        validate_independent_query_block_presence(&tree, sql, &tokens).unwrap();
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut deleted = tree;
        deleted.inputs[0].condition_rex = None;
        assert!(validate_independent_query_block_presence(&deleted, sql, &tokens).is_err());
    }

    #[test]
    fn exact_query_shape_extracts_rex_set_from_its_predicate_role() {
        let sql = "select * from t where t.a in (select u.a from u union all select 1)";
        let predicate = sql.find("t.a in").unwrap();
        let first = sql.find("select u.a from u").unwrap();
        let first_end = first + "select u.a from u".len();
        let second = sql.find("select 1").unwrap();
        let second_end = second + "select 1".len();
        let outer_block = span(0, sql.len());
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "inputs": [{
                "type": "LogicalFilter",
                "sourceQueryBlockId": outer_block,
                "sourceClause": "WHERE",
                "conditionRex": {
                    // Calcite's RexSubQuery role includes the left operand
                    // and IN token, and ends before the closing parenthesis.
                    "sourceNodeId": span(predicate, second_end),
                    "subqueryRel": {
                        "type": "LogicalUnion",
                        "setOp": "UNION",
                        "all": true,
                        "sourceNodeId": span(first_end, second_end),
                        "inputs": [{
                            "type": "LogicalProject",
                            "sourceQueryBlockId": span(first, first_end)
                        }, {
                            "type": "LogicalProject",
                            "sourceQueryBlockId": span(second, second_end),
                            "inputs": [{"type": "LogicalValues"}]
                        }]
                    }
                }
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut truncated = tree.clone();
        truncated.inputs[0]
            .condition_rex
            .as_mut()
            .unwrap()
            .source_node_id = Some(span(predicate, first + 3));
        assert!(validate_query_shape_bijection(&truncated, Some(sql)).is_err());

        let mut swapped = tree;
        swapped.inputs[0]
            .condition_rex
            .as_mut()
            .unwrap()
            .subquery_rel
            .as_mut()
            .unwrap()
            .inputs
            .swap(0, 1);
        assert!(validate_query_shape_bijection(&swapped, Some(sql)).is_err());
    }

    #[test]
    fn exact_exists_may_erase_only_its_root_select_output() {
        let sql = "select a from t where exists (select 1 from u where u.a = t.a)";
        let exists = sql.find("exists").unwrap();
        let close = sql.rfind(')').unwrap() + 1;
        let inner = sql.find("select 1").unwrap();
        let inner_end = close - 1;
        let outer_block = span(0, sql.len());
        let exists_text = &sql[exists..close];
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "inputs": [{
                "type": "LogicalFilter",
                "sourceQueryBlockId": outer_block,
                "sourceClause": "WHERE",
                "conditionRex": {
                    "kind": "EXISTS",
                    "class": "RexSubQuery",
                    "sourceNodeId": span(exists, close),
                    "sourceText": exists_text,
                    "subqueryRel": {
                        // PostgreSQL EXISTS observes row existence, not this
                        // root SELECT list; Calcite therefore removes SELECT 1.
                        "type": "LogicalFilter",
                        "sourceQueryBlockId": span(inner, inner_end),
                        "sourceClause": "WHERE",
                        "rowType": [{"name": "a", "type": "INTEGER"}],
                        "inputs": [{
                            "type": "LogicalTableScan",
                            "sourceQueryBlockId": span(inner, inner_end),
                            "rowType": [{"name": "a", "type": "INTEGER"}]
                        }]
                    }
                }
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut wrong_kind = tree.clone();
        wrong_kind.inputs[0].condition_rex.as_mut().unwrap().kind = Some("IN".to_owned());
        assert!(validate_query_shape_bijection(&wrong_kind, Some(sql)).is_err());

        let mut forged_text = tree;
        forged_text.inputs[0]
            .condition_rex
            .as_mut()
            .unwrap()
            .source_text = Some("exists (select 0)".to_owned());
        assert!(validate_query_shape_bijection(&forged_text, Some(sql)).is_err());
    }

    #[test]
    fn exact_exists_rejects_error_capable_erased_targets() {
        let (safe_sql, safe) = erased_exists_target("1");
        validate_query_shape_bijection(&safe, Some(&safe_sql)).unwrap();

        for target in [
            "1 / 0",
            "cast('not-an-integer' as integer)",
            "sum(a) over (order by a rows between 1 preceding and current row)",
            "'string allocation is not source-only total'",
            "1.5",
            "2147483648",
            "-2147483649",
        ] {
            let (sql, tree) = erased_exists_target(target);
            let subquery = tree.inputs[0]
                .condition_rex
                .as_ref()
                .unwrap()
                .subquery_rel
                .as_deref()
                .unwrap();
            assert!(
                !exists_root_select_targets_are_runtime_total(subquery, &sql, &lex(&sql).unwrap(),)
                    .unwrap(),
                "target {target:?} must not be certified runtime-total"
            );
            assert!(
                validate_query_shape_bijection(&tree, Some(&sql)).is_err(),
                "target {target:?} must require a real SELECT-output carrier"
            );
        }
    }

    #[test]
    fn exact_outer_wildcard_may_share_a_closed_derived_identity_select() {
        let sql = "select * from (select a, b from t where a > 0) s";
        let inner = sql.find("select a").unwrap();
        let inner_end = sql.rfind(')').unwrap();
        let outer_block = span(0, sql.len());
        let inner_block = span(inner, inner_end);
        let fields = json!([
            {"name": "a", "type": "INTEGER"},
            {"name": "b", "type": "INTEGER"}
        ]);
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "rowType": fields,
            "inputs": [{
                "type": "LogicalFilter",
                "sourceQueryBlockId": inner_block,
                "sourceClause": "WHERE",
                "rowType": fields,
                "inputs": [{
                    "type": "LogicalTableScan",
                    "sourceQueryBlockId": inner_block,
                    "rowType": fields
                }]
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut reordered_input = tree;
        reordered_input.inputs[0].inputs[0].row_type.swap(0, 1);
        assert!(
            validate_query_shape_bijection(&reordered_input, Some(sql)).is_err(),
            "an outer wildcard must not authorize a reordered collapsed SELECT"
        );
    }

    #[test]
    fn collapsed_derived_select_requires_one_exact_expansion_per_inner_output() {
        let sql = "select b as x, a as y from (select a, b from t) s";
        let inner = sql.rfind("select").unwrap();
        let inner_end = sql.find(") s").unwrap();
        let inner_a = inner + "select ".len();
        let inner_b = sql.find(", b from").unwrap() + 2;
        let outer_b = sql.find("b as x").unwrap();
        let outer_a = sql.find("a as y").unwrap();
        let inner_block = span(inner, inner_end);
        let outer_block = span(0, sql.len());
        let inner_text = &sql[inner..inner_end];
        let outer_from_text = &sql[inner..];
        let fields = json!([
            {"name": "a", "type": "INTEGER", "nullable": true},
            {"name": "b", "type": "INTEGER", "nullable": true}
        ]);
        let scan = rel(json!({
            "type": "LogicalTableScan",
            "sourceQueryBlockId": inner_block,
            "rowType": fields
        }));
        let block_root = rel(json!({
            "type": "LogicalFilter",
            "sourceQueryBlockId": inner_block,
            "sourceClause": "WHERE",
            "rowType": fields,
            "inputs": [serde_json::to_value(scan).unwrap()]
        }));
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "rowType": [
                {"name": "x", "type": "INTEGER", "nullable": true},
                {"name": "y", "type": "INTEGER", "nullable": true}
            ],
            "projectRex": [
                {
                    "kind": "INPUT_REF", "class": "RexInputRef", "index": 1,
                    "type": "INTEGER", "nullable": true,
                    "sourceNodeId": span(inner_b, inner_b + 1), "sourceText": "b",
                    "sourceExpansion": {
                        "kind": "DIRECT_DERIVED_PASSTHROUGH",
                        "referenceNodeId": span(outer_b, outer_b + 1),
                        "referenceText": "b",
                        "definitionNodeId": span(inner_b, inner_b + 1),
                        "definitionText": "b",
                        "projectItemNodeId": span(inner_b, inner_b + 1),
                        "projectItemText": "b",
                        "outputAliasNodeId": span(inner_b, inner_b + 1),
                        "outputAliasText": "b",
                        "innerSelectNodeId": inner_block,
                        "innerSelectText": inner_text,
                        "outerFromNodeId": span(inner, sql.len()),
                        "outerFromText": outer_from_text,
                        "outerSelectNodeId": outer_block,
                        "outerSelectText": sql
                    }
                },
                {
                    "kind": "INPUT_REF", "class": "RexInputRef", "index": 0,
                    "type": "INTEGER", "nullable": true,
                    "sourceNodeId": span(inner_a, inner_a + 1), "sourceText": "a",
                    "sourceExpansion": {
                        "kind": "DIRECT_DERIVED_PASSTHROUGH",
                        "referenceNodeId": span(outer_a, outer_a + 1),
                        "referenceText": "a",
                        "definitionNodeId": span(inner_a, inner_a + 1),
                        "definitionText": "a",
                        "projectItemNodeId": span(inner_a, inner_a + 1),
                        "projectItemText": "a",
                        "outputAliasNodeId": span(inner_a, inner_a + 1),
                        "outputAliasText": "a",
                        "innerSelectNodeId": inner_block,
                        "innerSelectText": inner_text,
                        "outerFromNodeId": span(inner, sql.len()),
                        "outerFromText": outer_from_text,
                        "outerSelectNodeId": outer_block,
                        "outerSelectText": sql
                    }
                }
            ],
            "inputs": [serde_json::to_value(block_root).unwrap()]
        }));
        let statement_tokens = lex(sql).unwrap();
        let inner_tokens = lex(inner_text).unwrap();
        let inner_range = inner..inner_end;
        let check = |tree: &CalciteRel| {
            let block_root = &tree.inputs[0];
            let carrier = &block_root.inputs[0];
            validate_collapsed_derived_identity_select(
                block_root,
                carrier,
                SourceBlockContext {
                    block_id: &inner_block,
                    statement: StatementContext {
                        sql,
                        tokens: &statement_tokens,
                    },
                    block_range: &inner_range,
                    block_source: inner_text,
                    tokens: &inner_tokens,
                    enclosing_project: Some(tree),
                },
            )
        };
        assert!(check(&tree).unwrap());

        // An Aggregate-input Project is a carrier for grouping/aggregate
        // arguments, not a positional copy of the outer SELECT list.  Its
        // one generated scalar may therefore contain exact uses of several
        // inner outputs.  The recursive expansion walk must close both
        // definitions even though source/generated arities differ.
        let mut nested_carrier = tree.clone();
        let left = nested_carrier.project_rex[0].clone();
        let right = nested_carrier.project_rex[1].clone();
        nested_carrier.project_rex = vec![
            serde_json::from_value(json!({
                "kind": "PLUS", "class": "RexCall", "type": "INTEGER", "nullable": true,
                "operands": [
                    serde_json::to_value(left).unwrap(),
                    serde_json::to_value(right).unwrap()
                ]
            }))
            .unwrap(),
        ];
        nested_carrier.row_type = vec![
            serde_json::from_value(json!({
                "name": "combined", "type": "INTEGER", "nullable": true
            }))
            .unwrap(),
        ];
        assert!(check(&nested_carrier).unwrap());

        let mut nested_cross_scope = nested_carrier;
        let nested_expansion = nested_cross_scope.project_rex[0].operands[0]
            .source_expansion
            .as_mut()
            .unwrap();
        nested_expansion.reference_node_id = span(inner_b, inner_b + 1);
        assert!(check(&nested_cross_scope).is_err());

        let mut duplicate = tree.clone();
        let duplicate_expansion = duplicate.project_rex[1].source_expansion.as_mut().unwrap();
        duplicate_expansion.project_item_node_id = span(inner_b, inner_b + 1);
        duplicate_expansion.project_item_text = "b".to_owned();
        assert!(check(&duplicate).is_err());

        let mut forged_outer_from = tree;
        let expansion = forged_outer_from.project_rex[0]
            .source_expansion
            .as_mut()
            .unwrap();
        expansion.outer_from_node_id = span(outer_b, outer_b + 1);
        expansion.outer_from_text = "b".to_owned();
        assert!(check(&forged_outer_from).is_err());
    }

    #[test]
    fn collapsed_derived_wildcard_requires_exact_consumer_input_bindings() {
        let sql = "select a from (select * from (select a, b from t) x where b > 0) y";
        let middle = sql.find("select *").unwrap();
        let middle_end = sql.rfind(") y").unwrap();
        let inner = sql.rfind("select a, b").unwrap();
        let inner_end = sql.find(") x").unwrap();
        let outer_a = "select ".len();
        let inner_a = inner + "select ".len();
        let middle_block = span(middle, middle_end);
        let inner_block = span(inner, inner_end);
        let outer_block = span(0, sql.len());
        let fields = json!([
            {"name": "a", "type": "INTEGER", "nullable": true},
            {"name": "b", "type": "INTEGER", "nullable": true}
        ]);
        let carrier = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": inner_block,
            "rowType": fields,
            "inputs": [{
                "type": "LogicalTableScan",
                "sourceQueryBlockId": inner_block,
                "rowType": fields
            }]
        }));
        let block_root = rel(json!({
            "type": "LogicalFilter",
            "sourceQueryBlockId": middle_block,
            "sourceClause": "WHERE",
            "rowType": fields,
            "inputs": [serde_json::to_value(carrier).unwrap()]
        }));
        let tree = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "rowType": [{"name": "a", "type": "INTEGER", "nullable": true}],
            "projectRex": [{
                "kind": "INPUT_REF", "class": "RexInputRef", "index": 0,
                "type": "INTEGER", "nullable": true,
                "sourceNodeId": span(outer_a, outer_a + 1), "sourceText": "a"
            }],
            "inputs": [serde_json::to_value(block_root).unwrap()]
        }));
        let middle_text = &sql[middle..middle_end];
        let statement_tokens = lex(sql).unwrap();
        let middle_tokens = lex(middle_text).unwrap();
        let middle_range = middle..middle_end;
        let check = |tree: &CalciteRel| {
            let block_root = &tree.inputs[0];
            let carrier = &block_root.inputs[0];
            validate_collapsed_derived_identity_select(
                block_root,
                carrier,
                SourceBlockContext {
                    block_id: &middle_block,
                    statement: StatementContext {
                        sql,
                        tokens: &statement_tokens,
                    },
                    block_range: &middle_range,
                    block_source: middle_text,
                    tokens: &middle_tokens,
                    enclosing_project: Some(tree),
                },
            )
        };
        assert!(check(&tree).unwrap());

        let mut wrong_input = tree.clone();
        wrong_input.project_rex[0].index = Some(1);
        assert!(check(&wrong_input).is_err());

        let mut forged_span = tree;
        forged_span.project_rex[0].source_node_id = Some(span(inner_a, inner_a + 1));
        assert!(check(&forged_span).is_err());
    }

    #[test]
    fn direct_distinct_aggregate_accepts_exact_aliases_and_wildcard_expansion() {
        let alias_sql = "select dept.deptno as deptno0 from dept group by dept.deptno";
        let alias_aggregate = rel(json!({
            "type": "LogicalAggregate",
            "rowType": [{"name": "DEPTNO0", "type": "INTEGER", "nullable": false}],
            "groupSet": [0],
            "groupSets": [[0]],
            "inputs": [{
                "type": "LogicalProject",
                "rowType": [{"name": "DEPTNO", "type": "INTEGER", "nullable": false}]
            }]
        }));
        let alias_tokens = lex(alias_sql).unwrap();
        let alias_range = 0..alias_sql.len();
        validate_direct_aggregate_select_output(
            &alias_aggregate,
            SourceBlockContext {
                block_id: "test",
                statement: StatementContext {
                    sql: alias_sql,
                    tokens: &alias_tokens,
                },
                block_range: &alias_range,
                block_source: alias_sql,
                tokens: &alias_tokens,
                enclosing_project: None,
            },
        )
        .unwrap();

        let wildcard_sql = "select distinct x.* from r x, r y";
        let wildcard_aggregate = rel(json!({
            "type": "LogicalAggregate",
            "rowType": [
                {"name": "a", "type": "INTEGER", "nullable": false},
                {"name": "b", "type": "VARCHAR", "nullable": true}
            ],
            "groupSet": [0, 1],
            "groupSets": [[0, 1]],
            "inputs": [{
                "type": "LogicalProject",
                "rowType": [
                    {"name": "a", "type": "INTEGER", "nullable": false},
                    {"name": "b", "type": "VARCHAR", "nullable": true}
                ]
            }]
        }));
        let wildcard_tokens = lex(wildcard_sql).unwrap();
        let wildcard_range = 0..wildcard_sql.len();
        validate_direct_aggregate_select_output(
            &wildcard_aggregate,
            SourceBlockContext {
                block_id: "test",
                statement: StatementContext {
                    sql: wildcard_sql,
                    tokens: &wildcard_tokens,
                },
                block_range: &wildcard_range,
                block_source: wildcard_sql,
                tokens: &wildcard_tokens,
                enclosing_project: None,
            },
        )
        .unwrap();

        let mut missing_column = wildcard_aggregate;
        missing_column.group_set = Some(vec![0]);
        assert!(
            validate_direct_aggregate_select_output(
                &missing_column,
                SourceBlockContext {
                    block_id: "test",
                    statement: StatementContext {
                        sql: wildcard_sql,
                        tokens: &wildcard_tokens,
                    },
                    block_range: &wildcard_range,
                    block_source: wildcard_sql,
                    tokens: &wildcard_tokens,
                    enclosing_project: None,
                },
            )
            .is_err()
        );
    }

    #[test]
    fn direct_aggregate_binds_exact_repeated_select_and_group_expression() {
        let sql = "select substring(a,1,2) from t group by substring(a,1,2)";
        let group_expression = sql.rfind("substring(a,1,2)").unwrap();
        let block = span(0, sql.len());
        let field = json!({"name": "EXPR$0", "type": "VARCHAR", "nullable": true});
        let tree = rel(json!({
            "type": "LogicalAggregate",
            "sourceQueryBlockId": block,
            "rowType": [field],
            "groupSet": [0],
            "groupSets": [[0]],
            "inputs": [{
                "type": "LogicalProject",
                "sourceQueryBlockId": block,
                "rowType": [field],
                "projectRex": [{
                    "kind": "OTHER_FUNCTION", "class": "RexCall",
                    "type": "VARCHAR", "nullable": true,
                    "sourceNodeId": span(
                        group_expression,
                        group_expression + "substring(a,1,2)".len()
                    ),
                    "sourceText": "substring(a,1,2)"
                }],
                "inputs": [{
                    "type": "LogicalTableScan",
                    "sourceQueryBlockId": block,
                    "rowType": [{"name": "a", "type": "VARCHAR", "nullable": true}]
                }]
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let divergent = sql.replacen("substring(a,1,2)", "substring(a,1,3)", 1);
        assert!(validate_query_shape_bijection(&tree, Some(&divergent)).is_err());

        let mut forged_text = tree;
        forged_text.inputs[0].project_rex[0].source_text = Some("substring(a,1,3)".to_owned());
        assert!(validate_query_shape_bijection(&forged_text, Some(sql)).is_err());
    }

    #[test]
    fn direct_cte_aggregate_permutation_rejects_unsafe_and_ambiguous_omissions() {
        fn fixture(extra_items: &str) -> (String, Range<usize>, String, CalciteRel) {
            let definition = format!("SELECT SUM(a) AS s, b, {extra_items} FROM t GROUP BY b");
            let sql = format!("WITH x AS ({definition}) SELECT s FROM x");
            let definition_start = sql.find(&definition).unwrap();
            let definition_end = definition_start + definition.len();
            let definition_range = definition_start..definition_end;
            let definition_block = span(definition_start, definition_end);
            let definition_name = "WITH ".len();
            let definition_item_start = definition_name;
            let definition_item_end = definition_end + 1;
            let body_text = "SELECT s FROM x";
            let body_start = sql.rfind(body_text).unwrap();
            let body_end = body_start + body_text.len();
            let outer_block = span(body_start, body_end);
            let relation = sql.rfind('x').unwrap();
            let reference = body_start + "SELECT ".len();
            let sum = definition_start + definition.find("SUM(a)").unwrap();
            let sum_item_end = definition_start + definition.find(',').unwrap();
            let sum_alias = definition_start + definition.find(" AS s").unwrap() + " AS ".len();
            let select_b = definition_start + definition.find(", b,").unwrap() + 2;
            let group_b = definition_start + definition.rfind('b').unwrap();
            let argument_a = sum + "SUM(".len();
            let cte_use = CalciteSourceCteUse {
                kind: "CTE_USE".to_owned(),
                relation_node_id: span(relation, relation + 1),
                relation_text: "x".to_owned(),
                reference_node_id: span(relation, relation + 1),
                reference_text: "x".to_owned(),
                definition_name_node_id: span(definition_name, definition_name + 1),
                definition_name_text: "x".to_owned(),
                definition_query_node_id: definition_block.clone(),
                definition_query_text: definition.clone(),
                definition_item_node_id: span(definition_item_start, definition_item_end),
                definition_item_text: sql[definition_item_start..definition_item_end].to_owned(),
                definition_list_node_id: span(definition_item_start, definition_item_end),
                definition_list_text: sql[definition_item_start..definition_item_end].to_owned(),
                definition_body_node_id: outer_block.clone(),
                definition_body_text: body_text.to_owned(),
                definition_with_node_id: span(0, sql.len()),
                definition_with_text: sql.clone(),
                reference_scope_kind: "BODY".to_owned(),
                reference_scope_node_id: outer_block.clone(),
                reference_scope_text: body_text.to_owned(),
            };
            let integer = json!({
                "name": "b", "type": "INTEGER", "nullable": true,
                "fullType": "INTEGER", "precision": 10, "scale": 0
            });
            let sum_field = json!({
                "name": "s", "type": "BIGINT", "nullable": true,
                "fullType": "BIGINT", "precision": 19, "scale": 0
            });
            let aggregate = rel(json!({
                "type": "LogicalAggregate",
                "sourceQueryBlockId": definition_block,
                "rowType": [integer, sum_field],
                "groupSet": [0], "groupSets": [[0]],
                "aggCallDetails": [{
                    "text": "SUM($1)", "function": "SUM", "kind": "SUM",
                    "type": "BIGINT", "fullType": "BIGINT",
                    "precision": 19, "scale": 0,
                    "sourceSql": "SUM(a)",
                    "sourceNodeId": span(sum, sum + "SUM(a)".len()),
                    "sourceText": "SUM(a)"
                }],
                "inputs": [{
                    "type": "LogicalProject",
                    "sourceQueryBlockId": definition_block,
                    "rowType": [integer, {
                        "name": "a", "type": "INTEGER", "nullable": true,
                        "fullType": "INTEGER", "precision": 10, "scale": 0
                    }],
                    "projectRex": [{
                        "kind": "INPUT_REF", "class": "RexInputRef", "index": 1,
                        "type": "INTEGER", "nullable": true, "fullType": "INTEGER",
                        "precision": 10, "scale": 0,
                        "sourceNodeId": span(group_b, group_b + 1), "sourceText": "b"
                    }, {
                        "kind": "INPUT_REF", "class": "RexInputRef", "index": 0,
                        "type": "INTEGER", "nullable": true, "fullType": "INTEGER",
                        "precision": 10, "scale": 0,
                        "sourceNodeId": span(argument_a, argument_a + 1), "sourceText": "a"
                    }],
                    "inputs": [{
                        "type": "LogicalTableScan",
                        "sourceQueryBlockId": definition_block,
                        "rowType": [{
                            "name": "a", "type": "INTEGER", "nullable": true,
                            "fullType": "INTEGER", "precision": 10, "scale": 0
                        }, integer]
                    }]
                }]
            }));
            let expansion = json!({
                "kind": "DIRECT_CTE_OUTPUT_ALIAS",
                "referenceNodeId": span(reference, reference + 1),
                "referenceText": "s",
                "definitionNodeId": span(sum, sum + "SUM(a)".len()),
                "definitionText": "SUM(a)",
                "projectItemNodeId": span(sum, sum_item_end),
                "projectItemText": &sql[sum..sum_item_end],
                "outputAliasNodeId": span(sum_alias, sum_alias + 1),
                "outputAliasText": "s",
                "innerSelectNodeId": definition_block,
                "innerSelectText": definition,
                "outerFromNodeId": span(relation, relation + 1),
                "outerFromText": "x",
                "outerSelectNodeId": outer_block,
                "outerSelectText": body_text,
                "publicOutputIndex": 0,
                "cteUse": serde_json::to_value(&cte_use).unwrap()
            });
            let project = rel(json!({
                "type": "LogicalProject",
                "sourceQueryBlockId": outer_block,
                "rowType": [sum_field],
                "projectRex": [{
                    "kind": "INPUT_REF", "class": "RexInputRef", "index": 1,
                    "type": "BIGINT", "nullable": true, "fullType": "BIGINT",
                    "precision": 19, "scale": 0,
                    "sourceNodeId": span(sum, sum + "SUM(a)".len()),
                    "sourceText": "SUM(a)", "sourceExpansion": expansion
                }],
                "sourceInputCteUses": [serde_json::to_value(cte_use).unwrap()],
                "inputs": [serde_json::to_value(aggregate).unwrap()]
            }));
            // These exact locations are independently exercised by the
            // permutation matcher; keep the fixture's SELECT/group roles
            // explicit rather than relying on generated field names.
            assert_eq!(&sql[select_b..select_b + 1], "b");
            (sql, definition_range, definition_block, project)
        }

        let check = |extra_items: &str| {
            let (sql, block_range, block_id, project) = fixture(extra_items);
            let aggregate = &project.inputs[0];
            let input = &aggregate.inputs[0];
            let group = aggregate.group_set.as_deref().unwrap();
            let block_source = &sql[block_range.clone()];
            let tokens = lex(block_source).unwrap();
            let items = direct_select_item_ranges(block_source, &tokens)
                .unwrap()
                .into_iter()
                .map(|range| block_range.start + range.start..block_range.start + range.end)
                .collect::<Vec<_>>();
            let repeated = direct_group_item_ranges(block_source, &tokens)
                .unwrap()
                .unwrap()
                .into_iter()
                .map(|range| block_range.start + range.start..block_range.start + range.end)
                .collect::<Vec<_>>();
            let statement_tokens = lex(&sql).unwrap();
            let context = AggregateOutputContext {
                block: SourceBlockContext {
                    block_id: &block_id,
                    statement: StatementContext {
                        sql: &sql,
                        tokens: &statement_tokens,
                    },
                    block_range: &block_range,
                    block_source,
                    tokens: &tokens,
                    enclosing_project: Some(&project),
                },
                input,
                group,
                items: &items,
                repeated_group_items: Some(&repeated),
            };
            validate_direct_cte_aggregate_select_output(aggregate, &context)
        };

        check("0 AS z").expect("an omitted exact INT4 zero is runtime-total");
        assert!(
            check("1/0 AS z").is_err(),
            "an omitted division must not be accepted as runtime-total"
        );
        assert!(
            check("b AS k, 0 AS z").is_err(),
            "two public items must not borrow one repeated group role"
        );
        assert!(
            check("abs(b) AS k, 0 AS z").is_err(),
            "an omitted function call must remain conservatively non-total"
        );
        assert!(
            check("SUM(a) AS t, 0 AS z").is_err(),
            "an omitted aggregate call must remain observable"
        );
        assert!(
            check("0 AS \"s\"").is_err(),
            "quoted and unquoted canonical PostgreSQL names must not form separate outputs"
        );
        assert!(
            check("0 AS S").is_err(),
            "unquoted PostgreSQL names must be folded before duplicate detection"
        );
        check("0 AS \"S\"")
            .expect("a case-distinct quoted PostgreSQL output remains a separate name");
    }

    #[test]
    fn source_aggregate_classifier_recognizes_only_direct_single_value_calls() {
        assert!(contains_source_aggregate_call(
            &lex("select single_value(x) from t").unwrap()
        ));
        assert!(!contains_source_aggregate_call(
            &lex("select single_value(x) over () from t").unwrap()
        ));
        assert!(!contains_source_aggregate_call(
            &lex("select x from t where exists (select single_value(y) from u)").unwrap()
        ));
        assert!(!contains_source_aggregate_call(
            &lex("select single_value_like(x) from t").unwrap()
        ));
    }

    #[test]
    fn direct_aggregate_allows_only_grouping_set_null_widening() {
        let mut aggregate = rel(json!({
            "type": "LogicalAggregate",
            "sourceGrouping": {
                "kind": "SOURCE_GROUPING",
                "queryBlockId": "1:1-1:1",
                "sourceSelectNodeId": "1:1-1:1",
                "sourceSelectText": "a",
                "sourceSelectSql": "a",
                "sourceGroupNodeId": "1:1-1:1",
                "sourceGroupText": "a",
                "sourceGroupSql": "a",
                "groupIndexes": [0],
                "groupingSets": [[0], []],
                "sourceHasWhere": false,
                "sourceHasHaving": false
            }
        }));
        let input = serde_json::from_value(json!({
            "name": "a", "type": "INTEGER", "nullable": false,
            "fullType": "INTEGER NOT NULL"
        }))
        .unwrap();
        let output = serde_json::from_value(json!({
            "name": "a", "type": "INTEGER", "nullable": true,
            "fullType": "INTEGER"
        }))
        .unwrap();
        assert!(aggregate_group_output_matches_input(
            &aggregate, 0, &output, &input
        ));

        let mut incoherent_input = input.clone();
        incoherent_input.full_type = Some("INTEGER".to_owned());
        assert!(
            !aggregate_group_output_matches_input(&aggregate, 0, &output, &incoherent_input),
            "group input fullType must agree with its structured nullability"
        );

        let mut incoherent_output = output.clone();
        incoherent_output.full_type = Some("INTEGER NOT NULL".to_owned());
        assert!(
            !aggregate_group_output_matches_input(&aggregate, 0, &incoherent_output, &input),
            "group output fullType must agree with its structured nullability"
        );

        aggregate.source_grouping.as_mut().unwrap().grouping_sets = vec![vec![0]];
        assert!(
            !aggregate_group_output_matches_input(&aggregate, 0, &output, &input),
            "ordinary grouping must not authorize unexplained nullability widening"
        );
    }

    #[test]
    fn direct_cte_aggregate_mapping_is_injective_and_omission_is_conservative() {
        let mut claimed = BTreeSet::new();
        assert_eq!(
            claim_unique_direct_cte_public_output(&[2], &mut claimed, "group output 0").unwrap(),
            2
        );
        assert!(
            claim_unique_direct_cte_public_output(&[2], &mut claimed, "call output 1").is_err(),
            "two generated outputs must not reuse one public SELECT item"
        );
        assert!(
            claim_unique_direct_cte_public_output(&[0, 1], &mut BTreeSet::new(), "group output 0")
                .is_err(),
            "one generated output must not choose arbitrarily between duplicate source roles"
        );

        for safe in [
            "column_name",
            "0",
            "1",
            "-2147483648",
            "NULL",
            "TRUE",
            "FALSE",
        ] {
            assert!(
                crate::calcite::convert::exact_cte_definition_is_conservatively_runtime_total(safe),
                "{safe}"
            );
        }
        for unsafe_definition in [
            "1/0",
            "abs(column_name)",
            "SUM(column_name)",
            "CAST(column_name AS INTEGER)",
            "2147483648",
        ] {
            assert!(
                !crate::calcite::convert::exact_cte_definition_is_conservatively_runtime_total(
                    unsafe_definition
                ),
                "{unsafe_definition} must not be silently omitted"
            );
        }
    }

    #[test]
    fn direct_cte_aggregate_carrier_accepts_only_same_block_typed_having_filters() {
        let block = "1:1-1:20";
        let field = json!({
            "name": "s", "type": "BIGINT", "nullable": true,
            "fullType": "BIGINT", "precision": 19, "scale": 0
        });
        let aggregate = rel(json!({
            "type": "LogicalAggregate",
            "sourceQueryBlockId": block,
            "rowType": [field.clone()],
            "inputs": []
        }));
        let having = rel(json!({
            "type": "LogicalFilter",
            "sourceQueryBlockId": block,
            "sourceClause": "HAVING",
            "sourceNativeHaving": {
                "kind": "DECLARATIVE_HAVING",
                "queryBlockId": block,
                "ownerNodeId": block,
                "sourceOwnerSql": "SELECT SUM(a) FROM t HAVING SUM(a) > 0",
                "sourceOwnerText": "SELECT SUM(a) FROM t HAVING SUM(a) > 0",
                "sourceSelectSql": "SELECT SUM(a) FROM t HAVING SUM(a) > 0",
                "sourceSelectText": "SELECT SUM(a) FROM t HAVING SUM(a) > 0",
                "sourceConditionNodeId": block,
                "sourceConditionSql": "SUM(a) > 0",
                "sourceConditionText": "SUM(a) > 0",
                "generatedConditionSql": ">($0, 0)",
                "aggregateOutputArity": 1,
                "aggregateCallCount": 1,
                "operandBindings": []
            },
            "rowType": [field.clone()],
            "inputs": [serde_json::to_value(&aggregate).unwrap()]
        }));
        assert!(exact_direct_cte_aggregate_input_carrier(
            &having,
            &having.inputs[0],
            block
        ));

        let mut wrong_clause = having.clone();
        wrong_clause.source_clause = Some("WHERE".to_owned());
        assert!(!exact_direct_cte_aggregate_input_carrier(
            &wrong_clause,
            &wrong_clause.inputs[0],
            block
        ));

        let mut unattested = having.clone();
        unattested.source_native_having = None;
        assert!(!exact_direct_cte_aggregate_input_carrier(
            &unattested,
            &unattested.inputs[0],
            block
        ));

        let mut wrong_block = having.clone();
        wrong_block.source_query_block_id = Some("1:21-1:40".to_owned());
        assert!(!exact_direct_cte_aggregate_input_carrier(
            &wrong_block,
            &wrong_block.inputs[0],
            block
        ));

        let mut type_drift = having.clone();
        type_drift.row_type[0].nullable = false;
        assert!(!exact_direct_cte_aggregate_input_carrier(
            &type_drift,
            &type_drift.inputs[0],
            block
        ));

        let unrelated_project = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": block,
            "rowType": [field],
            "inputs": [serde_json::to_value(having).unwrap()]
        }));
        assert!(!exact_direct_cte_aggregate_input_carrier(
            &unrelated_project,
            &unrelated_project.inputs[0].inputs[0],
            block
        ));
    }

    #[test]
    fn exact_relocated_derived_having_is_bound_to_its_inner_aggregate() {
        let sql = "select a from (select a from t group by a having a > 0) s group by rollup(a)";
        let inner = sql.find("select a from t").unwrap();
        let inner_end = sql.find(") s").unwrap();
        let inner_group = sql[inner..].find("group by a").unwrap() + inner;
        let inner_having = sql.find("a > 0").unwrap();
        let outer_group = sql.rfind("group by rollup(a)").unwrap();
        let outer_block = span(0, sql.len());
        let inner_block = span(inner, inner_end);
        let inner_text = &sql[inner..inner_end];
        let required_field = json!({
            "name": "a", "type": "INTEGER", "nullable": false,
            "fullType": "INTEGER NOT NULL"
        });
        let nullable_field = json!({
            "name": "a", "type": "INTEGER", "nullable": true,
            "fullType": "INTEGER"
        });
        let tree = rel(json!({
            "type": "LogicalAggregate",
            "sourceQueryBlockId": outer_block,
            "rowType": [nullable_field],
            "groupSet": [0],
            "groupSets": [[0], []],
            "sourceGrouping": {
                "kind": "ROLLUP",
                "queryBlockId": outer_block,
                "sourceSelectNodeId": outer_block,
                "sourceSelectText": sql,
                "sourceSelectSql": sql,
                "sourceGroupNodeId": span(outer_group, sql.len()),
                "sourceGroupText": &sql[outer_group..],
                "sourceGroupSql": &sql[outer_group..],
                "groupIndexes": [0],
                "groupingSets": [[0], []],
                "sourceHasWhere": false,
                "sourceHasHaving": false
            },
            "inputs": [{
                // Calcite flattens the derived table and assigns this Filter
                // to the outer block even though its exact condition is the
                // inner aggregate's direct HAVING role.
                "type": "LogicalFilter",
                "sourceQueryBlockId": outer_block,
                "rowType": [required_field],
                "conditionRex": {
                    "sourceNodeId": span(inner_having, inner_having + "a > 0".len()),
                    "sourceText": "a > 0"
                },
                "inputs": [{
                    "type": "LogicalAggregate",
                    "sourceQueryBlockId": inner_block,
                    "rowType": [required_field],
                    "groupSet": [0],
                    "groupSets": [[0]],
                    "sourceGrouping": {
                        "kind": "GROUP_BY",
                        "queryBlockId": inner_block,
                        "sourceSelectNodeId": inner_block,
                        "sourceSelectText": inner_text,
                        "sourceSelectSql": inner_text,
                        "sourceGroupNodeId": span(inner_group, inner_group + "group by a".len()),
                        "sourceGroupText": "group by a",
                        "sourceGroupSql": "group by a",
                        "groupIndexes": [0],
                        "groupingSets": [[0]],
                        "sourceHasWhere": false,
                        "sourceHasHaving": true
                    },
                    "inputs": [{
                        "type": "LogicalProject",
                        "sourceQueryBlockId": inner_block,
                        "rowType": [required_field]
                    }]
                }]
            }]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut truncated = tree.clone();
        truncated.inputs[0]
            .condition_rex
            .as_mut()
            .unwrap()
            .source_node_id = Some(span(inner_having, inner_having + 1));
        assert!(validate_query_shape_bijection(&truncated, Some(sql)).is_err());

        let mut unmarked = tree;
        unmarked.inputs[0].inputs[0]
            .source_grouping
            .as_mut()
            .unwrap()
            .source_has_having = false;
        assert!(validate_query_shape_bijection(&unmarked, Some(sql)).is_err());
    }

    #[test]
    fn exact_flattened_derived_group_rebinds_its_project_and_aggregate() {
        let sql = "select sum(a) from (select a from t group by a) s";
        let inner = sql.rfind("select").unwrap();
        let inner_end = sql.find(") s").unwrap();
        let inner_item = inner + "select ".len();
        let outer_reference = sql.find("sum(a)").unwrap() + "sum(".len();
        let sum_start = sql.find("sum(a)").unwrap();
        let outer_block = span(0, sql.len());
        let inner_block = span(inner, inner_end);
        let inner_text = &sql[inner..inner_end];
        let outer_from_text = &sql[inner..];
        let field = json!({"name": "a", "type": "INTEGER", "nullable": true});
        let scan = rel(json!({
            "type": "LogicalTableScan",
            "sourceQueryBlockId": inner_block,
            "rowType": [field]
        }));
        let project = rel(json!({
            "type": "LogicalProject",
            "sourceQueryBlockId": outer_block,
            "rowType": [field],
            "projectRex": [{
                "kind": "INPUT_REF", "class": "RexInputRef",
                "index": 0, "type": "INTEGER", "nullable": true,
                "sourceNodeId": span(inner_item, inner_item + 1),
                "sourceText": "a",
                "sourceExpansion": {
                    "kind": "DIRECT_DERIVED_PASSTHROUGH",
                    "referenceNodeId": span(outer_reference, outer_reference + 1),
                    "referenceText": "a",
                    "definitionNodeId": span(inner_item, inner_item + 1),
                    "definitionText": "a",
                    "projectItemNodeId": span(inner_item, inner_item + 1),
                    "projectItemText": "a",
                    "outputAliasNodeId": span(inner_item, inner_item + 1),
                    "outputAliasText": "a",
                    "innerSelectNodeId": inner_block,
                    "innerSelectText": inner_text,
                    "outerFromNodeId": span(inner, sql.len()),
                    "outerFromText": outer_from_text,
                    "outerSelectNodeId": outer_block,
                    "outerSelectText": sql
                }
            }],
            "inputs": [serde_json::to_value(scan).unwrap()]
        }));
        // Calcite assigns both nodes to the outer block after flattening the
        // derived table. The exact expansion independently binds them back.
        let inner_aggregate = rel(json!({
            "type": "LogicalAggregate",
            "sourceQueryBlockId": outer_block,
            "rowType": [field],
            "groupSet": [0],
            "groupSets": [[0]],
            "inputs": [serde_json::to_value(project).unwrap()]
        }));
        let tree = rel(json!({
            "type": "LogicalAggregate",
            "sourceQueryBlockId": outer_block,
            "rowType": [{"name": "EXPR$0", "type": "BIGINT", "nullable": true}],
            "groupSet": [],
            "groupSets": [[]],
            "aggCallDetails": [{
                "text": "SUM($0)", "function": "SUM", "kind": "SUM",
                "filterArg": null, "sourceSql": "SUM(a)",
                "sourceNodeId": span(sum_start, sum_start + "sum(a)".len()),
                "sourceText": "sum(a)"
            }],
            "inputs": [serde_json::to_value(inner_aggregate).unwrap()]
        }));
        validate_query_shape_bijection(&tree, Some(sql)).unwrap();

        let mut forged_source = tree.clone();
        forged_source.inputs[0].inputs[0].project_rex[0]
            .source_expansion
            .as_mut()
            .unwrap()
            .inner_select_text = "select a from forged".to_owned();
        assert!(validate_query_shape_bijection(&forged_source, Some(sql)).is_err());

        let mut wrong_group = tree;
        wrong_group.inputs[0].group_set = Some(vec![]);
        assert!(validate_query_shape_bijection(&wrong_group, Some(sql)).is_err());
    }

    #[test]
    fn native_grouping_is_not_relocated_by_derived_column_expansion() {
        let sql = "select a from (select a, b from t) s group by a";
        let inner = sql.rfind("select").unwrap();
        let inner_end = sql.find(") s").unwrap();
        let inner_a = inner + "select ".len();
        let outer_a = "select ".len();
        let group = sql.find("group by a").unwrap();
        let outer_block = span(0, sql.len());
        let inner_block = span(inner, inner_end);
        let field = json!({"name": "a", "type": "INTEGER", "nullable": true});
        let aggregate = rel(json!({
            "type": "LogicalAggregate",
            "sourceQueryBlockId": outer_block,
            "rowType": [field],
            "groupSet": [0],
            "groupSets": [[0]],
            "sourceGrouping": {
                "kind": "GROUP_BY",
                "queryBlockId": outer_block,
                "sourceSelectNodeId": outer_block,
                "sourceSelectText": sql,
                "sourceSelectSql": sql,
                "sourceGroupNodeId": span(group, sql.len()),
                "sourceGroupText": "group by a",
                "sourceGroupSql": "a",
                "groupIndexes": [0],
                "groupingSets": [[0]],
                "sourceHasWhere": false,
                "sourceHasHaving": false
            },
            "inputs": [{
                "type": "LogicalProject",
                "sourceQueryBlockId": outer_block,
                "rowType": [field],
                "projectRex": [{
                    "kind": "INPUT_REF", "class": "RexInputRef", "index": 0,
                    "sourceNodeId": span(inner_a, inner_a + 1), "sourceText": "a",
                    "sourceExpansion": {
                        "kind": "DIRECT_DERIVED_PASSTHROUGH",
                        "referenceNodeId": span(outer_a, outer_a + 1),
                        "referenceText": "a",
                        "definitionNodeId": span(inner_a, inner_a + 1),
                        "definitionText": "a",
                        "projectItemNodeId": span(inner_a, inner_a + 1),
                        "projectItemText": "a",
                        "outputAliasNodeId": span(inner_a, inner_a + 1),
                        "outputAliasText": "a",
                        "innerSelectNodeId": inner_block,
                        "innerSelectText": &sql[inner..inner_end],
                        "outerFromNodeId": span(inner, inner_end + 3),
                        "outerFromText": &sql[inner..inner_end + 3],
                        "outerSelectNodeId": outer_block,
                        "outerSelectText": sql
                    }
                }],
                "inputs": [{
                    "type": "LogicalProject",
                    "sourceQueryBlockId": inner_block,
                    "rowType": [
                        {"name": "a", "type": "INTEGER", "nullable": true},
                        {"name": "b", "type": "INTEGER", "nullable": true}
                    ]
                }]
            }]
        }));
        assert!(
            exact_flattened_derived_group_target(&aggregate, sql, &lex(sql).unwrap())
                .unwrap()
                .is_none()
        );

        let mut mismatched_owner = aggregate;
        mismatched_owner
            .source_grouping
            .as_mut()
            .unwrap()
            .query_block_id = inner_block;
        assert!(
            exact_flattened_derived_group_target(&mismatched_owner, sql, &lex(sql).unwrap())
                .is_err()
        );
    }

    #[test]
    fn exact_query_shape_rejects_deleted_order_and_join_roles() {
        let order_sql = "select a from t order by a";
        let order = rel(json!({
            "type": "LogicalSort", "sourceQueryBlockId": "1:1-1:15",
            "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
            "inputs": [{"type": "LogicalProject", "sourceQueryBlockId": "1:1-1:15"}]
        }));
        validate_query_shape_bijection(&order, Some(order_sql)).unwrap();
        let deleted_order = order.inputs[0].clone();
        assert!(validate_query_shape_bijection(&deleted_order, Some(order_sql)).is_err());

        let join_sql = "select t.a from t join u on t.a = u.a";
        let block = "1:1-1:37";
        let join = rel(json!({
            "type": "LogicalProject", "sourceQueryBlockId": block,
            "inputs": [{
                "type": "LogicalJoin", "sourceQueryBlockId": block,
                "sourceJoin": {
                    "kind": "DIRECT_JOIN", "queryBlockId": block,
                    "joinNodeId": "1:19-1:22", "joinText": "join",
                    "leftNodeId": "1:17-1:17", "leftText": "t",
                    "rightNodeId": "1:24-1:24", "rightText": "u",
                    "conditionType": "ON", "conditionNodeId": "1:29-1:37",
                    "conditionText": "t.a = u.a"
                },
                "inputs": [
                    {"type": "LogicalTableScan"},
                    {"type": "LogicalTableScan"}
                ]
            }]
        }));
        validate_query_shape_bijection(&join, Some(join_sql)).unwrap();
        let mut deleted_join = join;
        deleted_join.inputs[0] = deleted_join.inputs[0].inputs.remove(0);
        assert!(validate_query_shape_bijection(&deleted_join, Some(join_sql)).is_err());
    }
}
