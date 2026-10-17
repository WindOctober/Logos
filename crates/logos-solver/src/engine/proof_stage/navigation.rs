//! Host-derived query navigation. These artifacts describe syntax and signatures, never proof authority.

use crate::core::{
    FormalAttribute, FormalQueryDefinitionGraph, FormalQueryExpr, FormalQueryShapeKind,
    FormalQueryStatementSymbols, FormalScalarExpr, FormalScalarSelectItem, LoweredProgram,
    LoweredQuery, ProofLoweringReport, VerificationInput, VerificationIr,
    query_expr_output_signature,
};
use crate::error::{Error, Result};
use logos_ir::ir::RelExpr;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

use super::{lowering_programs_have_query_bindings, sha256_hex};

#[cfg(test)]
#[path = "../../../tests/proof_stage/navigation.rs"]
mod tests;

const COMPACT_DEFINITION_GRAPH_NOTATION: &str = "skeletonNodes[i]=[head,[ordered child node IDs]]; definitions retain every exact Rocq symbol, kind, and root node; @symbol heads bind exact Queries.v definitions. IDs are deterministic postorder. Reused nodes mean identical displayed skeleton only, never Rocq-term or SQL equality; opaque scalar/list payloads remain authoritative in Queries.v";
const COMPACT_FRONTEND_SKELETON_NOTATION: &str = "nodes[i]=[operator{compact fields},[ordered child node IDs]]; each typedFrontendTree.rootNode selects a source/target root. IDs are deterministic postorder. Reused nodes mean identical displayed skeleton only, never SQL equality; exact SQL and the typed IR remain authoritative";

/// Query identity owns both the wire label and node-ID prefix; callers cannot
/// accidentally pair "source" with the target prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum QuerySide {
    Source,
    Target,
}

impl QuerySide {
    fn node_prefix(self) -> char {
        match self {
            Self::Source => 'S',
            Self::Target => 'T',
        }
    }
}

impl std::fmt::Display for QuerySide {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Source => "source",
            Self::Target => "target",
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
enum OperatorKind {
    Error,
    Empty,
    EmptyTuple,
    Table,
    Set,
    CrossJoin,
    Join,
    Projection,
    Selection,
    Group,
    GroupingSets,
    Rank,
    Window,
    Distinct,
    OrderBy,
    Offset,
    Fetch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum EdgeKind {
    Relational,
    ScalarSubquery,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum MismatchKind {
    OrderedAttribute,
    Arity,
}

pub(super) struct NavigationArtifacts {
    pub(super) text: String,
    pub(super) ordered_signatures_text: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct QueryShape {
    schema_version: u32,
    authority: &'static str,
    frontend_sql_role: &'static str,
    operator_tree_notation: &'static str,
    source_sql_sha256: String,
    target_sql_sha256: String,
    schema_module_sha256: String,
    queries_module_sha256: String,
    emitted_rocq_symbols: Vec<String>,
    emitted_definition_graph: CompactDefinitionGraph,
    typed_frontend_skeleton: CompactSkeletonDag,
    source_program: Vec<StatementShape<CompactOperatorTreeRoot>>,
    target_program: Vec<StatementShape<CompactOperatorTreeRoot>>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct StatementShape<T> {
    statement_index: usize,
    exact_sql_sha256: String,
    frontend_sql_sha256: String,
    exact_frontend_bytes_equal: bool,
    emitted_rocq_root_symbol: String,
    emitted_rocq_output_signature_symbol: String,
    final_output_canonicalization: bool,
    output_signature: Vec<Attribute>,
    typed_frontend_tree: T,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct Attribute {
    name: String,
    r#type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    nullable: Option<bool>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureIndex {
    schema_version: u32,
    authority: &'static str,
    derivation: &'static str,
    occurrence_order: &'static str,
    signature_identity: &'static str,
    comparison_policy: &'static str,
    frontier_policy: &'static str,
    signatures: Vec<SignatureEntry>,
    source_program: Vec<SignatureStatement>,
    target_program: Vec<SignatureStatement>,
    nodes: Vec<SignatureNode>,
    comparisons: Vec<SignatureComparison>,
    normalization_frontier_hints: Vec<FrontierHint>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureEntry {
    signature_id: String,
    arity: usize,
    attributes: Vec<Attribute>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureStatement {
    statement_index: usize,
    emitted_rocq_root_symbol: String,
    root_node_id: String,
    node_count: usize,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureNode {
    node_id: String,
    side: QuerySide,
    statement_index: usize,
    preorder_index: usize,
    role_path: String,
    operator_kind: OperatorKind,
    signature_id: String,
    arity: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    parent_node_id: Option<String>,
    children: Vec<SignatureEdge>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureEdge {
    role: String,
    edge_kind: EdgeKind,
    node_id: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureComparison {
    statement_index: usize,
    role_path: String,
    source_node_id: String,
    target_node_id: String,
    source_operator_kind: OperatorKind,
    target_operator_kind: OperatorKind,
    operator_kind_equal: bool,
    source_signature_id: String,
    target_signature_id: String,
    signature_equal: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    mismatch: Option<SignatureMismatch>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignatureMismatch {
    kind: MismatchKind,
    source_arity: usize,
    target_arity: usize,
    first_differing_index: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_attribute: Option<Attribute>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_attribute: Option<Attribute>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct FrontierHint {
    statement_index: usize,
    role_path: String,
    source_node_id: String,
    target_node_id: String,
    operator_kind: OperatorKind,
    signature_id: String,
    incompatible_relational_child_roles: Vec<String>,
    reason: &'static str,
}

#[derive(Clone, Debug)]
struct SignatureNodeRecord {
    artifact: SignatureNode,
    exact_signature: Vec<FormalAttribute>,
}

#[derive(Clone, Debug)]
struct CompactOperatorTree {
    node_count: usize,
    max_depth: usize,
    expression: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactOperatorTreeRoot {
    node_count: usize,
    max_depth: usize,
    root_node: usize,
}

/// A lossless, topologically ordered structural DAG. Each node serializes as
/// `[head, [ordered child node IDs]]` to keep the navigation artifact small
/// without abbreviating any constructor, field, or emitted-symbol reference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct CompactSkeletonNode(pub(super) String, pub(super) Vec<usize>);

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactSkeletonDag {
    schema_version: u32,
    notation: &'static str,
    expanded_trees_sha256: String,
    nodes: Vec<CompactSkeletonNode>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct CompactShapeDefinition {
    pub(super) symbol: String,
    pub(super) kind: FormalQueryShapeKind,
    pub(super) root_node: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct CompactDefinitionGraph {
    pub(super) schema_version: u32,
    pub(super) notation: &'static str,
    pub(super) expanded_graph_sha256: String,
    pub(super) expanded_trees_sha256: String,
    pub(super) opaque_helper_symbols: Vec<String>,
    pub(super) skeleton_nodes: Vec<CompactSkeletonNode>,
    pub(super) definitions: Vec<CompactShapeDefinition>,
    pub(super) source_statements: Vec<FormalQueryStatementSymbols>,
    pub(super) target_statements: Vec<FormalQueryStatementSymbols>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct SkeletonTree {
    pub(super) head: String,
    pub(super) children: Vec<SkeletonTree>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CompactedSkeletonForest {
    pub(super) expanded_trees_sha256: String,
    pub(super) nodes: Vec<CompactSkeletonNode>,
    pub(super) roots: Vec<usize>,
}

struct TreeExpression {
    node_count: usize,
    max_depth: usize,
    expression: String,
}

struct SkeletonTreeParser<'a> {
    input: &'a str,
    position: usize,
    role: &'a str,
}

impl SkeletonTree {
    fn render(&self) -> String {
        let mut rendered = self.head.clone();
        if !self.children.is_empty() {
            rendered.push('(');
            for (index, child) in self.children.iter().enumerate() {
                if index > 0 {
                    rendered.push(',');
                }
                rendered.push_str(&child.render());
            }
            rendered.push(')');
        }
        rendered
    }

    fn metrics(&self) -> (usize, usize) {
        let mut node_count = 1;
        let mut child_depth = 0;
        for child in &self.children {
            let (child_nodes, depth) = child.metrics();
            node_count += child_nodes;
            child_depth = child_depth.max(depth);
        }
        (node_count, child_depth + 1)
    }
}

impl<'a> SkeletonTreeParser<'a> {
    fn error(&self, message: impl AsRef<str>) -> Error {
        Error::ProofAgentCommand(format!(
            "query context drift: malformed {} skeleton at byte {}: {}",
            self.role,
            self.position,
            message.as_ref()
        ))
    }

    fn parse(mut self) -> Result<SkeletonTree> {
        if self.input.is_empty() {
            return Err(self.error("empty tree"));
        }
        if !self.input.is_ascii() {
            return Err(self.error("tree must use the emitter's ASCII-safe notation"));
        }
        let tree = self.parse_node()?;
        if self.position != self.input.len() {
            return Err(self.error("trailing bytes after the root node"));
        }
        if tree.render() != self.input {
            return Err(self.error("parser round trip changed the tree"));
        }
        Ok(tree)
    }

    fn parse_node(&mut self) -> Result<SkeletonTree> {
        let bytes = self.input.as_bytes();
        let head_start = self.position;
        while self.position < bytes.len()
            && !matches!(bytes[self.position], b'{' | b'}' | b'(' | b')' | b',')
        {
            self.position += 1;
        }
        if self.position == head_start {
            return Err(self.error("missing node head"));
        }
        let bare_head = &self.input[head_start..self.position];
        if bare_head.trim() != bare_head
            || bare_head
                .bytes()
                .any(|byte| byte.is_ascii_whitespace() && byte != b' ')
        {
            return Err(self.error(
                "node heads may contain only internal ASCII spaces, not boundary or control whitespace",
            ));
        }
        let mut head = bare_head.to_owned();

        if bytes.get(self.position) == Some(&b'{') {
            let fields_start = self.position;
            self.position += 1;
            let content_start = self.position;
            while self.position < bytes.len() && bytes[self.position] != b'}' {
                if matches!(bytes[self.position], b'{' | b'(' | b')') {
                    return Err(self.error("invalid delimiter inside compact fields"));
                }
                self.position += 1;
            }
            if self.position == bytes.len() {
                return Err(self.error("unterminated compact fields"));
            }
            if self.position == content_start {
                return Err(self.error("empty compact fields"));
            }
            self.position += 1;
            head.push_str(&self.input[fields_start..self.position]);
        }

        let mut children = Vec::new();
        if bytes.get(self.position) == Some(&b'(') {
            self.position += 1;
            if bytes.get(self.position) == Some(&b')') {
                return Err(self.error("empty child list is not canonical"));
            }
            loop {
                if self.position == bytes.len() {
                    return Err(self.error("unterminated child list"));
                }
                children.push(self.parse_node()?);
                match bytes.get(self.position) {
                    Some(b',') => {
                        self.position += 1;
                        if bytes.get(self.position) == Some(&b')') {
                            return Err(self.error("trailing comma in child list"));
                        }
                    }
                    Some(b')') => {
                        self.position += 1;
                        break;
                    }
                    Some(_) => {
                        return Err(self.error("expected ',' or ')' after child node"));
                    }
                    None => return Err(self.error("unterminated child list")),
                }
            }
        }

        Ok(SkeletonTree { head, children })
    }
}

pub(super) fn parse_skeleton_tree(tree: &str, role: &str) -> Result<SkeletonTree> {
    SkeletonTreeParser {
        input: tree,
        position: 0,
        role,
    }
    .parse()
}

fn intern_skeleton_tree(
    tree: &SkeletonTree,
    index: &mut BTreeMap<(String, Vec<usize>), usize>,
    nodes: &mut Vec<CompactSkeletonNode>,
) -> usize {
    let children = tree
        .children
        .iter()
        .map(|child| intern_skeleton_tree(child, index, nodes))
        .collect::<Vec<_>>();
    let key = (tree.head.clone(), children.clone());
    if let Some(node_id) = index.get(&key) {
        return *node_id;
    }
    let node_id = nodes.len();
    nodes.push(CompactSkeletonNode(tree.head.clone(), children));
    index.insert(key, node_id);
    node_id
}

pub(super) fn expand_compact_skeleton_node(
    nodes: &[CompactSkeletonNode],
    node_id: usize,
) -> Result<String> {
    let CompactSkeletonNode(head, children) = nodes.get(node_id).ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "query context drift: compact skeleton root {node_id} is out of range"
        ))
    })?;
    let mut expanded = head.clone();
    if !children.is_empty() {
        expanded.push('(');
        for (index, child) in children.iter().enumerate() {
            if index > 0 {
                expanded.push(',');
            }
            expanded.push_str(&expand_compact_skeleton_node(nodes, *child)?);
        }
        expanded.push(')');
    }
    Ok(expanded)
}

pub(super) fn compact_skeleton_digest(trees: &[&str]) -> Result<String> {
    Ok(sha256_hex(&serde_json::to_vec(trees)?))
}

pub(super) fn validate_compacted_skeleton_forest(
    compacted: &CompactedSkeletonForest,
    expected_trees: &[&str],
    role: &str,
) -> Result<()> {
    if compacted.roots.len() != expected_trees.len() {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: compact {role} skeleton has {} roots for {} trees",
            compacted.roots.len(),
            expected_trees.len()
        )));
    }
    let mut unique_nodes = BTreeMap::new();
    for (node_id, CompactSkeletonNode(head, children)) in compacted.nodes.iter().enumerate() {
        if head.is_empty() {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton node {node_id} has an empty head"
            )));
        }
        if children.iter().any(|child| *child >= node_id) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton node {node_id} is not in strict postorder"
            )));
        }
        let key = (head.clone(), children.clone());
        if let Some(previous) = unique_nodes.insert(key, node_id) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton duplicates nodes {previous} and {node_id}"
            )));
        }
    }

    let mut reachable = BTreeSet::new();
    fn mark_reachable(
        nodes: &[CompactSkeletonNode],
        node_id: usize,
        reachable: &mut BTreeSet<usize>,
    ) -> Result<()> {
        let node = nodes.get(node_id).ok_or_else(|| {
            Error::ProofAgentCommand(format!(
                "query context drift: compact skeleton node {node_id} is out of range"
            ))
        })?;
        if reachable.insert(node_id) {
            for child in &node.1 {
                mark_reachable(nodes, *child, reachable)?;
            }
        }
        Ok(())
    }

    for ((root, expected), index) in compacted.roots.iter().zip(expected_trees).zip(1usize..) {
        mark_reachable(&compacted.nodes, *root, &mut reachable)?;
        let expanded = expand_compact_skeleton_node(&compacted.nodes, *root)?;
        if expanded != *expected {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton root {index} does not round-trip exactly"
            )));
        }
    }
    if reachable.len() != compacted.nodes.len() {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: compact {role} skeleton contains unreachable nodes"
        )));
    }
    // Both representations are host-owned in-memory values. The exact
    // round-trip comparison above validates the transformation; the digest is
    // serialized provenance, not an additional in-memory equality check.
    Ok(())
}

pub(super) fn compact_skeleton_forest(
    trees: &[&str],
    role: &str,
) -> Result<CompactedSkeletonForest> {
    let parsed = trees
        .iter()
        .map(|tree| parse_skeleton_tree(tree, role))
        .collect::<Result<Vec<_>>>()?;
    let mut nodes = Vec::new();
    let mut index = BTreeMap::new();
    let roots = parsed
        .iter()
        .map(|tree| intern_skeleton_tree(tree, &mut index, &mut nodes))
        .collect::<Vec<_>>();
    let compacted = CompactedSkeletonForest {
        expanded_trees_sha256: compact_skeleton_digest(trees)?,
        nodes,
        roots,
    };
    validate_compacted_skeleton_forest(&compacted, trees, role)?;
    Ok(compacted)
}

pub(super) fn validate_compact_definition_graph(
    compact: &CompactDefinitionGraph,
    expanded: &FormalQueryDefinitionGraph,
) -> Result<()> {
    if compact.schema_version != 2
        || compact.notation != COMPACT_DEFINITION_GRAPH_NOTATION
        || compact.opaque_helper_symbols != expanded.opaque_helper_symbols
        || compact.source_statements != expanded.source_statements
        || compact.target_statements != expanded.target_statements
        || compact.definitions.len() != expanded.definitions.len()
    {
        return Err(Error::ProofAgentCommand(
            "query context drift: compact emitted definition graph metadata disagrees with the emitter graph"
                .to_owned(),
        ));
    }
    let trees = expanded
        .definitions
        .iter()
        .map(|definition| definition.tree.as_str())
        .collect::<Vec<_>>();
    let compacted = CompactedSkeletonForest {
        expanded_trees_sha256: compact.expanded_trees_sha256.clone(),
        nodes: compact.skeleton_nodes.clone(),
        roots: compact
            .definitions
            .iter()
            .map(|definition| definition.root_node)
            .collect(),
    };
    validate_compacted_skeleton_forest(&compacted, &trees, "emitted definition graph")?;
    for (compact_definition, expanded_definition) in
        compact.definitions.iter().zip(&expanded.definitions)
    {
        if compact_definition.symbol != expanded_definition.symbol
            || compact_definition.kind != expanded_definition.kind
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact mapping for emitted definition {} changed its symbol or kind",
                expanded_definition.symbol
            )));
        }
    }
    Ok(())
}

pub(super) fn compact_definition_graph(
    graph: &FormalQueryDefinitionGraph,
) -> Result<CompactDefinitionGraph> {
    let trees = graph
        .definitions
        .iter()
        .map(|definition| definition.tree.as_str())
        .collect::<Vec<_>>();
    let compacted = compact_skeleton_forest(&trees, "emitted definition graph")?;
    let definitions = graph
        .definitions
        .iter()
        .zip(&compacted.roots)
        .map(|(definition, root_node)| CompactShapeDefinition {
            symbol: definition.symbol.clone(),
            kind: definition.kind,
            root_node: *root_node,
        })
        .collect::<Vec<_>>();
    let compact = CompactDefinitionGraph {
        schema_version: 2,
        notation: COMPACT_DEFINITION_GRAPH_NOTATION,
        expanded_graph_sha256: sha256_hex(&serde_json::to_vec(graph)?),
        expanded_trees_sha256: compacted.expanded_trees_sha256,
        opaque_helper_symbols: graph.opaque_helper_symbols.clone(),
        skeleton_nodes: compacted.nodes,
        definitions,
        source_statements: graph.source_statements.clone(),
        target_statements: graph.target_statements.clone(),
    };
    validate_compact_definition_graph(&compact, graph)?;
    Ok(compact)
}

fn compact_query_statement(
    statement: &StatementShape<CompactOperatorTree>,
    root_node: usize,
) -> StatementShape<CompactOperatorTreeRoot> {
    StatementShape {
        statement_index: statement.statement_index,
        exact_sql_sha256: statement.exact_sql_sha256.clone(),
        frontend_sql_sha256: statement.frontend_sql_sha256.clone(),
        exact_frontend_bytes_equal: statement.exact_frontend_bytes_equal,
        emitted_rocq_root_symbol: statement.emitted_rocq_root_symbol.clone(),
        emitted_rocq_output_signature_symbol: statement
            .emitted_rocq_output_signature_symbol
            .clone(),
        final_output_canonicalization: statement.final_output_canonicalization,
        output_signature: statement.output_signature.clone(),
        typed_frontend_tree: CompactOperatorTreeRoot {
            node_count: statement.typed_frontend_tree.node_count,
            max_depth: statement.typed_frontend_tree.max_depth,
            root_node,
        },
    }
}

fn compact_frontend_programs(
    source: &[StatementShape<CompactOperatorTree>],
    target: &[StatementShape<CompactOperatorTree>],
) -> Result<(
    CompactSkeletonDag,
    Vec<StatementShape<CompactOperatorTreeRoot>>,
    Vec<StatementShape<CompactOperatorTreeRoot>>,
)> {
    let statements = source.iter().chain(target).collect::<Vec<_>>();
    for statement in &statements {
        let parsed = parse_skeleton_tree(
            &statement.typed_frontend_tree.expression,
            "typed frontend operator",
        )?;
        let (node_count, max_depth) = parsed.metrics();
        if node_count != statement.typed_frontend_tree.node_count
            || max_depth != statement.typed_frontend_tree.max_depth
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: typed frontend skeleton metrics disagree for statement {}",
                statement.statement_index
            )));
        }
    }
    let trees = statements
        .iter()
        .map(|statement| statement.typed_frontend_tree.expression.as_str())
        .collect::<Vec<_>>();
    let compacted = compact_skeleton_forest(&trees, "typed frontend operator")?;
    let (source_roots, target_roots) = compacted.roots.split_at(source.len());
    let compact_source = source
        .iter()
        .zip(source_roots)
        .map(|(statement, root)| compact_query_statement(statement, *root))
        .collect();
    let compact_target = target
        .iter()
        .zip(target_roots)
        .map(|(statement, root)| compact_query_statement(statement, *root))
        .collect();
    Ok((
        CompactSkeletonDag {
            schema_version: 1,
            notation: COMPACT_FRONTEND_SKELETON_NOTATION,
            expanded_trees_sha256: compacted.expanded_trees_sha256,
            nodes: compacted.nodes,
        },
        compact_source,
        compact_target,
    ))
}

fn compact_formal_attributes(attributes: &[FormalAttribute]) -> Vec<Attribute> {
    attributes
        .iter()
        .map(|attribute| Attribute {
            name: attribute.name.clone(),
            r#type: format!("{:?}", attribute.ty),
            nullable: None,
        })
        .collect()
}

fn ordered_signature_operator_kind(query: &FormalQueryExpr) -> OperatorKind {
    match query {
        FormalQueryExpr::Error { .. } => OperatorKind::Error,
        FormalQueryExpr::Empty { .. } => OperatorKind::Empty,
        FormalQueryExpr::EmptyTuple => OperatorKind::EmptyTuple,
        FormalQueryExpr::Table { .. } => OperatorKind::Table,
        FormalQueryExpr::Set { .. } => OperatorKind::Set,
        FormalQueryExpr::CrossJoin { .. } => OperatorKind::CrossJoin,
        FormalQueryExpr::Join { .. } => OperatorKind::Join,
        FormalQueryExpr::Projection { .. } => OperatorKind::Projection,
        FormalQueryExpr::Selection { .. } => OperatorKind::Selection,
        FormalQueryExpr::Group { .. } => OperatorKind::Group,
        FormalQueryExpr::GroupingSets { .. } => OperatorKind::GroupingSets,
        FormalQueryExpr::Rank { .. } => OperatorKind::Rank,
        FormalQueryExpr::Window { .. } => OperatorKind::Window,
        FormalQueryExpr::Distinct { .. } => OperatorKind::Distinct,
        FormalQueryExpr::OrderBy { .. } => OperatorKind::OrderBy,
        FormalQueryExpr::Offset { .. } => OperatorKind::Offset,
        FormalQueryExpr::Fetch { .. } => OperatorKind::Fetch,
    }
}

#[derive(Default)]
struct SignatureIndexBuilder {
    exact_signatures: Vec<Vec<FormalAttribute>>,
    signature_pool: Vec<SignatureEntry>,
    nodes: Vec<SignatureNodeRecord>,
}

impl SignatureIndexBuilder {
    fn intern_signature(&mut self, signature: &[FormalAttribute]) -> String {
        if let Some(index) = self
            .exact_signatures
            .iter()
            .position(|candidate| candidate == signature)
        {
            return format!("SIG{index}");
        }
        let index = self.exact_signatures.len();
        self.exact_signatures.push(signature.to_vec());
        self.signature_pool.push(SignatureEntry {
            signature_id: format!("SIG{index}"),
            arity: signature.len(),
            attributes: compact_formal_attributes(signature),
        });
        format!("SIG{index}")
    }

    fn add_query_occurrence(
        &mut self,
        side: QuerySide,
        statement_index: usize,
        role_path: String,
        parent_node_id: Option<String>,
        query: &FormalQueryExpr,
        next_preorder: &mut usize,
    ) -> Result<String> {
        let exact_signature = query_expr_output_signature(query).ok_or_else(|| {
            Error::ProofAgentCommand(format!(
                "cannot derive ordered signature for {side} statement {statement_index} at {role_path}"
            ))
        })?;
        let preorder_index = *next_preorder;
        *next_preorder += 1;
        let node_id = format!("{}{statement_index}.N{preorder_index}", side.node_prefix());
        let signature_id = self.intern_signature(&exact_signature);
        let record_index = self.nodes.len();
        self.nodes.push(SignatureNodeRecord {
            artifact: SignatureNode {
                node_id: node_id.clone(),
                side,
                statement_index,
                preorder_index,
                role_path: role_path.clone(),
                operator_kind: ordered_signature_operator_kind(query),
                signature_id,
                arity: exact_signature.len(),
                parent_node_id,
                children: Vec::new(),
            },
            exact_signature,
        });

        let mut children = Vec::new();
        let mut add_relational_child =
            |builder: &mut Self, role: &str, child: &FormalQueryExpr| -> Result<()> {
                let child_id = builder.add_query_occurrence(
                    side,
                    statement_index,
                    format!("{role_path}.{role}"),
                    Some(node_id.clone()),
                    child,
                    next_preorder,
                )?;
                children.push(SignatureEdge {
                    role: role.to_owned(),
                    edge_kind: EdgeKind::Relational,
                    node_id: child_id,
                });
                Ok(())
            };

        match query {
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                add_relational_child(self, "left", left)?;
                add_relational_child(self, "right", right)?;
            }
            FormalQueryExpr::Join {
                predicate,
                matched_select,
                left_select,
                right_select,
                left,
                right,
                ..
            } => {
                add_relational_child(self, "left", left)?;
                add_relational_child(self, "right", right)?;
                self.add_scalar_subqueries(
                    side,
                    statement_index,
                    &role_path,
                    "predicate",
                    &node_id,
                    predicate,
                    next_preorder,
                    &mut children,
                )?;
                for (list_role, select) in [
                    ("matchedSelect", matched_select),
                    ("leftSelect", left_select),
                    ("rightSelect", right_select),
                ] {
                    for (index, item) in select.iter().enumerate() {
                        self.add_scalar_subqueries(
                            side,
                            statement_index,
                            &role_path,
                            &format!("{list_role}[{index}]"),
                            &node_id,
                            &item.expr,
                            next_preorder,
                            &mut children,
                        )?;
                    }
                }
            }
            FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => {
                add_relational_child(self, "input", input)?;
            }
            FormalQueryExpr::Projection { select, input } => {
                add_relational_child(self, "input", input)?;
                for (index, item) in select.iter().enumerate() {
                    self.add_scalar_subqueries(
                        side,
                        statement_index,
                        &role_path,
                        &format!("select[{index}]"),
                        &node_id,
                        &item.expr,
                        next_preorder,
                        &mut children,
                    )?;
                }
            }
            FormalQueryExpr::Selection { predicate, input } => {
                add_relational_child(self, "input", input)?;
                self.add_scalar_subqueries(
                    side,
                    statement_index,
                    &role_path,
                    "predicate",
                    &node_id,
                    predicate,
                    next_preorder,
                    &mut children,
                )?;
            }
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
                ..
            } => {
                add_relational_child(self, "input", input)?;
                for (index, item) in select.iter().enumerate() {
                    self.add_scalar_subqueries(
                        side,
                        statement_index,
                        &role_path,
                        &format!("select[{index}]"),
                        &node_id,
                        &item.expr,
                        next_preorder,
                        &mut children,
                    )?;
                }
                for (index, key) in group_by.iter().enumerate() {
                    self.add_scalar_subqueries(
                        side,
                        statement_index,
                        &role_path,
                        &format!("groupBy[{index}]"),
                        &node_id,
                        key,
                        next_preorder,
                        &mut children,
                    )?;
                }
                self.add_scalar_subqueries(
                    side,
                    statement_index,
                    &role_path,
                    "having",
                    &node_id,
                    having,
                    next_preorder,
                    &mut children,
                )?;
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                add_relational_child(self, "input", input)?;
                for (set_index, grouping_set) in grouping_sets.iter().enumerate() {
                    for (index, item) in grouping_set.select.iter().enumerate() {
                        self.add_scalar_subqueries(
                            side,
                            statement_index,
                            &role_path,
                            &format!("groupingSets[{set_index}].select[{index}]"),
                            &node_id,
                            &item.expr,
                            next_preorder,
                            &mut children,
                        )?;
                    }
                    for (index, key) in grouping_set.group_by.iter().enumerate() {
                        self.add_scalar_subqueries(
                            side,
                            statement_index,
                            &role_path,
                            &format!("groupingSets[{set_index}].groupBy[{index}]"),
                            &node_id,
                            key,
                            next_preorder,
                            &mut children,
                        )?;
                    }
                }
            }
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => {}
        }
        self.nodes[record_index].artifact.children = children;
        Ok(node_id)
    }

    #[allow(clippy::too_many_arguments)]
    fn add_scalar_subqueries(
        &mut self,
        side: QuerySide,
        statement_index: usize,
        parent_role_path: &str,
        scalar_role: &str,
        parent_node_id: &str,
        expression: &FormalScalarExpr,
        next_preorder: &mut usize,
        children: &mut Vec<SignatureEdge>,
    ) -> Result<()> {
        let mut visit =
            |builder: &mut Self, role: String, child: &FormalScalarExpr| -> Result<()> {
                builder.add_scalar_subqueries(
                    side,
                    statement_index,
                    parent_role_path,
                    &role,
                    parent_node_id,
                    child,
                    next_preorder,
                    children,
                )
            };
        match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => Ok(()),
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                for (index, arg) in args.iter().enumerate() {
                    visit(self, format!("{scalar_role}.args[{index}]"), arg)?;
                }
                Ok(())
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                visit(self, format!("{scalar_role}.condition"), condition)?;
                visit(self, format!("{scalar_role}.then"), then_expr)?;
                visit(self, format!("{scalar_role}.else"), else_expr)
            }
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => {
                visit(self, format!("{scalar_role}.expression"), expression)
            }
            FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
                for (index, operand) in operands.iter().enumerate() {
                    visit(self, format!("{scalar_role}.operands[{index}]"), operand)?;
                }
                Ok(())
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. } => {
                for (index, arg) in args.iter().enumerate() {
                    visit(self, format!("{scalar_role}.args[{index}]"), arg)?;
                }
                self.add_scalar_query(
                    side,
                    statement_index,
                    parent_role_path,
                    &format!("{scalar_role}.quantifiedComparison.query"),
                    parent_node_id,
                    query,
                    next_preorder,
                    children,
                )
            }
            FormalScalarExpr::In { args, query } => {
                for (index, arg) in args.iter().enumerate() {
                    visit(self, format!("{scalar_role}.args[{index}]"), arg)?;
                }
                self.add_scalar_query(
                    side,
                    statement_index,
                    parent_role_path,
                    &format!("{scalar_role}.in.query"),
                    parent_node_id,
                    query,
                    next_preorder,
                    children,
                )
            }
            FormalScalarExpr::Exists { query } => self.add_scalar_query(
                side,
                statement_index,
                parent_role_path,
                &format!("{scalar_role}.exists.query"),
                parent_node_id,
                query,
                next_preorder,
                children,
            ),
            FormalScalarExpr::Subquery { query, .. } => self.add_scalar_query(
                side,
                statement_index,
                parent_role_path,
                &format!("{scalar_role}.subquery.query"),
                parent_node_id,
                query,
                next_preorder,
                children,
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn add_scalar_query(
        &mut self,
        side: QuerySide,
        statement_index: usize,
        parent_role_path: &str,
        edge_role: &str,
        parent_node_id: &str,
        query: &FormalQueryExpr,
        next_preorder: &mut usize,
        children: &mut Vec<SignatureEdge>,
    ) -> Result<()> {
        let child_id = self.add_query_occurrence(
            side,
            statement_index,
            format!("{parent_role_path}.{edge_role}"),
            Some(parent_node_id.to_owned()),
            query,
            next_preorder,
        )?;
        children.push(SignatureEdge {
            role: edge_role.to_owned(),
            edge_kind: EdgeKind::ScalarSubquery,
            node_id: child_id,
        });
        Ok(())
    }

    fn add_program(
        &mut self,
        side: QuerySide,
        program: &LoweredProgram,
    ) -> Result<Vec<SignatureStatement>> {
        let statement_count = program.statements.len();
        program
            .statements
            .iter()
            .enumerate()
            .map(|(zero_index, statement)| {
                let statement_index = zero_index + 1;
                let query = statement.query_expr.as_ref().ok_or_else(|| {
                    Error::ProofAgentCommand(format!(
                        "cannot build ordered-signature navigation for {side} statement {statement_index}: FormalSQL lowering is incomplete"
                    ))
                })?;
                let declared_signature = statement.output_signature.as_ref().ok_or_else(|| {
                    Error::ProofAgentCommand(format!(
                        "cannot build ordered-signature navigation for {side} statement {statement_index}: lowered output signature is incomplete"
                    ))
                })?;
                let recomputed_signature = query_expr_output_signature(query).ok_or_else(|| {
                    Error::ProofAgentCommand(format!(
                        "cannot build ordered-signature navigation for {side} statement {statement_index}: root signature is inconsistent"
                    ))
                })?;
                if &recomputed_signature != declared_signature {
                    return Err(Error::ProofAgentCommand(format!(
                        "ordered-signature context drift for {side} statement {statement_index}: recomputed root signature differs from LoweredQuery.output_signature"
                    )));
                }
                let before = self.nodes.len();
                let mut next_preorder = 0;
                let root_node_id = self.add_query_occurrence(
                    side,
                    statement_index,
                    "root".to_owned(),
                    None,
                    query,
                    &mut next_preorder,
                )?;
                let suffix = if statement_count == 1 {
                    String::new()
                } else {
                    format!("_{zero_index}")
                };
                Ok(SignatureStatement {
                    statement_index,
                    emitted_rocq_root_symbol: format!("{side}_query_expr{suffix}"),
                    root_node_id,
                    node_count: self.nodes.len() - before,
                })
            })
            .collect()
    }
}

fn ordered_signature_mismatch(
    source: &[FormalAttribute],
    target: &[FormalAttribute],
) -> Option<SignatureMismatch> {
    if source == target {
        return None;
    }
    let first_differing_index = (0..source.len().max(target.len()))
        .find(|index| source.get(*index) != target.get(*index))
        .expect("unequal signatures have a first differing position");
    Some(SignatureMismatch {
        kind: if first_differing_index < source.len().min(target.len()) {
            MismatchKind::OrderedAttribute
        } else {
            MismatchKind::Arity
        },
        source_arity: source.len(),
        target_arity: target.len(),
        first_differing_index,
        source_attribute: source
            .get(first_differing_index)
            .map(|attribute| compact_formal_attributes(std::slice::from_ref(attribute)).remove(0)),
        target_attribute: target
            .get(first_differing_index)
            .map(|attribute| compact_formal_attributes(std::slice::from_ref(attribute)).remove(0)),
    })
}

fn ordered_signature_aligned_ancestor_chain_is_compatible(
    source_index: usize,
    target_index: usize,
    nodes: &[SignatureNodeRecord],
    node_by_id: &BTreeMap<String, usize>,
) -> bool {
    let mut source = &nodes[source_index];
    let mut target = &nodes[target_index];
    loop {
        if source.artifact.statement_index != target.artifact.statement_index
            || source.artifact.role_path != target.artifact.role_path
            || source.artifact.operator_kind != target.artifact.operator_kind
            || source.exact_signature != target.exact_signature
        {
            return false;
        }
        match (
            source.artifact.parent_node_id.as_ref(),
            target.artifact.parent_node_id.as_ref(),
        ) {
            (None, None) => return source.artifact.role_path == "root",
            (Some(source_parent), Some(target_parent)) => {
                let (Some(source_parent_index), Some(target_parent_index)) =
                    (node_by_id.get(source_parent), node_by_id.get(target_parent))
                else {
                    return false;
                };
                source = &nodes[*source_parent_index];
                target = &nodes[*target_parent_index];
            }
            _ => return false,
        }
    }
}

pub(super) fn build_ordered_signatures(
    source: &LoweredProgram,
    target: &LoweredProgram,
) -> Result<String> {
    let mut builder = SignatureIndexBuilder::default();
    let source_program = builder.add_program(QuerySide::Source, source)?;
    let target_program = builder.add_program(QuerySide::Target, target)?;

    let source_by_role = builder
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.artifact.side == QuerySide::Source)
        .map(|(index, node)| {
            (
                (
                    node.artifact.statement_index,
                    node.artifact.role_path.clone(),
                ),
                index,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let target_by_role = builder
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.artifact.side == QuerySide::Target)
        .map(|(index, node)| {
            (
                (
                    node.artifact.statement_index,
                    node.artifact.role_path.clone(),
                ),
                index,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let node_by_id = builder
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| (node.artifact.node_id.clone(), index))
        .collect::<BTreeMap<_, _>>();

    let mut comparisons = Vec::new();
    let mut frontier_hints = Vec::new();
    for ((statement_index, role_path), source_index) in &source_by_role {
        let Some(target_index) = target_by_role.get(&(*statement_index, role_path.clone())) else {
            continue;
        };
        let source_node = &builder.nodes[*source_index];
        let target_node = &builder.nodes[*target_index];
        let signature_equal = source_node.exact_signature == target_node.exact_signature;
        let operator_kind_equal =
            source_node.artifact.operator_kind == target_node.artifact.operator_kind;
        comparisons.push(SignatureComparison {
            statement_index: *statement_index,
            role_path: role_path.clone(),
            source_node_id: source_node.artifact.node_id.clone(),
            target_node_id: target_node.artifact.node_id.clone(),
            source_operator_kind: source_node.artifact.operator_kind,
            target_operator_kind: target_node.artifact.operator_kind,
            operator_kind_equal,
            source_signature_id: source_node.artifact.signature_id.clone(),
            target_signature_id: target_node.artifact.signature_id.clone(),
            signature_equal,
            mismatch: ordered_signature_mismatch(
                &source_node.exact_signature,
                &target_node.exact_signature,
            ),
        });

        if !signature_equal
            || !operator_kind_equal
            || !ordered_signature_aligned_ancestor_chain_is_compatible(
                *source_index,
                *target_index,
                &builder.nodes,
                &node_by_id,
            )
        {
            continue;
        }
        let source_relational = source_node
            .artifact
            .children
            .iter()
            .filter(|child| child.edge_kind == EdgeKind::Relational)
            .map(|child| (child.role.as_str(), child.node_id.as_str()))
            .collect::<BTreeMap<_, _>>();
        let target_relational = target_node
            .artifact
            .children
            .iter()
            .filter(|child| child.edge_kind == EdgeKind::Relational)
            .map(|child| (child.role.as_str(), child.node_id.as_str()))
            .collect::<BTreeMap<_, _>>();
        let roles = source_relational
            .keys()
            .chain(target_relational.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let incompatible_relational_child_roles = roles
            .into_iter()
            .filter(|role| {
                let (Some(source_child_id), Some(target_child_id)) =
                    (source_relational.get(role), target_relational.get(role))
                else {
                    return true;
                };
                let source_child = &builder.nodes[node_by_id[*source_child_id]];
                let target_child = &builder.nodes[node_by_id[*target_child_id]];
                source_child.artifact.operator_kind != target_child.artifact.operator_kind
                    || source_child.exact_signature != target_child.exact_signature
            })
            .map(str::to_owned)
            .collect::<Vec<_>>();

        // Experimental navigation heuristic: no controlled on/off ablation has
        // yet measured whether exposing these frontier hints improves proof
        // success, search time, or token use.  Existing runs changed other
        // prompts and proof interfaces at the same time, so they cannot support
        // that causal claim.  Treat a hint only as a candidate inspection point,
        // never as semantic evidence, and revisit this mechanism after an
        // otherwise-identical ablation.
        if !incompatible_relational_child_roles.is_empty() {
            frontier_hints.push(FrontierHint {
                statement_index: *statement_index,
                role_path: role_path.clone(),
                source_node_id: source_node.artifact.node_id.clone(),
                target_node_id: target_node.artifact.node_id.clone(),
                operator_kind: source_node.artifact.operator_kind,
                signature_id: source_node.artifact.signature_id.clone(),
                incompatible_relational_child_roles,
                reason: "same aligned operator kind and exact ordered signature, with at least one direct relational child that is missing, differently shaped, or has a different exact ordered signature; navigation hint only",
            });
        }
    }

    let artifact = SignatureIndex {
        schema_version: 2,
        authority: "navigation_only; exact SQL, generated Rocq, FormalSQL semantics, and Rocq kernel checking remain authoritative; no node, comparison, or frontier hint proves query equivalence",
        derivation: "host-derived from every occurrence in the successfully lowered FormalQueryExpr trees using the same query_expr_output_signature function that lowering validates",
        occurrence_order: "deterministic preorder per side and one-based statement: visit the query node, then relational children in constructor order, then subqueries in predicate/having scalar-expression order; node IDs are S<statement>.N<preorder> and T<statement>.N<preorder>",
        signature_identity: "signature IDs are interned by exact Rust Vec<FormalAttribute>::eq over ordered names and types; digests are not used for equality",
        comparison_policy: "comparisons pair only source and target occurrences with the same one-based statementIndex and exact rolePath; signatureEqual is exact ordered attribute equality and never semantic equivalence; mismatch.firstDifferingIndex is zero-based",
        frontier_policy: "a conservative navigation hint requires every aligned ancestor from root through the candidate to have the same operator kind and exact signature, while at least one aligned direct relational child is absent, differently shaped, or signature-incompatible; hints suggest where output layout is restored but prove nothing",
        signatures: builder.signature_pool,
        source_program,
        target_program,
        nodes: builder
            .nodes
            .into_iter()
            .map(|node| node.artifact)
            .collect(),
        comparisons,
        normalization_frontier_hints: frontier_hints,
    };
    let mut bytes = serde_json::to_vec(&artifact)?;
    bytes.push(b'\n');
    String::from_utf8(bytes).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "serialized ordered-signature navigation artifact was not UTF-8: {source}"
        ))
    })
}

fn compact_tree_node(
    operator: &'static str,
    detail: String,
    children: Vec<TreeExpression>,
) -> TreeExpression {
    let node_count = 1 + children.iter().map(|child| child.node_count).sum::<usize>();
    let max_depth = 1 + children
        .iter()
        .map(|child| child.max_depth)
        .max()
        .unwrap_or(0);
    let mut expression = operator.to_owned();
    if !detail.is_empty() {
        expression.push('{');
        expression.push_str(&detail);
        expression.push('}');
    }
    if !children.is_empty() {
        expression.push('(');
        for (index, child) in children.into_iter().enumerate() {
            if index > 0 {
                expression.push(',');
            }
            expression.push_str(&child.expression);
        }
        expression.push(')');
    }
    TreeExpression {
        node_count,
        max_depth,
        expression,
    }
}

fn compact_operator_tree(tree: TreeExpression) -> CompactOperatorTree {
    CompactOperatorTree {
        node_count: tree.node_count,
        max_depth: tree.max_depth,
        expression: tree.expression,
    }
}

pub(super) fn encode_tree_value(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.') {
            encoded.push(char::from(byte));
        } else {
            encoded.push('%');
            encoded.push(char::from(HEX[usize::from(byte >> 4)]));
            encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
        }
    }
    encoded
}

fn compact_surface_query(rel: &RelExpr) -> TreeExpression {
    match rel {
        RelExpr::Bindings {
            bindings,
            body,
            output,
        } => {
            let mut children = bindings
                .iter()
                .map(|binding| compact_surface_query(&binding.rel))
                .collect::<Vec<_>>();
            children.push(compact_surface_query(body));
            compact_tree_node(
                "bindings",
                format!("out={},defs={}", output.len(), bindings.len()),
                children,
            )
        }
        RelExpr::TableScan { table, output } => compact_tree_node(
            "table_scan",
            format!(
                "out={},table={}",
                output.len(),
                encode_tree_value(&table.join("."))
            ),
            Vec::new(),
        ),
        RelExpr::QueryRef { binding, output } => compact_tree_node(
            "query_ref",
            format!(
                "out={},binding={}",
                output.len(),
                encode_tree_value(binding)
            ),
            Vec::new(),
        ),
        RelExpr::Project {
            input,
            exprs,
            correlations,
            output,
        } => compact_tree_node(
            "project",
            format!(
                "out={},exprs={},corr={}",
                output.len(),
                exprs.len(),
                correlations.len()
            ),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Filter {
            input,
            correlations,
            output,
            ..
        } => compact_tree_node(
            "filter",
            format!("out={},corr={}", output.len(), correlations.len()),
            vec![compact_surface_query(input)],
        ),
        RelExpr::NativeHaving {
            input,
            correlations,
            output,
            ..
        } => compact_tree_node(
            "native_having",
            format!("out={},corr={}", output.len(), correlations.len()),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Join {
            left,
            right,
            join_type,
            correlations,
            output,
            ..
        } => compact_tree_node(
            "join",
            format!(
                "out={},kind={join_type:?},corr={}",
                output.len(),
                correlations.len()
            ),
            vec![compact_surface_query(left), compact_surface_query(right)],
        ),
        RelExpr::Aggregate {
            input,
            group_keys,
            grouping_sets,
            agg_calls,
            output,
        } => compact_tree_node(
            "aggregate",
            format!(
                "out={},keys={},sets={},aggs={}",
                output.len(),
                group_keys.len(),
                grouping_sets.len(),
                agg_calls.len()
            ),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Distinct { input, output } => compact_tree_node(
            "distinct",
            format!("out={}", output.len()),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Sort {
            input,
            collation,
            fetch,
            offset,
            output,
        } => compact_tree_node(
            "sort",
            format!(
                "out={},keys={},fetch={},offset={}",
                output.len(),
                collation.len(),
                fetch.is_some(),
                offset.is_some()
            ),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Set {
            op,
            all,
            inputs,
            output,
        } => compact_tree_node(
            "set",
            format!("out={},op={op:?},all={all}", output.len()),
            inputs.iter().map(compact_surface_query).collect(),
        ),
        RelExpr::Values { rows, output } => compact_tree_node(
            "values",
            format!("out={},rows={}", output.len(), rows.len()),
            Vec::new(),
        ),
    }
}

fn final_output_is_canonicalized(query: &FormalQueryExpr) -> bool {
    fn select_is_canonical(select: &[FormalScalarSelectItem]) -> bool {
        !select.is_empty()
            && select
                .iter()
                .enumerate()
                .all(|(index, item)| item.alias == format!("__logos_output_{index}"))
    }

    match query {
        FormalQueryExpr::Projection { select, .. } => select_is_canonical(select),
        _ => false,
    }
}

fn emitted_rocq_symbols(query_module: &str) -> Vec<String> {
    let mut symbols = BTreeSet::new();
    for line in query_module.lines() {
        let Some(rest) = line.strip_prefix("Definition ") else {
            continue;
        };
        let name = rest
            .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .next()
            .unwrap_or_default();
        if !name.is_empty() {
            symbols.insert(name.to_owned());
        }
    }
    symbols.into_iter().collect()
}

fn build_program_shape(
    side: QuerySide,
    exact_statements: &[&str],
    ir_queries: &[logos_ir::ir::Query],
    lowered: &LoweredProgram,
    emitted_symbols: &BTreeSet<String>,
) -> Result<Vec<StatementShape<CompactOperatorTree>>> {
    if exact_statements.len() != ir_queries.len()
        || exact_statements.len() != lowered.statements.len()
    {
        return Err(Error::ProofAgentCommand(format!(
            "cannot build {side} query context: exact SQL, typed IR, and lowered statement counts differ ({}, {}, {})",
            exact_statements.len(),
            ir_queries.len(),
            lowered.statements.len()
        )));
    }
    let singleton = exact_statements.len() == 1;
    exact_statements
        .iter()
        .zip(ir_queries)
        .zip(&lowered.statements)
        .enumerate()
        .map(|(index, ((exact_sql, ir_query), lowered_query))| {
            build_statement_shape(
                side,
                index,
                singleton,
                exact_sql,
                ir_query,
                lowered_query,
                emitted_symbols,
            )
        })
        .collect()
}

fn build_statement_shape(
    side: QuerySide,
    index: usize,
    singleton: bool,
    exact_sql: &str,
    ir_query: &logos_ir::ir::Query,
    lowered: &LoweredQuery,
    emitted_symbols: &BTreeSet<String>,
) -> Result<StatementShape<CompactOperatorTree>> {
    let query = lowered.query_expr.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "cannot build {side} query context for statement {}: FormalSQL lowering is incomplete",
            index + 1
        ))
    })?;
    let output_signature = lowered.output_signature.as_deref().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "cannot build {side} query context for statement {}: output signature is incomplete",
            index + 1
        ))
    })?;
    let frontend_sql = ir_query.source_sql.as_deref().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "cannot build {side} query context for statement {}: typed IR has no source SQL binding",
            index + 1
        ))
    })?;
    let suffix = if singleton {
        String::new()
    } else {
        format!("_{index}")
    };
    let root_symbol = format!("{side}_query_expr{suffix}");
    let output_signature_symbol = format!("{side}_output_signature{suffix}");
    for required in [&root_symbol, &output_signature_symbol] {
        if !emitted_symbols.contains(required) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitted Queries.v is missing required symbol {required}"
            )));
        }
    }
    let typed_frontend_tree = compact_operator_tree(compact_surface_query(&ir_query.rel));

    Ok(StatementShape {
        statement_index: index + 1,
        exact_sql_sha256: sha256_hex(exact_sql.as_bytes()),
        frontend_sql_sha256: sha256_hex(frontend_sql.as_bytes()),
        exact_frontend_bytes_equal: exact_sql == frontend_sql,
        emitted_rocq_root_symbol: root_symbol,
        emitted_rocq_output_signature_symbol: output_signature_symbol,
        final_output_canonicalization: final_output_is_canonicalized(query),
        output_signature: compact_formal_attributes(output_signature),
        typed_frontend_tree,
    })
}

fn graph_tree_references(tree: &str) -> Vec<String> {
    tree.split(|character: char| {
        !(character.is_ascii_alphanumeric() || matches!(character, '_' | '@'))
    })
    .filter_map(|token| token.strip_prefix('@'))
    .filter(|symbol| !symbol.is_empty())
    .map(str::to_owned)
    .collect()
}

fn definition_graph_has_cycle(edges: &BTreeMap<String, Vec<String>>) -> bool {
    fn visit(
        symbol: &str,
        edges: &BTreeMap<String, Vec<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
    ) -> bool {
        if visited.contains(symbol) {
            return false;
        }
        if !visiting.insert(symbol.to_owned()) {
            return true;
        }
        if edges.get(symbol).is_some_and(|targets| {
            targets
                .iter()
                .any(|target| visit(target, edges, visiting, visited))
        }) {
            return true;
        }
        visiting.remove(symbol);
        visited.insert(symbol.to_owned());
        false
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    edges
        .keys()
        .any(|symbol| visit(symbol, edges, &mut visiting, &mut visited))
}

fn validate_graph_statement_bindings(
    side: QuerySide,
    bindings: &[FormalQueryStatementSymbols],
    statements: &[StatementShape<CompactOperatorTree>],
    graph_definitions: &BTreeSet<String>,
    emitted_symbols: &BTreeSet<String>,
) -> Result<()> {
    if bindings.len() != statements.len() {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: emitter graph has {} {side} statement bindings for {} lowered statements",
            bindings.len(),
            statements.len()
        )));
    }
    for (index, (binding, statement)) in bindings.iter().zip(statements).enumerate() {
        let position = index + 1;
        if binding.statement_index != position
            || statement.statement_index != position
            || binding.root_symbol != statement.emitted_rocq_root_symbol
            || binding.output_signature_symbol != statement.emitted_rocq_output_signature_symbol
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter-owned {side} statement binding {position} disagrees with the typed lowering or emitted symbol contract"
            )));
        }
        if !graph_definitions.contains(&binding.root_symbol)
            || !emitted_symbols.contains(&binding.output_signature_symbol)
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter-owned {side} statement binding {position} does not resolve to its generated Rocq definitions"
            )));
        }
    }
    Ok(())
}

fn validate_emitted_definition_graph(
    graph: &FormalQueryDefinitionGraph,
    source_program: &[StatementShape<CompactOperatorTree>],
    target_program: &[StatementShape<CompactOperatorTree>],
    emitted_symbols: &BTreeSet<String>,
) -> Result<()> {
    if graph.schema_version != 2 || graph.notation.trim().is_empty() {
        return Err(Error::ProofAgentCommand(
            "query context drift: emitter definition graph has an unsupported schema or empty notation"
                .to_owned(),
        ));
    }
    let mut resolvable = BTreeSet::new();
    let mut graph_definitions = BTreeSet::new();
    for helper in &graph.opaque_helper_symbols {
        if helper.is_empty()
            || !resolvable.insert(helper.clone())
            || !emitted_symbols.contains(helper)
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter graph helper {helper:?} is duplicate, empty, or absent from Queries.v"
            )));
        }
    }
    for definition in &graph.definitions {
        if definition.symbol.is_empty()
            || definition.tree.trim().is_empty()
            || !resolvable.insert(definition.symbol.clone())
            || !graph_definitions.insert(definition.symbol.clone())
            || !emitted_symbols.contains(&definition.symbol)
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter graph definition {:?} is duplicate, empty, or absent from Queries.v",
                definition.symbol
            )));
        }
    }
    let mut edges = BTreeMap::new();
    for definition in &graph.definitions {
        let references = graph_tree_references(&definition.tree);
        for reference in &references {
            if !resolvable.contains(reference) || !emitted_symbols.contains(reference) {
                return Err(Error::ProofAgentCommand(format!(
                    "query context drift: emitter graph definition {} has unresolved Rocq reference @{reference}",
                    definition.symbol
                )));
            }
        }
        edges.insert(
            definition.symbol.clone(),
            references
                .into_iter()
                .filter(|reference| graph_definitions.contains(reference))
                .collect(),
        );
    }
    if definition_graph_has_cycle(&edges) {
        return Err(Error::ProofAgentCommand(
            "query context drift: emitter definition graph contains a reference cycle".to_owned(),
        ));
    }
    validate_graph_statement_bindings(
        QuerySide::Source,
        &graph.source_statements,
        source_program,
        &graph_definitions,
        emitted_symbols,
    )?;
    validate_graph_statement_bindings(
        QuerySide::Target,
        &graph.target_statements,
        target_program,
        &graph_definitions,
        emitted_symbols,
    )?;
    Ok(())
}

pub(super) fn build_query_shape(
    input: &VerificationInput,
    ir_input: &VerificationIr,
    lowering: &ProofLoweringReport,
    schema_module: &str,
    queries_module: &str,
) -> Result<NavigationArtifacts> {
    let emitted_rocq_symbols = emitted_rocq_symbols(queries_module);
    let emitted_symbol_set = emitted_rocq_symbols
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let has_query_bindings = lowering_programs_have_query_bindings(lowering);
    let required_program_symbols = if has_query_bindings {
        ["source_bound_query_program", "target_bound_query_program"]
    } else {
        ["source_query_program", "target_query_program"]
    };
    for required in required_program_symbols.into_iter().chain([
        "source_program_output_signatures",
        "target_program_output_signatures",
    ]) {
        if !emitted_symbol_set.contains(required) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitted Queries.v is missing required program symbol {required}"
            )));
        }
    }
    let emitted_query_module = lowering.query_module.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(
            "cannot build query context: FormalSQL emitter produced no query module".to_owned(),
        )
    })?;
    if emitted_query_module.rocq_module != queries_module {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: lowering query module digest {} differs from emitted Queries.v digest {}",
            sha256_hex(emitted_query_module.rocq_module.as_bytes()),
            sha256_hex(queries_module.as_bytes())
        )));
    }
    let source_exact = input.source_sql_program()?;
    let target_exact = input.target_sql_program()?;
    let source_program = build_program_shape(
        QuerySide::Source,
        &source_exact,
        ir_input.source_program_ir(),
        &lowering.source,
        &emitted_symbol_set,
    )?;
    let target_program = build_program_shape(
        QuerySide::Target,
        &target_exact,
        ir_input.target_program_ir(),
        &lowering.target,
        &emitted_symbol_set,
    )?;
    validate_emitted_definition_graph(
        &emitted_query_module.definition_graph,
        &source_program,
        &target_program,
        &emitted_symbol_set,
    )?;
    let ordered_signatures_text = build_ordered_signatures(&lowering.source, &lowering.target)?;
    let emitted_definition_graph =
        compact_definition_graph(&emitted_query_module.definition_graph)?;
    let (typed_frontend_skeleton, source_program, target_program) =
        compact_frontend_programs(&source_program, &target_program)?;
    let artifact = QueryShape {
        schema_version: 3,
        authority: "navigation_only; exact SQL is pipeline input and Schema.v, Queries.v, Goal.v, FormalSQL, and the Rocq kernel are authoritative",
        frontend_sql_role: "Calcite-normalized source spelling attached to the typed IR; its digest and exact-byte comparison are informational, never a replacement for exact source.sql or target.sql",
        operator_tree_notation: "typed frontend and emitted-definition trees use lossless shared structural DAGs; node heads retain the previous preorder Operator{k=v,...} spelling, with nonnumeric frontend values encoded as UTF-8 bytes (%HH). Root mappings and ordered children reconstruct every previous tree byte-for-byte; DAG sharing is navigation-only and proves no equality",
        source_sql_sha256: sha256_hex(input.source_sql().as_bytes()),
        target_sql_sha256: sha256_hex(input.target_sql().as_bytes()),
        schema_module_sha256: sha256_hex(schema_module.as_bytes()),
        queries_module_sha256: sha256_hex(queries_module.as_bytes()),
        emitted_rocq_symbols,
        emitted_definition_graph,
        typed_frontend_skeleton,
        source_program,
        target_program,
    };
    let mut bytes = serde_json::to_vec(&artifact)?;
    bytes.push(b'\n');
    let text = String::from_utf8(bytes).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "serialized query-shape artifact was not UTF-8: {source}"
        ))
    })?;
    Ok(NavigationArtifacts {
        text,
        ordered_signatures_text,
    })
}
