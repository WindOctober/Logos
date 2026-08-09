use serde::de::{self, Deserializer};
use serde::{Deserialize, Serialize};

use crate::ir::{ForeignKeyConstraint, SqlEnvironment, UniqueConstraint};

pub mod convert;
mod query_shape;
pub mod scalar;
mod source_lexer;
pub mod ty;

pub use convert::{convert_file, convert_raw_file};

/// Calcite's bit-set iteration order is the sole generated grouping-key
/// order. Reject hand-built or forged arrays that are duplicated or out of
/// that canonical ascending order before any semantic consumer uses them.
pub(super) fn group_set_is_canonical(value: &[usize]) -> bool {
    value.windows(2).all(|pair| pair[0] < pair[1])
}

pub(super) fn group_sets_are_canonical(values: &[Vec<usize>]) -> bool {
    values.iter().all(|value| group_set_is_canonical(value))
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteFile {
    #[serde(default)]
    pub environment: SqlEnvironment,
    #[serde(default)]
    pub schema: Vec<CalciteTable>,
    #[serde(default)]
    pub queries: Vec<CalciteQuery>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteTable {
    pub name: String,
    #[serde(default)]
    pub columns: Vec<CalciteColumn>,
    #[serde(default, skip_serializing_if = "CalciteTableConstraints::is_empty")]
    pub constraints: CalciteTableConstraints,
}

#[derive(Debug, Clone, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteTableConstraints {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub not_null: Vec<String>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "deserialize_nonempty_calcite_primary_key"
    )]
    pub primary_key: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unique: Vec<UniqueConstraint>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub foreign_keys: Vec<ForeignKeyConstraint>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub checks: Vec<CalciteCheckConstraint>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unique_indexes: Vec<CalciteUniqueIndexConstraint>,
}

fn deserialize_nonempty_calcite_primary_key<'de, D>(
    deserializer: D,
) -> std::result::Result<Option<Vec<String>>, D::Error>
where
    D: Deserializer<'de>,
{
    let primary_key = Option::<Vec<String>>::deserialize(deserializer)?;
    if primary_key.as_ref().is_some_and(Vec::is_empty) {
        return Err(de::Error::custom(
            "primaryKey must contain at least one column when present",
        ));
    }
    Ok(primary_key)
}

impl CalciteTableConstraints {
    pub fn is_empty(&self) -> bool {
        self.not_null.is_empty()
            && self.primary_key.is_none()
            && self.unique.is_empty()
            && self.foreign_keys.is_empty()
            && self.checks.is_empty()
            && self.unique_indexes.is_empty()
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteCheckConstraint {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub expression: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteUniqueIndexConstraint {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub terms: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub predicate: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteColumn {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(default)]
    pub full_type: Option<String>,
    #[serde(default)]
    pub declared_type: Option<String>,
    #[serde(default)]
    pub explicit_collation: bool,
    #[serde(default)]
    pub precision: Option<i32>,
    #[serde(default)]
    pub scale: Option<i32>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteQuery {
    pub sql: String,
    pub rel: Option<CalciteRel>,
    pub source_analysis_error: Option<CalciteQueryAnalysisError>,
    pub source_ambiguous_column_error: Option<CalciteAmbiguousColumnAnalysisError>,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteQueryAnalysisError {
    pub kind: String,
    pub sql_state: String,
    pub query_block_id: String,
    pub source_query_block_sql: String,
    pub source_order_item_node_id: String,
    pub source_order_item_sql: String,
    pub source_order_list_node_id: String,
    pub source_order_list_sql: String,
    pub source_order_expression_node_id: String,
    pub source_order_expression_sql: String,
    pub source_alias_reference_node_id: String,
    pub source_alias_reference_sql: String,
    pub source_output_alias_node_id: String,
    pub source_output_alias_sql: String,
    pub source_from_node_id: String,
    pub source_from_sql: String,
    pub output_alias: String,
    #[serde(default)]
    pub input_bindings: Vec<CalciteOrderByAliasInputBinding>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteAmbiguousColumnAnalysisError {
    pub kind: String,
    pub sql_state: String,
    pub query_block_id: String,
    pub source_query_block_sql: String,
    pub source_identifier_node_id: String,
    pub source_identifier_sql: String,
    pub source_relation_node_id: String,
    pub source_relation_sql: String,
    pub identifier_name: String,
    pub identifier_quoted: bool,
    pub duplicate_count: usize,
    #[serde(default)]
    pub matching_outputs: Vec<CalciteAmbiguousColumnOutput>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteAmbiguousColumnOutput {
    pub output_index: usize,
    pub output_name: String,
    pub source_output_item_node_id: String,
    pub source_output_item_sql: String,
    pub source_origin_relation_node_id: String,
    pub source_origin_relation_sql: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteOrderByAliasInputBinding {
    pub source_relation_node_id: String,
    pub source_relation_sql: String,
    pub source_table_node_id: String,
    pub source_table_sql: String,
    pub source_alias_node_id: Option<String>,
    pub source_alias_sql: Option<String>,
    #[serde(default)]
    pub base_table: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteRel {
    #[serde(rename = "type")]
    pub rel_type: String,
    #[serde(default)]
    pub row_type: Vec<CalciteField>,
    #[serde(default)]
    pub variables_set: Vec<String>,
    pub correlation_id: Option<String>,
    #[serde(default)]
    pub required_columns: Vec<usize>,
    #[serde(default)]
    pub inputs: Vec<CalciteRel>,

    /// Internal marker installed only after all source-provenance validation
    /// succeeds. It is never accepted from or emitted to the wrapper JSON.
    #[serde(skip)]
    pub(crate) shared_query_ref: Option<CalciteSharedQueryRef>,

    /// Lexical source-query identity emitted from the independently parsed
    /// PostgreSQL source AST.  This is deliberately absent when Calcite's
    /// relational node cannot be aligned with one exact source query block.
    pub source_query_block_id: Option<String>,
    /// Root query-block identity for this independently traversed relational
    /// query. Derived-table descendants retain the outer root, while a Rex
    /// subquery starts its own relational root.
    pub source_root_query_block_id: Option<String>,
    /// Exact relational source node selected by the wrapper's independent
    /// source-AST traversal.  These fields are retained for validating
    /// operator-local attestations; their absence must never be reconstructed
    /// from the statement text downstream.
    pub source_sql: Option<String>,
    pub source_kind: Option<String>,
    pub source_operator: Option<String>,
    pub source_node_id: Option<String>,
    /// Byte-exact original-statement fragment selected by `source_node_id`.
    /// Rendered `source_sql` remains structural metadata only.
    pub source_text: Option<String>,
    /// Direct source clause owning a Filter (`WHERE` or `HAVING`).  Nested
    /// scalar provenance never supplies this authorization marker.
    pub source_clause: Option<String>,
    /// Exact independently parsed WHERE ownership for this LogicalFilter.
    /// Ordinary scalar provenance and `source_clause` remain diagnostic; only
    /// this closed, converter-validated payload establishes the declarative
    /// pre-group WHERE role and its source-bound analysis errors.
    pub source_where: Option<CalciteWhereAttestation>,
    /// Exact native post-aggregate HAVING identity attested from one source
    /// query block and the positional RexInputRef leaves of its generated
    /// condition.  This is deliberately distinct from planner pushdown.
    pub source_native_having: Option<CalciteNativeHavingAttestation>,

    #[serde(default)]
    pub table: Vec<String>,
    /// Exact direct base-relation identity for every LogicalTableScan.
    /// This binds the generated catalog name to the original table token and
    /// retains the complete visible relation/alias node.
    pub source_table: Option<CalciteSourceTableAttestation>,
    #[serde(default)]
    pub project_rex: Vec<CalciteRex>,
    pub condition_rex: Option<CalciteRex>,
    pub join_type: Option<String>,
    pub source_join_type: Option<String>,
    pub source_join_syntax: Option<String>,
    pub source_join_syntax_node_id: Option<String>,
    pub source_join_syntax_text: Option<String>,
    /// Exact ordered source operands and ON/NONE condition owned by one
    /// declarative LogicalJoin.
    pub source_join: Option<CalciteSourceJoinAttestation>,
    /// Exact lexical CTE use, when a generated relational input is a clone of
    /// one WITH definition rather than a direct child of the current query.
    #[serde(default)]
    pub source_input_cte_uses: Vec<Option<CalciteSourceCteUse>>,
    pub group_set: Option<Vec<usize>>,
    pub group_sets: Option<Vec<Vec<usize>>>,
    /// Independently parsed source authority for one identifier-based ROLLUP
    /// or GROUPING SETS query block. Calcite group bitsets are accepted as
    /// PostgreSQL semantics only when this payload validates exactly.
    pub source_grouping: Option<CalciteSourceGroupingAttestation>,
    /// Exact source authority for a plain SELECT DISTINCT represented by
    /// Calcite as a call-free Aggregate over every output position.  This is
    /// separate from GROUP BY because both operators otherwise share the same
    /// generated relational shape.
    pub source_distinct: Option<CalciteSourceDistinctAttestation>,
    #[serde(default)]
    pub source_group_indexes: Vec<usize>,
    pub source_grouping_sets: Option<Vec<Vec<usize>>>,
    #[serde(default)]
    pub agg_call_details: Vec<CalciteAggregateCall>,
    pub set_op: Option<String>,
    pub all: Option<bool>,
    #[serde(default)]
    pub collation: Vec<CalciteCollation>,
    /// Exact declarative ORDER BY authority for one LogicalSort.  Calcite's
    /// positional collation is accepted only after every key is rebound to
    /// the independently parsed query, ordered source item, expression,
    /// direction, and PostgreSQL NULL placement.
    pub source_order: Option<CalciteSourceOrderAttestation>,
    pub fetch_rex: Option<CalciteRex>,
    pub offset_rex: Option<CalciteRex>,
    pub tuples: Option<Vec<Vec<CalciteRex>>>,
}

#[derive(Debug, Clone)]
pub(crate) struct CalciteSharedQueryRef {
    pub binding: String,
    pub output: Vec<crate::ir::Column>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceTableAttestation {
    pub kind: String,
    pub query_block_id: String,
    /// Stable identity of this exact lexical relation occurrence.  The
    /// current wrapper deliberately duplicates the relation span here so a
    /// downstream lineage edge cannot borrow an otherwise identical scan.
    #[serde(default)]
    pub relation_occurrence_id: String,
    pub relation_node_id: String,
    pub relation_text: String,
    pub table_node_id: String,
    pub table_text: String,
    #[serde(default)]
    pub table_names: Vec<String>,
    #[serde(default)]
    pub table_quoted: Vec<bool>,
    pub alias_node_id: Option<String>,
    pub alias_text: Option<String>,
    #[serde(default)]
    pub alias_names: Vec<String>,
    #[serde(default)]
    pub alias_quoted: Vec<bool>,
    /// Ordered explicit prefix supplied by a PostgreSQL relation alias column
    /// list.  Empty means that every public name is inherited from the base
    /// row; it never means that output lineage is unavailable.
    #[serde(default)]
    pub column_aliases: Vec<CalciteSourceTableColumnAlias>,
    /// Complete ordered binding from every generated scan output to this
    /// exact relation occurrence and its visible PostgreSQL column name.
    #[serde(default)]
    pub output_lineage: Vec<CalciteSourceTableOutputLineage>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceTableColumnAlias {
    pub output_index: usize,
    pub node_id: String,
    pub text: String,
    #[serde(default)]
    pub names: Vec<String>,
    #[serde(default)]
    pub quoted: Vec<bool>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceTableOutputLineage {
    pub output_index: usize,
    pub kind: String,
    pub relation_occurrence_id: String,
    pub base_column_index: usize,
    pub base_column_name: String,
    pub visible_column_name: String,
    pub generated_field_name: String,
    pub explicit_column_alias: bool,
    pub column_alias_node_id: Option<String>,
    pub column_alias_text: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceJoinAttestation {
    pub kind: String,
    pub query_block_id: String,
    pub join_node_id: String,
    pub join_text: String,
    pub left_node_id: String,
    pub left_text: String,
    pub right_node_id: String,
    pub right_text: String,
    pub condition_type: String,
    pub condition_node_id: Option<String>,
    pub condition_text: Option<String>,
    pub left_cte_use: Option<CalciteSourceCteUse>,
    pub right_cte_use: Option<CalciteSourceCteUse>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceCteUse {
    pub kind: String,
    pub relation_node_id: String,
    pub relation_text: String,
    pub reference_node_id: String,
    pub reference_text: String,
    pub definition_name_node_id: String,
    pub definition_name_text: String,
    pub definition_query_node_id: String,
    pub definition_query_text: String,
    pub definition_item_node_id: String,
    pub definition_item_text: String,
    pub definition_list_node_id: String,
    pub definition_list_text: String,
    pub definition_body_node_id: String,
    pub definition_body_text: String,
    pub definition_with_node_id: String,
    pub definition_with_text: String,
    pub reference_scope_kind: String,
    pub reference_scope_node_id: String,
    pub reference_scope_text: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceOrderAttestation {
    pub kind: String,
    pub query_node_id: String,
    pub query_text: String,
    pub order_list_node_id: String,
    pub order_list_text: String,
    #[serde(default)]
    pub items: Vec<CalciteSourceOrderItem>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceOrderItem {
    pub item_node_id: String,
    pub item_text: String,
    pub expression_node_id: String,
    pub expression_text: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceGroupingAttestation {
    pub kind: String,
    pub query_block_id: String,
    pub source_select_node_id: String,
    pub source_select_text: String,
    pub source_select_sql: String,
    pub source_group_node_id: String,
    pub source_group_text: String,
    pub source_group_sql: String,
    #[serde(default)]
    pub group_indexes: Vec<usize>,
    #[serde(default)]
    pub grouping_sets: Vec<Vec<usize>>,
    /// Exact source grouping expressions, preserving the source grouping-set
    /// nesting and every repeated occurrence.  `source_operand_indexes` has
    /// the identical shape and binds each expression to one generated
    /// Aggregate-input position.  Ordinary GROUP BY and ROLLUP each use one
    /// source row; GROUPING SETS uses one row per syntactic grouping set.
    #[serde(default)]
    pub source_operand_indexes: Vec<Vec<usize>>,
    #[serde(default)]
    pub source_operands: Vec<Vec<CalciteSourceNode>>,
    pub source_has_where: bool,
    pub source_has_having: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceDistinctAttestation {
    pub kind: String,
    pub query_block_id: String,
    pub source_select_node_id: String,
    pub source_select_text: String,
    #[serde(default)]
    pub group_indexes: Vec<usize>,
    #[serde(default)]
    pub grouping_sets: Vec<Vec<usize>>,
    pub input_output_arity: usize,
    pub output_arity: usize,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteWhereAttestation {
    pub kind: String,
    pub query_block_id: String,
    pub owner_node_id: String,
    pub source_condition_node_id: String,
    pub source_condition_sql: String,
    pub source_condition_kind: String,
    pub source_condition_operator: Option<String>,
    pub generated_condition_sql: String,
    pub filter_output_arity: usize,
    pub input_output_arity: usize,
    #[serde(default)]
    pub variables_set: Vec<String>,
    #[serde(default)]
    pub input_bindings: Vec<CalciteWhereInputBinding>,
    /// Closed, path-local PostgreSQL analysis errors that Calcite accepted
    /// only after changing the source operand types.  These are emitted by
    /// the wrapper while it still has both the independently parsed source
    /// AST and the generated Rex tree, then revalidated in full by the Rust
    /// importer before becoming typed provenance.
    #[serde(default)]
    pub analysis_errors: Vec<CalciteWhereAnalysisErrorBinding>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteWhereInputBinding {
    pub path: String,
    pub input_index: usize,
    pub source_sql: String,
    pub source_relation_node_id: String,
    pub source_relation_sql: String,
    #[serde(default)]
    pub base_table: Vec<String>,
    pub table_field_index: usize,
    pub base_field_name: String,
    pub generated_field_name: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteWhereAnalysisErrorBinding {
    pub kind: String,
    pub rex_path: String,
    pub identifier_operand: usize,
    pub literal_operand: usize,
    pub generated_comparison_sql: String,
    pub input_index: usize,
    #[serde(default)]
    pub base_table: Vec<String>,
    pub table_field_index: usize,
    pub base_field_name: String,
    pub source_literal_canonical_value: String,
    pub generated_literal_canonical_value: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteNativeHavingAttestation {
    pub kind: String,
    pub query_block_id: String,
    pub owner_node_id: String,
    pub source_owner_sql: String,
    pub source_owner_text: String,
    pub source_select_sql: String,
    pub source_select_text: String,
    pub source_condition_node_id: String,
    pub source_condition_sql: String,
    pub source_condition_text: String,
    pub generated_condition_sql: String,
    pub aggregate_output_arity: usize,
    pub aggregate_call_count: usize,
    #[serde(default)]
    pub operand_bindings: Vec<CalciteNativeHavingOperandBinding>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteNativeHavingOperandBinding {
    pub path: String,
    pub aggregate_output_index: usize,
    pub source_sql: String,
    pub source_kind: String,
    pub source_operator: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteRex {
    pub kind: Option<String>,
    pub class: Option<String>,
    pub text: Option<String>,
    #[serde(rename = "type")]
    pub ty: Option<String>,
    #[serde(default)]
    pub nullable: bool,
    pub full_type: Option<String>,
    pub precision: Option<i32>,
    pub scale: Option<i32>,
    pub source_sql: Option<String>,
    /// Exact parser-position identity for `source_sql` in the original
    /// statement.  This remains absent for generated or otherwise unbound
    /// source associations.
    pub source_node_id: Option<String>,
    /// Byte-exact statement fragment selected by `source_node_id`.
    pub source_text: Option<String>,
    /// Closed exact-source evidence for a generated Rex subtree that Calcite
    /// expanded through one directly nested derived-table output alias. The
    /// ordinary source identity remains the projected definition; this
    /// payload proves the otherwise out-of-parent alias boundary.
    pub source_expansion: Option<CalciteProjectedSourceExpansion>,
    pub source_kind: Option<String>,
    pub source_operator: Option<String>,
    /// Function named by an independently parsed source OVER expression.
    /// Calcite may replace that source function with a generated Rex root
    /// (notably CASE for nullable window SUM), so `operator` alone is not
    /// authoritative for PostgreSQL language semantics.
    pub source_window_function: Option<String>,
    #[serde(default)]
    pub source_identifier_names: Vec<String>,
    #[serde(default)]
    pub source_identifier_quoted: Vec<bool>,
    pub charset: Option<String>,
    pub type_collation: Option<String>,
    pub index: Option<usize>,
    pub field_name: Option<String>,
    pub field_index: Option<usize>,
    pub reference_expr: Option<Box<CalciteRex>>,
    pub correlation_id: Option<i32>,
    pub correlation_name: Option<String>,
    pub operator: Option<String>,
    pub op_kind: Option<String>,
    #[serde(default)]
    pub operands: Vec<CalciteRex>,
    pub literal_type_name: Option<String>,
    pub literal_value: Option<String>,
    pub literal_value2: Option<String>,
    pub literal_value_as_string: Option<String>,
    pub date_literal: Option<String>,
    pub time_literal: Option<String>,
    pub timestamp_literal: Option<String>,
    pub interval_type_name: Option<String>,
    pub interval_literal: Option<String>,
    pub interval_internal_value: Option<String>,
    pub interval_unit: Option<String>,
    /// Closed evidence for a structurally simple, non-sliced IN subquery
    /// whose PostgreSQL ORDER BY Calcite removes. The importer validates the
    /// source identities and schema-bound fields before reconstructing Sort.
    pub source_in_subquery_order: Option<CalciteInSubqueryOrderAttestation>,
    /// Complete operator-local, ordered-column correspondence for the
    /// generated relational tree owned by a RexSubQuery.  Rust validates this
    /// recursively before it can replace the older tree-isomorphism check.
    pub source_rel_correspondence: Option<Box<CalciteSourceRelCorrespondence>>,
    pub subquery_rel: Option<Box<CalciteRel>>,
    pub window: Option<Box<CalciteWindow>>,
    pub distinct: Option<bool>,
    pub ignore_nulls: Option<bool>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceRelCorrespondence {
    pub kind: String,
    pub source_role: String,
    pub generated_type: String,
    pub query_block_id: String,
    pub source_node_id: String,
    pub source_text: String,
    #[serde(default)]
    pub output_lineage: Vec<CalciteSourceRelOutputLineage>,
    #[serde(default)]
    pub inputs: Vec<CalciteSourceRelInput>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceRelOutputLineage {
    pub output_index: usize,
    pub kind: String,
    pub generated_field_name: String,
    pub source_node_id: Option<String>,
    pub source_text: Option<String>,
    #[serde(default)]
    pub inputs: Vec<CalciteSourceRelInputColumn>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceRelInputColumn {
    pub input_ordinal: usize,
    pub input_output_index: usize,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceRelInput {
    pub input_ordinal: usize,
    pub correspondence: Box<CalciteSourceRelCorrespondence>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteProjectedSourceExpansion {
    pub kind: String,
    pub reference_node_id: String,
    pub reference_text: String,
    pub definition_node_id: String,
    pub definition_text: String,
    pub project_item_node_id: String,
    pub project_item_text: String,
    pub output_alias_node_id: String,
    pub output_alias_text: String,
    pub inner_select_node_id: String,
    pub inner_select_text: String,
    pub outer_from_node_id: String,
    pub outer_from_text: String,
    pub outer_select_node_id: String,
    pub outer_select_text: String,
    /// Exact public output ordinal for a direct CTE expansion.  Derived-table
    /// expansions leave this absent.
    pub public_output_index: Option<usize>,
    /// Complete lexical CTE-use edge duplicated at the scalar association.
    /// The importer accepts it only when it is byte-for-byte equal to, and
    /// independently validates against, the containing Project's unique
    /// `sourceInputCteUses` edge.
    pub cte_use: Option<CalciteSourceCteUse>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteInSubqueryOrderAttestation {
    pub kind: String,
    pub query_block_id: String,
    pub select_node_id: String,
    pub select_text: String,
    pub order_by_node_id: String,
    pub order_by_text: String,
    pub source_select_sql: String,
    pub source_order_by_sql: String,
    pub project_item_node_id: String,
    pub project_item_text: String,
    pub source_project_item_sql: String,
    pub project_input_index: usize,
    pub project_base_field_name: String,
    pub project_field_type: String,
    pub project_field_nullable: bool,
    pub order_item_node_id: String,
    pub order_item_text: String,
    pub source_order_item_sql: String,
    pub direction: String,
    pub null_direction: String,
    pub source_relation_node_id: String,
    pub source_relation_text: String,
    pub source_relation_sql: String,
    #[serde(default)]
    pub base_table: Vec<String>,
    pub order_field_index: usize,
    pub order_base_field_name: String,
    pub order_field_type: String,
    pub order_field_nullable: bool,
    pub generated_project_arity: usize,
    pub generated_sort_input_arity: usize,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteAggregateCall {
    pub text: String,
    pub function: String,
    pub kind: String,
    #[serde(default)]
    pub distinct: bool,
    #[serde(default)]
    pub approximate: bool,
    #[serde(default)]
    pub ignore_nulls: bool,
    pub filter_arg: Option<i32>,
    #[serde(default)]
    pub arg_list: Vec<usize>,
    #[serde(default)]
    pub distinct_keys: Vec<usize>,
    #[serde(default)]
    pub collation: Vec<CalciteCollation>,
    #[serde(rename = "type")]
    pub ty: Option<String>,
    pub full_type: Option<String>,
    pub precision: Option<i32>,
    pub scale: Option<i32>,
    pub charset: Option<String>,
    pub type_collation: Option<String>,
    pub source_sql: Option<String>,
    pub source_node_id: Option<String>,
    pub source_text: Option<String>,
    pub source_kind: Option<String>,
    pub source_operator: Option<String>,
    pub source_distinct: Option<bool>,
    #[serde(default)]
    pub source_operands: Vec<CalciteSourceNode>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteSourceNode {
    pub source_sql: Option<String>,
    /// Exact parser-position identity for this source AST node in the
    /// original statement, when the wrapper could retain one.
    pub source_node_id: Option<String>,
    /// Byte-exact statement fragment selected by `source_node_id`.
    pub source_text: Option<String>,
    pub source_kind: Option<String>,
    pub source_operator: Option<String>,
    #[serde(default)]
    pub source_identifier_names: Vec<String>,
    #[serde(default)]
    pub source_identifier_quoted: Vec<bool>,
    #[serde(default)]
    pub source_operands: Vec<CalciteSourceNode>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteWindow {
    #[serde(default)]
    pub partition_keys: Vec<CalciteRex>,
    #[serde(default)]
    pub order_keys: Vec<CalciteWindowOrderKey>,
    #[serde(default)]
    pub is_rows: bool,
    pub lower_bound: Option<Box<CalciteWindowBound>>,
    pub upper_bound: Option<Box<CalciteWindowBound>>,
    pub exclude: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteWindowOrderKey {
    pub expr: CalciteRex,
    pub direction: String,
    pub null_direction: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteWindowBound {
    pub text: String,
    #[serde(default)]
    pub unbounded: bool,
    #[serde(default)]
    pub unbounded_preceding: bool,
    #[serde(default)]
    pub unbounded_following: bool,
    #[serde(default)]
    pub preceding: bool,
    #[serde(default)]
    pub following: bool,
    #[serde(default)]
    pub current_row: bool,
    pub offset: Option<Box<CalciteRex>>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CalciteField {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(default)]
    pub nullable: bool,
    pub full_type: Option<String>,
    pub precision: Option<i32>,
    pub scale: Option<i32>,
    pub charset: Option<String>,
    pub type_collation: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CalciteCollation {
    #[serde(rename = "fieldIndex")]
    pub field_index: usize,
    pub direction: String,
    #[serde(rename = "nullDirection")]
    pub null_direction: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn calcite_table_json_defaults_and_omits_empty_constraints() {
        let table: CalciteTable = serde_json::from_value(json!({
            "name": "t",
            "columns": []
        }))
        .unwrap();

        assert!(table.constraints.is_empty());
        assert_eq!(
            serde_json::to_value(table).unwrap(),
            json!({"name": "t", "columns": []})
        );
    }
}
