use serde::{Deserialize, Serialize};

pub mod convert;
pub mod rel_text_hydrate;
pub mod scalar;
pub mod sort_semantics;
pub mod text_plan;
pub mod ty;

pub use convert::{convert_file, convert_raw_file};

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CalciteFile {
    #[serde(default)]
    pub schema: Vec<CalciteTable>,
    #[serde(default)]
    pub queries: Vec<CalciteQuery>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct CalciteTable {
    pub name: String,
    #[serde(default)]
    pub columns: Vec<CalciteColumn>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct CalciteColumn {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(default)]
    pub full_type: Option<String>,
    #[serde(default)]
    pub precision: Option<i32>,
    #[serde(default)]
    pub scale: Option<i32>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CalciteQuery {
    pub sql: Option<String>,
    pub rel: Option<CalciteRel>,
    pub rel_text: Option<String>,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
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

    #[serde(default)]
    pub table: Vec<String>,
    #[serde(default)]
    pub projects: Vec<String>,
    #[serde(default)]
    pub project_rex: Vec<CalciteRex>,
    pub condition: Option<String>,
    pub condition_rex: Option<CalciteRex>,
    pub join_type: Option<String>,
    pub group_set: Option<String>,
    pub group_sets: Option<Vec<String>>,
    #[serde(default)]
    pub agg_calls: Vec<String>,
    #[serde(default)]
    pub agg_call_details: Vec<CalciteAggregateCall>,
    pub set_op: Option<String>,
    pub all: Option<bool>,
    #[serde(default)]
    pub collation: Vec<CalciteCollation>,
    pub fetch: Option<String>,
    pub fetch_rex: Option<CalciteRex>,
    pub offset: Option<String>,
    pub offset_rex: Option<CalciteRex>,
    pub tuples: Option<Vec<Vec<CalciteRex>>>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
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
    pub timestamp_literal: Option<String>,
    pub interval_type_name: Option<String>,
    pub interval_literal: Option<String>,
    pub interval_internal_value: Option<String>,
    pub interval_unit: Option<String>,
    pub subquery_rel: Option<Box<CalciteRel>>,
    pub window: Option<Box<CalciteWindow>>,
    pub sarg: Option<CalciteSarg>,
    pub distinct: Option<bool>,
    pub ignore_nulls: Option<bool>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
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
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
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
#[serde(rename_all = "camelCase")]
pub struct CalciteWindowOrderKey {
    pub expr: CalciteRex,
    pub direction: String,
    pub null_direction: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
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
#[serde(rename_all = "camelCase")]
pub struct CalciteSarg {
    pub text: String,
    pub null_as: Option<String>,
    pub point_count: Option<i32>,
    #[serde(default)]
    pub is_all: bool,
    #[serde(default)]
    pub is_none: bool,
    #[serde(default)]
    pub is_points: bool,
    #[serde(default)]
    pub is_complemented_points: bool,
    #[serde(default)]
    pub ranges: Vec<CalciteSargRange>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CalciteSargRange {
    pub text: String,
    #[serde(default)]
    pub has_lower_bound: bool,
    pub lower: Option<String>,
    pub lower_bound_type: Option<String>,
    #[serde(default)]
    pub has_upper_bound: bool,
    pub upper: Option<String>,
    pub upper_bound_type: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
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
pub struct CalciteCollation {
    #[serde(rename = "fieldIndex")]
    pub field_index: usize,
    pub direction: String,
    #[serde(rename = "nullDirection")]
    pub null_direction: Option<String>,
}
