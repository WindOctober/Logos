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
    pub set_op: Option<String>,
    pub all: Option<bool>,
    #[serde(default)]
    pub collation: Vec<CalciteCollation>,
    pub fetch: Option<String>,
    pub fetch_rex: Option<CalciteRex>,
    pub offset: Option<String>,
    pub offset_rex: Option<CalciteRex>,
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
    pub charset: Option<String>,
    pub type_collation: Option<String>,
    pub index: Option<usize>,
    pub operator: Option<String>,
    pub op_kind: Option<String>,
    #[serde(default)]
    pub operands: Vec<CalciteRex>,
    pub literal_type_name: Option<String>,
    pub literal_value: Option<String>,
    pub literal_value2: Option<String>,
    pub literal_value_as_string: Option<String>,
    pub interval_type_name: Option<String>,
    pub interval_literal: Option<String>,
    pub interval_internal_value: Option<String>,
    pub interval_unit: Option<String>,
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
