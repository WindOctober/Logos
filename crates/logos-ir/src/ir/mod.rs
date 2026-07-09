use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LogosIrFile {
    pub schema: Schema,
    pub queries: Vec<Query>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Schema {
    pub tables: Vec<Table>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Table {
    pub name: String,
    pub columns: Vec<Column>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Column {
    pub name: String,
    pub ty: SqlType,
    pub nullable: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub precision: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SqlType {
    Any,
    Null,
    Integer,
    BigInt,
    Float,
    Double,
    Decimal,
    Varchar,
    Boolean,
    Date,
    Time,
    Timestamp,
    TimestampTz,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Query {
    pub source_sql: Option<String>,
    pub rel: RelExpr,
    pub output: Vec<Column>,
    pub features: Vec<Feature>,
    pub calcite_rel_text: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub calcite_rel_plan: Option<TextRelNode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum RelExpr {
    TableScan {
        table: Vec<String>,
        output: Vec<Column>,
    },
    Project {
        input: Box<RelExpr>,
        exprs: Vec<ScalarExpr>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    Filter {
        input: Box<RelExpr>,
        predicate: ScalarExpr,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    Join {
        left: Box<RelExpr>,
        right: Box<RelExpr>,
        join_type: JoinType,
        condition: ScalarExpr,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    Aggregate {
        input: Box<RelExpr>,
        group_keys: Vec<usize>,
        grouping_sets: Option<Vec<Vec<usize>>>,
        agg_calls: Vec<AggregateCall>,
        output: Vec<Column>,
    },
    Sort {
        input: Box<RelExpr>,
        collation: Vec<SortKey>,
        fetch: Option<ScalarExpr>,
        offset: Option<ScalarExpr>,
        output: Vec<Column>,
    },
    Set {
        op: SetOp,
        all: bool,
        inputs: Vec<RelExpr>,
        output: Vec<Column>,
    },
    Values {
        tuples: ValuesTuples,
        output: Vec<Column>,
    },
}

impl RelExpr {
    pub fn output(&self) -> &[Column] {
        match self {
            RelExpr::TableScan { output, .. }
            | RelExpr::Project { output, .. }
            | RelExpr::Filter { output, .. }
            | RelExpr::Join { output, .. }
            | RelExpr::Aggregate { output, .. }
            | RelExpr::Sort { output, .. }
            | RelExpr::Set { output, .. }
            | RelExpr::Values { output, .. } => output,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CorrelationBinding {
    pub correlation: String,
    pub output: Vec<Column>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum JoinType {
    Inner,
    Left,
    Right,
    Full,
    Semi,
    Anti,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SetOp {
    Union,
    Intersect,
    Except,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SortKey {
    pub field_index: usize,
    pub direction: SortDirection,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub null_direction: Option<SortNullDirection>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SortDirection {
    Ascending,
    Descending,
    StrictlyAscending,
    StrictlyDescending,
    Clustered,
}

impl SortDirection {
    pub fn default_null_direction(self) -> Option<SortNullDirection> {
        match self {
            SortDirection::Ascending | SortDirection::StrictlyAscending => {
                Some(SortNullDirection::Last)
            }
            SortDirection::Descending | SortDirection::StrictlyDescending => {
                Some(SortNullDirection::First)
            }
            SortDirection::Clustered => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SortNullDirection {
    First,
    Last,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AggregateCall {
    pub raw: String,
    pub function: String,
    pub distinct: bool,
    #[serde(default, skip_serializing_if = "AggregateModifiers::is_empty")]
    pub modifiers: AggregateModifiers,
    pub args: Vec<ScalarExpr>,
    pub filter: Option<ScalarExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AggregateModifiers {
    #[serde(default)]
    pub approximate: bool,
    #[serde(default)]
    pub ignore_nulls: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub distinct_keys: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub collation: Vec<SortKey>,
}

impl AggregateModifiers {
    pub fn is_empty(&self) -> bool {
        !self.approximate
            && !self.ignore_nulls
            && self.distinct_keys.is_empty()
            && self.collation.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum ValuesTuples {
    Rows { rows: Vec<Vec<ScalarExpr>> },
    UnavailableFromCalcite,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScalarExpr {
    pub raw: String,
    pub class: ScalarClass,
    pub parsed: ScalarAst,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum ScalarClass {
    InputRef { index: usize },
    CorrelatedRef,
    Literal,
    Call,
    Subquery,
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum ScalarAst {
    InputRef {
        index: usize,
    },
    CorrelatedRef {
        correlation: String,
        field: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        index: Option<usize>,
        ty: SqlType,
        #[serde(skip_serializing_if = "Option::is_none")]
        precision: Option<u32>,
    },
    Literal {
        raw: String,
    },
    Call {
        operator: String,
        op: ScalarOp,
        args: Vec<ScalarAst>,
    },
    TypeAnnotation {
        expr: Box<ScalarAst>,
        ty: String,
    },
    Flag {
        name: String,
    },
    Window {
        raw: String,
        #[serde(default)]
        structured: bool,
        parsed: WindowAst,
    },
    RelSubquery {
        rel: Box<RelExpr>,
    },
    Sarg {
        raw: String,
        parsed: SargAst,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WindowAst {
    pub function: String,
    pub args: Vec<ScalarAst>,
    pub partition_by: Vec<ScalarAst>,
    pub order_by: Vec<WindowOrderKey>,
    #[serde(default)]
    pub distinct: bool,
    #[serde(default)]
    pub ignore_nulls: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exclude: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub frame: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WindowOrderKey {
    pub expr: ScalarAst,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub direction: Option<SortDirection>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub null_direction: Option<SortNullDirection>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SargAst {
    pub items: Vec<SargItem>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub null_as: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub point_count: Option<i32>,
    #[serde(default)]
    pub is_all: bool,
    #[serde(default)]
    pub is_none: bool,
    #[serde(default)]
    pub is_points: bool,
    #[serde(default)]
    pub is_complemented_points: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ty: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum SargItem {
    Point {
        raw: String,
    },
    Range {
        raw: String,
        lower: Option<SargBound>,
        upper: Option<SargBound>,
        lower_inclusive: bool,
        upper_inclusive: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SargBound {
    pub raw: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextRelNode {
    pub rel_type: String,
    pub kind: TextRelNodeKind,
    pub shape: TextRelShape,
    pub attrs: Vec<TextRelAttr>,
    pub inputs: Vec<TextRelNode>,
    pub raw_line: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextRelAttr {
    pub name: String,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum TextRelNodeKind {
    TableScan,
    Project,
    Filter,
    Join,
    Aggregate,
    Sort,
    Union,
    Intersect,
    Minus,
    Values,
    Other { rel_type: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum TextRelShape {
    TableScan {
        table: Vec<String>,
    },
    Project {
        exprs: Vec<TextRelProjectExpr>,
        #[serde(skip_serializing_if = "Option::is_none")]
        variables_set: Option<String>,
    },
    Filter {
        #[serde(skip_serializing_if = "Option::is_none")]
        condition: Option<Box<ScalarExpr>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        variables_set: Option<String>,
    },
    Join {
        #[serde(skip_serializing_if = "Option::is_none")]
        condition: Option<Box<ScalarExpr>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        join_type: Option<JoinType>,
    },
    Aggregate {
        #[serde(skip_serializing_if = "Option::is_none")]
        group_keys: Option<Vec<usize>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        grouping_sets: Option<Vec<Vec<usize>>>,
        agg_calls: Vec<TextRelAggregateCall>,
    },
    Sort {
        sort_keys: Vec<TextRelSortKey>,
        #[serde(skip_serializing_if = "Option::is_none")]
        fetch: Option<Box<ScalarExpr>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        offset: Option<Box<ScalarExpr>>,
    },
    Set {
        #[serde(skip_serializing_if = "Option::is_none")]
        all: Option<bool>,
    },
    Values {
        #[serde(skip_serializing_if = "Option::is_none")]
        tuples: Option<Vec<Vec<Box<ScalarExpr>>>>,
    },
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextRelProjectExpr {
    pub name: String,
    pub expr: Box<ScalarExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextRelAggregateCall {
    pub name: String,
    pub raw: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TextRelSortKey {
    pub index: usize,
    pub expr: Box<ScalarExpr>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub direction: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ScalarOp {
    Eq,
    NotEq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    Not,
    IsNull,
    IsNotNull,
    IsTrue,
    IsNotTrue,
    IsFalse,
    IsNotFalse,
    IsNotDistinctFrom,
    Like,
    Plus,
    Minus,
    Multiply,
    Divide,
    StringConcat,
    Cast,
    Case,
    Lower,
    Upper,
    Substring,
    Exp,
    Power,
    Extract,
    In,
    Exists,
    ScalarQuery,
    Search,
    Other(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Feature {
    TableScan,
    Projection,
    Selection,
    InnerJoin,
    OuterJoin,
    SemiJoin,
    AntiJoin,
    Aggregation,
    AggregateGroupingSetsUnavailable,
    DistinctAggregate,
    FilteredAggregate,
    Union,
    Intersect,
    Except,
    SetDistinct,
    Sort,
    Limit,
    Offset,
    Values,
    ValuesTuplesUnavailable,
    OpaqueScalar,
    SubqueryPredicate,
    CorrelatedPredicate,
    BasicAggregateFunction,
    AdvancedAggregateFunction,
    GroupingFunction,
    GroupingSets,
    Rollup,
    Cube,
    WindowFunction,
    AnySqlType,
    NullSqlType,
    FormalSqlOrderSensitive,
    FormalSqlUnsupported,
}
