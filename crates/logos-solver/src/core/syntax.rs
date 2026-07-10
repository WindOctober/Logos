use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofLoweringReport {
    pub backend: String,
    pub schema: LoweredSchema,
    pub source: LoweredQuery,
    pub target: LoweredQuery,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub query_module: Option<FormalQueryModule>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_module: Option<FormalProofModule>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweredSchema {
    pub status: LoweringStatus,
    pub schema: Option<FormalSchema>,
    pub diagnostics: Vec<LoweringDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweredQuery {
    pub status: LoweringStatus,
    pub query: Option<FormalQuery>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub list_query: Option<FormalListQuery>,
    pub diagnostics: Vec<LoweringDiagnostic>,
    pub feature_coverage: FeatureCoverage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LoweringStatus {
    Lowered,
    Blocked,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweringDiagnostic {
    pub severity: DiagnosticSeverity,
    pub path: String,
    pub code: String,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureCoverage {
    pub structurally_supported: Vec<String>,
    pub requires_audit: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalSchema {
    pub tables: Vec<FormalTable>,
    pub rocq_create_schema: String,
    pub rocq_module: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalQueryModule {
    pub source_definition: String,
    pub target_definition: String,
    pub rocq_module: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalProofModule {
    pub rocq_module: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalTable {
    pub relation: String,
    pub attributes: Vec<FormalAttribute>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalAttribute {
    pub name: String,
    pub ty: FormalAttributeType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalValueLiteral {
    pub raw: String,
    pub ty: FormalAttributeType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalAttributeType {
    String,
    Z,
    Bool,
    Float,
    Double,
    Decimal {
        precision: Option<u32>,
        scale: Option<u32>,
    },
    Date,
    Timestamp {
        precision: Option<u32>,
    },
    Timestamptz {
        precision: Option<u32>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalQuery {
    /// Empty bag with an explicit output shape.  Used for syntactically empty
    /// relations whose NULL-only output columns have no concrete SQL type.
    Empty { columns: Vec<FormalAttribute> },
    /// FormalSQL SqlAlgebra.Q_Empty_Tuple.
    EmptyTuple,
    /// FormalSQL SqlAlgebra.Q_Table.
    Table { relation: String },
    /// FormalSQL SqlAlgebra.Q_Set.
    Set {
        op: FormalSetOp,
        left: Box<FormalQuery>,
        right: Box<FormalQuery>,
    },
    /// FormalSQL SqlAlgebra.Q_NaturalJoin.
    NaturalJoin {
        left: Box<FormalQuery>,
        right: Box<FormalQuery>,
    },
    /// Logos-level cartesian product.
    CrossJoin {
        left: Box<FormalQuery>,
        right: Box<FormalQuery>,
    },
    /// FormalSQL SqlAlgebra.Q_Pi.
    Projection {
        select: Vec<FormalSelectItem>,
        input: Box<FormalQuery>,
    },
    /// FormalSQL SqlAlgebra.Q_Sigma.
    Selection {
        predicate: FormalFormula,
        input: Box<FormalQuery>,
    },
    /// FormalSQL SqlAlgebra.Q_Gamma.
    Group {
        select: Vec<FormalSelectItem>,
        group_by: Vec<FormalAggregateTerm>,
        having: FormalFormula,
        input: Box<FormalQuery>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalListQuery {
    Empty {
        columns: Vec<FormalAttribute>,
    },
    Bag {
        input: Box<FormalQuery>,
    },
    OrderBy {
        keys: Vec<FormalSortKey>,
        input: Box<FormalListQuery>,
    },
    Offset {
        count: u64,
        input: Box<FormalListQuery>,
    },
    Fetch {
        count: u64,
        input: Box<FormalListQuery>,
    },
}

impl FormalListQuery {
    pub fn as_bag_query(&self) -> Option<&FormalQuery> {
        match self {
            FormalListQuery::Bag { input } => Some(input),
            FormalListQuery::Empty { .. } => None,
            FormalListQuery::OrderBy { .. }
            | FormalListQuery::Offset { .. }
            | FormalListQuery::Fetch { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalSortKey {
    pub attribute_name: String,
    pub attribute_ty: FormalAttributeType,
    pub direction: FormalSortDirection,
    pub null_direction: FormalNullDirection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalSortDirection {
    Asc,
    Desc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalNullDirection {
    First,
    Last,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalSetOp {
    Union,
    UnionMax,
    Inter,
    Diff,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalSelectItem {
    pub expr: FormalAggregateTerm,
    pub alias: String,
    pub alias_ty: FormalAttributeType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalAggregateTerm {
    Expr {
        term: FormalFunctionTerm,
    },
    Aggregate {
        function: String,
        arg: FormalFunctionTerm,
    },
    CountStar,
    Function {
        symbol: String,
        args: Vec<FormalAggregateTerm>,
    },
    Case {
        branches: Vec<FormalCaseBranch>,
        #[serde(rename = "elseExpr")]
        else_expr: Box<FormalAggregateTerm>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalCaseBranch {
    pub when: FormalAggregateTerm,
    pub then_expr: FormalAggregateTerm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalFunctionTerm {
    Constant {
        raw: String,
        ty: Option<FormalAttributeType>,
    },
    Attribute {
        name: String,
        ty: FormalAttributeType,
    },
    Cast {
        function: String,
        arg: Box<FormalFunctionTerm>,
        ty: FormalAttributeType,
    },
    Function {
        symbol: String,
        args: Vec<FormalFunctionTerm>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalFormula {
    True,
    False,
    Predicate {
        predicate: String,
        args: Vec<FormalAggregateTerm>,
    },
    And {
        left: Box<FormalFormula>,
        right: Box<FormalFormula>,
    },
    Or {
        left: Box<FormalFormula>,
        right: Box<FormalFormula>,
    },
    Not {
        formula: Box<FormalFormula>,
    },
    Exists {
        query: Box<FormalQuery>,
    },
}
