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
    pub constructor: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalAttributeType {
    String,
    Z,
    Bool,
    Float,
    Date,
    Timestamp { precision: Option<u32> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalQuery {
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
    pub alias_constructor: String,
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
    Function {
        symbol: String,
        args: Vec<FormalAggregateTerm>,
    },
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
        constructor: String,
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
