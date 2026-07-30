use logos_ir::ir::{SqlEnvironment, SqlStringType};
use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofInputBindings {
    pub schema_version: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub case_id: Option<String>,
    pub schema_sql_sha256: String,
    pub source_sql_sha256: String,
    pub target_sql_sha256: String,
    pub verification_input_sha256: String,
    pub integrity_contract_sha256: String,
    pub schema_ir_sha256: String,
    pub source_ir_sha256: String,
    pub target_ir_sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofLoweringReport {
    pub backend: String,
    pub sql_environment: SqlEnvironment,
    /// Immutable boundary binding written only after the accepted frontend
    /// artifacts exist.  The transform runner independently rechecks every
    /// digest against the selected case inputs and artifacts before accepting
    /// this lowering report as evidence.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub input_bindings: Option<ProofInputBindings>,
    pub schema: LoweredSchema,
    pub source: LoweredProgram,
    pub target: LoweredProgram,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub query_module: Option<FormalQueryModule>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_module: Option<FormalProofModule>,
    /// Exact trusted wrapper written as `Goal.v` by the proof stage.  This is
    /// attached only after all case-specific lowering modules exist, so the
    /// lowering artifact is an authoritative byte-for-byte manifest of every
    /// generated Rocq source file.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goal_module: Option<FormalProofModule>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweredSchema {
    pub status: LoweringStatus,
    pub schema: Option<FormalSchema>,
    pub diagnostics: Vec<LoweringDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweredQuery {
    pub status: LoweringStatus,
    /// Authoritative normalized query syntax for the exact ordered-observation
    /// semantics. This is present for every successfully lowered query.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub query_expr: Option<FormalQueryExpr>,
    /// Exact original SQL output labels, types, and order derived from the
    /// authoritative `FormalQueryExpr`. Scope analysis may only enrich that
    /// signature with NUMERIC display-scale provenance; it cannot choose its
    /// labels, types, or order. Emission links this signature to
    /// `query_expr_outputs` and rejects any mismatch.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub output_signature: Option<Vec<FormalAttribute>>,
    pub diagnostics: Vec<LoweringDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweredProgram {
    /// A program is lowered only when every statement is represented.  No
    /// partial query module is emitted for a blocked statement.
    pub status: LoweringStatus,
    /// Statements remain in frontend order.  Their output signatures are
    /// intentionally nested rather than flattened because one SQL file may
    /// contain result sets with different arities.
    pub statements: Vec<LoweredQuery>,
    /// Aggregate view retained for campaign summaries.  Each statement
    /// diagnostic is prefixed with its stable program position.
    pub diagnostics: Vec<LoweringDiagnostic>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum LoweringStatus {
    Lowered,
    Blocked,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LoweringDiagnostic {
    pub severity: DiagnosticSeverity,
    pub path: String,
    pub code: String,
    pub message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalSchema {
    pub tables: Vec<FormalTable>,
    pub rocq_module: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalQueryModule {
    pub rocq_module: String,
    /// Compact navigation metadata emitted from the same definition registry
    /// and reference decisions as `rocq_module`.  This graph is not part of
    /// the proof contract; its `@name` leaves bind directly to definitions in
    /// the authoritative generated Rocq module.
    pub definition_graph: FormalQueryDefinitionGraph,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalQueryDefinitionGraph {
    pub schema_version: u32,
    /// Grammar for every `tree` below.  Constructors are the exact Rocq head
    /// identifiers selected by the emitter. References to emitted helpers or
    /// hoisted definitions are written as `@identifier` leaves. Braced fields
    /// contain only compact counts or literal control parameters, never full
    /// scalar expressions or attribute lists.
    pub notation: String,
    /// Select-list definitions are deliberately opaque in this compact graph.
    /// Their exact bodies remain authoritative in `rocq_module`; listing their
    /// symbols makes every `@select_list_N` reference resolvable without
    /// duplicating scalar or attribute payloads.
    pub opaque_helper_symbols: Vec<String>,
    /// Formula-expression and query-expression definitions in deterministic
    /// Rocq emission order, followed by the source and target statement roots.
    pub definitions: Vec<FormalQueryShapeDefinition>,
    pub source_statements: Vec<FormalQueryStatementSymbols>,
    pub target_statements: Vec<FormalQueryStatementSymbols>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalQueryShapeDefinition {
    pub symbol: String,
    pub kind: FormalQueryShapeKind,
    pub tree: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalQueryShapeKind {
    FormulaExpr,
    ScalarExpr,
    QueryExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalQueryStatementSymbols {
    /// One-based statement position, matching the proof-agent query-shape
    /// artifact and the human-facing SQL program order.
    pub statement_index: usize,
    pub root_symbol: String,
    pub output_signature_symbol: String,
    pub requires_numeric_exp_model: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalProofModule {
    pub rocq_module: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalTable {
    pub relation: String,
    pub attributes: Vec<FormalAttribute>,
    #[serde(skip_serializing_if = "FormalTableConstraints::is_empty")]
    pub constraints: FormalTableConstraints,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalTableConstraints {
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub not_null: Vec<FormalAttribute>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub primary_key: Option<Vec<FormalAttribute>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unique: Vec<FormalUniqueConstraint>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub foreign_keys: Vec<FormalForeignKeyConstraint>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub checks: Vec<FormalCheckConstraint>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unique_indexes: Vec<FormalUniqueIndexConstraint>,
}

impl FormalTableConstraints {
    pub fn is_empty(&self) -> bool {
        self.not_null.is_empty()
            && self.primary_key.is_none()
            && self.unique.is_empty()
            && self.foreign_keys.is_empty()
            && self.checks.is_empty()
            && self.unique_indexes.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalUniqueConstraint {
    pub columns: Vec<FormalAttribute>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalForeignKeyConstraint {
    pub columns: Vec<FormalAttribute>,
    pub referenced_relation: String,
    pub referenced_columns: Vec<FormalAttribute>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalCheckConstraint {
    pub formula: FormalConstraintFormula,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalUniqueIndexConstraint {
    pub terms: Vec<FormalFunctionTerm>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub predicate: Option<FormalConstraintFormula>,
}

/// Closed, row-local formula accepted in schema constraints.
///
/// CHECK constraints and partial unique-index predicates cannot contain
/// subqueries.  Keeping this type separate from query formulas makes that SQL
/// restriction structural and avoids retaining a second relational AST only
/// for schema emission.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalConstraintFormula {
    // Kept because the Rocq constraint language is closed under Boolean
    // constants even though Calcite's current IntegrityPredicate IR folds
    // them before this boundary.
    #[allow(dead_code)]
    True,
    #[allow(dead_code)]
    False,
    Predicate {
        predicate: FormalPredicate,
        args: Vec<FormalAggregateTerm>,
    },
    And {
        left: Box<FormalConstraintFormula>,
        right: Box<FormalConstraintFormula>,
    },
    Or {
        left: Box<FormalConstraintFormula>,
        right: Box<FormalConstraintFormula>,
    },
    Not {
        formula: Box<FormalConstraintFormula>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalAttribute {
    pub name: String,
    pub ty: FormalAttributeType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalValueLiteral {
    pub raw: String,
    pub ty: FormalAttributeType,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_ty: Option<FormalAttributeType>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalAttributeType {
    String { typmod: SqlStringType },
    Z,
    Int32,
    Int64,
    Bool,
    Float,
    Double,
    Numeric,
    Decimal { precision: u32, scale: u32 },
    Date,
    Time,
    Timestamp { precision: Option<u32> },
    Timestamptz { precision: Option<u32> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
/// Complete compositional normalized query syntax.
///
/// Its Rocq denotation is the exact outcome relation over ordered row lists.
/// Possible-bag reasoning enters only through abstraction of those
/// observations; no second relational syntax is embedded in this tree.
pub enum FormalQueryExpr {
    /// A PostgreSQL query-analysis failure whose result shape was resolved
    /// before the error.  It has no successful row-list observation.
    Error {
        columns: Vec<FormalAttribute>,
        error: FormalQueryError,
    },
    /// Empty relation with a resolved ordered output schema.  Emitted through
    /// `QExpr_Values` with an empty bag.
    Empty { columns: Vec<FormalAttribute> },
    /// The one-row, zero-column SQL unit relation.  Emitted through
    /// `QExpr_Values` with a singleton empty tuple.
    EmptyTuple,
    /// Database table scan with its independently resolved SQL column order.
    Table {
        relation: String,
        columns: Vec<FormalAttribute>,
    },
    /// Bag operation and permutation-closing observation boundary.
    Set {
        op: FormalSetOp,
        left: Box<FormalQueryExpr>,
        right: Box<FormalQueryExpr>,
    },
    /// Cartesian join and permutation-closing observation boundary.
    CrossJoin {
        left: Box<FormalQueryExpr>,
        right: Box<FormalQueryExpr>,
    },
    /// Native shared-child SQL join.  The exact denotation chooses one left
    /// and one right child outcome, evaluates one coherent condition matrix,
    /// then permutation-closes the projected result.
    Join {
        join_kind: FormalQueryJoinKind,
        predicate: FormalFormulaExpr,
        matched_select: Vec<FormalSelectItem>,
        left_select: Vec<FormalSelectItem>,
        right_select: Vec<FormalSelectItem>,
        left: Box<FormalQueryExpr>,
        right: Box<FormalQueryExpr>,
    },
    /// Order-preserving row projection.
    Projection {
        select: Vec<FormalSelectItem>,
        input: Box<FormalQueryExpr>,
    },
    /// Native typed scalar projection.  Unlike the legacy flat aggregate-term
    /// projection, every value is represented in the one exact-query scalar
    /// AST and may contain Boolean values or scalar subqueries.
    ScalarProjection {
        select: Vec<FormalScalarSelectItem>,
        input: Box<FormalQueryExpr>,
    },
    /// Declarative, order-preserving application of a constrained SQL row
    /// adapter. The adapter carries its complete typed input/output binding;
    /// no executor or plan choice participates in its meaning.
    RowMap {
        adapter: FormalRowMapAdapter,
        input: Box<FormalQueryExpr>,
    },
    /// Order-preserving row filtering with mutually recursive subqueries.
    Selection {
        predicate: FormalFormulaExpr,
        input: Box<FormalQueryExpr>,
    },
    /// Native WHERE-style Boolean scalar filtering.  Context validation
    /// rejects aggregates at this query level while retaining scalar
    /// subqueries and their exact runtime outcomes.
    ScalarSelection {
        predicate: FormalScalarExpr,
        input: Box<FormalQueryExpr>,
    },
    /// Native grouped scalar evaluation.  One child observation is grouped
    /// once; aggregate-capable scalar SELECT and HAVING expressions then
    /// share each finalized group environment.
    ScalarGroup {
        select: Vec<FormalScalarSelectItem>,
        group_by: Vec<FormalScalarExpr>,
        having: FormalScalarExpr,
        input: Box<FormalQueryExpr>,
    },
    /// Grouping/aggregation and permutation-closing observation boundary.
    Group {
        select: Vec<FormalSelectItem>,
        group_by: Vec<FormalAggregateTerm>,
        having: FormalFormulaExpr,
        input: Box<FormalQueryExpr>,
    },
    /// Native PostgreSQL GROUPING SETS reset. Every set consumes the same one
    /// successful child bag; branches are not independent query evaluations.
    GroupingSets {
        grouping_sets: Vec<FormalGroupingSet>,
        input: Box<FormalQueryExpr>,
    },
    /// PostgreSQL RANK over pre-evaluated partition/order attributes.  The
    /// formal operator consumes one child bag, attaches one-based BIGINT ranks
    /// with peer gaps, and permutation-closes the ranked result.
    Rank {
        partition_keys: Vec<FormalSortKey>,
        order_keys: Vec<FormalSortKey>,
        rank_attribute: FormalAttribute,
        input: Box<FormalQueryExpr>,
    },
    /// Declarative cumulative ROWS window. All items share one legal
    /// partition/order representative, preserving their correlation while
    /// exposing every peer ordering permitted by SQL.
    Window {
        partition_keys: Vec<FormalSortKey>,
        order_keys: Vec<FormalSortKey>,
        items: Vec<FormalWindowItem>,
        input: Box<FormalQueryExpr>,
    },
    /// Duplicate elimination and permutation-closing observation boundary.
    Distinct { input: Box<FormalQueryExpr> },
    /// Constrains legal permutations without choosing an order between ties.
    OrderBy {
        keys: Vec<FormalSortKey>,
        input: Box<FormalQueryExpr>,
    },
    /// Slices every legal child observation.
    Offset {
        count: u64,
        input: Box<FormalQueryExpr>,
    },
    /// Slices every legal child observation.
    Fetch {
        count: u64,
        input: Box<FormalQueryExpr>,
    },
}

impl FormalQueryExpr {
    pub fn requires_numeric_exp_model(&self) -> bool {
        match self {
            FormalQueryExpr::RowMap {
                adapter: FormalRowMapAdapter::NumericExp { .. },
                ..
            } => true,
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                left.requires_numeric_exp_model() || right.requires_numeric_exp_model()
            }
            FormalQueryExpr::Join {
                predicate,
                left,
                right,
                ..
            } => {
                formula_expr_requires_numeric_exp_model(predicate)
                    || left.requires_numeric_exp_model()
                    || right.requires_numeric_exp_model()
            }
            FormalQueryExpr::Selection { predicate, input } => {
                formula_expr_requires_numeric_exp_model(predicate)
                    || input.requires_numeric_exp_model()
            }
            FormalQueryExpr::ScalarSelection { predicate, input } => {
                scalar_expr_requires_numeric_exp_model(predicate)
                    || input.requires_numeric_exp_model()
            }
            FormalQueryExpr::ScalarGroup {
                select,
                group_by,
                having,
                input,
            } => {
                select
                    .iter()
                    .any(|item| scalar_expr_requires_numeric_exp_model(&item.expr))
                    || group_by.iter().any(scalar_expr_requires_numeric_exp_model)
                    || scalar_expr_requires_numeric_exp_model(having)
                    || input.requires_numeric_exp_model()
            }
            FormalQueryExpr::Group { having, input, .. } => {
                formula_expr_requires_numeric_exp_model(having)
                    || input.requires_numeric_exp_model()
            }
            FormalQueryExpr::Projection { input, .. }
            | FormalQueryExpr::GroupingSets { input, .. }
            | FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => input.requires_numeric_exp_model(),
            FormalQueryExpr::ScalarProjection { select, input } => {
                select
                    .iter()
                    .any(|item| scalar_expr_requires_numeric_exp_model(&item.expr))
                    || input.requires_numeric_exp_model()
            }
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalRowMapAdapter {
    /// PostgreSQL's declarative `EXP(AVG(int4))` value operation. The AVG
    /// value and display scale are explicit input attributes; the abstract
    /// model returns both the exact finite NUMERIC result and its display
    /// scale, or the language-level NUMERIC out-of-range error.
    NumericExp {
        passthrough: Vec<FormalAttribute>,
        avg_value: FormalAttribute,
        avg_dscale: FormalAttribute,
        output_numeric: FormalAttribute,
        output_dscale: FormalAttribute,
    },
}

impl FormalRowMapAdapter {
    pub fn output_attributes(&self) -> Vec<FormalAttribute> {
        match self {
            FormalRowMapAdapter::NumericExp {
                passthrough,
                output_numeric,
                output_dscale,
                ..
            } => {
                let mut output = passthrough.clone();
                output.push(output_numeric.clone());
                output.push(output_dscale.clone());
                output
            }
        }
    }
}

pub(super) fn formula_expr_requires_numeric_exp_model(formula: &FormalFormulaExpr) -> bool {
    match formula {
        FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
            formula_expr_requires_numeric_exp_model(left)
                || formula_expr_requires_numeric_exp_model(right)
        }
        FormalFormulaExpr::Not { formula } => formula_expr_requires_numeric_exp_model(formula),
        FormalFormulaExpr::In { query, .. }
        | FormalFormulaExpr::QuantifiedComparison { query, .. }
        | FormalFormulaExpr::Exists { query } => query.requires_numeric_exp_model(),
        FormalFormulaExpr::Scalar { expression } => {
            scalar_expr_requires_numeric_exp_model(expression)
        }
        FormalFormulaExpr::True
        | FormalFormulaExpr::False
        | FormalFormulaExpr::Predicate { .. } => false,
    }
}

pub(super) fn scalar_expr_requires_numeric_exp_model(expression: &FormalScalarExpr) -> bool {
    match expression {
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => false,
        FormalScalarExpr::Call { args, .. }
        | FormalScalarExpr::Predicate { args, .. }
        | FormalScalarExpr::In { args, .. }
        | FormalScalarExpr::QuantifiedComparison { args, .. } => {
            args.iter().any(scalar_expr_requires_numeric_exp_model)
                || match expression {
                    FormalScalarExpr::In { query, .. }
                    | FormalScalarExpr::QuantifiedComparison { query, .. } => {
                        query.requires_numeric_exp_model()
                    }
                    _ => false,
                }
        }
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            scalar_expr_requires_numeric_exp_model(condition)
                || scalar_expr_requires_numeric_exp_model(then_expr)
                || scalar_expr_requires_numeric_exp_model(else_expr)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => {
            scalar_expr_requires_numeric_exp_model(expression)
        }
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            scalar_expr_requires_numeric_exp_model(left)
                || scalar_expr_requires_numeric_exp_model(right)
        }
        FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
            query.requires_numeric_exp_model()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalWindowItem {
    pub output: FormalAttribute,
    pub function: FormalWindowFunction,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub numeric_dscale: Option<NumericDscaleProvenance>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum FormalWindowFunction {
    RowNumber,
    Aggregate {
        term: FormalAggregateTerm,
    },
    /// Aggregate evaluated over the complete current partition.  Unlike the
    /// old relational COUNT expansion, this item and the output row consume
    /// one shared observation of the window child.
    FullPartitionAggregate {
        term: FormalAggregateTerm,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalQueryError {
    /// PostgreSQL SQLSTATE 42702.
    AmbiguousColumn,
    /// PostgreSQL SQLSTATE 42703.
    UndefinedColumn,
    /// PostgreSQL SQLSTATE 42883.
    UndefinedFunction,
    /// PostgreSQL SQLSTATE 22P02.
    InvalidTextRepresentation,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalGroupingSet {
    pub select: Vec<FormalSelectItem>,
    pub group_by: Vec<FormalAggregateTerm>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalQueryJoinKind {
    Left,
    Right,
    Full,
    Semi,
    Anti,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalSortKey {
    pub attribute_name: String,
    pub attribute_ty: FormalAttributeType,
    pub direction: FormalSortDirection,
    pub null_direction: FormalNullDirection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalSortDirection {
    Asc,
    Desc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalNullDirection {
    First,
    Last,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalSetOp {
    Union,
    Inter,
    Diff,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalSelectItem {
    pub expr: FormalAggregateTerm,
    pub alias: String,
    pub alias_ty: FormalAttributeType,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub numeric_dscale: Option<NumericDscaleProvenance>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalScalarSelectItem {
    pub expr: FormalScalarExpr,
    pub alias: String,
    pub alias_ty: FormalAttributeType,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub numeric_dscale: Option<NumericDscaleProvenance>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalScalarResultKind {
    Value,
    Boolean,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalScalarQuantifier {
    Forall,
    Exists,
}

/// One typed scalar AST for every native exact-query scalar position.
///
/// The Rust enum mirrors FormalSQL's result-indexed [scalar_expr].  Value
/// constructors carry their resolved SQL type, while Boolean constructors are
/// identified structurally.  [BooleanValue] is the sole bridge from SQL
/// three-valued truth to a nullable BOOLEAN value.  [Subquery]'s result type
/// also determines the explicit typed NULL witness emitted for its zero-row
/// outcome.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalScalarExpr {
    Leaf {
        result_ty: FormalAttributeType,
        term: FormalAggregateTerm,
    },
    Call {
        result_ty: FormalAttributeType,
        operator: ScalarOperator,
        args: Vec<FormalScalarExpr>,
    },
    Case {
        result_ty: FormalAttributeType,
        condition: Box<FormalScalarExpr>,
        then_expr: Box<FormalScalarExpr>,
        else_expr: Box<FormalScalarExpr>,
    },
    BooleanValue {
        expression: Box<FormalScalarExpr>,
    },
    ValueBoolean {
        expression: Box<FormalScalarExpr>,
    },
    Predicate {
        predicate: FormalPredicate,
        args: Vec<FormalScalarExpr>,
    },
    And {
        left: Box<FormalScalarExpr>,
        right: Box<FormalScalarExpr>,
    },
    Or {
        left: Box<FormalScalarExpr>,
        right: Box<FormalScalarExpr>,
    },
    Not {
        expression: Box<FormalScalarExpr>,
    },
    True,
    QuantifiedComparison {
        quantifier: FormalScalarQuantifier,
        predicate: FormalPredicate,
        args: Vec<FormalScalarExpr>,
        query: Box<FormalQueryExpr>,
    },
    In {
        args: Vec<FormalScalarExpr>,
        query: Box<FormalQueryExpr>,
    },
    Exists {
        query: Box<FormalQueryExpr>,
    },
    Subquery {
        result_ty: FormalAttributeType,
        query: Box<FormalQueryExpr>,
    },
}

impl FormalScalarExpr {
    pub fn result_kind(&self) -> FormalScalarResultKind {
        match self {
            Self::Leaf { .. }
            | Self::Call { .. }
            | Self::Case { .. }
            | Self::BooleanValue { .. }
            | Self::Subquery { .. } => FormalScalarResultKind::Value,
            Self::Predicate { .. }
            | Self::ValueBoolean { .. }
            | Self::And { .. }
            | Self::Or { .. }
            | Self::Not { .. }
            | Self::True
            | Self::QuantifiedComparison { .. }
            | Self::In { .. }
            | Self::Exists { .. } => FormalScalarResultKind::Boolean,
        }
    }

    pub fn value_type(&self) -> Option<FormalAttributeType> {
        match self {
            Self::Leaf { result_ty, .. }
            | Self::Call { result_ty, .. }
            | Self::Case { result_ty, .. }
            | Self::Subquery { result_ty, .. } => Some(*result_ty),
            Self::BooleanValue { .. } => Some(FormalAttributeType::Bool),
            Self::Predicate { .. }
            | Self::ValueBoolean { .. }
            | Self::And { .. }
            | Self::Or { .. }
            | Self::Not { .. }
            | Self::True
            | Self::QuantifiedComparison { .. }
            | Self::In { .. }
            | Self::Exists { .. } => None,
        }
    }
}

/// Display-scale information that is safe to reuse after a relational
/// boundary.  `Representative(s)` means every nonzero value has PostgreSQL
/// dscale `s`, while zero values have dscale at most `s`.  This is sufficient
/// for scale-sensitive arithmetic because zero division results and zero
/// divisors are independent of their display scale.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind", content = "scale")]
pub enum NumericDscaleProvenance {
    Exact(u32),
    Representative(u32),
    /// The scale is carried by a hidden mathematical-integer attribute in
    /// the same logical row. This is used only while a later NUMERIC operator
    /// can still observe PostgreSQL's runtime-selected display scale.
    Attribute(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScalarNumericKind {
    Int32,
    Int64,
    Float,
    Double,
    Numeric,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScalarBooleanOperator {
    And,
    Or,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScalarStringCase {
    Upper,
    Lower,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScalarDatePart {
    Year,
    Month,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScalarNumericSource {
    Z,
    Int32,
    Int64,
    Numeric,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind", content = "source")]
pub enum ScalarCast {
    Identity,
    ToNumeric(ScalarNumericSource),
    ToNumericTypmod(ScalarNumericSource),
    Int32ToDouble,
    Int32ToInt64,
    Int64ToInt32,
    NumericToInt32,
    StringToInt32,
    StringToInt64,
    DateToTimestamp,
    TimestampToDate,
    StringExplicit,
    StringImplicit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ScalarTimestampUnit {
    Microsecond,
    Second,
    Minute,
    Hour,
    Day,
    Month,
    Year,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind", content = "argument")]
pub enum ScalarOperator {
    PredicateValue(FormalPredicate),
    Boolean(ScalarBooleanOperator),
    Case,
    StringCase(ScalarStringCase),
    ExtractDate(ScalarDatePart),
    Cast(ScalarCast),
    Add(ScalarNumericKind),
    Subtract(ScalarNumericKind),
    Multiply(ScalarNumericKind),
    Divide(ScalarNumericKind),
    Negate(ScalarNumericKind),
    NumericDivideResultScale,
    NumericDivideTypmod,
    PowerHalfInt64ToInt32,
    StringConcat,
    SubstringNonnegative,
    TimestampAdd(ScalarTimestampUnit),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum FormalAggregateTerm {
    Expr {
        term: FormalFunctionTerm,
    },
    Aggregate {
        function: FormalAggregateFunction,
        quantifier: FormalAggregateQuantifier,
        arg: FormalFunctionTerm,
    },
    CountStar,
    ScalarCall {
        operator: ScalarOperator,
        args: Vec<FormalAggregateTerm>,
    },
    Case {
        branches: Vec<FormalCaseBranch>,
        #[serde(rename = "elseExpr")]
        else_expr: Box<FormalAggregateTerm>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalAggregateQuantifier {
    All,
    Distinct,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalNumericAggregate {
    AverageInt32,
    StddevSampleInt32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalAggregateFunction {
    Count,
    SumZ,
    SumInt32,
    SumInt64Numeric,
    SumFloat,
    SumDouble,
    SumNumeric,
    BitAndInt32,
    BitOrInt32,
    BitAndInt64,
    BitOrInt64,
    MaxZ,
    MaxInt32,
    MaxInt64,
    MaxFloat,
    MaxDouble,
    MaxNumeric,
    MaxString,
    MinZ,
    MinInt32,
    MinInt64,
    MinFloat,
    MinDouble,
    MinNumeric,
    SingleValueInt32,
    AverageZ,
    AverageInt32Numeric,
    NumericDisplayScale(FormalNumericAggregate),
    AverageInt64Numeric,
    VariancePopulationInt32,
    VarianceSampleInt32,
    StddevPopulationInt32,
    StddevSampleInt32,
    StddevSampleNumericFixed {
        precision: u32,
        scale: u32,
    },
    /// PostgreSQL AVG over REAL input, with a DOUBLE PRECISION result/state.
    AverageFloat,
    /// PostgreSQL AVG over DOUBLE PRECISION input and result/state.
    AverageDouble,
    AverageNumericFixed {
        precision: u32,
        scale: u32,
    },
    AverageNumericAtScale {
        scale: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalCaseBranch {
    pub when: FormalAggregateTerm,
    pub then_expr: FormalAggregateTerm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
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
    ScalarCall {
        operator: ScalarOperator,
        args: Vec<FormalFunctionTerm>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FormalPredicate {
    Lt,
    FloatLt,
    DoubleLt,
    DateLtTimestamp,
    DateLteTimestamp,
    DateGtTimestamp,
    DateGteTimestamp,
    Lte,
    FloatLte,
    DoubleLte,
    Gt,
    FloatGt,
    DoubleGt,
    Gte,
    FloatGte,
    DoubleGte,
    Eq,
    Neq,
    LikePrefix,
    LikePercent,
    IsNull,
    IsNotNull,
    IsTrue,
    IsNotTrue,
    IsFalse,
    IsNotFalse,
    IsNotDistinctFrom,
}

impl FormalPredicate {
    pub fn accepts_arity(self, arity: usize) -> bool {
        let expected = match self {
            Self::IsNull
            | Self::IsNotNull
            | Self::IsTrue
            | Self::IsNotTrue
            | Self::IsFalse
            | Self::IsNotFalse => 1,
            _ => 2,
        };
        arity == expected
    }

    pub fn rocq_constructor(&self) -> &'static str {
        match self {
            Self::Lt => "PredicateLt",
            Self::FloatLt => "PredicateFloatLt",
            Self::DoubleLt => "PredicateDoubleLt",
            Self::DateLtTimestamp => "PredicateDateLtTimestamp",
            Self::DateLteTimestamp => "PredicateDateLteTimestamp",
            Self::DateGtTimestamp => "PredicateDateGtTimestamp",
            Self::DateGteTimestamp => "PredicateDateGteTimestamp",
            Self::Lte => "PredicateLte",
            Self::FloatLte => "PredicateFloatLte",
            Self::DoubleLte => "PredicateDoubleLte",
            Self::Gt => "PredicateGt",
            Self::FloatGt => "PredicateFloatGt",
            Self::DoubleGt => "PredicateDoubleGt",
            Self::Gte => "PredicateGte",
            Self::FloatGte => "PredicateFloatGte",
            Self::DoubleGte => "PredicateDoubleGte",
            Self::Eq => "PredicateEq",
            Self::Neq => "PredicateNeq",
            Self::LikePrefix => "PredicateLikePrefix",
            Self::LikePercent => "PredicateLikePercent",
            Self::IsNull => "PredicateIsNull",
            Self::IsNotNull => "PredicateIsNotNull",
            Self::IsTrue => "PredicateIsTrue",
            Self::IsNotTrue => "PredicateIsNotTrue",
            Self::IsFalse => "PredicateIsFalse",
            Self::IsNotFalse => "PredicateIsNotFalse",
            Self::IsNotDistinctFrom => "PredicateIsNotDistinctFrom",
        }
    }

    #[cfg(test)]
    pub fn model_name(&self) -> &'static str {
        match self {
            Self::Lt => "<",
            Self::FloatLt => "<.",
            Self::DoubleLt => "<_double",
            Self::DateLtTimestamp => "date_lt_timestamp",
            Self::DateLteTimestamp => "date_lte_timestamp",
            Self::DateGtTimestamp => "date_gt_timestamp",
            Self::DateGteTimestamp => "date_gte_timestamp",
            Self::Lte => "<=",
            Self::FloatLte => "<=.",
            Self::DoubleLte => "<=_double",
            Self::Gt => ">",
            Self::FloatGt => ">.",
            Self::DoubleGt => ">_double",
            Self::Gte => ">=",
            Self::FloatGte => ">=.",
            Self::DoubleGte => ">=_double",
            Self::Eq => "=",
            Self::Neq => "<>",
            Self::LikePrefix => "like_prefix",
            Self::LikePercent => "like_percent",
            Self::IsNull => "is_null",
            Self::IsNotNull => "is_not_null",
            Self::IsTrue => "is_true",
            Self::IsNotTrue => "is_not_true",
            Self::IsFalse => "is_false",
            Self::IsNotFalse => "is_not_false",
            Self::IsNotDistinctFrom => "is_not_distinct_from",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
/// Formula language mutually recursive with [FormalQueryExpr], so EXISTS
/// never collapses an order-sensitive child to one arbitrarily chosen bag.
pub enum FormalFormulaExpr {
    True,
    False,
    Predicate {
        predicate: FormalPredicate,
        args: Vec<FormalAggregateTerm>,
    },
    And {
        left: Box<FormalFormulaExpr>,
        right: Box<FormalFormulaExpr>,
    },
    Or {
        left: Box<FormalFormulaExpr>,
        right: Box<FormalFormulaExpr>,
    },
    Not {
        formula: Box<FormalFormulaExpr>,
    },
    /// SQL scalar or row-valued IN over a full compositional subquery.  The
    /// exact Rocq semantics compares aligned tuples componentwise in SQL
    /// three-valued logic, so a definite mismatch dominates NULL while an
    /// otherwise equal row containing NULL remains UNKNOWN.
    In {
        select: Vec<FormalSelectItem>,
        query: Box<FormalQueryExpr>,
    },
    /// A comparison between already-evaluated scalar arguments and every row
    /// of a query expression.  Lowering currently constructs this only for a
    /// structurally singleton, one-column global-aggregate scalar subquery,
    /// where PostgreSQL scalar-subquery comparison is exactly existential
    /// quantification over that sole row (including SQL UNKNOWN and errors).
    QuantifiedComparison {
        predicate: FormalPredicate,
        args: Vec<FormalAggregateTerm>,
        query: Box<FormalQueryExpr>,
    },
    Exists {
        query: Box<FormalQueryExpr>,
    },
    /// Native Boolean scalar bridge for ON/HAVING and compatibility predicate
    /// positions that still use FormalSQL's legacy formula-bearing query
    /// constructors.
    Scalar {
        expression: Box<FormalScalarExpr>,
    },
}

impl ScalarOperator {
    /// Whether the operator's complete FormalSQL value interpretation accepts
    /// this argument count.  Keeping this table beside the closed operator
    /// representation prevents an ill-shaped call from falling through a
    /// value interpreter branch as a successful SQL NULL.
    pub fn accepts_arity(self, arity: usize) -> bool {
        match self {
            Self::PredicateValue(predicate) => predicate.accepts_arity(arity),
            Self::Boolean(ScalarBooleanOperator::And | ScalarBooleanOperator::Or) => arity == 2,
            Self::Boolean(ScalarBooleanOperator::Not) => arity == 1,
            Self::Case => arity >= 3 && arity % 2 == 1,
            Self::StringCase(_) | Self::ExtractDate(_) => arity == 1,
            Self::Cast(
                ScalarCast::ToNumericTypmod(_)
                | ScalarCast::StringExplicit
                | ScalarCast::StringImplicit,
            ) => arity == 3,
            Self::Cast(_) => arity == 1,
            Self::Add(_) | Self::Subtract(_) | Self::Multiply(_) => arity == 2,
            Self::Divide(ScalarNumericKind::Numeric) => arity == 4,
            Self::Divide(_) => arity == 2,
            Self::Negate(_) | Self::PowerHalfInt64ToInt32 => arity == 1,
            Self::NumericDivideResultScale => arity == 4,
            Self::NumericDivideTypmod => arity == 6,
            Self::StringConcat | Self::TimestampAdd(_) => arity == 2,
            Self::SubstringNonnegative => arity == 3,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum FormalScalarContext {
    RowSelect,
    Select,
    Where,
    On,
    Having,
    GroupBy,
}

impl FormalScalarContext {
    fn name(self) -> &'static str {
        match self {
            Self::RowSelect | Self::Select => "SELECT",
            Self::Where => "WHERE",
            Self::On => "ON",
            Self::Having => "HAVING",
            Self::GroupBy => "GROUP BY",
        }
    }

    fn expected_kind(self) -> FormalScalarResultKind {
        match self {
            Self::RowSelect | Self::Select | Self::GroupBy => FormalScalarResultKind::Value,
            Self::Where | Self::On | Self::Having => FormalScalarResultKind::Boolean,
        }
    }

    fn permits_current_level_aggregates(self) -> bool {
        matches!(self, Self::Select | Self::Having)
    }

    fn permits_subqueries(self) -> bool {
        !matches!(self, Self::GroupBy)
    }
}

/// Validate every closed scalar call reachable from a compositional query.
/// This is the shared admission gate used before a lowered query is accepted
/// and before generated Rocq is emitted.
pub(super) fn validate_query_expr_scalar_operators(query: &FormalQueryExpr) -> Result<(), String> {
    if !matches!(query, FormalQueryExpr::Error { .. })
        && formal_query_expr_contains_analysis_error(query)
    {
        return Err(
            "query: an externally attested analysis error may occur only at the query root"
                .to_owned(),
        );
    }
    validate_query_expr_scalar_operators_at(query, "query")
}

fn formal_query_expr_contains_analysis_error(query: &FormalQueryExpr) -> bool {
    match query {
        FormalQueryExpr::Error { .. } => true,
        FormalQueryExpr::Empty { .. }
        | FormalQueryExpr::EmptyTuple
        | FormalQueryExpr::Table { .. } => false,
        FormalQueryExpr::Set { left, right, .. } | FormalQueryExpr::CrossJoin { left, right } => {
            formal_query_expr_contains_analysis_error(left)
                || formal_query_expr_contains_analysis_error(right)
        }
        FormalQueryExpr::Join {
            predicate,
            left,
            right,
            ..
        } => {
            formal_formula_expr_contains_analysis_error(predicate)
                || formal_query_expr_contains_analysis_error(left)
                || formal_query_expr_contains_analysis_error(right)
        }
        FormalQueryExpr::Projection { input, .. }
        | FormalQueryExpr::RowMap { input, .. }
        | FormalQueryExpr::GroupingSets { input, .. }
        | FormalQueryExpr::Rank { input, .. }
        | FormalQueryExpr::Window { input, .. }
        | FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => formal_query_expr_contains_analysis_error(input),
        FormalQueryExpr::ScalarProjection { select, input } => {
            select
                .iter()
                .any(|item| formal_scalar_expr_contains_analysis_error(&item.expr))
                || formal_query_expr_contains_analysis_error(input)
        }
        FormalQueryExpr::Selection { predicate, input } => {
            formal_formula_expr_contains_analysis_error(predicate)
                || formal_query_expr_contains_analysis_error(input)
        }
        FormalQueryExpr::ScalarSelection { predicate, input } => {
            formal_scalar_expr_contains_analysis_error(predicate)
                || formal_query_expr_contains_analysis_error(input)
        }
        FormalQueryExpr::ScalarGroup {
            select,
            group_by,
            having,
            input,
        } => {
            select
                .iter()
                .any(|item| formal_scalar_expr_contains_analysis_error(&item.expr))
                || group_by
                    .iter()
                    .any(formal_scalar_expr_contains_analysis_error)
                || formal_scalar_expr_contains_analysis_error(having)
                || formal_query_expr_contains_analysis_error(input)
        }
        FormalQueryExpr::Group { having, input, .. } => {
            formal_formula_expr_contains_analysis_error(having)
                || formal_query_expr_contains_analysis_error(input)
        }
    }
}

fn formal_formula_expr_contains_analysis_error(formula: &FormalFormulaExpr) -> bool {
    match formula {
        FormalFormulaExpr::True
        | FormalFormulaExpr::False
        | FormalFormulaExpr::Predicate { .. } => false,
        FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
            formal_formula_expr_contains_analysis_error(left)
                || formal_formula_expr_contains_analysis_error(right)
        }
        FormalFormulaExpr::Not { formula } => formal_formula_expr_contains_analysis_error(formula),
        FormalFormulaExpr::In { query, .. }
        | FormalFormulaExpr::QuantifiedComparison { query, .. }
        | FormalFormulaExpr::Exists { query } => formal_query_expr_contains_analysis_error(query),
        FormalFormulaExpr::Scalar { expression } => {
            formal_scalar_expr_contains_analysis_error(expression)
        }
    }
}

fn formal_scalar_expr_contains_analysis_error(expression: &FormalScalarExpr) -> bool {
    match expression {
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => false,
        FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
            args.iter().any(formal_scalar_expr_contains_analysis_error)
        }
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            formal_scalar_expr_contains_analysis_error(condition)
                || formal_scalar_expr_contains_analysis_error(then_expr)
                || formal_scalar_expr_contains_analysis_error(else_expr)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => {
            formal_scalar_expr_contains_analysis_error(expression)
        }
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            formal_scalar_expr_contains_analysis_error(left)
                || formal_scalar_expr_contains_analysis_error(right)
        }
        FormalScalarExpr::QuantifiedComparison { args, query, .. }
        | FormalScalarExpr::In { args, query } => {
            args.iter().any(formal_scalar_expr_contains_analysis_error)
                || formal_query_expr_contains_analysis_error(query)
        }
        FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
            formal_query_expr_contains_analysis_error(query)
        }
    }
}

fn validate_scalar_call(operator: ScalarOperator, arity: usize, path: &str) -> Result<(), String> {
    if operator.accepts_arity(arity) {
        Ok(())
    } else {
        Err(format!(
            "{path}: scalar operator {operator:?} does not accept {arity} arguments"
        ))
    }
}

fn validate_function_term_scalar_operators(
    term: &FormalFunctionTerm,
    path: &str,
) -> Result<(), String> {
    match term {
        FormalFunctionTerm::Constant { .. } | FormalFunctionTerm::Attribute { .. } => Ok(()),
        FormalFunctionTerm::ScalarCall { operator, args } => {
            validate_scalar_call(*operator, args.len(), path)?;
            for (index, arg) in args.iter().enumerate() {
                validate_function_term_scalar_operators(arg, &format!("{path}.args[{index}]"))?;
            }
            Ok(())
        }
    }
}

fn validate_aggregate_term_scalar_operators(
    term: &FormalAggregateTerm,
    path: &str,
) -> Result<(), String> {
    match term {
        FormalAggregateTerm::Expr { term } | FormalAggregateTerm::Aggregate { arg: term, .. } => {
            validate_function_term_scalar_operators(term, path)
        }
        FormalAggregateTerm::CountStar => Ok(()),
        FormalAggregateTerm::ScalarCall { operator, args } => {
            if *operator == ScalarOperator::Case {
                return Err(format!(
                    "{path}: aggregate ScalarCase must use FormalAggregateTerm::Case"
                ));
            }
            validate_scalar_call(*operator, args.len(), path)?;
            for (index, arg) in args.iter().enumerate() {
                validate_aggregate_term_scalar_operators(arg, &format!("{path}.args[{index}]"))?;
            }
            Ok(())
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            if branches.is_empty() {
                return Err(format!(
                    "{path}: structured CASE requires at least one WHEN/THEN branch"
                ));
            }
            for (index, branch) in branches.iter().enumerate() {
                validate_aggregate_term_scalar_operators(
                    &branch.when,
                    &format!("{path}.branches[{index}].when"),
                )?;
                validate_aggregate_term_scalar_operators(
                    &branch.then_expr,
                    &format!("{path}.branches[{index}].then"),
                )?;
            }
            validate_aggregate_term_scalar_operators(else_expr, &format!("{path}.else"))
        }
    }
}

fn aggregate_term_contains_current_level_aggregate(term: &FormalAggregateTerm) -> bool {
    match term {
        FormalAggregateTerm::Aggregate { .. } | FormalAggregateTerm::CountStar => true,
        FormalAggregateTerm::Expr { .. } => false,
        FormalAggregateTerm::ScalarCall { args, .. } => args
            .iter()
            .any(aggregate_term_contains_current_level_aggregate),
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            branches.iter().any(|branch| {
                aggregate_term_contains_current_level_aggregate(&branch.when)
                    || aggregate_term_contains_current_level_aggregate(&branch.then_expr)
            }) || aggregate_term_contains_current_level_aggregate(else_expr)
        }
    }
}

fn scalar_expr_contains_current_level_aggregate(expression: &FormalScalarExpr) -> bool {
    match expression {
        FormalScalarExpr::Leaf { term, .. } => {
            aggregate_term_contains_current_level_aggregate(term)
        }
        FormalScalarExpr::Call { args, .. }
        | FormalScalarExpr::Predicate { args, .. }
        | FormalScalarExpr::In { args, .. }
        | FormalScalarExpr::QuantifiedComparison { args, .. } => args
            .iter()
            .any(scalar_expr_contains_current_level_aggregate),
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            scalar_expr_contains_current_level_aggregate(condition)
                || scalar_expr_contains_current_level_aggregate(then_expr)
                || scalar_expr_contains_current_level_aggregate(else_expr)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => {
            scalar_expr_contains_current_level_aggregate(expression)
        }
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            scalar_expr_contains_current_level_aggregate(left)
                || scalar_expr_contains_current_level_aggregate(right)
        }
        FormalScalarExpr::True
        | FormalScalarExpr::Exists { .. }
        | FormalScalarExpr::Subquery { .. } => false,
    }
}

fn scalar_expr_contains_subquery(expression: &FormalScalarExpr) -> bool {
    match expression {
        FormalScalarExpr::In { .. }
        | FormalScalarExpr::QuantifiedComparison { .. }
        | FormalScalarExpr::Exists { .. }
        | FormalScalarExpr::Subquery { .. } => true,
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => false,
        FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
            args.iter().any(scalar_expr_contains_subquery)
        }
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            scalar_expr_contains_subquery(condition)
                || scalar_expr_contains_subquery(then_expr)
                || scalar_expr_contains_subquery(else_expr)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => scalar_expr_contains_subquery(expression),
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            scalar_expr_contains_subquery(left) || scalar_expr_contains_subquery(right)
        }
    }
}

fn require_scalar_kind(
    expression: &FormalScalarExpr,
    expected: FormalScalarResultKind,
    path: &str,
) -> Result<(), String> {
    let actual = expression.result_kind();
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "{path}: expected a {expected:?} scalar expression, found {actual:?}"
        ))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormalValueTypeClass {
    String,
    Z,
    Int32,
    Int64,
    Bool,
    Float,
    Double,
    Numeric,
    Date,
    Time,
    Timestamp,
    Timestamptz,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormalNumericResultShape {
    NotNumeric,
    Unconstrained,
    Decimal { precision: u32, scale: u32 },
}

fn numeric_result_shape_of_type(ty: FormalAttributeType) -> FormalNumericResultShape {
    match ty {
        FormalAttributeType::Numeric => FormalNumericResultShape::Unconstrained,
        FormalAttributeType::Decimal { precision, scale } => {
            FormalNumericResultShape::Decimal { precision, scale }
        }
        _ => FormalNumericResultShape::NotNumeric,
    }
}

fn numeric_result_shape_matches_type(
    shape: FormalNumericResultShape,
    ty: FormalAttributeType,
) -> bool {
    shape == numeric_result_shape_of_type(ty)
}

fn function_term_u32_constant(term: &FormalFunctionTerm) -> Option<u32> {
    match term {
        FormalFunctionTerm::Constant {
            raw,
            ty: Some(FormalAttributeType::Z),
        } => raw.trim().parse().ok(),
        _ => None,
    }
}

fn aggregate_term_u32_constant(term: &FormalAggregateTerm) -> Option<u32> {
    match term {
        FormalAggregateTerm::Expr { term } => function_term_u32_constant(term),
        _ => None,
    }
}

fn scalar_expr_u32_constant(expression: &FormalScalarExpr) -> Option<u32> {
    match expression {
        FormalScalarExpr::Leaf { term, .. } => aggregate_term_u32_constant(term),
        _ => None,
    }
}

fn numeric_scalar_operator_result_shape(
    operator: ScalarOperator,
    argument_shapes: &[FormalNumericResultShape],
    typmod: Option<(u32, u32)>,
) -> FormalNumericResultShape {
    match operator {
        ScalarOperator::Cast(ScalarCast::Identity) => argument_shapes
            .first()
            .copied()
            .unwrap_or(FormalNumericResultShape::NotNumeric),
        ScalarOperator::Cast(ScalarCast::ToNumericTypmod(_))
        | ScalarOperator::NumericDivideTypmod => typmod
            .map(|(precision, scale)| FormalNumericResultShape::Decimal { precision, scale })
            .unwrap_or(FormalNumericResultShape::NotNumeric),
        ScalarOperator::ExtractDate(_)
        | ScalarOperator::Cast(ScalarCast::ToNumeric(_))
        | ScalarOperator::Add(ScalarNumericKind::Numeric)
        | ScalarOperator::Subtract(ScalarNumericKind::Numeric)
        | ScalarOperator::Multiply(ScalarNumericKind::Numeric)
        | ScalarOperator::Divide(ScalarNumericKind::Numeric)
        | ScalarOperator::Negate(ScalarNumericKind::Numeric) => {
            FormalNumericResultShape::Unconstrained
        }
        _ => FormalNumericResultShape::NotNumeric,
    }
}

fn function_term_numeric_result_shape(term: &FormalFunctionTerm) -> FormalNumericResultShape {
    match term {
        FormalFunctionTerm::Constant { ty: Some(ty), .. }
        | FormalFunctionTerm::Attribute { ty, .. } => numeric_result_shape_of_type(*ty),
        FormalFunctionTerm::Constant { ty: None, .. } => FormalNumericResultShape::NotNumeric,
        FormalFunctionTerm::ScalarCall { operator, args } => {
            let argument_shapes = args
                .iter()
                .map(function_term_numeric_result_shape)
                .collect::<Vec<_>>();
            let typmod = match operator {
                ScalarOperator::Cast(ScalarCast::ToNumericTypmod(_)) => args
                    .get(1)
                    .and_then(function_term_u32_constant)
                    .zip(args.get(2).and_then(function_term_u32_constant)),
                ScalarOperator::NumericDivideTypmod => args
                    .get(4)
                    .and_then(function_term_u32_constant)
                    .zip(args.get(5).and_then(function_term_u32_constant)),
                _ => None,
            };
            numeric_scalar_operator_result_shape(*operator, &argument_shapes, typmod)
        }
    }
}

fn aggregate_term_numeric_result_shape(term: &FormalAggregateTerm) -> FormalNumericResultShape {
    match term {
        FormalAggregateTerm::Expr { term } => function_term_numeric_result_shape(term),
        FormalAggregateTerm::Aggregate { function, .. } => {
            if aggregate_function_type_class(*function) == FormalValueTypeClass::Numeric {
                FormalNumericResultShape::Unconstrained
            } else {
                FormalNumericResultShape::NotNumeric
            }
        }
        FormalAggregateTerm::CountStar => FormalNumericResultShape::NotNumeric,
        FormalAggregateTerm::ScalarCall { operator, args } => {
            let argument_shapes = args
                .iter()
                .map(aggregate_term_numeric_result_shape)
                .collect::<Vec<_>>();
            let typmod = match operator {
                ScalarOperator::Cast(ScalarCast::ToNumericTypmod(_)) => args
                    .get(1)
                    .and_then(aggregate_term_u32_constant)
                    .zip(args.get(2).and_then(aggregate_term_u32_constant)),
                ScalarOperator::NumericDivideTypmod => args
                    .get(4)
                    .and_then(aggregate_term_u32_constant)
                    .zip(args.get(5).and_then(aggregate_term_u32_constant)),
                _ => None,
            };
            numeric_scalar_operator_result_shape(*operator, &argument_shapes, typmod)
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            let result = aggregate_term_numeric_result_shape(else_expr);
            let branch_shapes = branches
                .iter()
                .map(|branch| aggregate_term_numeric_result_shape(&branch.then_expr))
                .collect::<Vec<_>>();
            if branch_shapes.iter().all(|shape| *shape == result) {
                result
            } else if branch_shapes
                .iter()
                .chain(std::iter::once(&result))
                .all(|shape| !matches!(shape, FormalNumericResultShape::NotNumeric))
            {
                // PostgreSQL removes a fixed numeric typmod when CASE arms do
                // not all carry the same exact typmod.
                FormalNumericResultShape::Unconstrained
            } else {
                FormalNumericResultShape::NotNumeric
            }
        }
    }
}

fn scalar_call_numeric_result_shape(
    operator: ScalarOperator,
    args: &[FormalScalarExpr],
) -> FormalNumericResultShape {
    let argument_shapes = args
        .iter()
        .map(|argument| {
            argument
                .value_type()
                .map(numeric_result_shape_of_type)
                .unwrap_or(FormalNumericResultShape::NotNumeric)
        })
        .collect::<Vec<_>>();
    let typmod = match operator {
        ScalarOperator::Cast(ScalarCast::ToNumericTypmod(_)) => args
            .get(1)
            .and_then(scalar_expr_u32_constant)
            .zip(args.get(2).and_then(scalar_expr_u32_constant)),
        ScalarOperator::NumericDivideTypmod => args
            .get(4)
            .and_then(scalar_expr_u32_constant)
            .zip(args.get(5).and_then(scalar_expr_u32_constant)),
        _ => None,
    };
    numeric_scalar_operator_result_shape(operator, &argument_shapes, typmod)
}

fn formal_value_type_class(ty: FormalAttributeType) -> FormalValueTypeClass {
    match ty {
        FormalAttributeType::String { .. } => FormalValueTypeClass::String,
        FormalAttributeType::Z => FormalValueTypeClass::Z,
        FormalAttributeType::Int32 => FormalValueTypeClass::Int32,
        FormalAttributeType::Int64 => FormalValueTypeClass::Int64,
        FormalAttributeType::Bool => FormalValueTypeClass::Bool,
        FormalAttributeType::Float => FormalValueTypeClass::Float,
        FormalAttributeType::Double => FormalValueTypeClass::Double,
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. } => {
            FormalValueTypeClass::Numeric
        }
        FormalAttributeType::Date => FormalValueTypeClass::Date,
        FormalAttributeType::Time => FormalValueTypeClass::Time,
        FormalAttributeType::Timestamp { .. } => FormalValueTypeClass::Timestamp,
        FormalAttributeType::Timestamptz { .. } => FormalValueTypeClass::Timestamptz,
    }
}

fn scalar_numeric_type_class(kind: ScalarNumericKind) -> FormalValueTypeClass {
    match kind {
        ScalarNumericKind::Int32 => FormalValueTypeClass::Int32,
        ScalarNumericKind::Int64 => FormalValueTypeClass::Int64,
        ScalarNumericKind::Float => FormalValueTypeClass::Float,
        ScalarNumericKind::Double => FormalValueTypeClass::Double,
        ScalarNumericKind::Numeric => FormalValueTypeClass::Numeric,
    }
}

fn scalar_numeric_source_type_class(source: ScalarNumericSource) -> FormalValueTypeClass {
    match source {
        ScalarNumericSource::Z => FormalValueTypeClass::Z,
        ScalarNumericSource::Int32 => FormalValueTypeClass::Int32,
        ScalarNumericSource::Int64 => FormalValueTypeClass::Int64,
        ScalarNumericSource::Numeric => FormalValueTypeClass::Numeric,
    }
}

fn scalar_type_class_is_integral(ty: FormalValueTypeClass) -> bool {
    matches!(
        ty,
        FormalValueTypeClass::Z | FormalValueTypeClass::Int32 | FormalValueTypeClass::Int64
    )
}

fn scalar_predicate_argument_types_are_valid(
    predicate: FormalPredicate,
    arguments: &[FormalValueTypeClass],
) -> bool {
    let exact = |expected: &[FormalValueTypeClass]| arguments == expected;
    let homogeneous_or_integral_pair = || {
        matches!(arguments, [left, right] if left == right
            || (scalar_type_class_is_integral(*left)
                && scalar_type_class_is_integral(*right)))
    };
    match predicate {
        FormalPredicate::IsNull | FormalPredicate::IsNotNull => arguments.len() == 1,
        FormalPredicate::IsTrue
        | FormalPredicate::IsNotTrue
        | FormalPredicate::IsFalse
        | FormalPredicate::IsNotFalse => exact(&[FormalValueTypeClass::Bool]),
        FormalPredicate::FloatLt
        | FormalPredicate::FloatLte
        | FormalPredicate::FloatGt
        | FormalPredicate::FloatGte => {
            exact(&[FormalValueTypeClass::Float, FormalValueTypeClass::Float])
        }
        FormalPredicate::DoubleLt
        | FormalPredicate::DoubleLte
        | FormalPredicate::DoubleGt
        | FormalPredicate::DoubleGte => {
            exact(&[FormalValueTypeClass::Double, FormalValueTypeClass::Double])
        }
        FormalPredicate::DateLtTimestamp
        | FormalPredicate::DateLteTimestamp
        | FormalPredicate::DateGtTimestamp
        | FormalPredicate::DateGteTimestamp => {
            exact(&[FormalValueTypeClass::Date, FormalValueTypeClass::Timestamp])
        }
        FormalPredicate::LikePrefix | FormalPredicate::LikePercent => {
            exact(&[FormalValueTypeClass::String, FormalValueTypeClass::String])
        }
        FormalPredicate::Lt | FormalPredicate::Lte | FormalPredicate::Gt | FormalPredicate::Gte => {
            matches!(arguments, [left, right]
            if (scalar_type_class_is_integral(*left)
                && scalar_type_class_is_integral(*right))
                || (left == right
                    && !matches!(left,
                        FormalValueTypeClass::Float | FormalValueTypeClass::Double)))
        }
        FormalPredicate::Eq | FormalPredicate::Neq | FormalPredicate::IsNotDistinctFrom => {
            homogeneous_or_integral_pair()
        }
    }
}

fn scalar_operator_result_type_class(
    operator: ScalarOperator,
    arguments: &[FormalValueTypeClass],
) -> Option<FormalValueTypeClass> {
    Some(match operator {
        ScalarOperator::PredicateValue(_) | ScalarOperator::Boolean(_) => {
            FormalValueTypeClass::Bool
        }
        ScalarOperator::Case => *arguments.get(1)?,
        ScalarOperator::Cast(ScalarCast::Identity) => *arguments.first()?,
        ScalarOperator::StringCase(_)
        | ScalarOperator::Cast(ScalarCast::StringExplicit | ScalarCast::StringImplicit)
        | ScalarOperator::StringConcat
        | ScalarOperator::SubstringNonnegative => FormalValueTypeClass::String,
        ScalarOperator::ExtractDate(_) => FormalValueTypeClass::Numeric,
        ScalarOperator::Cast(ScalarCast::ToNumeric(_) | ScalarCast::ToNumericTypmod(_))
        | ScalarOperator::NumericDivideTypmod => FormalValueTypeClass::Numeric,
        ScalarOperator::Cast(ScalarCast::Int32ToDouble) => FormalValueTypeClass::Double,
        ScalarOperator::Cast(ScalarCast::Int32ToInt64) => FormalValueTypeClass::Int64,
        ScalarOperator::Cast(
            ScalarCast::Int64ToInt32 | ScalarCast::NumericToInt32 | ScalarCast::StringToInt32,
        )
        | ScalarOperator::PowerHalfInt64ToInt32 => FormalValueTypeClass::Int32,
        ScalarOperator::Cast(ScalarCast::StringToInt64) => FormalValueTypeClass::Int64,
        ScalarOperator::Cast(ScalarCast::DateToTimestamp) | ScalarOperator::TimestampAdd(_) => {
            FormalValueTypeClass::Timestamp
        }
        ScalarOperator::Cast(ScalarCast::TimestampToDate) => FormalValueTypeClass::Date,
        ScalarOperator::Add(kind)
        | ScalarOperator::Subtract(kind)
        | ScalarOperator::Multiply(kind)
        | ScalarOperator::Divide(kind)
        | ScalarOperator::Negate(kind) => scalar_numeric_type_class(kind),
        ScalarOperator::NumericDivideResultScale => FormalValueTypeClass::Z,
    })
}

fn scalar_operator_argument_types_are_valid(
    operator: ScalarOperator,
    arguments: &[FormalValueTypeClass],
) -> bool {
    let exact = |expected: &[FormalValueTypeClass]| arguments == expected;
    match operator {
        ScalarOperator::PredicateValue(predicate) => {
            scalar_predicate_argument_types_are_valid(predicate, arguments)
        }
        ScalarOperator::Case => {
            arguments.len() >= 3
                && arguments.len() % 2 == 1
                && arguments[..arguments.len() - 1]
                    .chunks_exact(2)
                    .all(|branch| {
                        branch[0] == FormalValueTypeClass::Bool && branch[1] == arguments[1]
                    })
                && arguments.last() == arguments.get(1)
        }
        ScalarOperator::Boolean(ScalarBooleanOperator::And | ScalarBooleanOperator::Or) => {
            exact(&[FormalValueTypeClass::Bool, FormalValueTypeClass::Bool])
        }
        ScalarOperator::Boolean(ScalarBooleanOperator::Not) => exact(&[FormalValueTypeClass::Bool]),
        ScalarOperator::StringCase(_) => exact(&[FormalValueTypeClass::String]),
        ScalarOperator::ExtractDate(_) => exact(&[FormalValueTypeClass::Date]),
        ScalarOperator::Cast(ScalarCast::Identity) => arguments.len() == 1,
        ScalarOperator::Cast(ScalarCast::ToNumeric(source)) => {
            exact(&[scalar_numeric_source_type_class(source)])
        }
        ScalarOperator::Cast(ScalarCast::ToNumericTypmod(source)) => exact(&[
            scalar_numeric_source_type_class(source),
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Z,
        ]),
        ScalarOperator::Cast(ScalarCast::Int32ToDouble | ScalarCast::Int32ToInt64) => {
            exact(&[FormalValueTypeClass::Int32])
        }
        ScalarOperator::Cast(ScalarCast::Int64ToInt32) => exact(&[FormalValueTypeClass::Int64]),
        ScalarOperator::Cast(ScalarCast::NumericToInt32) => exact(&[FormalValueTypeClass::Numeric]),
        ScalarOperator::Cast(ScalarCast::StringToInt32 | ScalarCast::StringToInt64) => {
            exact(&[FormalValueTypeClass::String])
        }
        ScalarOperator::Cast(ScalarCast::DateToTimestamp) => exact(&[FormalValueTypeClass::Date]),
        ScalarOperator::Cast(ScalarCast::TimestampToDate) => {
            exact(&[FormalValueTypeClass::Timestamp])
        }
        ScalarOperator::Cast(ScalarCast::StringExplicit | ScalarCast::StringImplicit) => exact(&[
            FormalValueTypeClass::String,
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Z,
        ]),
        ScalarOperator::Add(kind)
        | ScalarOperator::Subtract(kind)
        | ScalarOperator::Multiply(kind) => {
            let ty = scalar_numeric_type_class(kind);
            exact(&[ty, ty])
        }
        ScalarOperator::Divide(ScalarNumericKind::Numeric) => exact(&[
            FormalValueTypeClass::Numeric,
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Numeric,
            FormalValueTypeClass::Z,
        ]),
        ScalarOperator::Divide(kind) => {
            let ty = scalar_numeric_type_class(kind);
            exact(&[ty, ty])
        }
        ScalarOperator::Negate(kind) => exact(&[scalar_numeric_type_class(kind)]),
        ScalarOperator::NumericDivideResultScale => exact(&[
            FormalValueTypeClass::Numeric,
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Numeric,
            FormalValueTypeClass::Z,
        ]),
        ScalarOperator::NumericDivideTypmod => exact(&[
            FormalValueTypeClass::Numeric,
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Numeric,
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Z,
            FormalValueTypeClass::Z,
        ]),
        ScalarOperator::PowerHalfInt64ToInt32 => exact(&[FormalValueTypeClass::Int64]),
        ScalarOperator::StringConcat => {
            exact(&[FormalValueTypeClass::String, FormalValueTypeClass::String])
        }
        ScalarOperator::SubstringNonnegative => exact(&[
            FormalValueTypeClass::String,
            FormalValueTypeClass::Int32,
            FormalValueTypeClass::Int32,
        ]),
        ScalarOperator::TimestampAdd(_) => {
            exact(&[FormalValueTypeClass::Timestamp, FormalValueTypeClass::Z])
        }
    }
}

fn function_term_type_class(term: &FormalFunctionTerm) -> Option<FormalValueTypeClass> {
    match term {
        FormalFunctionTerm::Constant { ty: Some(ty), .. } => Some(formal_value_type_class(*ty)),
        FormalFunctionTerm::Constant { ty: None, .. } => None,
        FormalFunctionTerm::Attribute { ty, .. } => Some(formal_value_type_class(*ty)),
        FormalFunctionTerm::ScalarCall { operator, args } => {
            let argument_types = args
                .iter()
                .map(function_term_type_class)
                .collect::<Option<Vec<_>>>()?;
            scalar_operator_argument_types_are_valid(*operator, &argument_types)
                .then(|| scalar_operator_result_type_class(*operator, &argument_types))?
        }
    }
}

fn aggregate_function_type_class(function: FormalAggregateFunction) -> FormalValueTypeClass {
    match function {
        FormalAggregateFunction::Count => FormalValueTypeClass::Int64,
        FormalAggregateFunction::SumZ
        | FormalAggregateFunction::MaxZ
        | FormalAggregateFunction::MinZ
        | FormalAggregateFunction::AverageZ => FormalValueTypeClass::Z,
        FormalAggregateFunction::SumInt32 => FormalValueTypeClass::Int64,
        FormalAggregateFunction::SumInt64Numeric
        | FormalAggregateFunction::SumNumeric
        | FormalAggregateFunction::MaxNumeric
        | FormalAggregateFunction::MinNumeric
        | FormalAggregateFunction::AverageInt32Numeric
        | FormalAggregateFunction::AverageInt64Numeric
        | FormalAggregateFunction::VariancePopulationInt32
        | FormalAggregateFunction::VarianceSampleInt32
        | FormalAggregateFunction::StddevPopulationInt32
        | FormalAggregateFunction::StddevSampleInt32
        | FormalAggregateFunction::StddevSampleNumericFixed { .. }
        | FormalAggregateFunction::AverageNumericFixed { .. }
        | FormalAggregateFunction::AverageNumericAtScale { .. } => FormalValueTypeClass::Numeric,
        FormalAggregateFunction::SumFloat
        | FormalAggregateFunction::MaxFloat
        | FormalAggregateFunction::MinFloat => FormalValueTypeClass::Float,
        FormalAggregateFunction::SumDouble
        | FormalAggregateFunction::MaxDouble
        | FormalAggregateFunction::MinDouble
        | FormalAggregateFunction::AverageFloat
        | FormalAggregateFunction::AverageDouble => FormalValueTypeClass::Double,
        FormalAggregateFunction::BitAndInt32
        | FormalAggregateFunction::BitOrInt32
        | FormalAggregateFunction::MaxInt32
        | FormalAggregateFunction::MinInt32
        | FormalAggregateFunction::SingleValueInt32 => FormalValueTypeClass::Int32,
        FormalAggregateFunction::BitAndInt64
        | FormalAggregateFunction::BitOrInt64
        | FormalAggregateFunction::MaxInt64
        | FormalAggregateFunction::MinInt64 => FormalValueTypeClass::Int64,
        FormalAggregateFunction::MaxString => FormalValueTypeClass::String,
        FormalAggregateFunction::NumericDisplayScale(_) => FormalValueTypeClass::Z,
    }
}

fn aggregate_function_accepts_input(
    function: FormalAggregateFunction,
    input: FormalValueTypeClass,
) -> bool {
    match function {
        FormalAggregateFunction::Count => true,
        FormalAggregateFunction::SumZ
        | FormalAggregateFunction::MaxZ
        | FormalAggregateFunction::MinZ
        | FormalAggregateFunction::AverageZ => input == FormalValueTypeClass::Z,
        FormalAggregateFunction::SumInt32
        | FormalAggregateFunction::BitAndInt32
        | FormalAggregateFunction::BitOrInt32
        | FormalAggregateFunction::MaxInt32
        | FormalAggregateFunction::MinInt32
        | FormalAggregateFunction::SingleValueInt32
        | FormalAggregateFunction::AverageInt32Numeric
        | FormalAggregateFunction::VariancePopulationInt32
        | FormalAggregateFunction::VarianceSampleInt32
        | FormalAggregateFunction::StddevPopulationInt32
        | FormalAggregateFunction::StddevSampleInt32
        | FormalAggregateFunction::NumericDisplayScale(_) => input == FormalValueTypeClass::Int32,
        FormalAggregateFunction::SumInt64Numeric
        | FormalAggregateFunction::BitAndInt64
        | FormalAggregateFunction::BitOrInt64
        | FormalAggregateFunction::MaxInt64
        | FormalAggregateFunction::MinInt64
        | FormalAggregateFunction::AverageInt64Numeric => input == FormalValueTypeClass::Int64,
        FormalAggregateFunction::SumFloat
        | FormalAggregateFunction::MaxFloat
        | FormalAggregateFunction::MinFloat
        | FormalAggregateFunction::AverageFloat => input == FormalValueTypeClass::Float,
        FormalAggregateFunction::SumDouble
        | FormalAggregateFunction::MaxDouble
        | FormalAggregateFunction::MinDouble
        | FormalAggregateFunction::AverageDouble => input == FormalValueTypeClass::Double,
        FormalAggregateFunction::SumNumeric
        | FormalAggregateFunction::MaxNumeric
        | FormalAggregateFunction::MinNumeric
        | FormalAggregateFunction::StddevSampleNumericFixed { .. }
        | FormalAggregateFunction::AverageNumericFixed { .. }
        | FormalAggregateFunction::AverageNumericAtScale { .. } => {
            input == FormalValueTypeClass::Numeric
        }
        FormalAggregateFunction::MaxString => input == FormalValueTypeClass::String,
    }
}

fn aggregate_term_type_class(term: &FormalAggregateTerm) -> Option<FormalValueTypeClass> {
    match term {
        FormalAggregateTerm::Expr { term } => function_term_type_class(term),
        FormalAggregateTerm::Aggregate { function, arg, .. } => {
            let input = function_term_type_class(arg)?;
            aggregate_function_accepts_input(*function, input)
                .then(|| aggregate_function_type_class(*function))
        }
        FormalAggregateTerm::CountStar => Some(FormalValueTypeClass::Int64),
        FormalAggregateTerm::ScalarCall { operator, args } => {
            let argument_types = args
                .iter()
                .map(aggregate_term_type_class)
                .collect::<Option<Vec<_>>>()?;
            scalar_operator_argument_types_are_valid(*operator, &argument_types)
                .then(|| scalar_operator_result_type_class(*operator, &argument_types))?
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            let result = aggregate_term_type_class(else_expr)?;
            branches
                .iter()
                .all(|branch| {
                    aggregate_term_type_class(&branch.when) == Some(FormalValueTypeClass::Bool)
                        && aggregate_term_type_class(&branch.then_expr) == Some(result)
                })
                .then_some(result)
        }
    }
}

fn validate_scalar_expr_structure(expression: &FormalScalarExpr, path: &str) -> Result<(), String> {
    match expression {
        FormalScalarExpr::Leaf { result_ty, term } => {
            validate_aggregate_term_scalar_operators(term, &format!("{path}.term"))?;
            let actual = aggregate_term_type_class(term).ok_or_else(|| {
                format!("{path}: cannot determine the FormalSQL value type of scalar leaf")
            })?;
            let declared = formal_value_type_class(*result_ty);
            if actual != declared {
                return Err(format!(
                    "{path}: scalar leaf declares {declared:?} but its aggregate term returns {actual:?}"
                ));
            }
            let numeric_shape = aggregate_term_numeric_result_shape(term);
            if !numeric_result_shape_matches_type(numeric_shape, *result_ty) {
                return Err(format!(
                    "{path}: scalar leaf declares {result_ty:?}, but its numeric typmod shape is {numeric_shape:?}"
                ));
            }
            Ok(())
        }
        FormalScalarExpr::Call {
            result_ty,
            operator,
            args,
        } => {
            if *operator == ScalarOperator::Case {
                return Err(format!(
                    "{path}: lazy SQL CASE must use FormalScalarExpr::Case"
                ));
            }
            validate_scalar_call(*operator, args.len(), path)?;
            for (index, arg) in args.iter().enumerate() {
                let arg_path = format!("{path}.args[{index}]");
                require_scalar_kind(arg, FormalScalarResultKind::Value, &arg_path)?;
                validate_scalar_expr_structure(arg, &arg_path)?;
            }
            let argument_types = args
                .iter()
                .map(|arg| arg.value_type().map(formal_value_type_class))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| format!("{path}: scalar call has a non-value argument"))?;
            if !scalar_operator_argument_types_are_valid(*operator, &argument_types) {
                return Err(format!(
                    "{path}: scalar operator {operator:?} rejects argument types {argument_types:?}"
                ));
            }
            let actual = scalar_operator_result_type_class(*operator, &argument_types)
                .ok_or_else(|| format!("{path}: scalar operator result type is not determined"))?;
            let declared = formal_value_type_class(*result_ty);
            if actual != declared {
                return Err(format!(
                    "{path}: scalar call declares {declared:?} but {operator:?} returns {actual:?}"
                ));
            }
            let numeric_shape = scalar_call_numeric_result_shape(*operator, args);
            if !numeric_result_shape_matches_type(numeric_shape, *result_ty) {
                return Err(format!(
                    "{path}: scalar call declares {result_ty:?}, but {operator:?} produces numeric typmod shape {numeric_shape:?}"
                ));
            }
            Ok(())
        }
        FormalScalarExpr::Case {
            result_ty,
            condition,
            then_expr,
            else_expr,
        } => {
            require_scalar_kind(
                condition,
                FormalScalarResultKind::Boolean,
                &format!("{path}.condition"),
            )?;
            validate_scalar_expr_structure(condition, &format!("{path}.condition"))?;
            for (role, branch) in [("then", then_expr), ("else", else_expr)] {
                let branch_path = format!("{path}.{role}");
                require_scalar_kind(branch, FormalScalarResultKind::Value, &branch_path)?;
                validate_scalar_expr_structure(branch, &branch_path)?;
                if branch.value_type() != Some(*result_ty) {
                    return Err(format!(
                        "{branch_path}: CASE branch type {:?} does not equal resolved result type {result_ty:?}",
                        branch.value_type()
                    ));
                }
            }
            Ok(())
        }
        FormalScalarExpr::BooleanValue { expression } => {
            require_scalar_kind(
                expression,
                FormalScalarResultKind::Boolean,
                &format!("{path}.expression"),
            )?;
            validate_scalar_expr_structure(expression, &format!("{path}.expression"))
        }
        FormalScalarExpr::ValueBoolean { expression } => {
            require_scalar_kind(
                expression,
                FormalScalarResultKind::Value,
                &format!("{path}.expression"),
            )?;
            validate_scalar_expr_structure(expression, &format!("{path}.expression"))?;
            if expression.value_type() != Some(FormalAttributeType::Bool) {
                return Err(format!(
                    "{path}.expression: nullable BOOLEAN bridge requires a BOOLEAN value, found {:?}",
                    expression.value_type()
                ));
            }
            Ok(())
        }
        FormalScalarExpr::Predicate { predicate, args } => {
            validate_predicate_call(*predicate, args.len(), path)?;
            for (index, arg) in args.iter().enumerate() {
                let arg_path = format!("{path}.args[{index}]");
                require_scalar_kind(arg, FormalScalarResultKind::Value, &arg_path)?;
                validate_scalar_expr_structure(arg, &arg_path)?;
            }
            let argument_types = args
                .iter()
                .map(|arg| arg.value_type().map(formal_value_type_class))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| format!("{path}: predicate has a non-value argument"))?;
            if !scalar_predicate_argument_types_are_valid(*predicate, &argument_types) {
                return Err(format!(
                    "{path}: predicate {predicate:?} rejects argument types {argument_types:?}"
                ));
            }
            Ok(())
        }
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            for (role, child) in [("left", left), ("right", right)] {
                let child_path = format!("{path}.{role}");
                require_scalar_kind(child, FormalScalarResultKind::Boolean, &child_path)?;
                validate_scalar_expr_structure(child, &child_path)?;
            }
            Ok(())
        }
        FormalScalarExpr::Not { expression } => {
            require_scalar_kind(
                expression,
                FormalScalarResultKind::Boolean,
                &format!("{path}.expression"),
            )?;
            validate_scalar_expr_structure(expression, &format!("{path}.expression"))
        }
        FormalScalarExpr::True => Ok(()),
        FormalScalarExpr::QuantifiedComparison {
            predicate,
            args,
            query,
            ..
        } => {
            if args.len() != 1 {
                return Err(format!(
                    "{path}: quantified comparison requires exactly one outer value"
                ));
            }
            for (index, arg) in args.iter().enumerate() {
                let arg_path = format!("{path}.args[{index}]");
                require_scalar_kind(arg, FormalScalarResultKind::Value, &arg_path)?;
                validate_scalar_expr_structure(arg, &arg_path)?;
            }
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))?;
            let outputs = query_expr_output_signature(query).ok_or_else(|| {
                format!("{path}: quantified subquery has no exact output signature")
            })?;
            if outputs.len() != 1 {
                return Err(format!(
                    "{path}: quantified comparison requires exactly one subquery output column"
                ));
            }
            validate_predicate_call(*predicate, args.len() + outputs.len(), path)?;
            let mut argument_types = args
                .iter()
                .map(|arg| arg.value_type().map(formal_value_type_class))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| format!("{path}: quantified comparison has a non-value argument"))?;
            argument_types.extend(
                outputs
                    .iter()
                    .map(|output| formal_value_type_class(output.ty)),
            );
            if !scalar_predicate_argument_types_are_valid(*predicate, &argument_types) {
                return Err(format!(
                    "{path}: quantified predicate {predicate:?} rejects argument types {argument_types:?}"
                ));
            }
            Ok(())
        }
        FormalScalarExpr::In { args, query } => {
            if args.is_empty() {
                return Err(format!("{path}: IN requires at least one left value"));
            }
            for (index, arg) in args.iter().enumerate() {
                let arg_path = format!("{path}.args[{index}]");
                require_scalar_kind(arg, FormalScalarResultKind::Value, &arg_path)?;
                validate_scalar_expr_structure(arg, &arg_path)?;
            }
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))?;
            let outputs = query_expr_output_signature(query)
                .ok_or_else(|| format!("{path}: IN subquery has no exact output signature"))?;
            if outputs.len() != args.len() {
                return Err(format!(
                    "{path}: IN has {} left values but {} subquery output columns",
                    args.len(),
                    outputs.len()
                ));
            }
            for (index, (arg, output)) in args.iter().zip(&outputs).enumerate() {
                if arg.value_type() != Some(output.ty) {
                    return Err(format!(
                        "{path}.args[{index}]: IN value type {:?} does not equal subquery output type {:?}",
                        arg.value_type(),
                        output.ty
                    ));
                }
            }
            Ok(())
        }
        FormalScalarExpr::Exists { query } => {
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))
        }
        FormalScalarExpr::Subquery { result_ty, query } => {
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))?;
            let outputs = query_expr_output_signature(query)
                .ok_or_else(|| format!("{path}: scalar subquery has no exact output signature"))?;
            let [output] = outputs.as_slice() else {
                return Err(format!(
                    "{path}: scalar subquery requires exactly one output column, found {}",
                    outputs.len()
                ));
            };
            if output.ty != *result_ty {
                return Err(format!(
                    "{path}: scalar subquery result type {result_ty:?} does not equal its output type {:?}",
                    output.ty
                ));
            }
            Ok(())
        }
    }
}

pub(crate) fn validate_scalar_expr_in_context(
    expression: &FormalScalarExpr,
    context: FormalScalarContext,
    path: &str,
) -> Result<(), String> {
    validate_scalar_expr_structure(expression, path)?;
    let expected = context.expected_kind();
    if expression.result_kind() != expected {
        return Err(format!(
            "{path}: {} requires a {expected:?} scalar expression, found {:?}",
            context.name(),
            expression.result_kind()
        ));
    }
    if !context.permits_current_level_aggregates()
        && scalar_expr_contains_current_level_aggregate(expression)
    {
        return Err(format!(
            "{path}: {} rejects aggregates at this query level",
            context.name()
        ));
    }
    if !context.permits_subqueries() && scalar_expr_contains_subquery(expression) {
        return Err(format!(
            "{path}: {} rejects scalar and Boolean subqueries",
            context.name()
        ));
    }
    Ok(())
}

fn validate_select_scalar_operators(select: &[FormalSelectItem], path: &str) -> Result<(), String> {
    for (index, item) in select.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        validate_aggregate_term_scalar_operators(&item.expr, &item_path)?;
        let actual = aggregate_term_type_class(&item.expr).ok_or_else(|| {
            format!("{item_path}: cannot determine the FormalSQL value type of select item")
        })?;
        let declared = formal_value_type_class(item.alias_ty);
        if actual != declared {
            return Err(format!(
                "{item_path}: select item returns {actual:?} but its output alias declares {declared:?}"
            ));
        }
        let numeric_shape = aggregate_term_numeric_result_shape(&item.expr);
        if !numeric_result_shape_matches_type(numeric_shape, item.alias_ty) {
            return Err(format!(
                "{item_path}: select item declares {:?}, but its numeric typmod shape is {numeric_shape:?}",
                item.alias_ty
            ));
        }
    }
    Ok(())
}

fn validate_scalar_select_operators(
    select: &[FormalScalarSelectItem],
    context: FormalScalarContext,
    path: &str,
) -> Result<(), String> {
    for (index, item) in select.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        validate_scalar_expr_in_context(&item.expr, context, &item_path)?;
        if item.expr.value_type() != Some(item.alias_ty) {
            return Err(format!(
                "{item_path}: scalar result type {:?} does not equal output alias type {:?}",
                item.expr.value_type(),
                item.alias_ty
            ));
        }
    }
    Ok(())
}

fn validate_formula_expr_scalar_operators(
    formula: &FormalFormulaExpr,
    path: &str,
    context: FormalScalarContext,
) -> Result<(), String> {
    match formula {
        FormalFormulaExpr::True | FormalFormulaExpr::False => Ok(()),
        FormalFormulaExpr::Predicate { predicate, args } => {
            validate_predicate_call(*predicate, args.len(), path)?;
            for (index, arg) in args.iter().enumerate() {
                validate_aggregate_term_scalar_operators(arg, &format!("{path}.args[{index}]"))?;
                if !context.permits_current_level_aggregates()
                    && aggregate_term_contains_current_level_aggregate(arg)
                {
                    return Err(format!(
                        "{path}.args[{index}]: {} rejects aggregates at this query level",
                        context.name()
                    ));
                }
            }
            let argument_types = args
                .iter()
                .map(aggregate_term_type_class)
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| {
                    format!("{path}: cannot determine a predicate aggregate-term type")
                })?;
            if !scalar_predicate_argument_types_are_valid(*predicate, &argument_types) {
                return Err(format!(
                    "{path}: predicate {predicate:?} rejects argument types {argument_types:?}"
                ));
            }
            Ok(())
        }
        FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
            validate_formula_expr_scalar_operators(left, &format!("{path}.left"), context)?;
            validate_formula_expr_scalar_operators(right, &format!("{path}.right"), context)
        }
        FormalFormulaExpr::Not { formula } => {
            validate_formula_expr_scalar_operators(formula, &format!("{path}.not"), context)
        }
        FormalFormulaExpr::In { select, query } => {
            validate_select_scalar_operators(select, &format!("{path}.select"))?;
            if !context.permits_current_level_aggregates()
                && select
                    .iter()
                    .any(|item| aggregate_term_contains_current_level_aggregate(&item.expr))
            {
                return Err(format!(
                    "{path}.select: {} rejects aggregates at this query level",
                    context.name()
                ));
            }
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))
        }
        FormalFormulaExpr::QuantifiedComparison {
            predicate,
            args,
            query,
        } => {
            if args.len() != 1 {
                return Err(format!(
                    "{path}: quantified comparison requires exactly one outer argument"
                ));
            }
            validate_predicate_call(*predicate, args.len() + 1, path)?;
            for (index, arg) in args.iter().enumerate() {
                validate_aggregate_term_scalar_operators(arg, &format!("{path}.args[{index}]"))?;
                if !context.permits_current_level_aggregates()
                    && aggregate_term_contains_current_level_aggregate(arg)
                {
                    return Err(format!(
                        "{path}.args[{index}]: {} rejects aggregates at this query level",
                        context.name()
                    ));
                }
            }
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))?;
            if query_expr_output_signature(query).map(|signature| signature.len()) != Some(1) {
                return Err(format!(
                    "{path}: quantified comparison requires exactly one subquery output column"
                ));
            }
            let mut argument_types = args
                .iter()
                .map(aggregate_term_type_class)
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| {
                    format!("{path}: cannot determine a quantified predicate argument type")
                })?;
            argument_types.extend(
                query_expr_output_signature(query)
                    .expect("singleton output signature checked")
                    .iter()
                    .map(|output| formal_value_type_class(output.ty)),
            );
            if !scalar_predicate_argument_types_are_valid(*predicate, &argument_types) {
                return Err(format!(
                    "{path}: quantified predicate {predicate:?} rejects argument types {argument_types:?}"
                ));
            }
            Ok(())
        }
        FormalFormulaExpr::Exists { query } => {
            validate_query_expr_scalar_operators_at(query, &format!("{path}.query"))
        }
        FormalFormulaExpr::Scalar { expression } => {
            validate_scalar_expr_in_context(expression, context, &format!("{path}.scalar"))
        }
    }
}

/// Authoritative ordered output signature derivation for compositional query
/// syntax. `None` means that a constructor's exact ordered type/arity
/// invariant is inconsistent, so lowering and emission must reject it.
pub(crate) fn query_expr_output_signature(query: &FormalQueryExpr) -> Option<Vec<FormalAttribute>> {
    match query {
        FormalQueryExpr::Error { columns, .. }
        | FormalQueryExpr::Empty { columns }
        | FormalQueryExpr::Table { columns, .. } => Some(columns.clone()),
        FormalQueryExpr::EmptyTuple => Some(Vec::new()),
        FormalQueryExpr::Set { left, right, .. } => {
            let left = query_expr_output_signature(left)?;
            let right = query_expr_output_signature(right)?;
            (left == right).then_some(left)
        }
        FormalQueryExpr::CrossJoin { left, right } => {
            let mut signature = query_expr_output_signature(left)?;
            signature.extend(query_expr_output_signature(right)?);
            Some(signature)
        }
        FormalQueryExpr::Join {
            join_kind,
            matched_select,
            left_select,
            ..
        } => Some(select_output_signature(match join_kind {
            FormalQueryJoinKind::Semi | FormalQueryJoinKind::Anti => left_select,
            _ => matched_select,
        })),
        FormalQueryExpr::Projection { select, .. } | FormalQueryExpr::Group { select, .. } => {
            Some(select_output_signature(select))
        }
        FormalQueryExpr::ScalarProjection { select, .. }
        | FormalQueryExpr::ScalarGroup { select, .. } => {
            Some(scalar_select_output_signature(select))
        }
        FormalQueryExpr::RowMap { adapter, .. } => Some(adapter.output_attributes()),
        FormalQueryExpr::Selection { input, .. }
        | FormalQueryExpr::ScalarSelection { input, .. }
        | FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => query_expr_output_signature(input),
        FormalQueryExpr::GroupingSets { grouping_sets, .. } => {
            let first = select_output_signature(&grouping_sets.first()?.select);
            grouping_sets
                .iter()
                .map(|grouping_set| select_output_signature(&grouping_set.select))
                .all(|signature| first == signature)
                .then_some(first)
        }
        FormalQueryExpr::Rank {
            rank_attribute,
            input,
            ..
        } => {
            let mut signature = query_expr_output_signature(input)?;
            signature.push(rank_attribute.clone());
            Some(signature)
        }
        FormalQueryExpr::Window { input, items, .. } => {
            let mut signature = query_expr_output_signature(input)?;
            signature.extend(items.iter().map(|item| item.output.clone()));
            Some(signature)
        }
    }
}

fn select_output_signature(select: &[FormalSelectItem]) -> Vec<FormalAttribute> {
    select
        .iter()
        .map(|item| FormalAttribute {
            name: item.alias.clone(),
            ty: item.alias_ty,
        })
        .collect()
}

fn scalar_select_output_signature(select: &[FormalScalarSelectItem]) -> Vec<FormalAttribute> {
    select
        .iter()
        .map(|item| FormalAttribute {
            name: item.alias.clone(),
            ty: item.alias_ty,
        })
        .collect()
}

fn validate_predicate_call(
    predicate: FormalPredicate,
    arity: usize,
    path: &str,
) -> Result<(), String> {
    if predicate.accepts_arity(arity) {
        Ok(())
    } else {
        Err(format!(
            "{path}: predicate {predicate:?} does not accept {arity} arguments"
        ))
    }
}

fn validate_query_expr_scalar_operators_at(
    query: &FormalQueryExpr,
    path: &str,
) -> Result<(), String> {
    query_expr_output_signature(query).ok_or_else(|| {
        format!("{path}: query expression has no consistent ordered typed output signature")
    })?;
    match query {
        FormalQueryExpr::Error { .. }
        | FormalQueryExpr::Empty { .. }
        | FormalQueryExpr::EmptyTuple
        | FormalQueryExpr::Table { .. } => Ok(()),
        FormalQueryExpr::Set { left, right, .. } | FormalQueryExpr::CrossJoin { left, right } => {
            validate_query_expr_scalar_operators_at(left, &format!("{path}.left"))?;
            validate_query_expr_scalar_operators_at(right, &format!("{path}.right"))
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
            validate_formula_expr_scalar_operators(
                predicate,
                &format!("{path}.predicate"),
                FormalScalarContext::On,
            )?;
            validate_select_scalar_operators(matched_select, &format!("{path}.matchedSelect"))?;
            validate_select_scalar_operators(left_select, &format!("{path}.leftSelect"))?;
            validate_select_scalar_operators(right_select, &format!("{path}.rightSelect"))?;
            validate_query_expr_scalar_operators_at(left, &format!("{path}.left"))?;
            validate_query_expr_scalar_operators_at(right, &format!("{path}.right"))
        }
        FormalQueryExpr::Projection { select, input } => {
            validate_select_scalar_operators(select, &format!("{path}.select"))?;
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::ScalarProjection { select, input } => {
            validate_scalar_select_operators(
                select,
                FormalScalarContext::RowSelect,
                &format!("{path}.select"),
            )?;
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::RowMap { input, .. } => {
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::Selection { predicate, input } => {
            validate_formula_expr_scalar_operators(
                predicate,
                &format!("{path}.predicate"),
                FormalScalarContext::Where,
            )?;
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::ScalarSelection { predicate, input } => {
            validate_scalar_expr_in_context(
                predicate,
                FormalScalarContext::Where,
                &format!("{path}.predicate"),
            )?;
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::ScalarGroup {
            select,
            group_by,
            having,
            input,
        } => {
            validate_scalar_select_operators(
                select,
                FormalScalarContext::Select,
                &format!("{path}.select"),
            )?;
            for (index, term) in group_by.iter().enumerate() {
                let key_path = format!("{path}.groupBy[{index}]");
                validate_scalar_expr_in_context(term, FormalScalarContext::GroupBy, &key_path)?;
                if !matches!(term, FormalScalarExpr::Leaf { .. }) {
                    return Err(format!(
                        "{key_path}: native GROUP BY keys must use a typed scalar leaf"
                    ));
                }
            }
            validate_scalar_expr_in_context(
                having,
                FormalScalarContext::Having,
                &format!("{path}.having"),
            )?;
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::Group {
            select,
            group_by,
            having,
            input,
        } => {
            validate_select_scalar_operators(select, &format!("{path}.select"))?;
            for (index, term) in group_by.iter().enumerate() {
                validate_aggregate_term_scalar_operators(
                    term,
                    &format!("{path}.groupBy[{index}]"),
                )?;
                aggregate_term_type_class(term).ok_or_else(|| {
                    format!(
                        "{path}.groupBy[{index}]: cannot determine the FormalSQL value type of GROUP BY key"
                    )
                })?;
                if aggregate_term_contains_current_level_aggregate(term) {
                    return Err(format!(
                        "{path}.groupBy[{index}]: GROUP BY rejects aggregates at this query level"
                    ));
                }
            }
            validate_formula_expr_scalar_operators(
                having,
                &format!("{path}.having"),
                FormalScalarContext::Having,
            )?;
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::GroupingSets {
            grouping_sets,
            input,
        } => {
            for (set_index, grouping_set) in grouping_sets.iter().enumerate() {
                validate_select_scalar_operators(
                    &grouping_set.select,
                    &format!("{path}.groupingSets[{set_index}].select"),
                )?;
                for (term_index, term) in grouping_set.group_by.iter().enumerate() {
                    validate_aggregate_term_scalar_operators(
                        term,
                        &format!("{path}.groupingSets[{set_index}].groupBy[{term_index}]"),
                    )?;
                    aggregate_term_type_class(term).ok_or_else(|| {
                        format!(
                            "{path}.groupingSets[{set_index}].groupBy[{term_index}]: cannot determine the FormalSQL value type of GROUP BY key"
                        )
                    })?;
                    if aggregate_term_contains_current_level_aggregate(term) {
                        return Err(format!(
                            "{path}.groupingSets[{set_index}].groupBy[{term_index}]: GROUP BY rejects aggregates at this query level"
                        ));
                    }
                }
            }
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::Window { items, input, .. } => {
            for (index, item) in items.iter().enumerate() {
                if let FormalWindowFunction::Aggregate { term }
                | FormalWindowFunction::FullPartitionAggregate { term } = &item.function
                {
                    validate_aggregate_term_scalar_operators(
                        term,
                        &format!("{path}.items[{index}]"),
                    )?;
                    let actual = aggregate_term_type_class(term).ok_or_else(|| {
                        format!(
                            "{path}.items[{index}]: cannot determine the FormalSQL value type of window item"
                        )
                    })?;
                    let declared = formal_value_type_class(item.output.ty);
                    if actual != declared {
                        return Err(format!(
                            "{path}.items[{index}]: window item returns {actual:?} but its output declares {declared:?}"
                        ));
                    }
                } else if item.output.ty != FormalAttributeType::Int64 {
                    return Err(format!(
                        "{path}.items[{index}]: ROW_NUMBER output must be BIGINT"
                    ));
                }
            }
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::Rank {
            rank_attribute,
            input,
            ..
        } => {
            if rank_attribute.ty != FormalAttributeType::Int64 {
                return Err(format!("{path}: RANK output must be BIGINT"));
            }
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
        FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => {
            validate_query_expr_scalar_operators_at(input, &format!("{path}.input"))
        }
    }
}
