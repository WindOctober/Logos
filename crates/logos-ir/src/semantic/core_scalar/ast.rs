use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CoreScalarExpr {
    Value { expr: CoreValueExpr },
    Predicate { expr: CorePredicateExpr },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CoreValueExpr {
    InputRef {
        index: usize,
    },
    CorrelatedRef {
        correlation: String,
        field: String,
    },
    Literal {
        raw: String,
    },
    TypeAnnotation {
        expr: Box<CoreValueExpr>,
        ty: String,
    },
    Cast {
        expr: Box<CoreValueExpr>,
        ty: String,
    },
    Case {
        branches: Vec<CoreCaseBranch>,
        else_expr: Box<CoreValueExpr>,
    },
    Arithmetic {
        op: CoreArithmeticOp,
        args: Vec<CoreValueExpr>,
    },
    StringConcat {
        args: Vec<CoreValueExpr>,
    },
    StringFunction {
        op: CoreStringFunctionOp,
        args: Vec<CoreValueExpr>,
    },
    NumericFunction {
        op: CoreNumericFunctionOp,
        args: Vec<CoreValueExpr>,
    },
    Extract {
        field: String,
        expr: Box<CoreValueExpr>,
    },
    WindowFunction {
        raw: String,
    },
    PredicateAsValue {
        predicate: Box<CorePredicateExpr>,
    },
    ScalarSubquery {
        rel: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CoreCaseBranch {
    pub when: CorePredicateExpr,
    pub then: CoreValueExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CorePredicateCaseBranch {
    pub when: CorePredicateExpr,
    pub then: CorePredicateExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreArithmeticOp {
    Plus,
    UnaryMinus,
    Minus,
    Multiply,
    Divide,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreStringFunctionOp {
    Lower,
    Upper,
    Substring,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreNumericFunctionOp {
    Exp,
    Power,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CorePredicateExpr {
    Comparison {
        op: CoreComparisonOp,
        left: Box<CoreValueExpr>,
        right: Box<CoreValueExpr>,
    },
    IsNull {
        expr: Box<CoreValueExpr>,
    },
    IsNotNull {
        expr: Box<CoreValueExpr>,
    },
    IsTrue {
        predicate: Box<CorePredicateExpr>,
    },
    IsNotTrue {
        predicate: Box<CorePredicateExpr>,
    },
    IsFalse {
        predicate: Box<CorePredicateExpr>,
    },
    IsNotFalse {
        predicate: Box<CorePredicateExpr>,
    },
    And {
        predicates: Vec<CorePredicateExpr>,
    },
    Or {
        predicates: Vec<CorePredicateExpr>,
    },
    Not {
        predicate: Box<CorePredicateExpr>,
    },
    Like {
        value: Box<CoreValueExpr>,
        pattern: Box<CoreValueExpr>,
        #[serde(skip_serializing_if = "Option::is_none")]
        escape: Option<Box<CoreValueExpr>>,
    },
    BooleanValue {
        expr: Box<CoreValueExpr>,
    },
    Case {
        branches: Vec<CorePredicateCaseBranch>,
        else_predicate: Box<CorePredicateExpr>,
    },
    Exists {
        rel: String,
    },
    InSubquery {
        values: Vec<CoreValueExpr>,
        rel: String,
    },
    Search {
        value: Box<CoreValueExpr>,
        sarg: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreComparisonOp {
    Eq,
    NotEq,
    Lt,
    Lte,
    Gt,
    Gte,
    IsNotDistinctFrom,
}
