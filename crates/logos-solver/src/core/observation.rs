use serde::Serialize;
use sha2::{Digest, Sha256};

use super::syntax::{FormalAggregateTerm, FormalFunctionTerm, FormalSchema, LoweringStatus};
use super::{
    FormalAttribute, FormalQueryExpr, FormalScalarExpr, FormalScalarSelectItem,
    ProofLoweringReport, query_expr_output_signature,
};

const OBSERVATION_CERTIFICATE_SCHEMA_VERSION: u32 = 1;

/// Host-recomputed facts about the possible successful observations of every
/// lowered statement.  These facts are deliberately separate from
/// permutation closure: a query may be closed under every permutation while
/// still admitting several different bags.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ObservationCertificateReport {
    pub schema_version: u32,
    pub verification_input_key: String,
    pub verification_input_sha256: String,
    pub lowering_sha256: String,
    pub source: Vec<StatementObservationFacts>,
    pub target: Vec<StatementObservationFacts>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct StatementObservationFacts {
    pub statement: usize,
    pub permutation_closed: bool,
    pub success_bag_functional: CertificateStatus,
    pub success_observation_functional: CertificateStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_success_rows: Option<u64>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub candidate_keys: Vec<ObservationKey>,
}

#[cfg(test)]
impl StatementObservationFacts {
    pub(crate) fn success_bag_is_functional(&self) -> bool {
        self.success_bag_functional.is_proven()
    }

    pub(crate) fn success_observation_is_functional(&self) -> bool {
        self.success_observation_functional.is_proven()
    }

    pub(crate) fn bag_residual(&self) -> String {
        self.success_bag_functional.explanation()
    }

    pub(crate) fn observation_residual(&self) -> String {
        self.success_observation_functional.explanation()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case", tag = "status")]
pub(crate) enum CertificateStatus {
    Proven { rule: String },
    Unknown { residual: String },
}

impl CertificateStatus {
    fn proven(rule: impl Into<String>) -> Self {
        Self::Proven { rule: rule.into() }
    }

    fn unknown(residual: impl Into<String>) -> Self {
        Self::Unknown {
            residual: residual.into(),
        }
    }

    #[cfg(test)]
    fn is_proven(&self) -> bool {
        matches!(self, Self::Proven { .. })
    }

    #[cfg(test)]
    fn explanation(&self) -> String {
        match self {
            Self::Proven { rule } => rule.clone(),
            Self::Unknown { residual } => residual.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ObservationKey {
    pub attributes: Vec<FormalAttribute>,
    pub basis: String,
}

#[derive(Debug, Clone)]
struct Facts {
    permutation_closed: bool,
    bag_functional: bool,
    bag_rule: String,
    observation_functional: bool,
    observation_rule: String,
    max_rows: Option<u64>,
    keys: Vec<ObservationKey>,
}

impl Facts {
    fn report(self, statement: usize) -> StatementObservationFacts {
        StatementObservationFacts {
            statement,
            permutation_closed: self.permutation_closed,
            success_bag_functional: if self.bag_functional {
                CertificateStatus::proven(self.bag_rule)
            } else {
                CertificateStatus::unknown(self.bag_rule)
            },
            success_observation_functional: if self.observation_functional {
                CertificateStatus::proven(self.observation_rule)
            } else {
                CertificateStatus::unknown(self.observation_rule)
            },
            max_success_rows: self.max_rows,
            candidate_keys: self.keys,
        }
    }

    fn unknown(reason: impl Into<String>) -> Self {
        let reason = reason.into();
        Self {
            permutation_closed: false,
            bag_functional: false,
            bag_rule: reason.clone(),
            observation_functional: false,
            observation_rule: reason,
            max_rows: None,
            keys: Vec::new(),
        }
    }
}

pub(crate) fn analyze_observation_certificates(
    lowering: &ProofLoweringReport,
    input: &super::VerificationInput,
) -> ObservationCertificateReport {
    let lowering_bytes =
        serde_json::to_vec(lowering).expect("serializable lowering report has a JSON encoding");
    let schema = (lowering.schema.status == LoweringStatus::Lowered)
        .then_some(lowering.schema.schema.as_ref())
        .flatten();
    ObservationCertificateReport {
        schema_version: OBSERVATION_CERTIFICATE_SCHEMA_VERSION,
        verification_input_key: input.stable_cache_key(),
        verification_input_sha256: format!(
            "{:x}",
            Sha256::digest(
                serde_json::to_vec(input)
                    .expect("serializable verification input has a JSON encoding")
            )
        ),
        lowering_sha256: format!("{:x}", Sha256::digest(&lowering_bytes)),
        source: analyze_program(schema, &lowering.source),
        target: analyze_program(schema, &lowering.target),
    }
}

fn analyze_program(
    schema: Option<&FormalSchema>,
    program: &super::LoweredProgram,
) -> Vec<StatementObservationFacts> {
    let program_is_authoritative = schema.is_some() && program.status == LoweringStatus::Lowered;
    program
        .statements
        .iter()
        .enumerate()
        .map(|(index, statement)| {
            if !program_is_authoritative || statement.status != LoweringStatus::Lowered {
                return Facts::unknown(
                    "the schema, program, or statement lowering is blocked and cannot authorize an observation certificate",
                )
                .report(index + 1);
            }
            if !statement.bindings.is_empty() {
                return Facts::unknown(
                    "query-local bindings require BoundQuery-aware observation analysis",
                )
                .report(index + 1);
            }
            statement.query_expr.as_ref().map_or_else(
                || {
                    Facts::unknown(
                        "the statement did not lower to an authoritative FormalQueryExpr",
                    )
                },
                |query| analyze_query(schema, query),
            )
            .report(index + 1)
        })
        .collect()
}

fn analyze_query(schema: Option<&FormalSchema>, query: &FormalQueryExpr) -> Facts {
    match query {
        FormalQueryExpr::Error { .. } => Facts::unknown(
            "the lowered statement is an analysis-error relation, not a successful observation",
        ),
        FormalQueryExpr::Empty { .. } => Facts {
            permutation_closed: true,
            bag_functional: true,
            bag_rule: "EMPTY has exactly one successful bag".to_owned(),
            observation_functional: true,
            observation_rule: "EMPTY has exactly one successful row list".to_owned(),
            max_rows: Some(0),
            keys: Vec::new(),
        },
        FormalQueryExpr::EmptyTuple => Facts {
            permutation_closed: true,
            bag_functional: true,
            bag_rule: "the SQL unit relation has one fixed singleton bag".to_owned(),
            observation_functional: true,
            observation_rule: "the SQL unit relation has one fixed singleton list".to_owned(),
            max_rows: Some(1),
            keys: vec![ObservationKey {
                attributes: Vec::new(),
                basis: "singleton unit relation".to_owned(),
            }],
        },
        FormalQueryExpr::Table { relation, columns } => {
            let keys = schema
                .and_then(|schema| {
                    schema
                        .tables
                        .iter()
                        .find(|table| table.relation == *relation)
                })
                .map(table_keys)
                .unwrap_or_default();
            Facts {
                permutation_closed: true,
                bag_functional: true,
                bag_rule: "a table scan reads one database relation bag".to_owned(),
                observation_functional: false,
                observation_rule: "a multi-row table scan admits every row permutation".to_owned(),
                max_rows: None,
                keys: keys
                    .into_iter()
                    .filter(|key| key.attributes.iter().all(|item| columns.contains(item)))
                    .collect(),
            }
        }
        FormalQueryExpr::Projection { select, input } => {
            let child = analyze_query(schema, input);
            if !select
                .iter()
                .all(|item| scalar_expr_is_row_local(&item.expr))
            {
                return Facts {
                    permutation_closed: false,
                    bag_functional: false,
                    bag_rule: "a subquery-bearing scalar projection needs a FormalSQL functionality proof"
                        .to_owned(),
                    observation_functional: false,
                    observation_rule:
                        "a scalar subquery may expose several legal values per containing evaluation"
                            .to_owned(),
                    max_rows: child.max_rows,
                    keys: Vec::new(),
                };
            }
            let keys = project_scalar_keys(&child.keys, select);
            Facts {
                permutation_closed: child.permutation_closed,
                bag_functional: child.bag_functional,
                bag_rule: if child.bag_functional {
                    "deterministic row-local scalar projection preserves a functional success bag"
                        .to_owned()
                } else {
                    format!(
                        "scalar projection still needs child bag uniqueness: {}",
                        child.bag_rule
                    )
                },
                observation_functional: child.observation_functional,
                observation_rule: if child.observation_functional {
                    "order-preserving scalar projection preserves a functional observation"
                        .to_owned()
                } else {
                    format!(
                        "scalar projection preserves rather than resolves child order choices: {}",
                        child.observation_rule
                    )
                },
                max_rows: child.max_rows,
                keys,
            }
        }
        FormalQueryExpr::Selection { predicate, input } => {
            let child = analyze_query(schema, input);
            if !scalar_expr_is_row_local(predicate) {
                return Facts {
                    permutation_closed: false,
                    bag_functional: false,
                    bag_rule:
                        "a subquery-bearing scalar predicate needs a FormalSQL functionality proof"
                            .to_owned(),
                    observation_functional: false,
                    observation_rule:
                        "a scalar subquery predicate may expose several legal acceptances"
                            .to_owned(),
                    max_rows: child.max_rows,
                    keys: child.keys,
                };
            }
            Facts {
                permutation_closed: child.permutation_closed,
                bag_functional: child.bag_functional,
                bag_rule: if child.bag_functional {
                    "a row-local deterministic scalar filter preserves a functional success bag"
                        .to_owned()
                } else {
                    format!(
                        "scalar filter still needs child bag uniqueness: {}",
                        child.bag_rule
                    )
                },
                observation_functional: child.observation_functional,
                observation_rule: if child.observation_functional {
                    "order-preserving scalar filtering preserves a functional observation"
                        .to_owned()
                } else {
                    format!(
                        "scalar filtering preserves rather than resolves child order choices: {}",
                        child.observation_rule
                    )
                },
                max_rows: child.max_rows,
                keys: child.keys,
            }
        }
        FormalQueryExpr::Set { op, left, right } => {
            let left = analyze_query(schema, left);
            let right = analyze_query(schema, right);
            let bag_functional = left.bag_functional && right.bag_functional;
            let max_rows = match op {
                super::syntax::FormalSetOp::Union => checked_sum(left.max_rows, right.max_rows),
                super::syntax::FormalSetOp::Inter => min_known(left.max_rows, right.max_rows),
                super::syntax::FormalSetOp::Diff => left.max_rows,
            };
            let observation_functional = bag_functional && max_rows.is_some_and(|bound| bound <= 1);
            Facts {
                permutation_closed: true,
                bag_functional,
                bag_rule: if bag_functional {
                    "the bag set operator is functional over two functional child bags".to_owned()
                } else {
                    "the bag set operator needs both child success bags to be functional".to_owned()
                },
                observation_functional,
                observation_rule: if observation_functional {
                    "the functional set result contains at most one row".to_owned()
                } else {
                    "a bag-reset set result may realize several row permutations".to_owned()
                },
                max_rows,
                keys: Vec::new(),
            }
        }
        FormalQueryExpr::CrossJoin { left, right } => {
            let left = analyze_query(schema, left);
            let right = analyze_query(schema, right);
            let bag_functional = left.bag_functional && right.bag_functional;
            let max_rows = checked_product(left.max_rows, right.max_rows);
            let observation_functional = bag_functional && max_rows.is_some_and(|bound| bound <= 1);
            let mut keys = Vec::new();
            if bag_functional {
                for left_key in &left.keys {
                    for right_key in &right.keys {
                        // Formal attributes are occurrence names rather than
                        // hidden origin IDs.  Do not collapse two same-named
                        // join columns into one apparent composite key.
                        if left_key
                            .attributes
                            .iter()
                            .any(|attribute| right_key.attributes.contains(attribute))
                        {
                            continue;
                        }
                        let mut attributes = left_key.attributes.clone();
                        attributes.extend(right_key.attributes.clone());
                        keys.push(ObservationKey {
                            attributes,
                            basis: format!(
                                "cartesian product of ({}) and ({})",
                                left_key.basis, right_key.basis
                            ),
                        });
                    }
                }
            }
            Facts {
                permutation_closed: true,
                bag_functional,
                bag_rule: if bag_functional {
                    "cartesian product is functional over two functional child bags".to_owned()
                } else {
                    "cartesian product needs both child success bags to be functional".to_owned()
                },
                observation_functional,
                observation_rule: if observation_functional {
                    "the functional cartesian result contains at most one row".to_owned()
                } else {
                    "cartesian join is a bag reset and may realize several permutations".to_owned()
                },
                max_rows,
                keys,
            }
        }
        FormalQueryExpr::Distinct { input } => {
            let child = analyze_query(schema, input);
            let max_rows = child.max_rows;
            let bag_functional = child.bag_functional;
            let observation_functional = bag_functional && max_rows.is_some_and(|bound| bound <= 1);
            let outputs = query_expr_output_signature(query).unwrap_or_default();
            let keys = if attributes_are_distinct(&outputs) {
                vec![ObservationKey {
                    attributes: outputs,
                    basis: "DISTINCT makes the complete output row duplicate-free".to_owned(),
                }]
            } else {
                Vec::new()
            };
            Facts {
                permutation_closed: true,
                bag_functional,
                bag_rule: if bag_functional {
                    "duplicate elimination is functional on a functional child bag".to_owned()
                } else {
                    format!(
                        "DISTINCT still needs child bag uniqueness: {}",
                        child.bag_rule
                    )
                },
                observation_functional,
                observation_rule: if observation_functional {
                    "the DISTINCT result contains at most one row".to_owned()
                } else {
                    "DISTINCT fixes a bag but not an order between distinct rows".to_owned()
                },
                max_rows,
                keys,
            }
        }
        FormalQueryExpr::OrderBy { keys, input } => {
            let child = analyze_query(schema, input);
            let outputs = query_expr_output_signature(query).unwrap_or_default();
            let sort_attributes = keys
                .iter()
                .map(|key| FormalAttribute {
                    name: key.attribute_name.clone(),
                    ty: key.attribute_ty,
                })
                .collect::<Vec<_>>();
            let unique_order = child.keys.iter().any(|key| {
                key.attributes
                    .iter()
                    .all(|attribute| sort_attributes.contains(attribute))
            });
            let observes_complete_row = !outputs.is_empty()
                && attributes_are_distinct(&outputs)
                && outputs
                    .iter()
                    .all(|attribute| sort_attributes.contains(attribute));
            let at_most_one = child.max_rows.is_some_and(|bound| bound <= 1);
            let observation_functional =
                child.bag_functional && (unique_order || observes_complete_row || at_most_one);
            let observation_rule = if observation_functional {
                if at_most_one {
                    "ORDER BY receives at most one successful row".to_owned()
                } else if unique_order {
                    "ORDER BY keys contain a proven output candidate key".to_owned()
                } else {
                    "ORDER BY compares every visible output attribute, so tied rows are observationally equal"
                        .to_owned()
                }
            } else if !child.bag_functional {
                format!(
                    "ORDER BY still needs child bag uniqueness: {}",
                    child.bag_rule
                )
            } else {
                "ORDER BY keys do not determine a unique observation; tied rows remain relational"
                    .to_owned()
            };
            Facts {
                permutation_closed: false,
                bag_functional: child.bag_functional,
                bag_rule: if child.bag_functional {
                    "ORDER BY changes only list order and preserves the functional child bag"
                        .to_owned()
                } else {
                    format!(
                        "ORDER BY still needs child bag uniqueness: {}",
                        child.bag_rule
                    )
                },
                observation_functional,
                observation_rule,
                max_rows: child.max_rows,
                keys: child.keys,
            }
        }
        FormalQueryExpr::Offset { count, input } => {
            let child = analyze_query(schema, input);
            let max_rows = child.max_rows.map(|bound| bound.saturating_sub(*count));
            Facts {
                permutation_closed: false,
                bag_functional: child.observation_functional,
                bag_rule: if child.observation_functional {
                    "OFFSET slices one functional child observation".to_owned()
                } else {
                    format!(
                        "OFFSET may select different bags until child order is unique: {}",
                        child.observation_rule
                    )
                },
                observation_functional: child.observation_functional,
                observation_rule: if child.observation_functional {
                    "OFFSET preserves a functional child observation".to_owned()
                } else {
                    format!(
                        "OFFSET consumes a non-unique child observation: {}",
                        child.observation_rule
                    )
                },
                max_rows,
                keys: child.keys,
            }
        }
        FormalQueryExpr::Fetch { count, input } => {
            let child = analyze_query(schema, input);
            let is_zero = *count == 0;
            let observation_functional = is_zero || child.observation_functional;
            Facts {
                permutation_closed: false,
                bag_functional: observation_functional,
                bag_rule: if is_zero {
                    "FETCH 0 has the unique empty successful bag".to_owned()
                } else if child.observation_functional {
                    "FETCH slices one functional child observation".to_owned()
                } else {
                    format!(
                        "FETCH may select different bags until child order is unique: {}",
                        child.observation_rule
                    )
                },
                observation_functional,
                observation_rule: if is_zero {
                    "FETCH 0 has the unique empty successful observation".to_owned()
                } else if child.observation_functional {
                    "FETCH preserves a functional child observation".to_owned()
                } else {
                    format!(
                        "FETCH consumes a non-unique child observation: {}",
                        child.observation_rule
                    )
                },
                max_rows: child
                    .max_rows
                    .map_or(Some(*count), |bound| Some(bound.min(*count))),
                keys: child.keys,
            }
        }
        FormalQueryExpr::Join { .. } => Facts {
            permutation_closed: true,
            ..Facts::unknown(
                "JOIN success-bag functionality needs predicate/select and child functionality contracts",
            )
        },
        FormalQueryExpr::Group { .. } => Facts {
            permutation_closed: true,
            ..Facts::unknown(
                "GROUP may retain several successful bags through correlated predicates or representation-sensitive runtime checks",
            )
        },
        FormalQueryExpr::GroupingSets { .. } => Facts {
            permutation_closed: true,
            ..Facts::unknown(
                "GROUPING SETS needs a shared-child aggregate functionality certificate",
            )
        },
        FormalQueryExpr::Rank { .. } => Facts {
            permutation_closed: true,
            ..Facts::unknown("RANK needs peer-order and child-bag functionality contracts")
        },
        FormalQueryExpr::Window { .. } => Facts {
            permutation_closed: true,
            ..Facts::unknown(
                "window peers can change even the output bag; a window-specific functionality proof is required",
            )
        },
    }
}

fn table_keys(table: &super::syntax::FormalTable) -> Vec<ObservationKey> {
    let mut keys = Vec::new();
    if let Some(primary_key) = &table.constraints.primary_key {
        keys.push(ObservationKey {
            attributes: primary_key.clone(),
            basis: format!("PRIMARY KEY of {}", table.relation),
        });
    }
    for unique in &table.constraints.unique {
        if unique
            .columns
            .iter()
            .all(|column| table.constraints.not_null.contains(column))
        {
            keys.push(ObservationKey {
                attributes: unique.columns.clone(),
                basis: format!("UNIQUE + NOT NULL of {}", table.relation),
            });
        }
    }
    keys
}

fn project_scalar_keys(
    keys: &[ObservationKey],
    select: &[FormalScalarSelectItem],
) -> Vec<ObservationKey> {
    keys.iter()
        .filter_map(|key| {
            let mut outputs = Vec::with_capacity(key.attributes.len());
            for attribute in &key.attributes {
                let item = select.iter().find(|item| {
                    matches!(
                        &item.expr,
                        FormalScalarExpr::Leaf {
                            term: FormalAggregateTerm::Expr {
                                term: FormalFunctionTerm::Attribute { name, ty }
                            },
                            ..
                        } if name == &attribute.name && ty == &attribute.ty
                    )
                })?;
                outputs.push(FormalAttribute {
                    name: item.alias.clone(),
                    ty: item.alias_ty,
                });
            }
            attributes_are_distinct(&outputs).then(|| ObservationKey {
                attributes: outputs,
                basis: format!("direct scalar projection of {}", key.basis),
            })
        })
        .collect()
}

fn attributes_are_distinct(attributes: &[FormalAttribute]) -> bool {
    attributes
        .iter()
        .enumerate()
        .all(|(index, attribute)| !attributes[..index].contains(attribute))
}

fn scalar_expr_is_row_local(expression: &FormalScalarExpr) -> bool {
    match expression {
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => true,
        FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
            args.iter().all(scalar_expr_is_row_local)
        }
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            scalar_expr_is_row_local(condition)
                && scalar_expr_is_row_local(then_expr)
                && scalar_expr_is_row_local(else_expr)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => scalar_expr_is_row_local(expression),
        FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
            operands.iter().all(scalar_expr_is_row_local)
        }
        FormalScalarExpr::QuantifiedComparison { .. }
        | FormalScalarExpr::In { .. }
        | FormalScalarExpr::Exists { .. }
        | FormalScalarExpr::Subquery { .. } => false,
    }
}

fn checked_sum(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    left?.checked_add(right?)
}

fn checked_product(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    left?.checked_mul(right?)
}

fn min_known(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    Some(left?.min(right?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::syntax::{
        FormalAttributeType, FormalNullDirection, FormalQueryBinding, FormalSortDirection,
        FormalSortKey, FormalTable, FormalTableConstraints, FormalUniqueConstraint,
    };

    fn attr(name: &str) -> FormalAttribute {
        FormalAttribute {
            name: name.to_owned(),
            ty: FormalAttributeType::Int32,
        }
    }

    fn table_with_primary_key() -> (FormalSchema, FormalQueryExpr) {
        let id = attr("id");
        let value = attr("value");
        (
            FormalSchema {
                tables: vec![FormalTable {
                    relation: "t".to_owned(),
                    attributes: vec![id.clone(), value.clone()],
                    constraints: FormalTableConstraints {
                        not_null: vec![id.clone()],
                        primary_key: Some(vec![id.clone()]),
                        ..FormalTableConstraints::default()
                    },
                }],
                rocq_module: String::new(),
            },
            FormalQueryExpr::Table {
                relation: "t".to_owned(),
                columns: vec![id, value],
            },
        )
    }

    #[test]
    fn primary_key_order_is_exact_but_non_key_order_is_not() {
        let (schema, table) = table_with_primary_key();
        let ordered_by_id = FormalQueryExpr::OrderBy {
            keys: vec![FormalSortKey {
                attribute_name: "id".to_owned(),
                attribute_ty: FormalAttributeType::Int32,
                direction: FormalSortDirection::Asc,
                null_direction: FormalNullDirection::Last,
            }],
            input: Box::new(table.clone()),
        };
        let ordered_by_value = FormalQueryExpr::OrderBy {
            keys: vec![FormalSortKey {
                attribute_name: "value".to_owned(),
                attribute_ty: FormalAttributeType::Int32,
                direction: FormalSortDirection::Asc,
                null_direction: FormalNullDirection::Last,
            }],
            input: Box::new(table),
        };

        assert!(analyze_query(Some(&schema), &ordered_by_id).observation_functional);
        assert!(!analyze_query(Some(&schema), &ordered_by_value).observation_functional);
    }

    #[test]
    fn fetch_requires_child_order_functionality_even_when_child_bag_is_fixed() {
        let (schema, table) = table_with_primary_key();
        let fetch = FormalQueryExpr::Fetch {
            count: 1,
            input: Box::new(table),
        };
        let facts = analyze_query(Some(&schema), &fetch);
        assert!(!facts.bag_functional);
        assert!(!facts.observation_functional);
    }

    #[test]
    fn bag_reset_is_not_mistaken_for_bag_functionality() {
        let (_, table) = table_with_primary_key();
        let group = FormalQueryExpr::Group {
            select: Vec::new(),
            group_by: Vec::new(),
            having: FormalScalarExpr::True,
            input: Box::new(table),
        };
        let facts = analyze_query(None, &group);
        assert!(facts.permutation_closed);
        assert!(!facts.bag_functional);
    }

    #[test]
    fn nullable_unique_is_not_an_order_key_certificate() {
        let value = attr("value");
        let table = FormalTable {
            relation: "t".to_owned(),
            attributes: vec![value.clone()],
            constraints: FormalTableConstraints {
                unique: vec![FormalUniqueConstraint {
                    columns: vec![value],
                }],
                ..FormalTableConstraints::default()
            },
        };
        assert!(table_keys(&table).is_empty());
    }

    #[test]
    fn same_named_cross_join_keys_are_not_collapsed_into_one_occurrence() {
        let id = attr("id");
        let schema = FormalSchema {
            tables: ["left_t", "right_t"]
                .into_iter()
                .map(|relation| FormalTable {
                    relation: relation.to_owned(),
                    attributes: vec![id.clone()],
                    constraints: FormalTableConstraints {
                        not_null: vec![id.clone()],
                        primary_key: Some(vec![id.clone()]),
                        ..FormalTableConstraints::default()
                    },
                })
                .collect(),
            rocq_module: String::new(),
        };
        let cross = FormalQueryExpr::CrossJoin {
            left: Box::new(FormalQueryExpr::Table {
                relation: "left_t".to_owned(),
                columns: vec![id.clone()],
            }),
            right: Box::new(FormalQueryExpr::Table {
                relation: "right_t".to_owned(),
                columns: vec![id.clone()],
            }),
        };
        let ordered = FormalQueryExpr::OrderBy {
            keys: vec![FormalSortKey {
                attribute_name: "id".to_owned(),
                attribute_ty: FormalAttributeType::Int32,
                direction: FormalSortDirection::Asc,
                null_direction: FormalNullDirection::Last,
            }],
            input: Box::new(cross),
        };
        assert!(!analyze_query(Some(&schema), &ordered).observation_functional);
    }

    #[test]
    fn retained_syntax_from_a_blocked_lowering_never_authorizes_a_certificate() {
        let (schema, query) = table_with_primary_key();
        let program = super::super::LoweredProgram {
            status: super::super::LoweringStatus::Blocked,
            statements: vec![super::super::LoweredQuery {
                status: super::super::LoweringStatus::Blocked,
                bindings: Vec::new(),
                query_expr: Some(query),
                output_signature: None,
                diagnostics: Vec::new(),
            }],
            diagnostics: Vec::new(),
        };
        let facts = analyze_program(Some(&schema), &program);
        assert!(!facts[0].success_bag_is_functional());
        assert!(!facts[0].success_observation_is_functional());
    }

    #[test]
    fn query_local_bindings_never_authorize_a_body_only_certificate() {
        let (schema, _) = table_with_primary_key();
        let body = FormalQueryExpr::EmptyTuple;
        let program = super::super::LoweredProgram {
            status: super::super::LoweringStatus::Lowered,
            statements: vec![super::super::LoweredQuery {
                status: super::super::LoweringStatus::Lowered,
                bindings: vec![FormalQueryBinding {
                    id: "binding_1".to_owned(),
                    source_name: "local".to_owned(),
                    relation: "__logos_local_1".to_owned(),
                    output_signature: Vec::new(),
                    query_expr: FormalQueryExpr::EmptyTuple,
                }],
                query_expr: Some(body),
                output_signature: Some(Vec::new()),
                diagnostics: Vec::new(),
            }],
            diagnostics: Vec::new(),
        };

        let facts = analyze_program(Some(&schema), &program);
        assert!(!facts[0].success_bag_is_functional());
        assert!(!facts[0].success_observation_is_functional());
        assert!(facts[0].bag_residual().contains("BoundQuery-aware"));
        assert!(facts[0].observation_residual().contains("BoundQuery-aware"));
    }
}
