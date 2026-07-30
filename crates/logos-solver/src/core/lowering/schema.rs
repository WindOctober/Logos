use super::emit::{emit_rocq_create_schema, emit_rocq_schema_module};
use super::scalar::{string_typmod_codes, z_constant_function};
use super::*;
use logos_ir::ir::{Table, UniqueIndexTerm};
use std::collections::{BTreeMap, BTreeSet};

impl LoweringContext {
    pub(super) fn lower_schema(&mut self, path: &str, schema: &Schema) -> Option<FormalSchema> {
        let mut relation_names = BTreeSet::new();
        for (index, table) in schema.tables.iter().enumerate() {
            if !relation_names.insert(table.name.as_str()) {
                self.error(
                    &format!("{path}.tables[{index}].name"),
                    "duplicate_schema_relation",
                    "PostgreSQL rejects multiple CREATE TABLE declarations with the same canonical relation identity; FormalSQL cannot soundly lower a schema that redeclares one relation name.",
                );
                return None;
            }
        }
        let mut tables = schema
            .tables
            .iter()
            .enumerate()
            .map(|(index, table)| self.lower_table(&format!("{path}.tables[{index}]"), table))
            .collect::<Option<Vec<_>>>()?;
        let formal_tables = tables
            .iter()
            .map(|table| (table.relation.clone(), table.attributes.clone()))
            .collect::<BTreeMap<_, _>>();
        for (index, (table, formal_table)) in
            schema.tables.iter().zip(tables.iter_mut()).enumerate()
        {
            formal_table.constraints = self.lower_table_constraints(
                &format!("{path}.tables[{index}]"),
                table,
                &formal_table.attributes,
                &formal_tables,
            )?;
        }
        let rocq_create_schema = emit_rocq_create_schema(&tables);
        let rocq_module =
            emit_rocq_schema_module(&rocq_create_schema, &tables, self.config.sql_environment);
        Some(FormalSchema {
            tables,
            rocq_module,
        })
    }

    fn lower_table(&mut self, path: &str, table: &Table) -> Option<FormalTable> {
        if table.name.is_empty() {
            self.error(
                path,
                "empty_table_name",
                "FormalSQL relation names must be non-empty.",
            );
            return None;
        }
        if !has_unique_column_names(&table.columns) {
            self.error(
                path,
                "duplicate_table_attribute",
                "FormalSQL table schema uses a finite set of attributes; duplicate column names cannot be represented soundly.",
            );
            return None;
        }
        let attributes = table
            .columns
            .iter()
            .enumerate()
            .map(|(index, column)| {
                self.lower_schema_attribute(&format!("{path}.columns[{index}]"), column)
            })
            .collect::<Option<Vec<_>>>()?;
        Some(FormalTable {
            relation: table.name.clone(),
            attributes,
            constraints: FormalTableConstraints::default(),
        })
    }

    fn lower_table_constraints(
        &mut self,
        path: &str,
        table: &Table,
        attributes: &[FormalAttribute],
        formal_tables: &BTreeMap<String, Vec<FormalAttribute>>,
    ) -> Option<FormalTableConstraints> {
        let column_positions = table
            .columns
            .iter()
            .enumerate()
            .map(|(position, column)| (column.name.as_str(), position))
            .collect::<BTreeMap<_, _>>();

        let mut not_null_names = BTreeSet::new();
        let mut previous_not_null_position = None;
        let mut not_null = Vec::with_capacity(table.constraints.not_null.len());
        for (index, name) in table.constraints.not_null.iter().enumerate() {
            let constraint_path = format!("{path}.constraints.notNull[{index}]");
            let Some(&position) = column_positions.get(name.as_str()) else {
                self.error(
                    &constraint_path,
                    "unknown_not_null_constraint_attribute",
                    &format!(
                        "table {:?} declares NOT NULL for unknown column {name:?}",
                        table.name
                    ),
                );
                return None;
            };
            if !not_null_names.insert(name.as_str()) {
                self.error(
                    &constraint_path,
                    "duplicate_not_null_constraint_attribute",
                    &format!("table {:?} repeats NOT NULL column {name:?}", table.name),
                );
                return None;
            }
            if previous_not_null_position.is_some_and(|previous| position <= previous) {
                self.error(
                    &constraint_path,
                    "not_null_constraint_declaration_order",
                    &format!(
                        "table {:?} NOT NULL columns must follow column declaration order",
                        table.name
                    ),
                );
                return None;
            }
            previous_not_null_position = Some(position);
            not_null.push(attributes[position].clone());
        }

        let primary_key = match &table.constraints.primary_key {
            None => None,
            Some(primary_key) => {
                if primary_key.is_empty() {
                    self.error(
                        &format!("{path}.constraints.primaryKey"),
                        "empty_primary_key_constraint",
                        &format!(
                            "table {:?} primary key must contain at least one column",
                            table.name
                        ),
                    );
                    return None;
                }
                let mut primary_key_names = BTreeSet::new();
                let mut lowered_primary_key = Vec::with_capacity(primary_key.len());
                for (index, name) in primary_key.iter().enumerate() {
                    let constraint_path = format!("{path}.constraints.primaryKey[{index}]");
                    let Some(&position) = column_positions.get(name.as_str()) else {
                        self.error(
                            &constraint_path,
                            "unknown_primary_key_constraint_attribute",
                            &format!(
                                "table {:?} primary key names unknown column {name:?}",
                                table.name
                            ),
                        );
                        return None;
                    };
                    if !primary_key_names.insert(name.as_str()) {
                        self.error(
                            &constraint_path,
                            "duplicate_primary_key_constraint_attribute",
                            &format!("table {:?} repeats primary-key column {name:?}", table.name),
                        );
                        return None;
                    }
                    if !not_null_names.contains(name.as_str()) {
                        self.error(
                            &constraint_path,
                            "primary_key_constraint_not_not_null",
                            &format!(
                                "table {:?} primary-key column {name:?} is missing from NOT NULL",
                                table.name
                            ),
                        );
                        return None;
                    }
                    lowered_primary_key.push(attributes[position].clone());
                }
                Some(lowered_primary_key)
            }
        };

        let unique = table
            .constraints
            .unique
            .iter()
            .enumerate()
            .map(|(index, unique)| {
                self.lower_constraint_attributes(
                    &format!("{path}.constraints.unique[{index}].columns"),
                    &table.name,
                    &unique.columns,
                    attributes,
                )
                .map(|columns| FormalUniqueConstraint { columns })
            })
            .collect::<Option<Vec<_>>>()?;

        let foreign_keys = table
            .constraints
            .foreign_keys
            .iter()
            .enumerate()
            .map(|(index, foreign)| {
                if foreign.match_type != ForeignKeyMatch::Simple {
                    self.error(
                        &format!("{path}.constraints.foreignKeys[{index}].matchType"),
                        "foreign_key_match_not_supported",
                        "The benchmark contract supports PostgreSQL MATCH SIMPLE snapshot semantics only.",
                    );
                    return None;
                }
                let columns = self.lower_constraint_attributes(
                    &format!("{path}.constraints.foreignKeys[{index}].columns"),
                    &table.name,
                    &foreign.columns,
                    attributes,
                )?;
                let Some(referenced_attributes) = formal_tables.get(&foreign.referenced_table)
                else {
                    self.error(
                        &format!(
                            "{path}.constraints.foreignKeys[{index}].referencedTable"
                        ),
                        "unknown_foreign_key_referenced_table",
                        &format!(
                            "foreign key on {:?} references unknown table {:?}",
                            table.name, foreign.referenced_table
                        ),
                    );
                    return None;
                };
                let referenced_columns = self.lower_constraint_attributes(
                    &format!(
                        "{path}.constraints.foreignKeys[{index}].referencedColumns"
                    ),
                    &foreign.referenced_table,
                    &foreign.referenced_columns,
                    referenced_attributes,
                )?;
                if columns.len() != referenced_columns.len() {
                    self.error(
                        &format!("{path}.constraints.foreignKeys[{index}]"),
                        "foreign_key_arity_mismatch",
                        "A PostgreSQL foreign key must have the same number of referencing and referenced columns.",
                    );
                    return None;
                }
                for (component_index, (source, referenced)) in
                    columns.iter().zip(&referenced_columns).enumerate()
                {
                    if !formal_foreign_key_attribute_compatible(source.ty, referenced.ty) {
                        self.error(
                            &format!(
                                "{path}.constraints.foreignKeys[{index}].columns[{component_index}]"
                            ),
                            "foreign_key_equality_not_supported",
                            &format!(
                                "FormalSQL supports foreign-key equality for identical declared types and INTEGER/BIGINT pairs; found {:?} referencing {:?}",
                                source.ty, referenced.ty
                            ),
                        );
                        return None;
                    }
                }
                Some(FormalForeignKeyConstraint {
                    columns,
                    referenced_relation: foreign.referenced_table.clone(),
                    referenced_columns,
                })
            })
            .collect::<Option<Vec<_>>>()?;

        let checks = table
            .constraints
            .checks
            .iter()
            .enumerate()
            .map(|(index, check)| {
                self.lower_integrity_predicate(
                    &format!("{path}.constraints.checks[{index}].expression"),
                    &check.expression,
                    attributes,
                )
                .map(|formula| FormalCheckConstraint { formula })
            })
            .collect::<Option<Vec<_>>>()?;

        let unique_indexes = table
            .constraints
            .unique_indexes
            .iter()
            .enumerate()
            .map(|(index, unique_index)| {
                let terms = unique_index
                    .terms
                    .iter()
                    .enumerate()
                    .map(|(term_index, term)| {
                        self.lower_unique_index_term(
                            &format!(
                                "{path}.constraints.uniqueIndexes[{index}].terms[{term_index}]"
                            ),
                            term,
                            attributes,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                let predicate = match unique_index.predicate.as_ref() {
                    Some(predicate) => Some(self.lower_integrity_predicate(
                        &format!("{path}.constraints.uniqueIndexes[{index}].predicate"),
                        predicate,
                        attributes,
                    )?),
                    None => None,
                };
                Some(FormalUniqueIndexConstraint { terms, predicate })
            })
            .collect::<Option<Vec<_>>>()?;

        let constraints = FormalTableConstraints {
            not_null,
            primary_key,
            unique,
            foreign_keys,
            checks,
            unique_indexes,
        };
        if formal_constraints_use_string_equality(&constraints)
            && !self
                .config
                .sql_environment
                .has_postgres_utf8_c_text_semantics()
        {
            self.error(
                &format!("{path}.constraints"),
                "integrity_text_environment_not_attested",
                "String-valued PRIMARY KEY, UNIQUE, FOREIGN KEY, CHECK, or unique-index semantics require the exact PostgreSQL UTF8/libc/C collation and character-classification environment.",
            );
            return None;
        }
        Some(constraints)
    }

    fn lower_constraint_attributes(
        &mut self,
        path: &str,
        table: &str,
        names: &[String],
        attributes: &[FormalAttribute],
    ) -> Option<Vec<FormalAttribute>> {
        if names.is_empty() {
            self.error(
                path,
                "empty_integrity_key",
                &format!("integrity key on table {table:?} must not be empty"),
            );
            return None;
        }
        let positions = attributes
            .iter()
            .enumerate()
            .map(|(index, attribute)| (attribute.name.as_str(), index))
            .collect::<BTreeMap<_, _>>();
        let mut seen = BTreeSet::new();
        names
            .iter()
            .enumerate()
            .map(|(index, name)| {
                if !seen.insert(name.as_str()) {
                    self.error(
                        &format!("{path}[{index}]"),
                        "duplicate_integrity_key_attribute",
                        &format!("integrity key on table {table:?} repeats column {name:?}"),
                    );
                    return None;
                }
                positions
                    .get(name.as_str())
                    .map(|position| attributes[*position].clone())
                    .or_else(|| {
                        self.error(
                            &format!("{path}[{index}]"),
                            "unknown_integrity_key_attribute",
                            &format!(
                                "integrity key on table {table:?} names unknown column {name:?}"
                            ),
                        );
                        None
                    })
            })
            .collect()
    }

    fn lower_unique_index_term(
        &mut self,
        path: &str,
        term: &UniqueIndexTerm,
        attributes: &[FormalAttribute],
    ) -> Option<FormalFunctionTerm> {
        let (expression, ty) =
            self.lower_integrity_value_expr(path, &term.expression, attributes)?;
        match term.operator_class.as_deref() {
            None => {}
            Some("varchar_pattern_ops")
                if matches!(
                    ty,
                    FormalAttributeType::String {
                        typmod: SqlStringType::Text | SqlStringType::Varchar { .. }
                    }
                ) => {}
            Some(other) => {
                self.error(
                    path,
                    "unique_index_operator_class_not_supported",
                    &format!("unsupported unique-index operator class {other:?}"),
                );
                return None;
            }
        }
        // Direction and NULL placement affect physical index ordering, not
        // the set of snapshots satisfying uniqueness.
        Some(expression)
    }

    fn lower_integrity_predicate(
        &mut self,
        path: &str,
        predicate: &IntegrityPredicate,
        attributes: &[FormalAttribute],
    ) -> Option<FormalConstraintFormula> {
        match predicate {
            IntegrityPredicate::Truth { expression } => {
                let (term, ty) = self.lower_integrity_value_expr(path, expression, attributes)?;
                if ty != FormalAttributeType::Bool {
                    self.error(
                        path,
                        "integrity_truth_expression_not_boolean",
                        "A bare integrity predicate must have PostgreSQL BOOLEAN type.",
                    );
                    return None;
                }
                Some(FormalConstraintFormula::Predicate {
                    predicate: FormalPredicate::Eq,
                    args: vec![
                        aggregate_expr(term),
                        aggregate_expr(FormalFunctionTerm::Constant {
                            raw: "true".to_owned(),
                            ty: Some(FormalAttributeType::Bool),
                        }),
                    ],
                })
            }
            IntegrityPredicate::IsTrue { expression } => {
                let (term, ty) = self.lower_integrity_value_expr(path, expression, attributes)?;
                if ty != FormalAttributeType::Bool {
                    self.error(
                        path,
                        "integrity_is_true_expression_not_boolean",
                        "An IS TRUE integrity predicate must have PostgreSQL BOOLEAN type.",
                    );
                    return None;
                }
                Some(FormalConstraintFormula::Predicate {
                    predicate: FormalPredicate::IsTrue,
                    args: vec![aggregate_expr(term)],
                })
            }
            IntegrityPredicate::IsNull { expression }
            | IntegrityPredicate::IsNotNull { expression } => {
                let (term, _) = self.lower_integrity_value_expr(path, expression, attributes)?;
                Some(FormalConstraintFormula::Predicate {
                    predicate: if matches!(predicate, IntegrityPredicate::IsNull { .. }) {
                        FormalPredicate::IsNull
                    } else {
                        FormalPredicate::IsNotNull
                    },
                    args: vec![aggregate_expr(term)],
                })
            }
            IntegrityPredicate::Comparison {
                comparison,
                left,
                right,
            } => {
                let (left, _) = self.lower_integrity_value_expr(path, left, attributes)?;
                let (right, _) = self.lower_integrity_value_expr(path, right, attributes)?;
                Some(FormalConstraintFormula::Predicate {
                    predicate: match comparison {
                        IntegrityComparison::Equal => FormalPredicate::Eq,
                        IntegrityComparison::NotEqual => FormalPredicate::Neq,
                    },
                    args: vec![aggregate_expr(left), aggregate_expr(right)],
                })
            }
            IntegrityPredicate::Any {
                comparison,
                left,
                values,
            } => {
                let (left, _) = self.lower_integrity_value_expr(path, left, attributes)?;
                let mut formulas = values.iter().map(|value| {
                    let (right, _) = self.lower_integrity_value_expr(path, value, attributes)?;
                    Some(FormalConstraintFormula::Predicate {
                        predicate: match comparison {
                            IntegrityComparison::Equal => FormalPredicate::Eq,
                            IntegrityComparison::NotEqual => FormalPredicate::Neq,
                        },
                        args: vec![aggregate_expr(left.clone()), aggregate_expr(right)],
                    })
                });
                let Some(first) = formulas.next().flatten() else {
                    self.error(path, "empty_integrity_any", "ANY array must not be empty.");
                    return None;
                };
                formulas.try_fold(first, |left, right| {
                    right.map(|right| FormalConstraintFormula::Or {
                        left: Box::new(left),
                        right: Box::new(right),
                    })
                })
            }
            IntegrityPredicate::And { left, right } | IntegrityPredicate::Or { left, right } => {
                let left = self.lower_integrity_predicate(path, left, attributes)?;
                let right = self.lower_integrity_predicate(path, right, attributes)?;
                Some(if matches!(predicate, IntegrityPredicate::And { .. }) {
                    FormalConstraintFormula::And {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                } else {
                    FormalConstraintFormula::Or {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                })
            }
            IntegrityPredicate::Not { predicate } => Some(FormalConstraintFormula::Not {
                formula: Box::new(self.lower_integrity_predicate(path, predicate, attributes)?),
            }),
        }
    }

    fn lower_integrity_value_expr(
        &mut self,
        path: &str,
        expression: &IntegrityValueExpr,
        attributes: &[FormalAttribute],
    ) -> Option<(FormalFunctionTerm, FormalAttributeType)> {
        match expression {
            IntegrityValueExpr::Column { name } => attributes
                .iter()
                .find(|attribute| attribute.name == *name)
                .map(|attribute| {
                    (
                        FormalFunctionTerm::Attribute {
                            name: attribute.name.clone(),
                            ty: attribute.ty,
                        },
                        attribute.ty,
                    )
                })
                .or_else(|| {
                    self.error(
                        path,
                        "unknown_integrity_expression_attribute",
                        &format!("integrity expression names unknown column {name:?}"),
                    );
                    None
                }),
            IntegrityValueExpr::Literal { raw, ty } => {
                let formal_ty = sql_type_to_formal_attribute_type(ty);
                let raw = if matches!(ty, SqlType::String(_)) {
                    format!("'{}'", raw.replace('\'', "''"))
                } else {
                    raw.clone()
                };
                Some((
                    FormalFunctionTerm::Constant {
                        raw,
                        ty: Some(formal_ty),
                    },
                    formal_ty,
                ))
            }
            IntegrityValueExpr::Cast { expression, ty } => {
                let (expression, source_ty) =
                    self.lower_integrity_value_expr(path, expression, attributes)?;
                let target_ty = sql_type_to_formal_attribute_type(ty);
                if source_ty == target_ty {
                    return Some((expression, target_ty));
                }
                let Some((tag, length)) = string_typmod_codes(target_ty) else {
                    self.error(
                        path,
                        "integrity_cast_not_supported",
                        &format!("unsupported integrity cast from {source_ty:?} to {target_ty:?}"),
                    );
                    return None;
                };
                if !matches!(source_ty, FormalAttributeType::String { .. }) {
                    self.error(
                        path,
                        "integrity_cast_not_supported",
                        "Only benchmark-observed character-to-character casts are supported in integrity expressions.",
                    );
                    return None;
                }
                Some((
                    FormalFunctionTerm::ScalarCall {
                        operator: ScalarOperator::Cast(ScalarCast::StringExplicit),
                        args: vec![
                            expression,
                            z_constant_function(tag),
                            z_constant_function(length),
                        ],
                    },
                    target_ty,
                ))
            }
            IntegrityValueExpr::Lower { expression } => {
                let (expression, source_ty) =
                    self.lower_integrity_value_expr(path, expression, attributes)?;
                if !matches!(source_ty, FormalAttributeType::String { .. }) {
                    self.error(
                        path,
                        "integrity_lower_not_string",
                        "lower() in an integrity expression requires a character input.",
                    );
                    return None;
                }
                let target_ty = FormalAttributeType::String {
                    typmod: SqlStringType::Text,
                };
                Some((
                    FormalFunctionTerm::ScalarCall {
                        operator: ScalarOperator::StringCase(ScalarStringCase::Lower),
                        args: vec![expression],
                    },
                    target_ty,
                ))
            }
            IntegrityValueExpr::Coalesce { arguments } => {
                let mut lowered = arguments
                    .iter()
                    .map(|argument| self.lower_integrity_value_expr(path, argument, attributes))
                    .collect::<Option<Vec<_>>>()?;
                let Some((_, result_ty)) = lowered.first() else {
                    self.error(
                        path,
                        "empty_integrity_coalesce",
                        "COALESCE in an integrity expression must have arguments.",
                    );
                    return None;
                };
                let result_ty = *result_ty;
                if lowered.iter().any(|(_, ty)| *ty != result_ty) {
                    self.error(
                        path,
                        "integrity_coalesce_type_mismatch",
                        "COALESCE integrity arguments must have one already-resolved PostgreSQL type.",
                    );
                    return None;
                }
                let last = lowered.pop().expect("nonempty checked").0;
                let term = lowered
                    .into_iter()
                    .rev()
                    .fold(last, |fallback, (value, _)| {
                        let condition = FormalFunctionTerm::ScalarCall {
                            operator: ScalarOperator::PredicateValue(FormalPredicate::IsNotNull),
                            args: vec![value.clone()],
                        };
                        FormalFunctionTerm::ScalarCall {
                            operator: ScalarOperator::Case,
                            args: vec![condition, value, fallback],
                        }
                    });
                Some((term, result_ty))
            }
        }
    }

    fn lower_schema_attribute(&mut self, path: &str, column: &Column) -> Option<FormalAttribute> {
        if column.name.is_empty() {
            self.error(
                path,
                "empty_attribute_name",
                "FormalSQL attributes must be non-empty.",
            );
            return None;
        }
        let ty = self.lower_attribute_type(path, column, AttributeTypeContext::Schema)?;
        Some(FormalAttribute {
            name: column.name.clone(),
            ty,
        })
    }
}

fn aggregate_expr(term: FormalFunctionTerm) -> FormalAggregateTerm {
    FormalAggregateTerm::Expr { term }
}

fn formal_attribute_is_string(attribute: &FormalAttribute) -> bool {
    matches!(attribute.ty, FormalAttributeType::String { .. })
}

fn formal_foreign_key_attribute_compatible(
    source: FormalAttributeType,
    referenced: FormalAttributeType,
) -> bool {
    source == referenced
        || matches!(
            (source, referenced),
            (FormalAttributeType::Int32, FormalAttributeType::Int64)
                | (FormalAttributeType::Int64, FormalAttributeType::Int32)
        )
}

fn formal_constraints_use_string_equality(constraints: &FormalTableConstraints) -> bool {
    constraints
        .primary_key
        .iter()
        .flatten()
        .any(formal_attribute_is_string)
        || constraints
            .unique
            .iter()
            .flat_map(|constraint| &constraint.columns)
            .any(formal_attribute_is_string)
        || constraints
            .foreign_keys
            .iter()
            .flat_map(|constraint| {
                constraint
                    .columns
                    .iter()
                    .chain(&constraint.referenced_columns)
            })
            .any(formal_attribute_is_string)
        || constraints
            .checks
            .iter()
            .any(|constraint| formal_constraint_formula_uses_string(&constraint.formula))
        || constraints.unique_indexes.iter().any(|constraint| {
            constraint.terms.iter().any(formal_function_uses_string)
                || constraint
                    .predicate
                    .as_ref()
                    .is_some_and(formal_constraint_formula_uses_string)
        })
}

fn formal_function_uses_string(term: &FormalFunctionTerm) -> bool {
    match term {
        FormalFunctionTerm::Constant { ty, .. } => {
            matches!(ty, Some(FormalAttributeType::String { .. }))
        }
        FormalFunctionTerm::Attribute { ty, .. } => {
            matches!(ty, FormalAttributeType::String { .. })
        }
        FormalFunctionTerm::ScalarCall { args, .. } => args.iter().any(formal_function_uses_string),
    }
}

fn formal_aggregate_uses_string(term: &FormalAggregateTerm) -> bool {
    match term {
        FormalAggregateTerm::Expr { term } | FormalAggregateTerm::Aggregate { arg: term, .. } => {
            formal_function_uses_string(term)
        }
        FormalAggregateTerm::CountStar => false,
        FormalAggregateTerm::ScalarCall { args, .. } => {
            args.iter().any(formal_aggregate_uses_string)
        }
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => {
            branches.iter().any(|branch| {
                formal_aggregate_uses_string(&branch.when)
                    || formal_aggregate_uses_string(&branch.then_expr)
            }) || formal_aggregate_uses_string(else_expr)
        }
    }
}

fn formal_constraint_formula_uses_string(formula: &FormalConstraintFormula) -> bool {
    match formula {
        FormalConstraintFormula::True | FormalConstraintFormula::False => false,
        FormalConstraintFormula::Predicate { args, .. } => {
            args.iter().any(formal_aggregate_uses_string)
        }
        FormalConstraintFormula::And { left, right }
        | FormalConstraintFormula::Or { left, right } => {
            formal_constraint_formula_uses_string(left)
                || formal_constraint_formula_uses_string(right)
        }
        FormalConstraintFormula::Not { formula } => formal_constraint_formula_uses_string(formula),
    }
}
