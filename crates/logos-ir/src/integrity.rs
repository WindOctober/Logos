//! Benchmark-facing PostgreSQL schema-integrity contract.
//!
//! SQLSolver's materialized DDL intentionally omits parts of the source
//! contract.  This module reconstructs those declarations from the adjacent
//! frozen metadata/WeTune sidecar, parses the closed benchmark expression
//! language, and provides the one contract consumed by IR lowering,
//! PostgreSQL snapshot validation, prompts, and generated artifacts.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};

use crate::error::{Error, Result};
use crate::ir::{
    CheckConstraint, ForeignKeyConstraint, ForeignKeyMatch, IntegrityComparison,
    IntegrityNullsOrder, IntegrityPredicate, IntegritySortDirection, IntegrityValueExpr, Schema,
    SqlStringType, SqlType, TableConstraints, UniqueConstraint, UniqueIndexConstraint,
    UniqueIndexTerm,
};

const WETUNE_RAW_TYPE_SEMANTICS: &str = "sourceType/sourceDeclaration are authoritative for benchmark semantics; normalizedFrontendType is a tool-facing lowering.";
const WETUNE_TYPE_AUTHORITY: &str = "parser_facing_normalized_ddl";
const WETUNE_SIDECAR_AUTHORITY: &str = "integrity_declarations_only";
const WETUNE_RAW_TYPE_DISPOSITION: &str = "preserved_for_audit_but_overridden_by_typeAuthority";
const WETUNE_UNIQUE_SEMANTICS: &str = "sql_unique_allows_multiple_nulls";
const RBOT_MATERIALIZATION_POLICY: &str = "logos-postgres-calcite-source-preserving-v1";

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SchemaIntegrityContract {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub case_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<PathBuf>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub tables: Vec<ContractTable>,
    #[serde(default, skip_serializing_if = "is_false")]
    pub requires_postgres_utf8_c_text_semantics: bool,
}

fn is_false(value: &bool) -> bool {
    !*value
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ContractTable {
    pub name: String,
    pub constraints: TableConstraints,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct IntegrityValidationCheck {
    pub kind: String,
    pub table: String,
    pub description: String,
    pub sql: String,
}

impl SchemaIntegrityContract {
    pub fn is_empty(&self) -> bool {
        self.tables.iter().all(|table| table.constraints.is_empty())
    }

    pub fn constraint_kinds(&self) -> Vec<String> {
        let mut kinds = BTreeSet::new();
        for table in &self.tables {
            let constraints = &table.constraints;
            if !constraints.not_null.is_empty() {
                kinds.insert("not_null".to_owned());
            }
            if constraints.primary_key.is_some() {
                kinds.insert("primary_key".to_owned());
            }
            if !constraints.unique.is_empty() {
                kinds.insert("unique".to_owned());
            }
            if !constraints.foreign_keys.is_empty() {
                kinds.insert("foreign_key".to_owned());
            }
            if !constraints.checks.is_empty() {
                kinds.insert("check".to_owned());
            }
            if !constraints.unique_indexes.is_empty() {
                kinds.insert("partial_expression_unique_index".to_owned());
            }
        }
        kinds.into_iter().collect()
    }

    /// Form the single effective contract after the parser-facing DDL has
    /// been converted to typed Logos IR.  Adjacent benchmark metadata is
    /// merged first, so the returned value contains both DDL declarations and
    /// declarations retained only in pair metadata or a WeTune sidecar.
    pub fn merged_with_schema(&self, schema: &Schema) -> Result<Self> {
        let mut schema = schema.clone();
        self.merge_into_schema(&mut schema)?;
        let requires_postgres_utf8_c_text_semantics =
            schema_integrity_uses_string_semantics(&schema)?;
        Ok(Self {
            case_id: self.case_id.clone(),
            source: self.source.clone(),
            tables: schema
                .tables
                .into_iter()
                .filter(|table| !table.constraints.is_empty())
                .map(|table| ContractTable {
                    name: table.name,
                    constraints: table.constraints,
                })
                .collect(),
            requires_postgres_utf8_c_text_semantics,
        })
    }

    /// Merge metadata declarations with DDL declarations transported by the
    /// Calcite boundary.  Semantic duplicates are coalesced; disagreements
    /// fail closed instead of allowing either source to win silently.
    pub fn merge_into_schema(&self, schema: &mut Schema) -> Result<()> {
        for contract_table in &self.tables {
            let position = resolve_schema_table(schema, &contract_table.name)?;
            let constraints =
                canonicalize_contract_constraints(schema, position, &contract_table.constraints)?;
            let table_name = schema.tables[position].name.clone();
            merge_table_constraints(
                &mut schema.tables[position].constraints,
                &constraints,
                &table_name,
            )?;
        }
        validate_and_normalize_schema_constraints(schema)?;
        Ok(())
    }

    pub fn human_readable(&self) -> String {
        if self.is_empty() {
            return "No benchmark integrity constraints.".to_owned();
        }
        let mut lines = Vec::new();
        if self.requires_postgres_utf8_c_text_semantics {
            lines.push(
                "Environment: PostgreSQL UTF8 with libc C collation and C character classification (required for string integrity semantics)."
                    .to_owned(),
            );
        }
        for table in &self.tables {
            let c = &table.constraints;
            if !c.not_null.is_empty() {
                lines.push(format!(
                    "{}: NOT NULL ({})",
                    display_ident(&table.name),
                    display_columns(&c.not_null)
                ));
            }
            if let Some(columns) = &c.primary_key {
                lines.push(format!(
                    "{}: PRIMARY KEY ({})",
                    display_ident(&table.name),
                    display_columns(columns)
                ));
            }
            for unique in &c.unique {
                lines.push(format!(
                    "{}: UNIQUE ({}) [NULL values are distinct]",
                    display_ident(&table.name),
                    display_columns(&unique.columns)
                ));
            }
            for foreign in &c.foreign_keys {
                lines.push(format!(
                    "{}: FOREIGN KEY ({}) REFERENCES {} ({}) MATCH SIMPLE{}",
                    display_ident(&table.name),
                    display_columns(&foreign.columns),
                    display_ident(&foreign.referenced_table),
                    display_columns(&foreign.referenced_columns),
                    foreign
                        .referential_actions
                        .as_deref()
                        .filter(|value| !value.is_empty())
                        .map(|value| format!(" [{value}; snapshot semantics]"))
                        .unwrap_or_default()
                ));
            }
            for check in &c.checks {
                lines.push(format!(
                    "{}: CHECK ({}) [TRUE/UNKNOWN pass; FALSE/error violate]",
                    display_ident(&table.name),
                    check.source_sql
                ));
            }
            for index in &c.unique_indexes {
                let terms = index
                    .terms
                    .iter()
                    .map(|term| term.source_sql.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                let predicate = index
                    .predicate_sql
                    .as_deref()
                    .filter(|value| !value.is_empty())
                    .map(|value| format!(" WHERE {value}"))
                    .unwrap_or_default();
                lines.push(format!(
                    "{}: UNIQUE INDEX ({terms}){predicate} [predicate TRUE participates; NULL values are distinct]",
                    display_ident(&table.name)
                ));
            }
        }
        lines.join("\n")
    }

    /// PostgreSQL queries which validate the final read-only snapshot using
    /// PostgreSQL's own typed equality, collation, casts, and error behavior.
    pub fn validation_checks(&self) -> Vec<IntegrityValidationCheck> {
        let mut checks = Vec::new();
        for table in &self.tables {
            let table_sql = quote_ident(&table.name);
            let constraints = &table.constraints;
            for column in &constraints.not_null {
                let description = format!(
                    "{}.{} is NOT NULL",
                    display_ident(&table.name),
                    display_ident(column)
                );
                checks.push(IntegrityValidationCheck {
                    kind: "not_null".to_owned(),
                    table: table.name.clone(),
                    description,
                    sql: format!(
                        "SELECT NOT EXISTS (SELECT 1 FROM {table_sql} WHERE {} IS NULL)",
                        quote_ident(column)
                    ),
                });
            }
            if let Some(columns) = &constraints.primary_key {
                checks.push(unique_validation_check(
                    "primary_key",
                    &table.name,
                    columns.iter().map(|column| quote_ident(column)).collect(),
                    "TRUE",
                    true,
                    format!("PRIMARY KEY ({})", display_columns(columns)),
                ));
            }
            for unique in &constraints.unique {
                checks.push(unique_validation_check(
                    "unique",
                    &table.name,
                    unique
                        .columns
                        .iter()
                        .map(|column| quote_ident(column))
                        .collect(),
                    "TRUE",
                    true,
                    format!("UNIQUE ({})", display_columns(&unique.columns)),
                ));
            }
            for foreign in &constraints.foreign_keys {
                let child_non_null = foreign
                    .columns
                    .iter()
                    .map(|column| format!("child.{} IS NOT NULL", quote_ident(column)))
                    .collect::<Vec<_>>()
                    .join(" AND ");
                let equality = foreign
                    .columns
                    .iter()
                    .zip(&foreign.referenced_columns)
                    .map(|(child, parent)| {
                        format!(
                            "child.{} = parent.{}",
                            quote_ident(child),
                            quote_ident(parent)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" AND ");
                checks.push(IntegrityValidationCheck {
                    kind: "foreign_key".to_owned(),
                    table: table.name.clone(),
                    description: format!(
                        "FOREIGN KEY ({}) REFERENCES {} ({}) MATCH SIMPLE",
                        display_columns(&foreign.columns),
                        display_ident(&foreign.referenced_table),
                        display_columns(&foreign.referenced_columns)
                    ),
                    sql: format!(
                        "SELECT NOT EXISTS (SELECT 1 FROM {} AS child WHERE {child_non_null} AND NOT EXISTS (SELECT 1 FROM {} AS parent WHERE {equality}))",
                        quote_ident(&table.name),
                        quote_ident(&foreign.referenced_table)
                    ),
                });
            }
            for check in &constraints.checks {
                checks.push(IntegrityValidationCheck {
                    kind: "check".to_owned(),
                    table: table.name.clone(),
                    description: format!("CHECK ({})", check.source_sql),
                    sql: format!(
                        "SELECT NOT EXISTS (SELECT 1 FROM {table_sql} WHERE ({}) IS FALSE)",
                        render_predicate(&check.expression)
                    ),
                });
            }
            for index in &constraints.unique_indexes {
                checks.push(unique_validation_check(
                    "partial_expression_unique_index",
                    &table.name,
                    index
                        .terms
                        .iter()
                        .map(|term| render_value_expr(&term.expression))
                        .collect(),
                    index
                        .predicate
                        .as_ref()
                        .map(render_predicate)
                        .as_deref()
                        .unwrap_or("TRUE"),
                    true,
                    format!(
                        "UNIQUE INDEX ({}){}",
                        index
                            .terms
                            .iter()
                            .map(|term| term.source_sql.as_str())
                            .collect::<Vec<_>>()
                            .join(", "),
                        index
                            .predicate_sql
                            .as_deref()
                            .filter(|value| !value.is_empty())
                            .map(|value| format!(" WHERE {value}"))
                            .unwrap_or_default()
                    ),
                ));
            }
        }
        checks
    }
}

fn resolve_schema_table(schema: &Schema, requested: &str) -> Result<usize> {
    resolve_identifier(
        requested,
        schema.tables.iter().map(|table| table.name.as_str()),
        "table",
    )
}

fn resolve_table_column(table: &crate::ir::Table, requested: &str) -> Result<String> {
    let index = resolve_identifier(
        requested,
        table.columns.iter().map(|column| column.name.as_str()),
        &format!("column of table {:?}", table.name),
    )?;
    Ok(table.columns[index].name.clone())
}

/// PostgreSQL folds unquoted ASCII identifiers to lowercase, while quoted
/// identifiers remain case-sensitive.  Frozen pair metadata retains source
/// spellings but not quote markers.  Exact matching therefore has precedence;
/// a case-folded fallback is admitted only when it selects one unique parsed
/// identifier.  Ambiguity and absence fail closed.
fn resolve_identifier<'a>(
    requested: &str,
    candidates: impl Iterator<Item = &'a str>,
    kind: &str,
) -> Result<usize> {
    let candidates = candidates.collect::<Vec<_>>();
    if let Some(index) = candidates
        .iter()
        .position(|candidate| *candidate == requested)
    {
        return Ok(index);
    }
    let folded = requested.to_ascii_lowercase();
    let matches = candidates
        .iter()
        .enumerate()
        .filter(|(_, candidate)| candidate.to_ascii_lowercase() == folded)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(invalid_contract(format!(
            "contract names unknown {kind} {requested:?}"
        ))),
        _ => Err(invalid_contract(format!(
            "contract identifier {requested:?} ambiguously case-folds to multiple {kind} names"
        ))),
    }
}

fn canonicalize_contract_constraints(
    schema: &Schema,
    table_position: usize,
    source: &TableConstraints,
) -> Result<TableConstraints> {
    let table = &schema.tables[table_position];
    let columns = |names: &[String]| {
        names
            .iter()
            .map(|name| resolve_table_column(table, name))
            .collect::<Result<Vec<_>>>()
    };
    let mut constraints = source.clone();
    constraints.not_null = columns(&source.not_null)?;
    constraints.primary_key = source
        .primary_key
        .as_ref()
        .map(|key| columns(key))
        .transpose()?;
    for unique in &mut constraints.unique {
        unique.columns = columns(&unique.columns)?;
    }
    for foreign in &mut constraints.foreign_keys {
        foreign.columns = columns(&foreign.columns)?;
        let referenced_position = resolve_schema_table(schema, &foreign.referenced_table)?;
        let referenced_table = &schema.tables[referenced_position];
        foreign.referenced_table = referenced_table.name.clone();
        foreign.referenced_columns = foreign
            .referenced_columns
            .iter()
            .map(|column| resolve_table_column(referenced_table, column))
            .collect::<Result<Vec<_>>>()?;
    }
    for check in &mut constraints.checks {
        canonicalize_predicate_columns(&mut check.expression, table)?;
    }
    for index in &mut constraints.unique_indexes {
        for term in &mut index.terms {
            canonicalize_value_columns(&mut term.expression, table)?;
        }
        if let Some(predicate) = &mut index.predicate {
            canonicalize_predicate_columns(predicate, table)?;
        }
    }
    Ok(constraints)
}

fn canonicalize_predicate_columns(
    predicate: &mut IntegrityPredicate,
    table: &crate::ir::Table,
) -> Result<()> {
    match predicate {
        IntegrityPredicate::Truth { expression }
        | IntegrityPredicate::IsTrue { expression }
        | IntegrityPredicate::IsNull { expression }
        | IntegrityPredicate::IsNotNull { expression } => {
            canonicalize_value_columns(expression, table)?;
        }
        IntegrityPredicate::Comparison { left, right, .. } => {
            canonicalize_value_columns(left, table)?;
            canonicalize_value_columns(right, table)?;
        }
        IntegrityPredicate::Any { left, values, .. } => {
            canonicalize_value_columns(left, table)?;
            for value in values {
                canonicalize_value_columns(value, table)?;
            }
        }
        IntegrityPredicate::And { left, right } | IntegrityPredicate::Or { left, right } => {
            canonicalize_predicate_columns(left, table)?;
            canonicalize_predicate_columns(right, table)?;
        }
        IntegrityPredicate::Not { predicate } => {
            canonicalize_predicate_columns(predicate, table)?;
        }
    }
    Ok(())
}

fn canonicalize_value_columns(
    expression: &mut IntegrityValueExpr,
    table: &crate::ir::Table,
) -> Result<()> {
    match expression {
        IntegrityValueExpr::Column { name } => *name = resolve_table_column(table, name)?,
        IntegrityValueExpr::Literal { .. } => {}
        IntegrityValueExpr::Cast { expression, .. } | IntegrityValueExpr::Lower { expression } => {
            canonicalize_value_columns(expression, table)?;
        }
        IntegrityValueExpr::Coalesce { arguments } => {
            for argument in arguments {
                canonicalize_value_columns(argument, table)?;
            }
        }
    }
    Ok(())
}

fn unique_validation_check(
    kind: &str,
    table: &str,
    terms: Vec<String>,
    predicate: &str,
    nulls_distinct: bool,
    description: String,
) -> IntegrityValidationCheck {
    let aliases = (0..terms.len())
        .map(|index| format!("logos_key_{}", index + 1))
        .collect::<Vec<_>>();
    let projected = terms
        .iter()
        .zip(&aliases)
        .map(|(term, alias)| format!("({term}) AS {}", quote_ident(alias)))
        .collect::<Vec<_>>()
        .join(", ");
    let non_null = aliases
        .iter()
        .map(|alias| format!("{} IS NOT NULL", quote_ident(alias)))
        .collect::<Vec<_>>()
        .join(" AND ");
    let group = aliases
        .iter()
        .map(|alias| quote_ident(alias))
        .collect::<Vec<_>>()
        .join(", ");
    let null_filter = if nulls_distinct {
        format!("WHERE {non_null}")
    } else {
        String::new()
    };
    IntegrityValidationCheck {
        kind: kind.to_owned(),
        table: table.to_owned(),
        description,
        sql: format!(
            "SELECT NOT EXISTS (SELECT 1 FROM (SELECT {projected} FROM {} WHERE ({predicate}) IS TRUE) AS logos_unique_rows {null_filter} GROUP BY {group} HAVING count(*) > 1)",
            quote_ident(table)
        ),
    }
}

pub fn load_adjacent_integrity_contract(schema_path: &Path) -> Result<SchemaIntegrityContract> {
    let Some(directory) = schema_path.parent() else {
        return Ok(SchemaIntegrityContract::default());
    };
    let metadata_path = directory.join("metadata.json");
    let schema_claims_native_rbot = path_claims_native_rbot_case(schema_path);
    if !metadata_path.is_file() {
        if schema_claims_native_rbot {
            return Err(invalid_contract(format!(
                "Logos-native R-Bot schema has no adjacent regular metadata: {}",
                metadata_path.display()
            )));
        }
        return Ok(SchemaIntegrityContract::default());
    }
    let metadata = read_json(&metadata_path)?;
    let source_benchmark = optional_string(&metadata, "sourceBenchmark")?;
    if schema_claims_native_rbot || metadata_claims_native_rbot_authority(&metadata) {
        validate_native_rbot_materialization_authority(schema_path, &metadata_path, &metadata)?;
    }
    if source_benchmark.is_some() {
        validate_integrity_metadata_reference(&metadata_path, &metadata)?;
    }
    match source_benchmark.as_deref() {
        Some("wetune-issues") => load_wetune_contract(&metadata_path, &metadata),
        Some(_) if metadata.get("flatCaseId").is_some() => {
            load_pair_contract(&metadata_path, &metadata)
        }
        Some(other) => Err(invalid_contract(format!(
            "{} has benchmark {other:?} but no frozen flatCaseId",
            metadata_path.display()
        ))),
        None => Ok(SchemaIntegrityContract::default()),
    }
}

fn path_claims_native_rbot_case(schema_path: &Path) -> bool {
    schema_path.file_name().and_then(|value| value.to_str()) == Some("schema.sql")
        && schema_path
            .parent()
            .and_then(Path::file_name)
            .and_then(|value| value.to_str())
            .is_some_and(|name| name.starts_with("rbot-dsb__") || name.starts_with("rbot-tpch__"))
}

fn metadata_claims_native_rbot_authority(metadata: &Value) -> bool {
    metadata
        .get("sourceBenchmark")
        .and_then(Value::as_str)
        .is_some_and(|value| value.starts_with("rbot-"))
        || metadata
            .get("flatCaseId")
            .and_then(Value::as_str)
            .is_some_and(|value| value.starts_with("rbot-"))
        || metadata
            .pointer("/materializationContract/policy")
            .and_then(Value::as_str)
            == Some(RBOT_MATERIALIZATION_POLICY)
        || metadata
            .pointer("/materializationContract/sourceManifest")
            .and_then(Value::as_str)
            == Some("benchmarks/core/rbot/rewrite-pairs.manifest.json")
        || (metadata.get("profile").and_then(Value::as_str) == Some("logos")
            && (metadata.get("materializationContract").is_some()
                || metadata.get("calciteAuthorityInputs").is_some()
                || metadata.pointer("/integrityContract/ddlComplete").is_some()))
}

fn regular_file_sha256(path: &Path, label: &str) -> Result<String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|_| invalid_contract(format!("{label} is missing: {}", path.display())))?;
    if !metadata.file_type().is_file() {
        return Err(invalid_contract(format!(
            "{label} must be a regular non-symlink file: {}",
            path.display()
        )));
    }
    let bytes = std::fs::read(path).map_err(|source| Error::Read {
        path: path.to_path_buf(),
        source,
    })?;
    Ok(format!("{:x}", Sha256::digest(bytes)))
}

fn validate_native_rbot_materialization_authority(
    schema_path: &Path,
    metadata_path: &Path,
    metadata: &Value,
) -> Result<()> {
    let source_benchmark = metadata.get("sourceBenchmark").and_then(Value::as_str);
    let flat_case_id = metadata.get("flatCaseId").and_then(Value::as_str);
    let path_components = metadata_path
        .components()
        .filter_map(|component| match component {
            std::path::Component::Normal(value) => value.to_str(),
            _ => None,
        })
        .collect::<Vec<_>>();
    let under_logos_generated_root = path_components
        .windows(2)
        .any(|pair| pair == [".generated", "logos"]);
    let under_legacy_sqlsolver_root = path_components
        .windows(2)
        .any(|pair| pair == [".generated", "sqlsolver"]);
    let native = under_logos_generated_root
        || (!under_legacy_sqlsolver_root && path_claims_native_rbot_case(schema_path))
        || metadata.get("profile").and_then(Value::as_str) == Some("logos")
        || metadata.get("materializationContract").is_some()
        || metadata.pointer("/integrityContract/ddlComplete").is_some();
    if !native {
        // The frozen legacy SQLSolver campaign carries the same benchmark IDs
        // but intentionally predates the independent Logos authority contract.
        return Ok(());
    }

    let workload = match source_benchmark {
        Some("rbot-dsb") => "dsb",
        Some("rbot-tpch") => "tpch",
        _ => {
            return Err(invalid_contract(
                "Logos-native R-Bot metadata has a borrowed sourceBenchmark",
            ));
        }
    };
    let case_id = flat_case_id
        .ok_or_else(|| invalid_contract("Logos-native R-Bot metadata has no flatCaseId"))?;
    if !case_id.starts_with(&format!("rbot-{workload}__")) {
        return Err(invalid_contract(format!(
            "R-Bot case/workload identity is inconsistent: {case_id}"
        )));
    }
    let source_case = case_id
        .split_once("__")
        .map(|(_, value)| value)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| invalid_contract(format!("invalid R-Bot case ID {case_id:?}")))?;

    if schema_path.file_name().and_then(|value| value.to_str()) != Some("schema.sql") {
        return Err(invalid_contract(
            "Logos-native R-Bot schema authority must be adjacent schema.sql",
        ));
    }
    let _metadata_digest = regular_file_sha256(metadata_path, "R-Bot metadata")?;

    let manifest_path = resolve_repository_path(
        metadata_path,
        "benchmarks/core/rbot/rewrite-pairs.manifest.json",
    )?;
    let manifest_digest = regular_file_sha256(&manifest_path, "R-Bot manifest")?;
    let manifest = read_json(&manifest_path)?;
    let rows = manifest
        .get("cases")
        .and_then(Value::as_array)
        .filter(|rows| !rows.is_empty())
        .ok_or_else(|| invalid_contract("R-Bot manifest must contain a nonempty cases array"))?;
    let matching = rows
        .iter()
        .filter(|row| row.get("case").and_then(Value::as_str) == Some(case_id))
        .collect::<Vec<_>>();
    if matching.len() != 1 {
        return Err(invalid_contract(format!(
            "R-Bot metadata case {case_id:?} is absent or duplicated in the frozen manifest"
        )));
    }
    let row = matching[0];
    if row.get("workload").and_then(Value::as_str) != Some(workload) {
        return Err(invalid_contract(format!(
            "R-Bot manifest workload changed for {case_id}"
        )));
    }
    let source_relative = row
        .get("source")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid_contract(format!("R-Bot manifest source missing for {case_id}")))?;
    let source_digest = row
        .get("sourceSha256")
        .and_then(Value::as_str)
        .ok_or_else(|| {
            invalid_contract(format!(
                "R-Bot manifest source digest missing for {case_id}"
            ))
        })?;
    let target_relative = row
        .get("target")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid_contract(format!("R-Bot manifest target missing for {case_id}")))?;
    let target_digest = row
        .get("targetSha256")
        .and_then(Value::as_str)
        .ok_or_else(|| {
            invalid_contract(format!(
                "R-Bot manifest target digest missing for {case_id}"
            ))
        })?;

    let schema_authority = resolve_repository_path(
        metadata_path,
        &format!("benchmarks/core/rbot/{workload}/create_tables.sql"),
    )?;
    let source_authority = resolve_repository_path(
        metadata_path,
        &format!("benchmarks/core/rbot/{source_relative}"),
    )?;
    let target_authority = resolve_repository_path(
        metadata_path,
        &format!("benchmarks/core/rbot/{target_relative}"),
    )?;
    let schema_digest = regular_file_sha256(&schema_authority, "R-Bot workload schema")?;
    for (path, expected, label) in [
        (
            schema_authority.as_path(),
            schema_digest.as_str(),
            "frozen R-Bot workload schema",
        ),
        (
            source_authority.as_path(),
            source_digest,
            "frozen R-Bot source query",
        ),
        (
            target_authority.as_path(),
            target_digest,
            "frozen R-Bot target query",
        ),
        (schema_path, schema_digest.as_str(), "adjacent R-Bot schema"),
    ] {
        if regular_file_sha256(path, label)? != expected {
            return Err(invalid_contract(format!(
                "{label} digest changed for {case_id}"
            )));
        }
    }
    let directory = metadata_path
        .parent()
        .ok_or_else(|| invalid_contract("R-Bot metadata has no parent directory"))?;
    for (name, expected, label) in [
        ("sql1.sql", source_digest, "adjacent R-Bot source query"),
        ("sql2.sql", target_digest, "adjacent R-Bot target query"),
    ] {
        if regular_file_sha256(&directory.join(name), label)? != expected {
            return Err(invalid_contract(format!(
                "{label} digest changed for {case_id}"
            )));
        }
    }

    let expected_benchmark = format!("rbot-{workload}");
    for (field, expected) in [
        ("profile", "logos"),
        ("sourceBenchmark", expected_benchmark.as_str()),
        ("sourceCase", source_case),
        ("flatCaseId", case_id),
    ] {
        if metadata.get(field).and_then(Value::as_str) != Some(expected) {
            return Err(invalid_contract(format!(
                "R-Bot metadata identity field {field:?} changed for {case_id}"
            )));
        }
    }
    let expected_source = serde_json::json!({
        "directory": source_case,
        "manifestCase": case_id,
        "manifestProfile": manifest.get("profile").and_then(Value::as_str),
        "source": format!("benchmarks/core/rbot/{workload}"),
    });
    if metadata.get("source") != Some(&expected_source) {
        return Err(invalid_contract(format!(
            "R-Bot source identity metadata changed for {case_id}"
        )));
    }
    let expected_integrity = serde_json::json!({
        "authoritativeForLogos": true,
        "ddlComplete": true,
        "ddlLimitation": null,
        "silentDrops": 0,
        "sources": [{"kind": "parser_facing_ddl", "path": "schema.sql"}],
    });
    if metadata.get("integrityContract") != Some(&expected_integrity)
        || metadata.get("constraintScope").and_then(Value::as_str) != Some("none")
        || !metadata
            .get("constraints")
            .and_then(Value::as_array)
            .is_some_and(Vec::is_empty)
    {
        return Err(invalid_contract(format!(
            "R-Bot integrity/constraint identity changed for {case_id}"
        )));
    }

    let expected_inputs = serde_json::json!({
        "schema": {
            "inputPath": format!("benchmarks/core/rbot/{workload}/create_tables.sql"),
            "inputSha256": schema_digest,
            "outputPath": "schema.sql",
            "outputSha256": schema_digest,
            "repairs": [],
            "unchanged": true,
        },
        "source": {
            "inputPath": format!("benchmarks/core/rbot/{source_relative}"),
            "inputSha256": source_digest,
            "outputPath": "sql1.sql",
            "outputSha256": source_digest,
            "repairs": [],
            "unchanged": true,
        },
        "target": {
            "inputPath": format!("benchmarks/core/rbot/{target_relative}"),
            "inputSha256": target_digest,
            "outputPath": "sql2.sql",
            "outputSha256": target_digest,
            "repairs": [],
            "unchanged": true,
        },
    });
    let expected_materialization = serde_json::json!({
        "inputs": expected_inputs,
        "policy": RBOT_MATERIALIZATION_POLICY,
        "semanticPreservation": {
            "established": true,
            "identifierDelimitersPreserved": true,
            "queryStructurePreserved": true,
            "repairs": [],
        },
        "sourceManifest": "benchmarks/core/rbot/rewrite-pairs.manifest.json",
        "sourceManifestSha256": manifest_digest,
    });
    if metadata.get("materializationContract") != Some(&expected_materialization) {
        return Err(invalid_contract(format!(
            "R-Bot materialization contract changed for {case_id}"
        )));
    }
    let expected_calcite_inputs = serde_json::json!({
        "schema": {"path": "schema.sql", "sha256": schema_digest},
        "source": {"path": "sql1.sql", "sha256": source_digest},
        "target": {"path": "sql2.sql", "sha256": target_digest},
    });
    if metadata.get("calciteAuthorityInputs") != Some(&expected_calcite_inputs) {
        return Err(invalid_contract(format!(
            "R-Bot Calcite authority inputs changed for {case_id}"
        )));
    }
    Ok(())
}

fn validate_integrity_metadata_reference(metadata_path: &Path, metadata: &Value) -> Result<()> {
    let label = metadata_path.display().to_string();
    let marker = metadata
        .get("integrityContract")
        .ok_or_else(|| invalid_contract(format!("{label} is missing integrityContract")))?;
    let source_benchmark = required_string(metadata, "sourceBenchmark", metadata_path)?;
    let logos_native_pair_contract =
        source_benchmark != "wetune-issues" && marker.get("ddlComplete").is_some();
    if source_benchmark == "wetune-issues" {
        require_exact_object_fields(
            marker,
            &[
                "authoritativeForLogos",
                "identifierRenames",
                "parserFacingDdl",
                "semanticSidecar",
                "sidecarAuthority",
                "sidecarRawTypeSemantics",
                "sidecarRawTypeSemanticsDisposition",
                "silentDrops",
                "sourceKind",
                "sqlsolverDdlComplete",
                "typeAuthority",
            ],
            &format!("{label}.integrityContract"),
        )?;
    } else if logos_native_pair_contract {
        require_exact_object_fields(
            marker,
            &[
                "authoritativeForLogos",
                "ddlComplete",
                "ddlLimitation",
                "silentDrops",
                "sources",
            ],
            &format!("{label}.integrityContract"),
        )?;
        if metadata
            .pointer("/materializationContract/policy")
            .and_then(Value::as_str)
            != Some("logos-postgres-calcite-source-preserving-v1")
        {
            return Err(invalid_contract(format!(
                "{label} Logos-native integrity contract lacks the independent source-preserving materialization policy"
            )));
        }
    } else {
        require_exact_object_fields(
            marker,
            &[
                "authoritativeForLogos",
                "silentDrops",
                "sources",
                "sqlsolverDdlComplete",
                "sqlsolverDdlLimitation",
            ],
            &format!("{label}.integrityContract"),
        )?;
    }
    if marker.get("authoritativeForLogos").and_then(Value::as_bool) != Some(true)
        || marker.get("silentDrops").and_then(Value::as_u64) != Some(0)
    {
        return Err(invalid_contract(format!(
            "{label}.integrityContract must declare authoritativeForLogos=true and silentDrops=0"
        )));
    }
    if source_benchmark == "wetune-issues" {
        if marker.get("sqlsolverDdlComplete").and_then(Value::as_bool) != Some(false) {
            return Err(invalid_contract(format!(
                "{label}.integrityContract.sqlsolverDdlComplete must be false for WeTune sidecars"
            )));
        }
        let semantic_source = metadata
            .pointer("/semanticConstraints/source")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid_contract(format!("{label} has no semantic sidecar source")))?;
        for (field, expected) in [
            ("identifierRenames", "metadata.json#/renamedIdentifiers"),
            ("parserFacingDdl", "schema.sql"),
            ("semanticSidecar", semantic_source),
            ("sourceKind", "wetune_base_schema_sidecar"),
            ("typeAuthority", WETUNE_TYPE_AUTHORITY),
            ("sidecarAuthority", WETUNE_SIDECAR_AUTHORITY),
            ("sidecarRawTypeSemantics", WETUNE_RAW_TYPE_SEMANTICS),
            (
                "sidecarRawTypeSemanticsDisposition",
                WETUNE_RAW_TYPE_DISPOSITION,
            ),
        ] {
            if marker.get(field).and_then(Value::as_str) != Some(expected) {
                return Err(invalid_contract(format!(
                    "{label}.integrityContract.{field} must be {expected:?}"
                )));
            }
        }
        let renames = metadata
            .get("renamedIdentifiers")
            .and_then(Value::as_object)
            .ok_or_else(|| {
                invalid_contract(format!("{label}.renamedIdentifiers must be an object"))
            })?;
        if renames
            .iter()
            .any(|(source, target)| source.is_empty() || target.as_str().is_none())
        {
            return Err(invalid_contract(format!(
                "{label}.renamedIdentifiers must map nonempty strings to strings"
            )));
        }
    } else {
        let scope = required_string(metadata, "constraintScope", metadata_path)?;
        let ddl_complete_field = if logos_native_pair_contract {
            "ddlComplete"
        } else {
            "sqlsolverDdlComplete"
        };
        let ddl_limitation_field = if logos_native_pair_contract {
            "ddlLimitation"
        } else {
            "sqlsolverDdlLimitation"
        };
        let ddl_complete = marker
            .get(ddl_complete_field)
            .and_then(Value::as_bool)
            .ok_or_else(|| {
                invalid_contract(format!(
                    "{label}.integrityContract.{ddl_complete_field} must be Boolean"
                ))
            })?;
        let pair_constraints_empty = metadata
            .get("constraints")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid_contract(format!("{label}.constraints must be an array")))?
            .is_empty();
        match scope.as_str() {
            "none" | "pair"
                if pair_constraints_empty
                    && ddl_complete
                    && marker.get(ddl_limitation_field) == Some(&Value::Null) => {}
            "pair"
                if !pair_constraints_empty
                    && !ddl_complete
                    && marker
                        .get(ddl_limitation_field)
                        .and_then(Value::as_str)
                        .is_some_and(|value| !value.is_empty()) => {}
            "none" | "pair" => {
                return Err(invalid_contract(format!(
                    "{label}.integrityContract DDL completeness/limitation disagrees with constraintScope={scope:?}"
                )));
            }
            _ => {
                return Err(invalid_contract(format!(
                    "{label} has unsupported constraintScope {scope:?}"
                )));
            }
        }
        let sources = marker
            .get("sources")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                invalid_contract(format!(
                    "{label}.integrityContract.sources must be an array"
                ))
            })?;
        let mut parser_ddl = false;
        let mut pair_metadata = false;
        for (index, source) in sources.iter().enumerate() {
            let source = require_exact_object_fields(
                source,
                &["kind", "path"],
                &format!("{label}.integrityContract.sources[{index}]"),
            )?;
            match (
                source.get("kind").and_then(Value::as_str),
                source.get("path").and_then(Value::as_str),
            ) {
                (Some("parser_facing_ddl"), Some("schema.sql")) => parser_ddl = true,
                (Some("pair_metadata"), Some("metadata.json#/constraints")) => pair_metadata = true,
                _ => {
                    return Err(invalid_contract(format!(
                        "{label}.integrityContract.sources[{index}] is unsupported"
                    )));
                }
            }
        }
        if !parser_ddl || scope == "pair" && !pair_metadata {
            return Err(invalid_contract(format!(
                "{label}.integrityContract does not enumerate every authoritative source"
            )));
        }
    }
    Ok(())
}

fn load_pair_contract(metadata_path: &Path, metadata: &Value) -> Result<SchemaIntegrityContract> {
    let case_id = required_string(metadata, "flatCaseId", metadata_path)?;
    let scope = required_string(metadata, "constraintScope", metadata_path)?;
    let constraints = metadata
        .get("constraints")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            invalid_contract(format!(
                "{} pair constraints field must be an array",
                metadata_path.display()
            ))
        })?;
    if scope == "none" && !constraints.is_empty() {
        return Err(invalid_contract(format!(
            "{case_id} declares constraintScope=none but carries constraints"
        )));
    }
    if scope != "none" && scope != "pair" {
        return Err(invalid_contract(format!(
            "{case_id} has unsupported constraint scope {scope:?}"
        )));
    }
    let mut tables: BTreeMap<String, TableConstraints> = BTreeMap::new();
    for (index, constraint) in constraints.iter().enumerate() {
        let object = constraint.as_object().ok_or_else(|| {
            invalid_contract(format!("{case_id} constraints[{index}] is not an object"))
        })?;
        if object.len() != 1 {
            return Err(invalid_contract(format!(
                "{case_id} constraints[{index}] must contain exactly one constraint kind"
            )));
        }
        let (kind, payload) = object.iter().next().expect("one entry checked");
        match kind.as_str() {
            "not_null" => {
                require_exact_object_fields(
                    payload,
                    &["value"],
                    &format!("{case_id} constraints[{index}].not_null"),
                )?;
                let (table, column) = parse_pair_endpoint(
                    required_string(payload, "value", metadata_path)?.as_str(),
                    &case_id,
                )?;
                tables.entry(table).or_default().not_null.push(column);
            }
            "primary" => {
                let endpoints = required_array(payload, "primary", &case_id, index)?;
                let mut table_name = None;
                let mut columns = Vec::new();
                for (endpoint_index, endpoint) in endpoints.iter().enumerate() {
                    let endpoint = require_exact_object_fields(
                        endpoint,
                        &["value"],
                        &format!("{case_id} constraints[{index}].primary[{endpoint_index}]"),
                    )?;
                    let value = endpoint
                        .get("value")
                        .and_then(Value::as_str)
                        .ok_or_else(|| {
                            invalid_contract(format!(
                                "{case_id} primary constraint contains a malformed endpoint"
                            ))
                        })?;
                    let (table, column) = parse_pair_endpoint(value, &case_id)?;
                    if table_name
                        .as_ref()
                        .is_some_and(|expected| expected != &table)
                    {
                        return Err(invalid_contract(format!(
                            "{case_id} primary constraint crosses tables"
                        )));
                    }
                    table_name = Some(table);
                    columns.push(column);
                }
                if columns.is_empty() {
                    return Err(invalid_contract(format!(
                        "{case_id} primary constraint is empty"
                    )));
                }
                let table_name = table_name.expect("nonempty endpoints");
                let table = tables.entry(table_name.clone()).or_default();
                if let Some(existing) = &table.primary_key {
                    if existing != &columns {
                        return Err(invalid_contract(format!(
                            "{case_id} declares conflicting primary keys for {table_name:?}"
                        )));
                    }
                } else {
                    table.primary_key = Some(columns);
                }
            }
            "foreign" => {
                let endpoints = required_array(payload, "foreign", &case_id, index)?;
                if endpoints.len() != 2 {
                    return Err(invalid_contract(format!(
                        "{case_id} foreign constraint has {} endpoints; the frozen pair grammar requires exactly source and target",
                        endpoints.len()
                    )));
                }
                let endpoint = |endpoint_index: usize, value: &Value| -> Result<(String, String)> {
                    let value = require_exact_object_fields(
                        value,
                        &["value"],
                        &format!("{case_id} constraints[{index}].foreign[{endpoint_index}]"),
                    )?
                    .get("value")
                    .and_then(Value::as_str)
                    .ok_or_else(|| {
                        invalid_contract(format!(
                            "{case_id} foreign constraint contains a malformed endpoint"
                        ))
                    })?;
                    parse_pair_endpoint(value, &case_id)
                };
                let (table, column) = endpoint(0, &endpoints[0])?;
                let (referenced_table, referenced_column) = endpoint(1, &endpoints[1])?;
                tables
                    .entry(table)
                    .or_default()
                    .foreign_keys
                    .push(ForeignKeyConstraint {
                        name: None,
                        columns: vec![column],
                        referenced_table,
                        referenced_columns: vec![referenced_column],
                        match_type: ForeignKeyMatch::Simple,
                        referential_actions: None,
                    });
            }
            other => {
                return Err(invalid_contract(format!(
                    "{case_id} uses unsupported pair constraint kind {other:?}"
                )));
            }
        }
    }
    let mut contract = SchemaIntegrityContract {
        case_id: Some(case_id),
        source: Some(metadata_path.to_path_buf()),
        tables: tables
            .into_iter()
            .map(|(name, constraints)| ContractTable { name, constraints })
            .collect(),
        requires_postgres_utf8_c_text_semantics: false,
    };
    normalize_contract_primary_not_null(&mut contract);
    validate_contract_referenced_keys(&contract)?;
    Ok(contract)
}

fn required_array<'a>(
    payload: &'a Value,
    kind: &str,
    case_id: &str,
    index: usize,
) -> Result<&'a Vec<Value>> {
    payload.as_array().ok_or_else(|| {
        invalid_contract(format!(
            "{case_id} constraints[{index}].{kind} is not an array"
        ))
    })
}

fn parse_pair_endpoint(value: &str, case_id: &str) -> Result<(String, String)> {
    let Some((table, column)) = value.rsplit_once("__") else {
        return Err(invalid_contract(format!(
            "{case_id} constraint endpoint {value:?} is not TABLE__COLUMN"
        )));
    };
    if table.is_empty() || column.is_empty() {
        return Err(invalid_contract(format!(
            "{case_id} constraint endpoint {value:?} has an empty table or column"
        )));
    }
    Ok((table.to_owned(), column.to_owned()))
}

fn load_wetune_contract(metadata_path: &Path, metadata: &Value) -> Result<SchemaIntegrityContract> {
    let source_case = required_string(metadata, "sourceCase", metadata_path)?;
    let case_id = required_string(metadata, "flatCaseId", metadata_path)?;
    if case_id != format!("wetune-issues__{source_case}") {
        return Err(invalid_contract(format!(
            "{} has inconsistent sourceCase {source_case:?} and flatCaseId {case_id:?}",
            metadata_path.display()
        )));
    }
    let app_name = required_string(metadata, "appName", metadata_path)?;
    let semantic = metadata.get("semanticConstraints").ok_or_else(|| {
        invalid_contract(format!(
            "{} is missing semanticConstraints",
            metadata_path.display()
        ))
    })?;
    let semantic = semantic.as_object().ok_or_else(|| {
        invalid_contract(format!(
            "{}.semanticConstraints is not an object",
            metadata_path.display()
        ))
    })?;
    require_exact_object_fields(
        &Value::Object(semantic.clone()),
        &[
            "checks",
            "columns",
            "foreignKeys",
            "includedInSqlsolverDdl",
            "primaryKeys",
            "reason",
            "source",
            "typeLowerings",
            "uniqueIndexes",
            "uniqueKeys",
            "unsupportedSemanticConstraints",
        ],
        &format!("{}.semanticConstraints", metadata_path.display()),
    )?;
    if semantic
        .get("includedInSqlsolverDdl")
        .and_then(Value::as_bool)
        != Some(false)
        || semantic
            .get("reason")
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
        || [
            "checks",
            "columns",
            "foreignKeys",
            "primaryKeys",
            "typeLowerings",
            "uniqueIndexes",
            "uniqueKeys",
        ]
        .iter()
        .any(|field| semantic.get(*field).and_then(Value::as_u64).is_none())
    {
        return Err(invalid_contract(format!(
            "{case_id} semanticConstraints has malformed authority/count fields"
        )));
    }
    let Some(unsupported_count) = semantic
        .get("unsupportedSemanticConstraints")
        .and_then(Value::as_u64)
    else {
        return Err(invalid_contract(format!(
            "{case_id} semanticConstraints.unsupportedSemanticConstraints must be a nonnegative integer"
        )));
    };
    if unsupported_count != 0 {
        return Err(invalid_contract(format!(
            "{case_id} sidecar reports unsupported semantic constraints"
        )));
    }
    let source = semantic
        .get("source")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid_contract(format!("{case_id} has no semantic sidecar source")))?;
    let expected_source =
        format!("benchmarks/core/wetune/schemas/core/{app_name}.base.schema.constraints.json");
    if source != expected_source {
        return Err(invalid_contract(format!(
            "{case_id} semantic sidecar source must be {expected_source:?}, found {source:?}"
        )));
    }
    let sidecar_path = resolve_repository_path(metadata_path, source)?;
    let sidecar = read_json(&sidecar_path)?;
    validate_wetune_sidecar_shape(&sidecar, &case_id, &sidecar_path)?;
    for field in [
        "checks",
        "foreignKeys",
        "primaryKeys",
        "uniqueIndexes",
        "uniqueKeys",
    ] {
        let declared = semantic
            .get(field)
            .and_then(Value::as_u64)
            .expect("semantic count types checked");
        let actual = sidecar_array(&sidecar, field, &case_id)?.len() as u64;
        if declared != actual {
            return Err(invalid_contract(format!(
                "{case_id} semanticConstraints.{field}={declared}, but the authoritative sidecar carries {actual}"
            )));
        }
    }
    let sidecar_columns = sidecar
        .pointer("/semanticSchema/tables")
        .and_then(Value::as_array)
        .expect("sidecar shape checked")
        .iter()
        .map(|table| {
            table
                .get("columns")
                .and_then(Value::as_array)
                .expect("sidecar shape checked")
                .len() as u64
        })
        .sum::<u64>();
    if semantic.get("columns").and_then(Value::as_u64) != Some(sidecar_columns) {
        return Err(invalid_contract(format!(
            "{case_id} semanticConstraints.columns does not match the authoritative sidecar"
        )));
    }
    let rename_map = metadata
        .get("renamedIdentifiers")
        .and_then(Value::as_object)
        .map(|object| {
            object
                .iter()
                .map(|(key, value)| {
                    value
                        .as_str()
                        .map(|value| (key.clone(), value.to_owned()))
                        .ok_or_else(|| {
                            invalid_contract(format!(
                                "{case_id} renamedIdentifiers[{key:?}] is not a string"
                            ))
                        })
                })
                .collect::<Result<BTreeMap<_, _>>>()
        })
        .transpose()?
        .ok_or_else(|| {
            invalid_contract(format!("{case_id} renamedIdentifiers must be an object"))
        })?;
    let rename = |name: &str| {
        rename_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    };

    let mut tables: BTreeMap<String, TableConstraints> = BTreeMap::new();
    let semantic_tables = sidecar
        .pointer("/semanticSchema/tables")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            invalid_contract(format!("{case_id} sidecar has no semanticSchema.tables"))
        })?;
    for table in semantic_tables {
        let table_name = rename(required_string(table, "name", &sidecar_path)?.as_str());
        let columns = table
            .get("columns")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                invalid_contract(format!(
                    "{case_id} semantic table {table_name:?} has no columns"
                ))
            })?;
        let constraints = tables.entry(table_name).or_default();
        for column in columns {
            if column
                .get("notNull")
                .and_then(Value::as_bool)
                .unwrap_or(false)
            {
                constraints.not_null.push(rename(
                    required_string(column, "name", &sidecar_path)?.as_str(),
                ));
            }
        }
    }

    for key in sidecar_array(&sidecar, "primaryKeys", &case_id)? {
        let table_name = rename(required_string(key, "table", &sidecar_path)?.as_str());
        let columns = renamed_string_array(key, "columns", &rename, &case_id)?;
        let table = tables.entry(table_name.clone()).or_default();
        if let Some(existing) = &table.primary_key {
            if existing != &columns {
                return Err(invalid_contract(format!(
                    "{case_id} sidecar has conflicting primary keys for {table_name:?}"
                )));
            }
        } else {
            table.primary_key = Some(columns);
        }
    }
    for key in sidecar_array(&sidecar, "uniqueKeys", &case_id)? {
        let table_name = rename(required_string(key, "table", &sidecar_path)?.as_str());
        let columns = renamed_string_array(key, "columns", &rename, &case_id)?;
        tables
            .entry(table_name)
            .or_default()
            .unique
            .push(UniqueConstraint {
                name: None,
                columns,
            });
    }
    for foreign in sidecar_array(&sidecar, "foreignKeys", &case_id)? {
        let table_name = rename(required_string(foreign, "table", &sidecar_path)?.as_str());
        let columns = renamed_string_array(foreign, "columns", &rename, &case_id)?;
        let referenced_table =
            rename(required_string(foreign, "refTable", &sidecar_path)?.as_str());
        let referenced_columns = renamed_string_array(foreign, "refColumns", &rename, &case_id)?;
        tables
            .entry(table_name)
            .or_default()
            .foreign_keys
            .push(ForeignKeyConstraint {
                name: None,
                columns,
                referenced_table,
                referenced_columns,
                match_type: ForeignKeyMatch::Simple,
                referential_actions: optional_string(foreign, "actions")?
                    .filter(|value| !value.is_empty()),
            });
    }
    for check in sidecar_array(&sidecar, "checks", &case_id)? {
        let table_name = rename(required_string(check, "table", &sidecar_path)?.as_str());
        let source_sql = required_string(check, "expression", &sidecar_path)?;
        let expression = parse_integrity_predicate_with_rename(&source_sql, &rename).map_err(
            |message| {
                invalid_contract(format!(
                    "{case_id} CHECK on {table_name:?} is unsupported: {message}; expression {source_sql:?}"
                ))
            },
        )?;
        tables
            .entry(table_name)
            .or_default()
            .checks
            .push(CheckConstraint {
                name: None,
                expression,
                source_sql: rename_expression_source(&source_sql, &rename),
            });
    }
    for index in sidecar_array(&sidecar, "uniqueIndexes", &case_id)? {
        let table_name = rename(required_string(index, "table", &sidecar_path)?.as_str());
        let raw_terms = index
            .get("terms")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                invalid_contract(format!(
                    "{case_id} unique index on {table_name:?} has no terms"
                ))
            })?;
        let mut terms = Vec::new();
        for raw_term in raw_terms {
            let raw_term = raw_term.as_str().ok_or_else(|| {
                invalid_contract(format!(
                    "{case_id} unique index on {table_name:?} has a non-string term"
                ))
            })?;
            terms.push(parse_unique_index_term_with_rename(raw_term, &rename).map_err(
                |message| invalid_contract(format!(
                    "{case_id} unique index on {table_name:?} is unsupported: {message}; term {raw_term:?}"
                )),
            )?);
        }
        if terms.is_empty() {
            return Err(invalid_contract(format!(
                "{case_id} unique index on {table_name:?} has no terms"
            )));
        }
        let predicate_source = optional_string(index, "where")?.filter(|value| !value.is_empty());
        let predicate = predicate_source
            .as_deref()
            .map(|source| parse_integrity_predicate_with_rename(source, &rename))
            .transpose()
            .map_err(|message| invalid_contract(format!(
                "{case_id} unique-index predicate on {table_name:?} is unsupported: {message}; predicate {predicate_source:?}"
            )))?;
        tables
            .entry(table_name)
            .or_default()
            .unique_indexes
            .push(UniqueIndexConstraint {
                name: None,
                terms,
                predicate,
                predicate_sql: predicate_source
                    .map(|source| rename_expression_source(&source, &rename)),
            });
    }
    let unsupported = sidecar_array(&sidecar, "unsupportedSemanticConstraints", &case_id)?;
    if !unsupported.is_empty() {
        return Err(invalid_contract(format!(
            "{case_id} sidecar contains {} unsupported semantic constraint(s)",
            unsupported.len()
        )));
    }

    let mut contract = SchemaIntegrityContract {
        case_id: Some(case_id),
        source: Some(sidecar_path),
        tables: tables
            .into_iter()
            .map(|(name, constraints)| ContractTable { name, constraints })
            .collect(),
        requires_postgres_utf8_c_text_semantics: false,
    };
    normalize_contract_primary_not_null(&mut contract);
    deduplicate_contract(&mut contract);
    validate_contract_referenced_keys(&contract)?;
    Ok(contract)
}

fn validate_wetune_sidecar_shape(sidecar: &Value, case_id: &str, path: &Path) -> Result<()> {
    let sidecar = require_exact_object_fields(
        sidecar,
        &[
            "checks",
            "foreignKeys",
            "primaryKeys",
            "semanticSchema",
            "uniqueIndexes",
            "uniqueKeys",
            "unsupportedSemanticConstraints",
        ],
        &format!("{case_id} sidecar"),
    )?;
    let semantic_schema = require_exact_object_fields(
        sidecar
            .get("semanticSchema")
            .expect("exact field set checked"),
        &["tables", "typeSemantics"],
        &format!("{case_id} sidecar.semanticSchema"),
    )?;
    if semantic_schema.get("typeSemantics").and_then(Value::as_str)
        != Some(WETUNE_RAW_TYPE_SEMANTICS)
    {
        return Err(invalid_contract(format!(
            "{case_id} sidecar.semanticSchema.typeSemantics must retain the frozen raw-type audit statement {WETUNE_RAW_TYPE_SEMANTICS:?}"
        )));
    }
    let semantic_tables = semantic_schema
        .get("tables")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            invalid_contract(format!(
                "{case_id} sidecar.semanticSchema.tables must be an array"
            ))
        })?;
    let mut catalog: BTreeMap<String, BTreeMap<String, bool>> = BTreeMap::new();
    for (table_index, table) in semantic_tables.iter().enumerate() {
        let table = require_exact_object_fields(
            table,
            &["columns", "name"],
            &format!("{case_id} sidecar.semanticSchema.tables[{table_index}]"),
        )?;
        let table_name = required_nonempty_sidecar_string(
            table,
            "name",
            case_id,
            &format!("semanticSchema.tables[{table_index}]"),
        )?;
        let columns = table
            .get("columns")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                invalid_contract(format!(
                    "{case_id} semantic table {table_name:?} columns must be an array"
                ))
            })?;
        let mut catalog_columns = BTreeMap::new();
        for (column_index, column) in columns.iter().enumerate() {
            let label = format!("semanticSchema.tables[{table_index}].columns[{column_index}]");
            let column = require_exact_object_fields(
                column,
                &[
                    "autoIncrement",
                    "default",
                    "generated",
                    "inlinePrimary",
                    "inlineUnique",
                    "name",
                    "normalizedFrontendType",
                    "notNull",
                    "nullable",
                    "sourceDeclaration",
                    "sourceType",
                ],
                &format!("{case_id} sidecar.{label}"),
            )?;
            let column_name = required_nonempty_sidecar_string(column, "name", case_id, &label)?;
            for type_field in ["normalizedFrontendType", "sourceDeclaration", "sourceType"] {
                required_nonempty_sidecar_string(column, type_field, case_id, &label)?;
            }
            let auto_increment = required_sidecar_bool(column, "autoIncrement", case_id, &label)?;
            let generated = required_sidecar_bool(column, "generated", case_id, &label)?;
            let inline_primary = required_sidecar_bool(column, "inlinePrimary", case_id, &label)?;
            let inline_unique = required_sidecar_bool(column, "inlineUnique", case_id, &label)?;
            let not_null = required_sidecar_bool(column, "notNull", case_id, &label)?;
            let nullable = required_sidecar_bool(column, "nullable", case_id, &label)?;
            let _ = auto_increment;
            if generated || inline_primary || inline_unique {
                return Err(invalid_contract(format!(
                    "{case_id} sidecar.{label} uses an unsupported generated/inline-key declaration"
                )));
            }
            if nullable == not_null {
                return Err(invalid_contract(format!(
                    "{case_id} sidecar.{label} has inconsistent nullable={nullable} and notNull={not_null}"
                )));
            }
            if !matches!(column.get("default"), Some(Value::Null | Value::String(_))) {
                return Err(invalid_contract(format!(
                    "{case_id} sidecar.{label}.default must be null or preserved SQL text"
                )));
            }
            if catalog_columns
                .insert(column_name.clone(), nullable)
                .is_some()
            {
                return Err(invalid_contract(format!(
                    "{case_id} semantic table {table_name:?} repeats column {column_name:?}"
                )));
            }
        }
        if catalog
            .insert(table_name.clone(), catalog_columns)
            .is_some()
        {
            return Err(invalid_contract(format!(
                "{case_id} sidecar repeats semantic table {table_name:?}"
            )));
        }
    }

    for (index, key) in sidecar_object_array(sidecar, "primaryKeys", case_id)?
        .iter()
        .enumerate()
    {
        let key = require_exact_object_fields(
            key,
            &["columns", "table"],
            &format!("{case_id} sidecar.primaryKeys[{index}]"),
        )?;
        let table = required_nonempty_sidecar_string(key, "table", case_id, "primaryKeys")?;
        let columns = required_sidecar_string_array(key, "columns", case_id, "primaryKeys", false)?;
        validate_sidecar_column_references(&catalog, &table, &columns, case_id, "PRIMARY KEY")?;
    }
    for (index, key) in sidecar_object_array(sidecar, "uniqueKeys", case_id)?
        .iter()
        .enumerate()
    {
        let key = require_exact_object_fields(
            key,
            &["columns", "nullableColumns", "semantics", "table"],
            &format!("{case_id} sidecar.uniqueKeys[{index}]"),
        )?;
        let table = required_nonempty_sidecar_string(key, "table", case_id, "uniqueKeys")?;
        let columns = required_sidecar_string_array(key, "columns", case_id, "uniqueKeys", false)?;
        let nullable_columns =
            required_sidecar_string_array(key, "nullableColumns", case_id, "uniqueKeys", true)?;
        if key.get("semantics").and_then(Value::as_str) != Some(WETUNE_UNIQUE_SEMANTICS) {
            return Err(invalid_contract(format!(
                "{case_id} UNIQUE on {table:?} does not declare {WETUNE_UNIQUE_SEMANTICS:?}"
            )));
        }
        validate_sidecar_column_references(&catalog, &table, &columns, case_id, "UNIQUE")?;
        let table_columns = catalog.get(&table).expect("table was validated");
        let expected_nullable = columns
            .iter()
            .filter(|column| table_columns.get(*column) == Some(&true))
            .cloned()
            .collect::<Vec<_>>();
        if nullable_columns != expected_nullable {
            return Err(invalid_contract(format!(
                "{case_id} UNIQUE on {table:?} has nullableColumns {nullable_columns:?}, expected {expected_nullable:?}"
            )));
        }
    }
    for (index, foreign) in sidecar_object_array(sidecar, "foreignKeys", case_id)?
        .iter()
        .enumerate()
    {
        let foreign = require_exact_object_fields(
            foreign,
            &[
                "actions",
                "columns",
                "refColumns",
                "refTable",
                "source",
                "table",
            ],
            &format!("{case_id} sidecar.foreignKeys[{index}]"),
        )?;
        let table = required_nonempty_sidecar_string(foreign, "table", case_id, "foreignKeys")?;
        let columns =
            required_sidecar_string_array(foreign, "columns", case_id, "foreignKeys", false)?;
        let referenced_table =
            required_nonempty_sidecar_string(foreign, "refTable", case_id, "foreignKeys")?;
        let referenced_columns =
            required_sidecar_string_array(foreign, "refColumns", case_id, "foreignKeys", false)?;
        if columns.len() != referenced_columns.len() {
            return Err(invalid_contract(format!(
                "{case_id} FOREIGN KEY on {table:?} has mismatched local/referenced arity"
            )));
        }
        validate_sidecar_column_references(&catalog, &table, &columns, case_id, "FOREIGN KEY")?;
        validate_sidecar_column_references(
            &catalog,
            &referenced_table,
            &referenced_columns,
            case_id,
            "FOREIGN KEY reference",
        )?;
        let source = required_nonempty_sidecar_string(foreign, "source", case_id, "foreignKeys")?;
        if !matches!(source.as_str(), "alter_table" | "create_table") {
            return Err(invalid_contract(format!(
                "{case_id} FOREIGN KEY uses unsupported source discriminator {source:?}"
            )));
        }
        let actions = foreign
            .get("actions")
            .and_then(Value::as_str)
            .ok_or_else(|| {
                invalid_contract(format!("{case_id} FOREIGN KEY actions must be a string"))
            })?;
        if !matches!(
            actions,
            "" | "ON DELETE CASCADE"
                | "ON DELETE CASCADE ON UPDATE CASCADE"
                | "ON DELETE RESTRICT"
                | "ON DELETE SET NULL"
        ) {
            return Err(invalid_contract(format!(
                "{case_id} FOREIGN KEY uses unsupported referential-action metadata {actions:?}"
            )));
        }
    }
    for (index, check) in sidecar_object_array(sidecar, "checks", case_id)?
        .iter()
        .enumerate()
    {
        let check = require_exact_object_fields(
            check,
            &["expression", "source", "table"],
            &format!("{case_id} sidecar.checks[{index}]"),
        )?;
        let table = required_nonempty_sidecar_string(check, "table", case_id, "checks")?;
        if !catalog.contains_key(&table) {
            return Err(invalid_contract(format!(
                "{case_id} CHECK names unknown table {table:?}"
            )));
        }
        required_nonempty_sidecar_string(check, "expression", case_id, "checks")?;
        let source = required_nonempty_sidecar_string(check, "source", case_id, "checks")?;
        if source != "create_table" {
            return Err(invalid_contract(format!(
                "{case_id} CHECK uses unsupported source discriminator {source:?}"
            )));
        }
    }
    for (index, unique_index) in sidecar_object_array(sidecar, "uniqueIndexes", case_id)?
        .iter()
        .enumerate()
    {
        let unique_index = require_exact_object_fields(
            unique_index,
            &["source", "table", "terms", "where"],
            &format!("{case_id} sidecar.uniqueIndexes[{index}]"),
        )?;
        let table =
            required_nonempty_sidecar_string(unique_index, "table", case_id, "uniqueIndexes")?;
        if !catalog.contains_key(&table) {
            return Err(invalid_contract(format!(
                "{case_id} unique index names unknown table {table:?}"
            )));
        }
        required_sidecar_string_array(unique_index, "terms", case_id, "uniqueIndexes", false)?;
        if unique_index.get("where").and_then(Value::as_str).is_none() {
            return Err(invalid_contract(format!(
                "{case_id} unique index predicate must be preserved SQL text (possibly empty)"
            )));
        }
        let source =
            required_nonempty_sidecar_string(unique_index, "source", case_id, "uniqueIndexes")?;
        if source != "create_unique_index" {
            return Err(invalid_contract(format!(
                "{case_id} unique index uses unsupported source discriminator {source:?}"
            )));
        }
    }
    let unsupported = sidecar_object_array(sidecar, "unsupportedSemanticConstraints", case_id)?;
    if !unsupported.is_empty() {
        return Err(invalid_contract(format!(
            "{case_id} sidecar has {} unsupported semantic constraint(s)",
            unsupported.len()
        )));
    }
    let _ = path;
    Ok(())
}

fn required_nonempty_sidecar_string(
    object: &Map<String, Value>,
    field: &str,
    case_id: &str,
    label: &str,
) -> Result<String> {
    let value = object.get(field).and_then(Value::as_str).ok_or_else(|| {
        invalid_contract(format!(
            "{case_id} sidecar.{label}.{field} must be a string"
        ))
    })?;
    if value.is_empty() {
        return Err(invalid_contract(format!(
            "{case_id} sidecar.{label}.{field} must not be empty"
        )));
    }
    Ok(value.to_owned())
}

fn required_sidecar_bool(
    object: &Map<String, Value>,
    field: &str,
    case_id: &str,
    label: &str,
) -> Result<bool> {
    object.get(field).and_then(Value::as_bool).ok_or_else(|| {
        invalid_contract(format!("{case_id} sidecar.{label}.{field} must be Boolean"))
    })
}

fn required_sidecar_string_array(
    object: &Map<String, Value>,
    field: &str,
    case_id: &str,
    label: &str,
    allow_empty: bool,
) -> Result<Vec<String>> {
    let values = object.get(field).and_then(Value::as_array).ok_or_else(|| {
        invalid_contract(format!(
            "{case_id} sidecar.{label}.{field} must be an array"
        ))
    })?;
    if !allow_empty && values.is_empty() {
        return Err(invalid_contract(format!(
            "{case_id} sidecar.{label}.{field} must not be empty"
        )));
    }
    let mut result = Vec::with_capacity(values.len());
    let mut seen = BTreeSet::new();
    for value in values {
        let value = value
            .as_str()
            .filter(|value| !value.is_empty())
            .ok_or_else(|| {
                invalid_contract(format!(
                    "{case_id} sidecar.{label}.{field} must contain nonempty strings"
                ))
            })?;
        if !seen.insert(value) {
            return Err(invalid_contract(format!(
                "{case_id} sidecar.{label}.{field} repeats {value:?}"
            )));
        }
        result.push(value.to_owned());
    }
    Ok(result)
}

fn validate_sidecar_column_references(
    catalog: &BTreeMap<String, BTreeMap<String, bool>>,
    table: &str,
    columns: &[String],
    case_id: &str,
    kind: &str,
) -> Result<()> {
    let table_columns = catalog.get(table).ok_or_else(|| {
        invalid_contract(format!("{case_id} {kind} names unknown table {table:?}"))
    })?;
    for column in columns {
        if !table_columns.contains_key(column) {
            return Err(invalid_contract(format!(
                "{case_id} {kind} names unknown column {table}.{column}"
            )));
        }
    }
    Ok(())
}

fn normalize_contract_primary_not_null(contract: &mut SchemaIntegrityContract) {
    for table in &mut contract.tables {
        if let Some(primary_key) = &table.constraints.primary_key {
            for column in primary_key {
                if !table.constraints.not_null.contains(column) {
                    table.constraints.not_null.push(column.clone());
                }
            }
        }
    }
}

fn deduplicate_contract(contract: &mut SchemaIntegrityContract) {
    for table in &mut contract.tables {
        dedup_preserving_order(&mut table.constraints.not_null);
        table
            .constraints
            .unique
            .dedup_by(|left, right| left.columns == right.columns);
        table.constraints.foreign_keys.dedup_by(|left, right| {
            left.columns == right.columns
                && left.referenced_table == right.referenced_table
                && left.referenced_columns == right.referenced_columns
                && left.match_type == right.match_type
        });
        table
            .constraints
            .checks
            .dedup_by(|left, right| left.expression == right.expression);
        table
            .constraints
            .unique_indexes
            .dedup_by(|left, right| left.terms == right.terms && left.predicate == right.predicate);
    }
}

fn dedup_preserving_order(values: &mut Vec<String>) {
    let mut seen = BTreeSet::new();
    values.retain(|value| seen.insert(value.clone()));
}

fn validate_contract_referenced_keys(contract: &SchemaIntegrityContract) -> Result<()> {
    let tables = contract
        .tables
        .iter()
        .map(|table| (table.name.as_str(), &table.constraints))
        .collect::<BTreeMap<_, _>>();
    for table in &contract.tables {
        for foreign in &table.constraints.foreign_keys {
            if foreign.columns.is_empty()
                || foreign.columns.len() != foreign.referenced_columns.len()
            {
                return Err(invalid_contract(format!(
                    "foreign key on {:?} has {} local and {} referenced columns",
                    table.name,
                    foreign.columns.len(),
                    foreign.referenced_columns.len()
                )));
            }
            let referenced = tables
                .get(foreign.referenced_table.as_str())
                .ok_or_else(|| {
                    invalid_contract(format!(
                        "foreign key on {:?} references unknown contract table {:?}",
                        table.name, foreign.referenced_table
                    ))
                })?;
            let well_formed = referenced
                .primary_key
                .as_ref()
                .is_some_and(|key| key == &foreign.referenced_columns)
                || referenced
                    .unique
                    .iter()
                    .any(|key| key.columns == foreign.referenced_columns);
            if !well_formed {
                return Err(invalid_contract(format!(
                    "foreign key on {:?} references {:?}({}), which is not an ordinary PRIMARY KEY or UNIQUE key in the same contract",
                    table.name,
                    foreign.referenced_table,
                    foreign.referenced_columns.join(", ")
                )));
            }
        }
    }
    Ok(())
}

fn merge_table_constraints(
    target: &mut TableConstraints,
    source: &TableConstraints,
    table: &str,
) -> Result<()> {
    for column in &source.not_null {
        if !target.not_null.contains(column) {
            target.not_null.push(column.clone());
        }
    }
    match (&target.primary_key, &source.primary_key) {
        (Some(left), Some(right)) if left != right => {
            return Err(invalid_contract(format!(
                "DDL and metadata disagree on the primary key for {table:?}: {left:?} versus {right:?}"
            )));
        }
        (None, Some(key)) => target.primary_key = Some(key.clone()),
        _ => {}
    }
    for unique in &source.unique {
        if !target
            .unique
            .iter()
            .any(|existing| existing.columns == unique.columns)
        {
            target.unique.push(unique.clone());
        }
    }
    for foreign in &source.foreign_keys {
        if !target.foreign_keys.iter().any(|existing| {
            existing.columns == foreign.columns
                && existing.referenced_table == foreign.referenced_table
                && existing.referenced_columns == foreign.referenced_columns
                && existing.match_type == foreign.match_type
        }) {
            target.foreign_keys.push(foreign.clone());
        }
    }
    for check in &source.checks {
        if !target
            .checks
            .iter()
            .any(|existing| existing.expression == check.expression)
        {
            target.checks.push(check.clone());
        }
    }
    for index in &source.unique_indexes {
        if !target
            .unique_indexes
            .iter()
            .any(|existing| existing.terms == index.terms && existing.predicate == index.predicate)
        {
            target.unique_indexes.push(index.clone());
        }
    }
    Ok(())
}

pub fn validate_and_normalize_schema_constraints(schema: &mut Schema) -> Result<()> {
    let table_positions = schema
        .tables
        .iter()
        .enumerate()
        .map(|(index, table)| (table.name.clone(), index))
        .collect::<BTreeMap<_, _>>();
    // Referenced-key validation needs a stable view while local NOT NULL
    // order is normalized in place.
    let schema_snapshot = schema.tables.clone();
    for table in &mut schema.tables {
        let positions = table
            .columns
            .iter()
            .enumerate()
            .map(|(index, column)| (column.name.clone(), index))
            .collect::<BTreeMap<_, _>>();
        for column in table.constraints.primary_key.iter().flatten() {
            if !table.constraints.not_null.contains(column) {
                table.constraints.not_null.push(column.clone());
            }
        }
        table
            .constraints
            .not_null
            .sort_by_key(|column| positions.get(column).copied().unwrap_or(usize::MAX));
        dedup_preserving_order(&mut table.constraints.not_null);
        validate_column_list(
            &table.name,
            "NOT NULL",
            &table.constraints.not_null,
            &positions,
            true,
        )?;
        if let Some(primary_key) = &table.constraints.primary_key {
            validate_column_list(&table.name, "PRIMARY KEY", primary_key, &positions, false)?;
        }
        for unique in &table.constraints.unique {
            validate_column_list(&table.name, "UNIQUE", &unique.columns, &positions, false)?;
        }
        for foreign in &table.constraints.foreign_keys {
            validate_column_list(
                &table.name,
                "FOREIGN KEY",
                &foreign.columns,
                &positions,
                false,
            )?;
            if foreign.columns.len() != foreign.referenced_columns.len() {
                return Err(invalid_contract(format!(
                    "foreign key on {:?} has mismatched local/referenced arity",
                    table.name
                )));
            }
            let Some(&referenced_position) = table_positions.get(&foreign.referenced_table) else {
                return Err(invalid_contract(format!(
                    "foreign key on {:?} references unknown table {:?}",
                    table.name, foreign.referenced_table
                )));
            };
            let referenced_table = &schema_snapshot[referenced_position];
            let referenced_columns = referenced_table
                .columns
                .iter()
                .map(|column| (column.name.as_str(), &column.ty))
                .collect::<BTreeMap<_, _>>();
            for (local, referenced) in foreign.columns.iter().zip(&foreign.referenced_columns) {
                let local_ty = &table.columns[*positions.get(local).expect("validated local")].ty;
                let referenced_ty =
                    referenced_columns.get(referenced.as_str()).ok_or_else(|| {
                        invalid_contract(format!(
                            "foreign key on {:?} references unknown column {:?}.{:?}",
                            table.name, foreign.referenced_table, referenced
                        ))
                    })?;
                if !foreign_key_types_compatible(local_ty, referenced_ty) {
                    return Err(invalid_contract(format!(
                        "foreign key equality type mismatch: {:?}.{:?} is {local_ty:?}, but {:?}.{:?} is {referenced_ty:?}",
                        table.name, local, foreign.referenced_table, referenced
                    )));
                }
            }
            let referenced_key = referenced_table
                .constraints
                .primary_key
                .as_ref()
                .is_some_and(|key| key == &foreign.referenced_columns)
                || referenced_table
                    .constraints
                    .unique
                    .iter()
                    .any(|key| key.columns == foreign.referenced_columns);
            if !referenced_key {
                return Err(invalid_contract(format!(
                    "foreign key on {:?} references columns which are not an ordinary PRIMARY KEY or UNIQUE key on {:?}",
                    table.name, foreign.referenced_table
                )));
            }
        }
        for check in &table.constraints.checks {
            let ty = infer_predicate(&check.expression, table, &positions)?;
            if ty != SqlType::Boolean {
                return Err(invalid_contract(format!(
                    "CHECK on {:?} did not infer BOOLEAN",
                    table.name
                )));
            }
        }
        for index in &table.constraints.unique_indexes {
            if index.terms.is_empty() {
                return Err(invalid_contract(format!(
                    "unique index on {:?} has no terms",
                    table.name
                )));
            }
            for term in &index.terms {
                let ty = infer_value_expr(&term.expression, table, &positions)?;
                if let Some(operator_class) = &term.operator_class
                    && (operator_class != "varchar_pattern_ops"
                        || !matches!(
                            ty,
                            SqlType::String(SqlStringType::Text | SqlStringType::Varchar { .. })
                        ))
                {
                    return Err(invalid_contract(format!(
                        "unsupported unique-index operator class {operator_class:?} for {ty:?} on {:?}",
                        table.name
                    )));
                }
            }
            if let Some(predicate) = &index.predicate {
                infer_predicate(predicate, table, &positions)?;
            }
        }
    }
    Ok(())
}

fn validate_column_list(
    table: &str,
    kind: &str,
    columns: &[String],
    positions: &BTreeMap<String, usize>,
    allow_empty: bool,
) -> Result<()> {
    if !allow_empty && columns.is_empty() {
        return Err(invalid_contract(format!(
            "{kind} on {table:?} has no columns"
        )));
    }
    let mut seen = BTreeSet::new();
    for column in columns {
        if !positions.contains_key(column) {
            return Err(invalid_contract(format!(
                "{kind} on {table:?} names unknown column {column:?}"
            )));
        }
        if !seen.insert(column) {
            return Err(invalid_contract(format!(
                "{kind} on {table:?} repeats column {column:?}"
            )));
        }
    }
    Ok(())
}

fn infer_predicate(
    predicate: &IntegrityPredicate,
    table: &crate::ir::Table,
    positions: &BTreeMap<String, usize>,
) -> Result<SqlType> {
    match predicate {
        IntegrityPredicate::Truth { expression } | IntegrityPredicate::IsTrue { expression } => {
            let ty = infer_value_expr(expression, table, positions)?;
            if ty != SqlType::Boolean {
                return Err(invalid_contract(format!(
                    "truth-test expression on {:?} has non-BOOLEAN type {ty:?}",
                    table.name
                )));
            }
        }
        IntegrityPredicate::IsNull { expression }
        | IntegrityPredicate::IsNotNull { expression } => {
            infer_value_expr(expression, table, positions)?;
        }
        IntegrityPredicate::Comparison { left, right, .. } => {
            let left = infer_value_expr(left, table, positions)?;
            let right = infer_value_expr(right, table, positions)?;
            if !integrity_types_comparable(&left, &right) {
                return Err(invalid_contract(format!(
                    "integrity comparison on {:?} has incompatible types {left:?} and {right:?}",
                    table.name
                )));
            }
        }
        IntegrityPredicate::Any { left, values, .. } => {
            if values.is_empty() {
                return Err(invalid_contract("ANY array must not be empty"));
            }
            let left = infer_value_expr(left, table, positions)?;
            for value in values {
                let right = infer_value_expr(value, table, positions)?;
                if !integrity_types_comparable(&left, &right) {
                    return Err(invalid_contract(format!(
                        "ANY comparison on {:?} has incompatible types {left:?} and {right:?}",
                        table.name
                    )));
                }
            }
        }
        IntegrityPredicate::And { left, right } | IntegrityPredicate::Or { left, right } => {
            infer_predicate(left, table, positions)?;
            infer_predicate(right, table, positions)?;
        }
        IntegrityPredicate::Not { predicate } => {
            infer_predicate(predicate, table, positions)?;
        }
    }
    Ok(SqlType::Boolean)
}

fn integrity_types_comparable(left: &SqlType, right: &SqlType) -> bool {
    left == right
        || matches!((left, right), (SqlType::String(_), SqlType::String(_)))
        || matches!(
            (left, right),
            (SqlType::Integer, SqlType::BigInt) | (SqlType::BigInt, SqlType::Integer)
        )
}

fn foreign_key_types_compatible(source: &SqlType, referenced: &SqlType) -> bool {
    source == referenced
        || matches!(
            (source, referenced),
            (SqlType::Integer, SqlType::BigInt) | (SqlType::BigInt, SqlType::Integer)
        )
}

fn schema_integrity_uses_string_semantics(schema: &Schema) -> Result<bool> {
    let table_positions = schema
        .tables
        .iter()
        .enumerate()
        .map(|(index, table)| (table.name.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    for table in &schema.tables {
        let positions = table
            .columns
            .iter()
            .enumerate()
            .map(|(index, column)| (column.name.clone(), index))
            .collect::<BTreeMap<_, _>>();
        let column_is_string = |column: &str| {
            positions
                .get(column)
                .is_some_and(|index| matches!(table.columns[*index].ty, SqlType::String(_)))
        };
        if table
            .constraints
            .primary_key
            .iter()
            .flatten()
            .any(|column| column_is_string(column))
            || table
                .constraints
                .unique
                .iter()
                .any(|unique| unique.columns.iter().any(|column| column_is_string(column)))
        {
            return Ok(true);
        }
        for foreign in &table.constraints.foreign_keys {
            if foreign
                .columns
                .iter()
                .any(|column| column_is_string(column))
            {
                return Ok(true);
            }
            let referenced_position = table_positions
                .get(foreign.referenced_table.as_str())
                .ok_or_else(|| {
                    invalid_contract(format!(
                        "foreign key on {:?} references unknown table {:?}",
                        table.name, foreign.referenced_table
                    ))
                })?;
            let referenced = &schema.tables[*referenced_position];
            if foreign.referenced_columns.iter().any(|column| {
                referenced
                    .columns
                    .iter()
                    .find(|candidate| candidate.name == *column)
                    .is_some_and(|candidate| matches!(candidate.ty, SqlType::String(_)))
            }) {
                return Ok(true);
            }
        }
        for check in &table.constraints.checks {
            if integrity_predicate_uses_string(&check.expression, table, &positions)? {
                return Ok(true);
            }
        }
        for index in &table.constraints.unique_indexes {
            for term in &index.terms {
                if matches!(
                    infer_value_expr(&term.expression, table, &positions)?,
                    SqlType::String(_)
                ) {
                    return Ok(true);
                }
            }
            if let Some(predicate) = &index.predicate
                && integrity_predicate_uses_string(predicate, table, &positions)?
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn integrity_predicate_uses_string(
    predicate: &IntegrityPredicate,
    table: &crate::ir::Table,
    positions: &BTreeMap<String, usize>,
) -> Result<bool> {
    let expression_is_string = |expression: &IntegrityValueExpr| {
        infer_value_expr(expression, table, positions).map(|ty| matches!(ty, SqlType::String(_)))
    };
    match predicate {
        IntegrityPredicate::Truth { expression }
        | IntegrityPredicate::IsTrue { expression }
        | IntegrityPredicate::IsNull { expression }
        | IntegrityPredicate::IsNotNull { expression } => expression_is_string(expression),
        IntegrityPredicate::Comparison { left, right, .. } => {
            Ok(expression_is_string(left)? || expression_is_string(right)?)
        }
        IntegrityPredicate::Any { left, values, .. } => {
            if expression_is_string(left)? {
                return Ok(true);
            }
            for value in values {
                if expression_is_string(value)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        IntegrityPredicate::And { left, right } | IntegrityPredicate::Or { left, right } => {
            Ok(integrity_predicate_uses_string(left, table, positions)?
                || integrity_predicate_uses_string(right, table, positions)?)
        }
        IntegrityPredicate::Not { predicate } => {
            integrity_predicate_uses_string(predicate, table, positions)
        }
    }
}

fn infer_value_expr(
    expression: &IntegrityValueExpr,
    table: &crate::ir::Table,
    positions: &BTreeMap<String, usize>,
) -> Result<SqlType> {
    match expression {
        IntegrityValueExpr::Column { name } => positions
            .get(name)
            .map(|position| table.columns[*position].ty.clone())
            .ok_or_else(|| {
                invalid_contract(format!(
                    "integrity expression on {:?} names unknown column {name:?}",
                    table.name
                ))
            }),
        IntegrityValueExpr::Literal { raw, ty } => {
            match ty {
                SqlType::Integer => {
                    raw.parse::<i32>().map_err(|_| {
                        invalid_contract(format!(
                            "integrity integer literal {raw:?} is outside PostgreSQL int4 range"
                        ))
                    })?;
                }
                SqlType::BigInt => {
                    raw.parse::<i64>().map_err(|_| {
                        invalid_contract(format!(
                            "integrity bigint literal {raw:?} is outside PostgreSQL int8 range"
                        ))
                    })?;
                }
                SqlType::Boolean
                    if raw.eq_ignore_ascii_case("true") || raw.eq_ignore_ascii_case("false") => {}
                SqlType::String(_) => {}
                _ => {
                    return Err(invalid_contract(format!(
                        "unsupported or malformed integrity literal {raw:?} with type {ty:?}"
                    )));
                }
            }
            Ok(ty.clone())
        }
        IntegrityValueExpr::Cast { expression, ty } => {
            if !matches!(
                ty,
                SqlType::Integer | SqlType::BigInt | SqlType::Boolean | SqlType::String(_)
            ) {
                return Err(invalid_contract(format!(
                    "unsupported integrity cast target {ty:?} on {:?}",
                    table.name
                )));
            }
            let source = infer_value_expr(expression, table, positions)?;
            let supported =
                source == *ty || matches!((&source, ty), (SqlType::String(_), SqlType::String(_)));
            if !supported {
                return Err(invalid_contract(format!(
                    "unsupported integrity cast from {source:?} to {ty:?} on {:?}",
                    table.name
                )));
            }
            Ok(ty.clone())
        }
        IntegrityValueExpr::Lower { expression } => {
            let source = infer_value_expr(expression, table, positions)?;
            if !matches!(source, SqlType::String(_)) {
                return Err(invalid_contract(format!(
                    "lower() integrity expression on {:?} has non-string input {source:?}",
                    table.name
                )));
            }
            Ok(SqlType::text())
        }
        IntegrityValueExpr::Coalesce { arguments } => {
            let Some(first) = arguments.first() else {
                return Err(invalid_contract(
                    "coalesce integrity expression has no arguments",
                ));
            };
            let ty = infer_value_expr(first, table, positions)?;
            for argument in &arguments[1..] {
                let argument_ty = infer_value_expr(argument, table, positions)?;
                if !integrity_types_comparable(&ty, &argument_ty) {
                    return Err(invalid_contract(format!(
                        "coalesce integrity expression on {:?} mixes {ty:?} and {argument_ty:?}",
                        table.name
                    )));
                }
            }
            Ok(ty)
        }
    }
}

fn sidecar_array<'a>(sidecar: &'a Value, name: &str, case_id: &str) -> Result<&'a Vec<Value>> {
    sidecar.get(name).and_then(Value::as_array).ok_or_else(|| {
        invalid_contract(format!(
            "{case_id} sidecar field {name:?} is missing or is not an array"
        ))
    })
}

fn sidecar_object_array<'a>(
    sidecar: &'a Map<String, Value>,
    name: &str,
    case_id: &str,
) -> Result<&'a Vec<Value>> {
    sidecar.get(name).and_then(Value::as_array).ok_or_else(|| {
        invalid_contract(format!(
            "{case_id} sidecar field {name:?} is missing or is not an array"
        ))
    })
}

fn renamed_string_array(
    value: &Value,
    field: &str,
    rename: &impl Fn(&str) -> String,
    case_id: &str,
) -> Result<Vec<String>> {
    value
        .get(field)
        .and_then(Value::as_array)
        .ok_or_else(|| {
            invalid_contract(format!("{case_id} sidecar field {field:?} is not an array"))
        })?
        .iter()
        .map(|value| {
            value.as_str().map(rename).ok_or_else(|| {
                invalid_contract(format!(
                    "{case_id} sidecar field {field:?} contains a non-string value"
                ))
            })
        })
        .collect()
}

fn resolve_repository_path(metadata_path: &Path, value: &str) -> Result<PathBuf> {
    let path = Path::new(value);
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                std::path::Component::ParentDir
                    | std::path::Component::RootDir
                    | std::path::Component::Prefix(_)
            )
        })
    {
        return Err(invalid_contract(format!(
            "semantic sidecar path must be a repository-relative descendant, found {value:?}"
        )));
    }
    if path.is_file() {
        return Ok(path.to_path_buf());
    }
    for ancestor in metadata_path.ancestors() {
        let candidate = ancestor.join(path);
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(invalid_contract(format!(
        "cannot resolve semantic sidecar path {value:?} from {}",
        metadata_path.display()
    )))
}

fn read_json(path: &Path) -> Result<Value> {
    let text = std::fs::read_to_string(path).map_err(|source| Error::Read {
        path: path.to_path_buf(),
        source,
    })?;
    serde_json::from_str(&text).map_err(|source| Error::Json {
        path: path.to_path_buf(),
        source,
    })
}

fn require_exact_object_fields<'a>(
    value: &'a Value,
    expected: &[&str],
    label: &str,
) -> Result<&'a Map<String, Value>> {
    let object = value
        .as_object()
        .ok_or_else(|| invalid_contract(format!("{label} must be an object")))?;
    let mut actual = object.keys().map(String::as_str).collect::<Vec<_>>();
    actual.sort_unstable();
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    if actual != expected {
        return Err(invalid_contract(format!(
            "{label} has fields {actual:?}; expected exactly {expected:?}"
        )));
    }
    Ok(object)
}

fn required_string(value: &Value, field: &str, path: &Path) -> Result<String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| {
            invalid_contract(format!(
                "{} field {field:?} is missing or is not a string",
                path.display()
            ))
        })
}

fn optional_string(value: &Value, field: &str) -> Result<Option<String>> {
    match value.get(field) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(value)) => Ok(Some(value.clone())),
        Some(_) => Err(invalid_contract(format!("field {field:?} is not a string"))),
    }
}

fn invalid_contract(message: impl Into<String>) -> Error {
    Error::InvalidSchema(format!("integrity contract: {}", message.into()))
}

fn display_columns(columns: &[String]) -> String {
    columns
        .iter()
        .map(|column| display_ident(column))
        .collect::<Vec<_>>()
        .join(", ")
}

fn display_ident(value: &str) -> String {
    quote_ident(value)
}

fn quote_ident(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

fn render_value_expr(expression: &IntegrityValueExpr) -> String {
    match expression {
        IntegrityValueExpr::Column { name } => quote_ident(name),
        IntegrityValueExpr::Literal { raw, ty } => render_typed_literal(raw, ty),
        IntegrityValueExpr::Cast { expression, ty } => format!(
            "CAST(({}) AS {})",
            render_value_expr(expression),
            render_type(ty)
        ),
        IntegrityValueExpr::Lower { expression } => {
            format!("lower(({}))", render_value_expr(expression))
        }
        IntegrityValueExpr::Coalesce { arguments } => format!(
            "coalesce({})",
            arguments
                .iter()
                .map(render_value_expr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn render_predicate(predicate: &IntegrityPredicate) -> String {
    match predicate {
        IntegrityPredicate::Truth { expression } => render_value_expr(expression),
        IntegrityPredicate::IsTrue { expression } => {
            format!("({}) IS TRUE", render_value_expr(expression))
        }
        IntegrityPredicate::IsNull { expression } => {
            format!("({}) IS NULL", render_value_expr(expression))
        }
        IntegrityPredicate::IsNotNull { expression } => {
            format!("({}) IS NOT NULL", render_value_expr(expression))
        }
        IntegrityPredicate::Comparison {
            comparison,
            left,
            right,
        } => format!(
            "({}) {} ({})",
            render_value_expr(left),
            comparison_sql(*comparison),
            render_value_expr(right)
        ),
        IntegrityPredicate::Any {
            comparison,
            left,
            values,
        } => format!(
            "({}) {} ANY (ARRAY[{}])",
            render_value_expr(left),
            comparison_sql(*comparison),
            values
                .iter()
                .map(render_value_expr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        IntegrityPredicate::And { left, right } => {
            format!(
                "({}) AND ({})",
                render_predicate(left),
                render_predicate(right)
            )
        }
        IntegrityPredicate::Or { left, right } => {
            format!(
                "({}) OR ({})",
                render_predicate(left),
                render_predicate(right)
            )
        }
        IntegrityPredicate::Not { predicate } => {
            format!("NOT ({})", render_predicate(predicate))
        }
    }
}

fn comparison_sql(comparison: IntegrityComparison) -> &'static str {
    match comparison {
        IntegrityComparison::Equal => "=",
        IntegrityComparison::NotEqual => "<>",
    }
}

fn render_typed_literal(raw: &str, ty: &SqlType) -> String {
    match ty {
        SqlType::String(_) => format!("{}::{}", quote_literal(raw), render_type(ty)),
        SqlType::Boolean if raw.eq_ignore_ascii_case("true") => "TRUE".to_owned(),
        SqlType::Boolean if raw.eq_ignore_ascii_case("false") => "FALSE".to_owned(),
        _ => format!("{}::{}", raw, render_type(ty)),
    }
}

fn quote_literal(value: &str) -> String {
    format!("'{}'", value.replace('\'', "''"))
}

fn render_type(ty: &SqlType) -> String {
    match ty {
        SqlType::Integer => "integer".to_owned(),
        SqlType::BigInt => "bigint".to_owned(),
        SqlType::Boolean => "boolean".to_owned(),
        SqlType::String(SqlStringType::Text) => "text".to_owned(),
        SqlType::String(SqlStringType::Varchar { length: None }) => "varchar".to_owned(),
        SqlType::String(SqlStringType::Varchar {
            length: Some(length),
        }) => format!("varchar({length})"),
        SqlType::String(SqlStringType::Char { length }) => format!("char({length})"),
        SqlType::String(SqlStringType::Bpchar) => "bpchar".to_owned(),
        other => panic!("validated integrity expression reached unsupported SQL type {other:?}"),
    }
}

/// The sanitizer has already tokenized/normalized these expressions.  This
/// second parser is intentionally independent and fail-closed: it accepts only
/// the exact logical forms whose FormalSQL and validator semantics are wired.
pub fn parse_integrity_predicate(source: &str) -> std::result::Result<IntegrityPredicate, String> {
    parse_integrity_predicate_with_rename(source, &str::to_owned)
}

fn parse_integrity_predicate_with_rename(
    source: &str,
    rename: &impl Fn(&str) -> String,
) -> std::result::Result<IntegrityPredicate, String> {
    let tokens = lex_integrity_expression(source)?;
    let mut parser = IntegrityParser::new(tokens, rename);
    let predicate = parser.parse_or()?;
    parser.expect_end()?;
    Ok(predicate)
}

pub fn parse_unique_index_term(source: &str) -> std::result::Result<UniqueIndexTerm, String> {
    parse_unique_index_term_with_rename(source, &str::to_owned)
}

fn parse_unique_index_term_with_rename(
    source: &str,
    rename: &impl Fn(&str) -> String,
) -> std::result::Result<UniqueIndexTerm, String> {
    let tokens = lex_integrity_expression(source)?;
    let mut parser = IntegrityParser::new(tokens, rename);
    let expression = parser.parse_value()?;
    let operator_class = if parser.consume_keyword("varchar_pattern_ops") {
        Some("varchar_pattern_ops".to_owned())
    } else {
        None
    };
    let mut direction = IntegritySortDirection::Asc;
    if parser.consume_keyword("ASC") {
        direction = IntegritySortDirection::Asc;
    } else if parser.consume_keyword("DESC") {
        direction = IntegritySortDirection::Desc;
    }
    let nulls = if parser.consume_keyword("NULLS") {
        if parser.consume_keyword("FIRST") {
            Some(IntegrityNullsOrder::First)
        } else if parser.consume_keyword("LAST") {
            Some(IntegrityNullsOrder::Last)
        } else {
            return Err("NULLS must be followed by FIRST or LAST".to_owned());
        }
    } else {
        None
    };
    if !parser.at_end() {
        return Err(format!(
            "unsupported, repeated, or out-of-order unique-index decoration {}; expected [varchar_pattern_ops] [ASC|DESC] [NULLS FIRST|LAST]",
            parser.current_description()
        ));
    }
    Ok(UniqueIndexTerm {
        expression,
        source_sql: rename_expression_source(source, rename),
        direction,
        nulls,
        operator_class,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Identifier(String),
    QuotedIdentifier(String),
    String(String),
    Integer(String),
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Cast,
    Equal,
    NotEqual,
    Minus,
}

fn lex_integrity_expression(source: &str) -> std::result::Result<Vec<Token>, String> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            byte if byte.is_ascii_whitespace() => index += 1,
            b'(' => {
                tokens.push(Token::LParen);
                index += 1;
            }
            b')' => {
                tokens.push(Token::RParen);
                index += 1;
            }
            b'[' => {
                tokens.push(Token::LBracket);
                index += 1;
            }
            b']' => {
                tokens.push(Token::RBracket);
                index += 1;
            }
            b',' => {
                tokens.push(Token::Comma);
                index += 1;
            }
            b':' if bytes.get(index + 1) == Some(&b':') => {
                tokens.push(Token::Cast);
                index += 2;
            }
            b'=' => {
                tokens.push(Token::Equal);
                index += 1;
            }
            b'<' if bytes.get(index + 1) == Some(&b'>') => {
                tokens.push(Token::NotEqual);
                index += 2;
            }
            b'!' if bytes.get(index + 1) == Some(&b'=') => {
                tokens.push(Token::NotEqual);
                index += 2;
            }
            b'-' => {
                tokens.push(Token::Minus);
                index += 1;
            }
            b'\'' => {
                let mut value = String::new();
                index += 1;
                loop {
                    if index >= bytes.len() {
                        return Err("unterminated string literal".to_owned());
                    }
                    if bytes[index] == b'\'' {
                        if bytes.get(index + 1) == Some(&b'\'') {
                            value.push('\'');
                            index += 2;
                        } else {
                            index += 1;
                            break;
                        }
                    } else if bytes[index].is_ascii() {
                        value.push(bytes[index] as char);
                        index += 1;
                    } else {
                        let rest = std::str::from_utf8(&bytes[index..])
                            .map_err(|_| "invalid UTF-8 string literal".to_owned())?;
                        let ch = rest.chars().next().expect("nonempty utf8");
                        value.push(ch);
                        index += ch.len_utf8();
                    }
                }
                tokens.push(Token::String(value));
            }
            b'"' => {
                let mut value = String::new();
                index += 1;
                loop {
                    if index >= bytes.len() {
                        return Err("unterminated quoted identifier".to_owned());
                    }
                    if bytes[index] == b'"' {
                        if bytes.get(index + 1) == Some(&b'"') {
                            value.push('"');
                            index += 2;
                        } else {
                            index += 1;
                            break;
                        }
                    } else if bytes[index].is_ascii() {
                        value.push(bytes[index] as char);
                        index += 1;
                    } else {
                        let rest = std::str::from_utf8(&bytes[index..])
                            .map_err(|_| "invalid UTF-8 quoted identifier".to_owned())?;
                        let ch = rest.chars().next().expect("nonempty utf8");
                        value.push(ch);
                        index += ch.len_utf8();
                    }
                }
                tokens.push(Token::QuotedIdentifier(value));
            }
            byte if byte.is_ascii_digit() => {
                let start = index;
                while index < bytes.len() && bytes[index].is_ascii_digit() {
                    index += 1;
                }
                tokens.push(Token::Integer(source[start..index].to_owned()));
            }
            byte if byte.is_ascii_alphabetic() || byte == b'_' => {
                let start = index;
                index += 1;
                while index < bytes.len()
                    && (bytes[index].is_ascii_alphanumeric() || matches!(bytes[index], b'_' | b'$'))
                {
                    index += 1;
                }
                // PostgreSQL folds bare identifiers to lower case.
                tokens.push(Token::Identifier(source[start..index].to_ascii_lowercase()));
            }
            other => {
                return Err(format!(
                    "unsupported byte {:?} at offset {index}",
                    other as char
                ));
            }
        }
    }
    Ok(tokens)
}

struct IntegrityParser<'a, F> {
    tokens: Vec<Token>,
    position: usize,
    rename: &'a F,
}

impl<'a, F: Fn(&str) -> String> IntegrityParser<'a, F> {
    fn new(tokens: Vec<Token>, rename: &'a F) -> Self {
        Self {
            tokens,
            position: 0,
            rename,
        }
    }

    fn parse_or(&mut self) -> std::result::Result<IntegrityPredicate, String> {
        let mut predicate = self.parse_and()?;
        while self.consume_keyword("OR") {
            predicate = IntegrityPredicate::Or {
                left: Box::new(predicate),
                right: Box::new(self.parse_and()?),
            };
        }
        Ok(predicate)
    }

    fn parse_and(&mut self) -> std::result::Result<IntegrityPredicate, String> {
        let mut predicate = self.parse_not()?;
        while self.consume_keyword("AND") {
            predicate = IntegrityPredicate::And {
                left: Box::new(predicate),
                right: Box::new(self.parse_not()?),
            };
        }
        Ok(predicate)
    }

    fn parse_not(&mut self) -> std::result::Result<IntegrityPredicate, String> {
        if self.consume_keyword("NOT") {
            return Ok(IntegrityPredicate::Not {
                predicate: Box::new(self.parse_not()?),
            });
        }
        self.parse_predicate_atom()
    }

    fn parse_predicate_atom(&mut self) -> std::result::Result<IntegrityPredicate, String> {
        let saved = self.position;
        if let Ok(value) = self.parse_value() {
            if self.consume_keyword("IS") {
                let not = self.consume_keyword("NOT");
                if self.consume_keyword("NULL") {
                    return Ok(if not {
                        IntegrityPredicate::IsNotNull { expression: value }
                    } else {
                        IntegrityPredicate::IsNull { expression: value }
                    });
                }
                if !not && self.consume_keyword("TRUE") {
                    return Ok(IntegrityPredicate::IsTrue { expression: value });
                }
                return Err(
                    "the frozen integrity grammar supports only IS NULL, IS NOT NULL, and IS TRUE"
                        .to_owned(),
                );
            }
            let comparison = if self.consume(&Token::Equal) {
                Some(IntegrityComparison::Equal)
            } else if self.consume(&Token::NotEqual) {
                Some(IntegrityComparison::NotEqual)
            } else {
                None
            };
            if let Some(comparison) = comparison {
                if self.consume_keyword("ANY") {
                    self.expect(Token::LParen)?;
                    self.expect_keyword("ARRAY")?;
                    self.expect(Token::LBracket)?;
                    let mut values = Vec::new();
                    if !self.consume(&Token::RBracket) {
                        loop {
                            values.push(self.parse_value()?);
                            if self.consume(&Token::Comma) {
                                continue;
                            }
                            self.expect(Token::RBracket)?;
                            break;
                        }
                    }
                    self.expect(Token::RParen)?;
                    if values.is_empty() {
                        return Err("ANY array must not be empty".to_owned());
                    }
                    return Ok(IntegrityPredicate::Any {
                        comparison,
                        left: value,
                        values,
                    });
                }
                return Ok(IntegrityPredicate::Comparison {
                    comparison,
                    left: value,
                    right: self.parse_value()?,
                });
            }
            return Ok(IntegrityPredicate::Truth { expression: value });
        }
        self.position = saved;
        self.expect(Token::LParen)?;
        let predicate = self.parse_or()?;
        self.expect(Token::RParen)?;
        Ok(predicate)
    }

    fn parse_value(&mut self) -> std::result::Result<IntegrityValueExpr, String> {
        let mut expression = if self.consume_keyword("LOWER") {
            self.expect(Token::LParen)?;
            let expression = self.parse_value()?;
            self.expect(Token::RParen)?;
            IntegrityValueExpr::Lower {
                expression: Box::new(expression),
            }
        } else if self.consume_keyword("COALESCE") {
            self.expect(Token::LParen)?;
            let mut arguments = Vec::new();
            loop {
                arguments.push(self.parse_value()?);
                if self.consume(&Token::Comma) {
                    continue;
                }
                self.expect(Token::RParen)?;
                break;
            }
            if arguments.len() < 2 {
                return Err("coalesce requires at least two arguments".to_owned());
            }
            IntegrityValueExpr::Coalesce { arguments }
        } else if self.consume(&Token::LParen) {
            let expression = self.parse_value()?;
            self.expect(Token::RParen)?;
            expression
        } else if self.consume(&Token::Minus) {
            let Some(Token::Integer(value)) = self.tokens.get(self.position).cloned() else {
                return Err("unary minus is supported only for integer literals".to_owned());
            };
            self.position += 1;
            let raw = format!("-{value}");
            raw.parse::<i32>()
                .map_err(|_| format!("integer literal {raw:?} is out of int4 range"))?;
            IntegrityValueExpr::Literal {
                raw,
                ty: SqlType::Integer,
            }
        } else {
            match self.tokens.get(self.position).cloned() {
                Some(Token::Identifier(value)) if value.eq_ignore_ascii_case("TRUE") => {
                    self.position += 1;
                    IntegrityValueExpr::Literal {
                        raw: "true".to_owned(),
                        ty: SqlType::Boolean,
                    }
                }
                Some(Token::Identifier(value)) if value.eq_ignore_ascii_case("FALSE") => {
                    self.position += 1;
                    IntegrityValueExpr::Literal {
                        raw: "false".to_owned(),
                        ty: SqlType::Boolean,
                    }
                }
                Some(Token::Identifier(value)) => {
                    self.position += 1;
                    IntegrityValueExpr::Column {
                        name: (self.rename)(&value),
                    }
                }
                Some(Token::QuotedIdentifier(value)) => {
                    self.position += 1;
                    IntegrityValueExpr::Column {
                        name: (self.rename)(&value),
                    }
                }
                Some(Token::String(value)) => {
                    self.position += 1;
                    IntegrityValueExpr::Literal {
                        raw: value,
                        ty: SqlType::text(),
                    }
                }
                Some(Token::Integer(value)) => {
                    self.position += 1;
                    value
                        .parse::<i32>()
                        .map_err(|_| format!("integer literal {value:?} is out of int4 range"))?;
                    IntegrityValueExpr::Literal {
                        raw: value,
                        ty: SqlType::Integer,
                    }
                }
                _ => {
                    return Err(format!(
                        "expected integrity value expression, found {}",
                        self.current_description()
                    ));
                }
            }
        };
        while self.consume(&Token::Cast) {
            let target = self.parse_cast_type()?;
            expression = fold_integrity_cast(expression, target)?;
        }
        Ok(expression)
    }

    fn parse_cast_type(&mut self) -> std::result::Result<SqlType, String> {
        let Some(Token::Identifier(name)) = self.tokens.get(self.position).cloned() else {
            return Err("cast target is not a supported type name".to_owned());
        };
        self.position += 1;
        match name.as_str() {
            "text" => Ok(SqlType::text()),
            "integer" | "int" | "int4" => Ok(SqlType::Integer),
            other => Err(format!("unsupported integrity cast target {other:?}")),
        }
    }

    fn consume_keyword(&mut self, keyword: &str) -> bool {
        match self.tokens.get(self.position) {
            Some(Token::Identifier(value)) if value.eq_ignore_ascii_case(keyword) => {
                self.position += 1;
                true
            }
            _ => false,
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> std::result::Result<(), String> {
        if self.consume_keyword(keyword) {
            Ok(())
        } else {
            Err(format!(
                "expected keyword {keyword}, found {}",
                self.current_description()
            ))
        }
    }

    fn consume(&mut self, expected: &Token) -> bool {
        if self.tokens.get(self.position) == Some(expected) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: Token) -> std::result::Result<(), String> {
        if self.consume(&expected) {
            Ok(())
        } else {
            Err(format!(
                "expected {expected:?}, found {}",
                self.current_description()
            ))
        }
    }

    fn at_end(&self) -> bool {
        self.position == self.tokens.len()
    }

    fn expect_end(&self) -> std::result::Result<(), String> {
        if self.at_end() {
            Ok(())
        } else {
            Err(format!(
                "unexpected trailing token {}",
                self.current_description()
            ))
        }
    }

    fn current_description(&self) -> String {
        self.tokens
            .get(self.position)
            .map(|token| format!("{token:?}"))
            .unwrap_or_else(|| "end of expression".to_owned())
    }
}

fn fold_integrity_cast(
    expression: IntegrityValueExpr,
    target: SqlType,
) -> std::result::Result<IntegrityValueExpr, String> {
    if target == SqlType::Integer
        && let IntegrityValueExpr::Literal {
            raw,
            ty: SqlType::String(_),
        } = &expression
    {
        let parsed = raw
            .parse::<i32>()
            .map_err(|_| format!("integer literal cast {raw:?} is out of int4 range"))?;
        return Ok(IntegrityValueExpr::Literal {
            raw: parsed.to_string(),
            ty: SqlType::Integer,
        });
    }
    Ok(IntegrityValueExpr::Cast {
        expression: Box::new(expression),
        ty: target,
    })
}

/// Source is diagnostic-only.  Replace identifiers conservatively using the
/// same lexer so the displayed contract never presents pre-alpha-renaming
/// table columns as if they were executable names.
fn rename_expression_source(source: &str, rename: &impl Fn(&str) -> String) -> String {
    let Ok(tokens) = lex_integrity_expression(source) else {
        return source.to_owned();
    };
    tokens
        .iter()
        .map(|token| match token {
            Token::Identifier(value) if !is_integrity_keyword(value) => quote_ident(&rename(value)),
            Token::Identifier(value) => value.to_ascii_uppercase(),
            Token::QuotedIdentifier(value) => quote_ident(&rename(value)),
            Token::String(value) => quote_literal(value),
            Token::Integer(value) => value.clone(),
            Token::LParen => "(".to_owned(),
            Token::RParen => ")".to_owned(),
            Token::LBracket => "[".to_owned(),
            Token::RBracket => "]".to_owned(),
            Token::Comma => ",".to_owned(),
            Token::Cast => "::".to_owned(),
            Token::Equal => "=".to_owned(),
            Token::NotEqual => "<>".to_owned(),
            Token::Minus => "-".to_owned(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn is_integrity_keyword(value: &str) -> bool {
    [
        "and",
        "or",
        "not",
        "is",
        "null",
        "true",
        "false",
        "any",
        "array",
        "lower",
        "coalesce",
        "text",
        "integer",
        "int",
        "int4",
        "asc",
        "desc",
        "nulls",
        "first",
        "last",
        "varchar_pattern_ops",
    ]
    .contains(&value.to_ascii_lowercase().as_str())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect_metadata(directory: &Path, output: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(directory).expect("read generated benchmark directory") {
            let entry = entry.expect("read generated benchmark entry");
            let path = entry.path();
            if path.is_dir() {
                collect_metadata(&path, output);
            } else if path.file_name().is_some_and(|name| name == "metadata.json") {
                output.push(path);
            }
        }
    }

    #[test]
    fn parses_all_frozen_check_forms() {
        for expression in [
            "((category_id IS NOT NULL) OR ((archetype):: text <> 'regular':: text))",
            "((category_id IS NULL) OR ((archetype):: text <> 'private_message':: text))",
        ] {
            parse_integrity_predicate(expression).expect(expression);
        }
    }

    #[test]
    fn parses_frozen_partial_index_predicates() {
        for expression in [
            "active",
            "(bounce_key IS NOT NULL)",
            "((notification_type = 6) AND (NOT read))",
            "(read OR (notification_type <> 6))",
            "((instance IS TRUE) AND (template IS TRUE))",
            "((post_action_type_id = ANY (ARRAY [3, 4, 7, 8])))",
            "(visibility_level = ANY (ARRAY[10, 20]))",
        ] {
            parse_integrity_predicate(expression).expect(expression);
        }
    }

    #[test]
    fn is_true_preserves_two_valued_postgres_semantics_and_requires_boolean() {
        let parsed = parse_integrity_predicate("flag IS TRUE").expect("parse IS TRUE");
        assert!(matches!(parsed, IntegrityPredicate::IsTrue { .. }));
        assert_eq!(render_predicate(&parsed), "(\"flag\") IS TRUE");

        let table_with = |ty, predicate| crate::ir::Table {
            name: "items".to_owned(),
            columns: vec![crate::ir::Column {
                name: "flag".to_owned(),
                ty,
                nullable: true,
            }],
            constraints: TableConstraints {
                unique_indexes: vec![UniqueIndexConstraint {
                    name: None,
                    terms: vec![parse_unique_index_term("flag").expect("index term")],
                    predicate: Some(predicate),
                    predicate_sql: Some("flag IS TRUE".to_owned()),
                }],
                ..TableConstraints::default()
            },
        };
        let mut boolean_schema = Schema {
            tables: vec![table_with(SqlType::Boolean, parsed.clone())],
        };
        validate_and_normalize_schema_constraints(&mut boolean_schema)
            .expect("Boolean IS TRUE must validate");

        let mut integer_schema = Schema {
            tables: vec![table_with(SqlType::Integer, parsed)],
        };
        assert!(validate_and_normalize_schema_constraints(&mut integer_schema).is_err());
    }

    #[test]
    fn foreign_keys_reject_heterogeneous_string_equality() {
        let column = |name: &str, ty: SqlType| crate::ir::Column {
            name: name.to_owned(),
            ty,
            nullable: false,
        };
        let mut schema = Schema {
            tables: vec![
                crate::ir::Table {
                    name: "parent".to_owned(),
                    columns: vec![column(
                        "id",
                        SqlType::String(SqlStringType::Char { length: 4 }),
                    )],
                    constraints: TableConstraints {
                        primary_key: Some(vec!["id".to_owned()]),
                        ..TableConstraints::default()
                    },
                },
                crate::ir::Table {
                    name: "child".to_owned(),
                    columns: vec![column("id", SqlType::text())],
                    constraints: TableConstraints {
                        foreign_keys: vec![ForeignKeyConstraint {
                            name: None,
                            columns: vec!["id".to_owned()],
                            referenced_table: "parent".to_owned(),
                            referenced_columns: vec!["id".to_owned()],
                            match_type: ForeignKeyMatch::Simple,
                            referential_actions: None,
                        }],
                        ..TableConstraints::default()
                    },
                },
            ],
        };

        let error = validate_and_normalize_schema_constraints(&mut schema)
            .expect_err("mixed TEXT/CHAR foreign keys must fail closed");
        assert!(
            error
                .to_string()
                .contains("foreign key equality type mismatch")
        );
    }

    #[test]
    fn varchar_pattern_ops_rejects_character_operand() {
        let mut schema = Schema {
            tables: vec![crate::ir::Table {
                name: "items".to_owned(),
                columns: vec![crate::ir::Column {
                    name: "code".to_owned(),
                    ty: SqlType::String(SqlStringType::Char { length: 4 }),
                    nullable: false,
                }],
                constraints: TableConstraints {
                    unique_indexes: vec![UniqueIndexConstraint {
                        name: None,
                        terms: vec![UniqueIndexTerm {
                            expression: IntegrityValueExpr::Column {
                                name: "code".to_owned(),
                            },
                            source_sql: "code varchar_pattern_ops".to_owned(),
                            direction: IntegritySortDirection::Asc,
                            nulls: None,
                            operator_class: Some("varchar_pattern_ops".to_owned()),
                        }],
                        predicate: None,
                        predicate_sql: None,
                    }],
                    ..TableConstraints::default()
                },
            }],
        };

        let error = validate_and_normalize_schema_constraints(&mut schema)
            .expect_err("varchar_pattern_ops must reject CHAR/BPCHAR operands");
        assert!(
            error
                .to_string()
                .contains("unsupported unique-index operator class")
        );
    }

    #[test]
    fn contract_merge_canonicalizes_unquoted_names_and_preserves_ddl_constraints() {
        let contract = SchemaIntegrityContract {
            case_id: Some("case".to_owned()),
            source: None,
            tables: vec![ContractTable {
                name: "DEPT".to_owned(),
                constraints: TableConstraints {
                    primary_key: Some(vec!["DEPTNO".to_owned()]),
                    ..TableConstraints::default()
                },
            }],
            requires_postgres_utf8_c_text_semantics: false,
        };
        let schema = Schema {
            tables: vec![crate::ir::Table {
                name: "dept".to_owned(),
                columns: vec![
                    crate::ir::Column {
                        name: "deptno".to_owned(),
                        ty: SqlType::Integer,
                        nullable: true,
                    },
                    crate::ir::Column {
                        name: "name".to_owned(),
                        ty: SqlType::text(),
                        nullable: true,
                    },
                ],
                constraints: TableConstraints {
                    unique: vec![UniqueConstraint {
                        name: Some("ddl_name_key".to_owned()),
                        columns: vec!["name".to_owned()],
                    }],
                    ..TableConstraints::default()
                },
            }],
        };
        let merged = contract
            .merged_with_schema(&schema)
            .expect("merge contract");
        assert_eq!(merged.tables[0].name, "dept");
        assert_eq!(
            merged.tables[0].constraints.primary_key.as_deref(),
            Some(["deptno".to_owned()].as_slice())
        );
        assert_eq!(merged.tables[0].constraints.not_null, ["deptno"]);
        assert_eq!(merged.tables[0].constraints.unique[0].columns, ["name"]);
    }

    #[test]
    fn contract_case_fold_fallback_fails_on_quoted_name_ambiguity() {
        let schema = Schema {
            tables: ["Foo", "foo"]
                .into_iter()
                .map(|name| crate::ir::Table {
                    name: name.to_owned(),
                    columns: vec![],
                    constraints: TableConstraints::default(),
                })
                .collect(),
        };
        let contract = SchemaIntegrityContract {
            case_id: Some("case".to_owned()),
            source: None,
            tables: vec![ContractTable {
                name: "FOO".to_owned(),
                constraints: TableConstraints {
                    not_null: vec!["id".to_owned()],
                    ..TableConstraints::default()
                },
            }],
            requires_postgres_utf8_c_text_semantics: false,
        };
        assert!(contract.merged_with_schema(&schema).is_err());
    }

    #[test]
    fn parses_frozen_expression_index_terms_and_decorations() {
        for expression in [
            "id DESC",
            "COALESCE(parent_category_id, '-1':: integer)",
            "lower((name):: text)",
            "lower((path)::text) varchar_pattern_ops",
        ] {
            parse_unique_index_term(expression).expect(expression);
        }
    }

    #[test]
    fn unsupported_integrity_forms_fail_closed() {
        for expression in [
            "upper(name)",
            "name LIKE 'x%'",
            "id + 1 = 2",
            "id = ANY (SELECT id FROM t)",
        ] {
            assert!(
                parse_integrity_predicate(expression).is_err(),
                "{expression}"
            );
        }
        assert!(parse_unique_index_term("lower(name) text_pattern_ops").is_err());
    }

    #[test]
    fn integrity_expression_parser_rejects_range_and_duplicate_decorations() {
        for expression in ["id = 2147483648", "id = -2147483649"] {
            assert!(
                parse_integrity_predicate(expression).is_err(),
                "{expression}"
            );
        }
        for term in [
            "id ASC DESC",
            "id DESC DESC",
            "id NULLS FIRST NULLS LAST",
            "id NULLS FIRST DESC",
            "name DESC varchar_pattern_ops",
        ] {
            assert!(parse_unique_index_term(term).is_err(), "{term}");
        }
        parse_unique_index_term("lower(name) varchar_pattern_ops DESC NULLS LAST")
            .expect("PostgreSQL decoration order must remain supported");
    }

    #[test]
    fn quoted_keyword_identifiers_never_become_keywords_or_decorations() {
        let predicate = parse_integrity_predicate("\"true\"").expect("quoted column");
        assert!(matches!(
            predicate,
            IntegrityPredicate::Truth {
                expression: IntegrityValueExpr::Column { ref name }
            } if name == "true"
        ));
        let term = parse_unique_index_term("\"desc\"").expect("quoted column term");
        assert!(matches!(
            term.expression,
            IntegrityValueExpr::Column { ref name } if name == "desc"
        ));
        assert_eq!(term.direction, IntegritySortDirection::Asc);
        assert_eq!(
            rename_expression_source("\"true\"", &|name| format!("renamed_{name}")),
            "\"renamed_true\""
        );
    }

    #[test]
    fn pair_constraint_payloads_reject_unknown_fields() {
        let metadata_path = Path::new("metadata.json");
        for constraints in [
            serde_json::json!([{"not_null": {"value": "T__C", "extra": true}}]),
            serde_json::json!([{"primary": [{"value": "T__C", "extra": true}]}]),
            serde_json::json!([{"foreign": [
                {"value": "T__C"},
                {"value": "U__C", "extra": true}
            ]}]),
        ] {
            let metadata = serde_json::json!({
                "flatCaseId": "strict-pair",
                "constraintScope": "pair",
                "constraints": constraints,
            });
            assert!(load_pair_contract(metadata_path, &metadata).is_err());
        }
    }

    #[test]
    fn wetune_authority_markers_and_sidecars_are_runtime_strict() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("logos-ir is nested under repository root");
        let metadata_path =
            repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/4/metadata.json");
        let metadata = read_json(&metadata_path).expect("read frozen metadata");
        validate_integrity_metadata_reference(&metadata_path, &metadata)
            .expect("frozen authority markers");
        let mut wrong_authority = metadata.clone();
        wrong_authority["integrityContract"]["typeAuthority"] =
            Value::String("raw_sidecar_types".to_owned());
        assert!(validate_integrity_metadata_reference(&metadata_path, &wrong_authority).is_err());

        let sidecar_path =
            repo.join("benchmarks/core/wetune/schemas/core/discourse.base.schema.constraints.json");
        let sidecar = read_json(&sidecar_path).expect("read frozen sidecar");
        validate_wetune_sidecar_shape(&sidecar, "wetune-issues__4", &sidecar_path)
            .expect("frozen sidecar shape");

        let mut unknown_field = sidecar.clone();
        unknown_field["futureConstraintKind"] = Value::Array(Vec::new());
        assert!(
            validate_wetune_sidecar_shape(&unknown_field, "wetune-issues__4", &sidecar_path)
                .is_err()
        );

        let mut nulls_not_distinct = sidecar.clone();
        nulls_not_distinct["uniqueKeys"][0]["semantics"] =
            Value::String("nulls_not_distinct".to_owned());
        assert!(
            validate_wetune_sidecar_shape(&nulls_not_distinct, "wetune-issues__4", &sidecar_path)
                .is_err()
        );

        let mut inconsistent_nullable = sidecar.clone();
        inconsistent_nullable["uniqueKeys"][6]["nullableColumns"] = Value::Array(Vec::new());
        assert!(
            validate_wetune_sidecar_shape(
                &inconsistent_nullable,
                "wetune-issues__4",
                &sidecar_path
            )
            .is_err()
        );

        let mut unsupported_source = sidecar;
        unsupported_source["uniqueIndexes"][0]["source"] =
            Value::String("planner_index".to_owned());
        assert!(
            validate_wetune_sidecar_shape(&unsupported_source, "wetune-issues__4", &sidecar_path)
                .is_err()
        );
    }

    #[test]
    fn frozen_sqlsolver_metadata_contracts_all_parse_without_silent_forms() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("logos-ir is nested under repository root");
        let root = repo.join("benchmarks/core/.generated/sqlsolver");
        if !root.is_dir() {
            return;
        }
        let mut metadata = Vec::new();
        collect_metadata(&root, &mut metadata);
        metadata.sort();
        assert_eq!(metadata.len(), 389);
        let mut cases = BTreeSet::new();
        for path in metadata {
            let schema = path.parent().unwrap().join("schema.sql");
            let contract = load_adjacent_integrity_contract(&schema)
                .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
            let case_id = contract
                .case_id
                .expect("every frozen metadata row has a case id");
            assert!(cases.insert(case_id.clone()), "duplicate case id {case_id}");
        }
        assert!(cases.contains("verieql-calcite__calcite-148"));
        assert!(cases.contains("verieql-literature__conditional-fkPennTR-5"));
        assert!(cases.contains("wetune-issues__4"));
        assert!(cases.contains("wetune-issues__41"));
    }

    #[test]
    fn logos_native_pair_contract_is_policy_bound_and_fail_closed() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("logos-ir is nested under repository root");
        let metadata_path = repo.join(
            "benchmarks/core/.generated/logos/nonwetune-flat/rbot-tpch__query22/metadata.json",
        );
        if !metadata_path.is_file() {
            return;
        }
        let metadata = read_json(&metadata_path).expect("read Logos-native R-Bot metadata");
        let schema_path = metadata_path.parent().unwrap().join("schema.sql");
        validate_native_rbot_materialization_authority(&schema_path, &metadata_path, &metadata)
            .expect("frozen R-Bot authority binding");
        validate_integrity_metadata_reference(&metadata_path, &metadata)
            .expect("independent Logos integrity contract");

        let mut missing_policy = metadata.clone();
        missing_policy["materializationContract"]["policy"] = Value::Null;
        assert!(
            validate_integrity_metadata_reference(&metadata_path, &missing_policy).is_err(),
            "generic DDL field names must not be accepted without the independent Logos policy"
        );

        let mut mixed_frontends = metadata.clone();
        mixed_frontends["integrityContract"]["sqlsolverDdlComplete"] = Value::Bool(true);
        assert!(
            validate_integrity_metadata_reference(&metadata_path, &mixed_frontends).is_err(),
            "mixed Logos/SQLSolver integrity fields must fail the exact-shape check"
        );

        let mut stale_completeness = metadata;
        stale_completeness["integrityContract"]["ddlComplete"] = Value::Bool(false);
        assert!(
            validate_integrity_metadata_reference(&metadata_path, &stale_completeness).is_err()
        );
    }

    #[test]
    fn logos_native_rbot_authority_rejects_adjacent_and_metadata_mutations() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("logos-ir is nested under repository root");
        let canonical =
            repo.join("benchmarks/core/.generated/logos/nonwetune-flat/rbot-tpch__query22");
        if !canonical.is_dir() {
            return;
        }
        let scratch_root = repo.join("target");
        std::fs::create_dir_all(&scratch_root).expect("create target directory");
        let temporary = tempfile::Builder::new()
            .prefix("logos-rbot-integrity-")
            .tempdir_in(scratch_root)
            .expect("create R-Bot integrity scratch directory");

        let stage = |name: &str| {
            let directory = temporary.path().join(".generated/logos").join(name);
            std::fs::create_dir_all(&directory).expect("create staged case");
            for filename in ["schema.sql", "sql1.sql", "sql2.sql", "metadata.json"] {
                std::fs::copy(canonical.join(filename), directory.join(filename))
                    .expect("copy staged R-Bot input");
            }
            directory
        };

        let pristine = stage("pristine");
        load_adjacent_integrity_contract(&pristine.join("schema.sql"))
            .expect("pristine staged R-Bot authority");

        let stale_schema = stage("stale-schema");
        std::fs::write(
            stale_schema.join("schema.sql"),
            b"CREATE TABLE forged (value INTEGER);\n",
        )
        .expect("mutate schema");
        assert!(load_adjacent_integrity_contract(&stale_schema.join("schema.sql")).is_err());

        let co_mutated = stage("co-mutated-source");
        let source_path = co_mutated.join("sql1.sql");
        let mut source = std::fs::read(&source_path).expect("read staged source");
        source.extend_from_slice(b"\n-- forged\n");
        std::fs::write(&source_path, source).expect("mutate staged source");
        let forged_digest =
            regular_file_sha256(&source_path, "staged source").expect("hash staged source");
        let metadata_path = co_mutated.join("metadata.json");
        let mut metadata = read_json(&metadata_path).expect("read staged metadata");
        metadata["materializationContract"]["inputs"]["source"]["inputSha256"] =
            Value::String(forged_digest.clone());
        metadata["materializationContract"]["inputs"]["source"]["outputSha256"] =
            Value::String(forged_digest.clone());
        metadata["calciteAuthorityInputs"]["source"]["sha256"] = Value::String(forged_digest);
        std::fs::write(
            &metadata_path,
            serde_json::to_vec(&metadata).expect("serialize forged metadata"),
        )
        .expect("write forged metadata");
        assert!(load_adjacent_integrity_contract(&co_mutated.join("schema.sql")).is_err());

        let borrowed = stage("borrowed-source-identity");
        let borrowed_metadata_path = borrowed.join("metadata.json");
        let mut borrowed_metadata =
            read_json(&borrowed_metadata_path).expect("read borrowed fixture metadata");
        let other = read_json(&repo.join(
            "benchmarks/core/.generated/logos/nonwetune-flat/rbot-tpch__query21/metadata.json",
        ))
        .expect("read other R-Bot metadata");
        borrowed_metadata["source"] = other["source"].clone();
        std::fs::write(
            &borrowed_metadata_path,
            serde_json::to_vec(&borrowed_metadata).expect("serialize borrowed metadata"),
        )
        .expect("write borrowed metadata");
        assert!(load_adjacent_integrity_contract(&borrowed.join("schema.sql")).is_err());

        let fabricated = stage("fabricated-repair");
        let fabricated_metadata_path = fabricated.join("metadata.json");
        let mut fabricated_metadata =
            read_json(&fabricated_metadata_path).expect("read fabricated fixture metadata");
        fabricated_metadata["materializationContract"]["semanticPreservation"]["repairs"] =
            serde_json::json!(["unchecked"]);
        std::fs::write(
            &fabricated_metadata_path,
            serde_json::to_vec(&fabricated_metadata).expect("serialize fabricated metadata"),
        )
        .expect("write fabricated metadata");
        assert!(load_adjacent_integrity_contract(&fabricated.join("schema.sql")).is_err());

        let missing_authority = stage("missing-calcite-authority");
        let missing_metadata_path = missing_authority.join("metadata.json");
        let mut missing_metadata =
            read_json(&missing_metadata_path).expect("read missing-authority metadata");
        missing_metadata["calciteAuthorityInputs"] = Value::Null;
        std::fs::write(
            &missing_metadata_path,
            serde_json::to_vec(&missing_metadata).expect("serialize missing authority"),
        )
        .expect("write missing authority");
        assert!(load_adjacent_integrity_contract(&missing_authority.join("schema.sql")).is_err());

        for (label, replacement) in [
            ("missing-source-benchmark", None),
            ("null-source-benchmark", Some(Value::Null)),
            ("empty-source-benchmark", Some(Value::String(String::new()))),
            (
                "typed-source-benchmark",
                Some(Value::Number(serde_json::Number::from(1))),
            ),
        ] {
            let directory = stage(label);
            let metadata_path = directory.join("metadata.json");
            let mut metadata = read_json(&metadata_path).expect("read identity mutation");
            match replacement {
                Some(value) => metadata["sourceBenchmark"] = value,
                None => {
                    metadata
                        .as_object_mut()
                        .expect("metadata object")
                        .remove("sourceBenchmark");
                }
            }
            std::fs::write(
                &metadata_path,
                serde_json::to_vec(&metadata).expect("serialize identity mutation"),
            )
            .expect("write identity mutation");
            assert!(
                load_adjacent_integrity_contract(&directory.join("schema.sql")).is_err(),
                "native R-Bot authority admitted {label}"
            );
        }

        let co_deleted_identity = stage("co-deleted-rbot-identity");
        let co_deleted_metadata_path = co_deleted_identity.join("metadata.json");
        let mut co_deleted_metadata =
            read_json(&co_deleted_metadata_path).expect("read co-deleted identity");
        let object = co_deleted_metadata
            .as_object_mut()
            .expect("metadata object");
        object.remove("sourceBenchmark");
        object.remove("flatCaseId");
        std::fs::write(
            &co_deleted_metadata_path,
            serde_json::to_vec(&co_deleted_metadata).expect("serialize co-deleted identity"),
        )
        .expect("write co-deleted identity");
        assert!(load_adjacent_integrity_contract(&co_deleted_identity.join("schema.sql")).is_err());

        let missing_metadata = stage("rbot-tpch__query22");
        std::fs::remove_file(missing_metadata.join("metadata.json"))
            .expect("remove staged metadata");
        assert!(load_adjacent_integrity_contract(&missing_metadata.join("schema.sql")).is_err());

        let empty_metadata = stage("rbot-tpch__query22-empty-metadata");
        std::fs::write(empty_metadata.join("metadata.json"), b"{}\n")
            .expect("write empty staged metadata");
        assert!(load_adjacent_integrity_contract(&empty_metadata.join("schema.sql")).is_err());

        let renamed_missing_metadata = stage("renamed-missing-metadata");
        std::fs::remove_file(renamed_missing_metadata.join("metadata.json"))
            .expect("remove renamed staged metadata");
        load_adjacent_integrity_contract(&renamed_missing_metadata.join("schema.sql"))
            .expect("a renamed schema without R-Bot identity is an ordinary standalone input");

        let renamed_empty_metadata = stage("renamed-empty-metadata");
        std::fs::write(renamed_empty_metadata.join("metadata.json"), b"{}\n")
            .expect("write renamed empty metadata");
        load_adjacent_integrity_contract(&renamed_empty_metadata.join("schema.sql"))
            .expect("empty metadata without R-Bot identity is an ordinary standalone input");

        let downgraded = stage("downgraded-native-metadata");
        let downgraded_metadata_path = downgraded.join("metadata.json");
        let mut downgraded_metadata =
            read_json(&downgraded_metadata_path).expect("read downgrade fixture metadata");
        downgraded_metadata["profile"] = Value::String("sqlsolver".to_owned());
        downgraded_metadata
            .as_object_mut()
            .expect("metadata object")
            .remove("materializationContract");
        downgraded_metadata
            .as_object_mut()
            .expect("metadata object")
            .remove("calciteAuthorityInputs");
        downgraded_metadata["integrityContract"] = serde_json::json!({
            "authoritativeForLogos": true,
            "silentDrops": 0,
            "sources": [{"kind": "parser_facing_ddl", "path": "schema.sql"}],
            "sqlsolverDdlComplete": true,
            "sqlsolverDdlLimitation": null,
        });
        std::fs::write(
            &downgraded_metadata_path,
            serde_json::to_vec(&downgraded_metadata).expect("serialize downgraded metadata"),
        )
        .expect("write downgraded metadata");
        assert!(load_adjacent_integrity_contract(&downgraded.join("schema.sql")).is_err());
    }

    #[test]
    fn frozen_logos_metadata_contracts_all_parse_without_frontend_field_mixing() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("logos-ir is nested under repository root");
        let root = repo.join("benchmarks/core/.generated/logos");
        if !root.is_dir() {
            return;
        }
        let mut metadata = Vec::new();
        collect_metadata(&root, &mut metadata);
        metadata.sort();
        assert_eq!(metadata.len(), 389);
        let mut cases = BTreeSet::new();
        for path in metadata {
            let schema = path.parent().unwrap().join("schema.sql");
            let contract = load_adjacent_integrity_contract(&schema)
                .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
            let case_id = contract
                .case_id
                .expect("every frozen Logos metadata row has a case id");
            assert!(cases.insert(case_id.clone()), "duplicate case id {case_id}");
        }
        assert!(cases.contains("rbot-dsb__query075"));
        assert!(cases.contains("rbot-tpch__query22"));
        assert!(cases.contains("wetune-issues__4"));
    }
}
