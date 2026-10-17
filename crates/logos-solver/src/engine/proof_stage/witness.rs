//! Typed witness encoding and Rocq certificate generation.

use crate::artifacts::ArtifactWriter;
use crate::core::{FormalAttribute, FormalAttributeType, FormalSchema};
use crate::error::{Error, Result};
use crate::validation::{FormalWitnessSnapshot, FormalWitnessValue};
use logos_ir::ir::SqlStringType;

use super::WITNESS_MODULE_DIRECTORY;

fn unavailable_formal_sql_witness_module() -> String {
    "From SQLFS Require Import SqlSyntax GenericInstance SchemaConstraints.\n\
From LogosGenerated Require Import Schema.\n\
\n\
(** No PostgreSQL candidate was losslessly frozen for this proof run.  Keeping\n\
    a fixed, unavailable witness makes the countermodel branch fail closed; an\n\
    agent may still prove the independent equivalence branch. *)\n\
Definition generated_witness_available : bool := false.\n\
Definition generated_witness_db : db_state := Schema.generated_schema.\n\
\n\
Lemma generated_witness_schema_conforms :\n\
  generated_witness_available = true ->\n\
  Schema.generated_schema_conforms generated_witness_db.\n\
Proof. discriminate. Qed.\n"
        .to_owned()
}

fn rocq_byte_string(value: &str) -> String {
    value
        .as_bytes()
        .iter()
        .rev()
        .fold("EmptyString".to_owned(), |rest, byte| {
            format!("String (Ascii.ascii_of_nat {}) ({rest})", byte)
        })
}

fn rocq_identifier_string(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

pub(super) fn rocq_witness_string_typmod(typmod: SqlStringType) -> String {
    match typmod {
        SqlStringType::Text => "StringText".to_owned(),
        SqlStringType::Varchar { length: None } => "StringVarchar".to_owned(),
        SqlStringType::Varchar {
            length: Some(length),
        } => format!("StringVarcharN {length}"),
        SqlStringType::Char { length } => format!("StringChar {length}"),
        SqlStringType::Bpchar => "StringBpchar".to_owned(),
    }
}

fn rocq_witness_attribute(attribute: &FormalAttribute) -> String {
    let name = rocq_identifier_string(&attribute.name);
    match attribute.ty {
        FormalAttributeType::Z => format!("Attr_Z ({name})"),
        FormalAttributeType::Int32 => format!("Attr_int32 ({name})"),
        FormalAttributeType::Int64 => format!("Attr_int64 ({name})"),
        FormalAttributeType::String { typmod } => format!(
            "Attr_string ({name}) ({})",
            rocq_witness_string_typmod(typmod)
        ),
        FormalAttributeType::Bool => format!("Attr_bool ({name})"),
        FormalAttributeType::Float => format!("Attr_float ({name})"),
        FormalAttributeType::Double => format!("Attr_double ({name})"),
        FormalAttributeType::Numeric => format!("Attr_numeric ({name})"),
        FormalAttributeType::Decimal { precision, scale } => {
            format!("Attr_decimal ({name}) {precision} {scale}")
        }
        FormalAttributeType::Date => format!("Attr_date ({name})"),
        FormalAttributeType::Time => format!("Attr_time ({name})"),
        FormalAttributeType::Timestamp { precision } => {
            format!("Attr_timestamp ({name}) {}", precision.unwrap_or(6))
        }
        FormalAttributeType::Timestamptz { precision } => {
            format!("Attr_timestamptz ({name}) {}", precision.unwrap_or(6))
        }
    }
}

fn rocq_witness_null(ty: FormalAttributeType) -> String {
    match ty {
        FormalAttributeType::Z => "Value_Z None".to_owned(),
        FormalAttributeType::Int32 => "Value_int32 None".to_owned(),
        FormalAttributeType::Int64 => "Value_int64 None".to_owned(),
        FormalAttributeType::String { typmod } => format!(
            "Value_string (StringValue ({}) None)",
            rocq_witness_string_typmod(typmod)
        ),
        FormalAttributeType::Bool => "Value_bool None".to_owned(),
        FormalAttributeType::Float => "Value_float None".to_owned(),
        FormalAttributeType::Double => "Value_double None".to_owned(),
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. } => {
            "Value_numeric None".to_owned()
        }
        FormalAttributeType::Date => "Value_date None".to_owned(),
        FormalAttributeType::Time => "Value_time None".to_owned(),
        FormalAttributeType::Timestamp { .. } => "Value_timestamp None".to_owned(),
        FormalAttributeType::Timestamptz { .. } => "Value_timestamptz None".to_owned(),
    }
}

pub(super) fn rocq_witness_value(
    value: &FormalWitnessValue,
    ty: FormalAttributeType,
) -> Result<String> {
    match (value, ty) {
        (FormalWitnessValue::Null, ty) => Ok(rocq_witness_null(ty)),
        (FormalWitnessValue::Bool(value), FormalAttributeType::Bool) => {
            Ok(format!("Value_bool (Some {value})"))
        }
        (FormalWitnessValue::Int32(value), FormalAttributeType::Int32) => {
            // Do not emit [int32_checked] here.  Its executable branch is
            // driven by an opaque range proof, so closed reflection gets
            // stuck while merely deciding whether the payload is [Some].
            // Rust's [i32] already establishes the range; Rocq independently
            // checks the explicit constructor proof below.
            Ok(format!(
                "Value_int32 (Some (Int32 ({value})%Z ltac:(unfold int32_min, int32_max; lia)))"
            ))
        }
        (FormalWitnessValue::Int64(value), FormalAttributeType::Int64) => Ok(format!(
            "Value_int64 (Some (Int64 ({value})%Z ltac:(unfold int64_min, int64_max; lia)))"
        )),
        (FormalWitnessValue::String(value), FormalAttributeType::String { typmod }) => Ok(format!(
            "Value_string (StringValue ({}) (Some ({})))",
            rocq_witness_string_typmod(typmod),
            rocq_byte_string(value)
        )),
        (FormalWitnessValue::Float32Bits(bits), FormalAttributeType::Float) => {
            Ok(format!("Value_float (Some (Float32OfBits ({bits})%Z))"))
        }
        (FormalWitnessValue::Float64Bits(bits), FormalAttributeType::Double) => {
            Ok(format!("Value_double (Some (Float64OfBits ({bits})%Z))"))
        }
        (
            FormalWitnessValue::NumericFinite { coefficient, scale },
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok(format!(
            "Value_numeric (Some (numeric_of_scaled ({coefficient})%Z ({scale})%Z))"
        )),
        (
            FormalWitnessValue::NumericNegInfinity,
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok("Value_numeric (Some NumericNegInfinity)".to_owned()),
        (
            FormalWitnessValue::NumericPosInfinity,
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok("Value_numeric (Some NumericPosInfinity)".to_owned()),
        (
            FormalWitnessValue::NumericNaN,
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok("Value_numeric (Some NumericNaN)".to_owned()),
        (FormalWitnessValue::Date(value), FormalAttributeType::Date) => {
            Ok(format!("Value_date (Some ({value})%Z)"))
        }
        (FormalWitnessValue::Time(value), FormalAttributeType::Time) => {
            Ok(format!("Value_time (Some ({value})%Z)"))
        }
        (FormalWitnessValue::Timestamp(value), FormalAttributeType::Timestamp { .. }) => {
            Ok(format!("Value_timestamp (Some ({value})%Z)"))
        }
        (FormalWitnessValue::Timestamptz(value), FormalAttributeType::Timestamptz { .. }) => {
            Ok(format!("Value_timestamptz (Some ({value})%Z)"))
        }
        (value, ty) => Err(Error::ProofAgentCommand(format!(
            "typed witness cell {value:?} does not match FormalSQL column type {ty:?}"
        ))),
    }
}

fn rocq_list(items: &[String]) -> String {
    if items.is_empty() {
        "[]".to_owned()
    } else {
        format!("[{}]", items.join("; "))
    }
}

fn rocq_forall_certificate_chain(lemmas: &[String]) -> String {
    let mut proof = String::new();
    for lemma in lemmas {
        proof.push_str(&format!("  constructor; [exact {lemma}|].\n"));
    }
    proof.push_str("  constructor.");
    proof
}

pub(super) struct WitnessModules {
    pub(super) witness: String,
    pub(super) data: Option<String>,
    pub(super) constraint_modules: Vec<(String, String)>,
}

pub(super) fn formal_sql_witness_modules(
    schema: &FormalSchema,
    snapshot: Option<&FormalWitnessSnapshot>,
) -> Result<WitnessModules> {
    let Some(snapshot) = snapshot else {
        return Ok(WitnessModules {
            witness: unavailable_formal_sql_witness_module(),
            data: Some(
                "From LogosGenerated Require Import Schema.\n\
                 Definition generated_witness_data_unavailable_marker : Prop := True.\n"
                    .to_owned(),
            ),
            constraint_modules: Vec::new(),
        });
    };
    if snapshot.schema_version != 1 || snapshot.tables.len() != schema.tables.len() {
        return Err(Error::ProofAgentCommand(format!(
            "typed witness snapshot schema mismatch: version {}, {} tables; expected version 1 and {} tables",
            snapshot.schema_version,
            snapshot.tables.len(),
            schema.tables.len()
        )));
    }

    let mut row_definitions = Vec::with_capacity(schema.tables.len());
    let mut table_values = Vec::with_capacity(schema.tables.len());
    let mut table_relations = Vec::with_capacity(schema.tables.len());
    let mut cardinality_lemmas = Vec::with_capacity(schema.tables.len());
    for (index, (table, snapshot_table)) in schema.tables.iter().zip(&snapshot.tables).enumerate() {
        let snapshot_attributes = snapshot_table
            .columns
            .iter()
            .map(|column| FormalAttribute {
                name: column.name.clone(),
                ty: column.ty,
            })
            .collect::<Vec<_>>();
        if snapshot_table.relation != table.relation || snapshot_attributes != table.attributes {
            return Err(Error::ProofAgentCommand(format!(
                "typed witness table {index} does not exactly match the lowered FormalSQL schema"
            )));
        }
        let attributes = table
            .attributes
            .iter()
            .map(rocq_witness_attribute)
            .collect::<Vec<_>>();
        let attribute_list = rocq_list(&attributes);
        let attribute_name = format!("generated_witness_table_{index}_attributes");
        let mut rows = Vec::with_capacity(snapshot_table.rows.len());
        for (row_index, row) in snapshot_table.rows.iter().enumerate() {
            if row.cells.len() != table.attributes.len() {
                return Err(Error::ProofAgentCommand(format!(
                    "typed witness row {row_index} of table {:?} has {} cells, expected {}",
                    table.relation,
                    row.cells.len(),
                    table.attributes.len()
                )));
            }
            let values = row
                .cells
                .iter()
                .zip(&table.attributes)
                .map(|(value, attribute)| rocq_witness_value(value, attribute.ty))
                .collect::<Result<Vec<_>>>()?;
            rows.push(format!(
                "mk_tuple_lists {attribute_name} ({})",
                rocq_list(&values)
            ));
        }
        if rows.is_empty() {
            continue;
        }
        let row_name = format!("generated_witness_table_{index}_rows");
        row_definitions.push(format!(
            "Definition {attribute_name} : list (attribute TNull) :=\n  {attribute_list}."
        ));
        row_definitions.push(format!(
            "Definition {row_name} : list (tuple TNull) :=\n  {}.",
            rocq_list(&rows)
        ));
        let relation = rocq_identifier_string(&table.relation);
        cardinality_lemmas.push(format!(
            "Lemma generated_witness_table_{index}_instance_cardinal :\n\
  Febag.cardinal (Fecol.CBag (CTuple TNull))\n\
    (@_instance TNull generated_witness_db (Rel ({relation}))) =\n\
  ({}%N).\n\
Proof.\n\
  rewrite generated_witness_instance_cardinal.\n\
  reflexivity.\n\
Qed.",
            snapshot_table.rows.len()
        ));
        table_values.push(format!("WitnessTable (Rel ({})) {row_name}", relation));
        table_relations.push(format!("Rel ({relation})"));
    }
    // [create_table] prepends each relation to [_relnames].  The witness
    // inventory follows that exact generated-schema order, while the snapshot
    // JSON remains in declaration order for a direct schema binding audit.
    table_values.reverse();
    table_relations.reverse();

    let mut table_constraint_certificates = Vec::new();
    let mut constraint_modules = Vec::new();
    let mut table_constraint_lemma_names = Vec::with_capacity(schema.tables.len());
    for (index, (table, snapshot_table)) in schema.tables.iter().zip(&snapshot.tables).enumerate() {
        if snapshot_table.rows.is_empty() {
            let relation = rocq_identifier_string(&table.relation);
            table_constraint_certificates.push(format!(
                "Lemma generated_witness_table_constraint_{index}_conforms :\n\
  table_constraint_conforms generated_witness_db\n\
    Schema.generated_table_constraint_{index}.\n\
Proof.\n\
  apply (table_constraint_conforms_empty\n\
    generated_witness_db Schema.generated_schema_constraints).\n\
  - exact Schema.generated_table_constraint_{index}_declarations_well_formed.\n\
  - change (instance_rows\n\
      (witness_database Schema.generated_schema WitnessData.generated_witness_tables)\n\
      (constraint_relation Schema.generated_table_constraint_{index}) = nil).\n\
    rewrite witness_database_instance_rows.\n\
    change (witness_instance_rows WitnessData.generated_witness_tables\n\
      (Rel ({relation})) = nil).\n\
    apply witness_instance_rows_absent.\n\
    rewrite WitnessData.generated_witness_table_relations.\n\
    vm_compute.\n\
    intuition discriminate.\n\
Qed."
            ));
            table_constraint_lemma_names.push(format!(
                "generated_witness_table_constraint_{index}_conforms"
            ));
        } else {
            let relation = rocq_identifier_string(&table.relation);
            let rows = format!(
                "witness_instance_rows WitnessData.generated_witness_tables (Rel ({relation}))"
            );
            let header = "From SQLFS Require Import SqlSyntax GenericInstance Values FTuples SchemaConstraints.\nFrom Logos Require Import FormalSQL.WitnessFacts.\nFrom LogosGenerated Require Import Schema.\nFrom LogosGenerated Require WitnessData.\nFrom Stdlib Require Import List String SetoidList.\nImport ListNotations.\nOpen Scope string_scope.\n\n";
            let mut component_imports = Vec::new();
            let mut add_component = |module: String,
                                     theorem: String,
                                     statement: String,
                                     proof: String| {
                constraint_modules.push((
                    module.clone(),
                    format!("{header}Lemma {theorem} :\n  {statement}.\nProof.\n{proof}\nQed.\n"),
                ));
                component_imports.push(module.clone());
                format!("{module}.{theorem}")
            };
            let not_null = add_component(
                format!("Table{index:04}NotNull"),
                format!("generated_witness_table_{index}_not_null"),
                format!(
                    "rows_attributes_not_null (constraint_not_null Schema.generated_table_constraint_{index}) ({rows})"
                ),
                "  apply rows_attributes_not_nullb_sound.\n  vm_compute.\n  reflexivity."
                    .to_owned(),
            );
            let primary = table.constraints.primary_key.as_ref().map(|_| add_component(
                format!("Table{index:04}Primary"),
                format!("generated_witness_table_{index}_primary"),
                format!("forall key, constraint_primary_key Schema.generated_table_constraint_{index} = Some key -> primary_key_conforms key ({rows})"),
                "  intros key Hkey.\n  vm_compute in Hkey.\n  inversion Hkey; subst; clear Hkey.\n  apply primary_key_conformsb_sound.\n  vm_compute.\n  reflexivity.".to_owned(),
            ));
            let mut make_group = |kind: &str,
                                  count: usize,
                                  list: &str,
                                  conclusion: &str,
                                  sound: &str| {
                (0..count).map(|position| {
                    let module = format!("Table{index:04}{kind}{position:04}");
                    let theorem = format!("generated_witness_table_{index}_{}_{}", kind.to_ascii_lowercase(), position);
                    add_component(
                        module,
                        theorem,
                        format!("forall item, nth_error ({list}) {position} = Some item -> {conclusion}"),
                        format!("  intros item Hitem.\n  vm_compute in Hitem.\n  inversion Hitem; subst; clear Hitem.\n  {sound}\n  vm_compute.\n  reflexivity."),
                    )
                }).collect::<Vec<_>>()
            };
            let unique = make_group(
                "Unique",
                table.constraints.unique.len(),
                &format!("constraint_unique_keys Schema.generated_table_constraint_{index}"),
                &format!("unique_key_conforms item ({rows})"),
                "apply unique_key_conformsb_sound.",
            );
            let foreign = make_group(
                "Foreign",
                table.constraints.foreign_keys.len(),
                &format!("constraint_foreign_keys Schema.generated_table_constraint_{index}"),
                &format!("foreign_key_conforms WitnessData.generated_witness_db ({rows}) item"),
                "apply (foreign_key_conformsb_sound Schema.generated_schema WitnessData.generated_witness_tables).",
            );
            let checks = make_group(
                "Check",
                table.constraints.checks.len(),
                &format!("constraint_checks Schema.generated_table_constraint_{index}"),
                &format!(
                    "check_constraint_conforms WitnessData.generated_witness_db ({rows}) item"
                ),
                "apply check_constraint_conformsb_sound.",
            );
            drop(make_group);
            drop(add_component);
            let index_list =
                format!("constraint_unique_indexes Schema.generated_table_constraint_{index}");
            let mut indexes = Vec::new();
            for position in 0..table.constraints.unique_indexes.len() {
                let premise = format!("nth_error ({index_list}) {position} = Some item");
                let mut parts = Vec::new();
                for (suffix, conclusion, finish) in [
                    (
                        "Nonempty",
                        "list_nonemptyb (unique_index_terms item) = true".to_owned(),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                    (
                        "Predicate",
                        format!(
                            "forallb (fun row => unique_index_predicate_succeedsb WitnessData.generated_witness_db row item) ({rows}) = true"
                        ),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                    (
                        "Terms",
                        format!(
                            "forallb (fun row => if unique_index_row_participates WitnessData.generated_witness_db item row then unique_index_row_terms_succeedb item row else true) ({rows}) = true"
                        ),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                    (
                        "Unique",
                        format!(
                            "no_relatedb sql_key_equal_trueb (map (unique_index_key (unique_index_terms item)) (filter (unique_index_row_participates WitnessData.generated_witness_db item) ({rows}))) = true"
                        ),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                ] {
                    let module = format!("Table{index:04}Index{position:04}{suffix}");
                    let theorem = format!(
                        "generated_witness_table_{index}_index_{position}_{}",
                        suffix.to_ascii_lowercase()
                    );
                    constraint_modules.push((module.clone(), format!(
                        "{header}Lemma {theorem} :\n  forall item, {premise} -> {conclusion}.\nProof.\n  intros item Hitem.\n  vm_compute in Hitem.\n  inversion Hitem; subst; clear Hitem.\n{finish}\nQed.\n"
                    )));
                    component_imports.push(module.clone());
                    parts.push(format!("{module}.{theorem}"));
                }
                let module = format!("Table{index:04}Index{position:04}");
                let theorem = format!("generated_witness_table_{index}_index_{position}");
                let imports = component_imports.join(" ");
                constraint_modules.push((module.clone(), format!(
                    "{header}From LogosGenerated.WitnessModules Require {imports}.\nLemma {theorem} :\n  forall item, {premise} -> unique_index_conforms WitnessData.generated_witness_db ({rows}) item.\nProof.\n  intros item Hitem.\n  apply unique_index_conforms_of_reflected_components.\n  - apply {}; exact Hitem.\n  - apply {}; exact Hitem.\n  - apply {}; exact Hitem.\n  - apply {}; exact Hitem.\nQed.\n",
                    parts[0], parts[1], parts[2], parts[3],
                )));
                component_imports.push(module.clone());
                indexes.push(format!("{module}.{theorem}"));
            }
            let forall_proof = |references: &[String]| {
                let mut result = String::new();
                for reference in references {
                    result.push_str(&format!(
                        "    constructor; [apply {reference}; reflexivity|].\n"
                    ));
                }
                result.push_str("    constructor.");
                result
            };
            let module = format!("TableConstraint{index:04}");
            let theorem = format!("generated_witness_table_constraint_{index}_conforms");
            let imports = component_imports.join(" ");
            constraint_modules.push((module.clone(), format!(
                "From SQLFS Require Import SqlSyntax GenericInstance SchemaConstraints.\nFrom Logos Require Import FormalSQL.WitnessFacts.\nFrom LogosGenerated Require Import Schema.\nFrom LogosGenerated Require WitnessData.\nFrom LogosGenerated.WitnessModules Require {imports}.\nFrom Stdlib Require Import List String.\nImport ListNotations.\nOpen Scope string_scope.\n\nLemma {theorem} :\n  table_constraint_conforms WitnessData.generated_witness_db Schema.generated_table_constraint_{index}.\nProof.\n  change (table_constraint_conforms (witness_database Schema.generated_schema WitnessData.generated_witness_tables) Schema.generated_table_constraint_{index}).\n  apply table_constraint_conforms_of_components with (rows := {rows}).\n  - apply witness_database_instance_rows.\n  - exact {not_null}.\n  - rewrite Schema.generated_table_constraint_{index}_primary_key.\n    {}\n  - rewrite Schema.generated_table_constraint_{index}_unique_keys.\n{}\n  - rewrite Schema.generated_table_constraint_{index}_foreign_keys.\n{}\n  - rewrite Schema.generated_table_constraint_{index}_checks.\n{}\n  - rewrite Schema.generated_table_constraint_{index}_unique_indexes.\n{}\nQed.\n",
                primary.as_ref().map_or("exact I.".to_owned(), |reference| format!("apply {reference}; reflexivity.")),
                forall_proof(&unique), forall_proof(&foreign), forall_proof(&checks), forall_proof(&indexes),
            )));
            table_constraint_lemma_names.push(format!("{module}.{theorem}"));
        }
    }
    let table_constraints_aggregate = format!(
        "Lemma generated_witness_table_constraints_conform :\n\
  Forall (table_constraint_conforms generated_witness_db)\n\
    Schema.generated_schema_constraints.\n\
Proof.\n\
  unfold Schema.generated_schema_constraints.\n{}\n\
Qed.",
        rocq_forall_certificate_chain(&table_constraint_lemma_names)
    );

    let data = format!(
        "From SQLFS Require Import SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection SchemaConstraints.\n\
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.WitnessFacts.\n\
From LogosGenerated Require Import Schema.\n\
From Stdlib Require Import List String Ascii ZArith NArith Lia.\n\
Import ListNotations Tuple.\n\
Open Scope string_scope.\n\
Open Scope Z_scope.\n\
\n\
{}\n\
\n\
Definition generated_witness_tables : list witness_table :=\n  {}.\n\
\n\
Definition generated_witness_relations : list relname :=\n  {}.\n\
\n\
Lemma generated_witness_table_relations :\n\
  map witness_table_relation generated_witness_tables =\n\
  generated_witness_relations.\n\
Proof. reflexivity. Qed.\n\
\n\
Definition generated_witness_available : bool := true.\n\
Definition generated_witness_db : db_state :=\n\
  witness_database Schema.generated_schema generated_witness_tables.\n\
\n\
Lemma generated_witness_instance_cardinal :\n\
  forall relation,\n\
    Febag.cardinal (Fecol.CBag (CTuple TNull))\n\
      (@_instance TNull generated_witness_db relation) =\n\
    N.of_nat (List.length (witness_rows_for generated_witness_tables relation)).\n\
Proof.\n\
  intro relation.\n\
  unfold generated_witness_db.\n\
  apply witness_database_instance_cardinal.\n\
Qed.\n\
\n\
{}\n\
\n\
Lemma generated_witness_values_reflection :\n\
  witness_values_conformb\n\
    Schema.generated_schema generated_witness_tables = true.\n\
Proof.\n\
  vm_compute.\n\
  reflexivity.\n\
Qed.\n\
\n\
",
        row_definitions.join("\n\n"),
        rocq_list(&table_values),
        rocq_list(&table_relations),
        cardinality_lemmas.join("\n\n"),
    );
    let constraint_imports = constraint_modules
        .iter()
        .map(|(module, _)| module.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let witness = format!(
        "From SQLFS Require Import SqlSyntax GenericInstance SchemaConstraints.\n\
From Logos Require Import FormalSQL.WitnessFacts.\n\
From LogosGenerated Require Import Schema.\n\
From LogosGenerated Require WitnessData.\n\
{}\n\
From Stdlib Require Import List String.\n\
Import ListNotations.\n\
Open Scope string_scope.\n\
\n\
Definition generated_witness_available : bool :=\n\
  WitnessData.generated_witness_available.\n\
Definition generated_witness_db : db_state :=\n\
  WitnessData.generated_witness_db.\n\
\n\
{}\n\
\n\
{}\n\
\n\
Lemma generated_witness_schema_conforms :\n\
  generated_witness_available = true ->\n\
  Schema.generated_schema_conforms generated_witness_db.\n\
Proof.\n\
  intros _.\n\
  unfold Schema.generated_schema_conforms, generated_witness_db.\n\
  apply witness_database_conforms_of_certificates.\n\
  - exact WitnessData.generated_witness_values_reflection.\n\
  - exact Schema.generated_schema_constraints_well_formed.\n\
  - exact generated_witness_table_constraints_conform.\n\
Qed.\n",
        if constraint_imports.is_empty() {
            String::new()
        } else {
            format!("From LogosGenerated.WitnessModules Require {constraint_imports}.")
        },
        table_constraint_certificates.join("\n\n"),
        table_constraints_aggregate,
    );
    Ok(WitnessModules {
        witness,
        data: Some(data),
        constraint_modules,
    })
}

pub(super) fn write_formal_sql_witness_modules(
    artifacts: &ArtifactWriter,
    modules: &WitnessModules,
) -> Result<()> {
    artifacts.write_text("proof-stage/formal-sql/Witness.v", &modules.witness)?;
    if let Some(data) = modules.data.as_ref() {
        artifacts.write_text("proof-stage/formal-sql/WitnessData.v", data)?;
    }
    let mut order = String::new();
    for (module, source) in &modules.constraint_modules {
        let file = format!("{module}.v");
        artifacts.write_text(
            &format!("proof-stage/formal-sql/{WITNESS_MODULE_DIRECTORY}/{file}"),
            source,
        )?;
        order.push_str(&file);
        order.push('\n');
    }
    artifacts.write_text(
        &format!("proof-stage/formal-sql/{WITNESS_MODULE_DIRECTORY}/ORDER"),
        &order,
    )
}

/// Write the minimal trusted-check workspace used only by the deterministic
/// typed-witness coverage gate. Query lowering is intentionally absent here:
/// support for a query operator must not decide whether the lowered schema and
/// its Witness.v inventory can be emitted and kernel-checked.
pub(in crate::engine) fn write_typed_witness_audit_workspace(
    artifacts: &ArtifactWriter,
    schema: &FormalSchema,
    snapshot: &FormalWitnessSnapshot,
) -> Result<()> {
    let witness_modules = formal_sql_witness_modules(schema, Some(snapshot))?;
    artifacts.write_text("proof-stage/formal-sql/Schema.v", &schema.rocq_module)?;
    artifacts.write_text(
        "proof-stage/formal-sql/Queries.v",
        "From LogosGenerated Require Import Schema.\n\
         Definition typed_witness_audit_queries_marker : Prop := True.\n",
    )?;
    write_formal_sql_witness_modules(artifacts, &witness_modules)?;
    artifacts.write_text(
        "proof-stage/formal-sql/Problem.v",
        "From LogosGenerated Require Import Schema Queries Witness.\n\
         Lemma typed_witness_audit_available :\n\
           Witness.generated_witness_available = true.\n\
         Proof. reflexivity. Qed.\n\
         Lemma typed_witness_audit_schema_conforms :\n\
           Schema.generated_schema_conforms Witness.generated_witness_db.\n\
         Proof.\n\
           apply Witness.generated_witness_schema_conforms.\n\
           exact typed_witness_audit_available.\n\
         Qed.\n",
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/Goal.v",
        "From LogosGenerated Require Import Problem.\n\
         Definition typed_witness_audit_goal : Prop := True.\n",
    )?;
    Ok(())
}
