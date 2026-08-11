use std::collections::{HashMap, HashSet};

use super::*;
use crate::core::VerificationMode;
use crate::core::syntax::{
    FormalQueryBinding, FormalQueryDefinitionGraph, FormalQueryShapeDefinition,
    FormalQueryShapeKind, FormalQueryStatementSymbols, FormalScalarExpr, FormalScalarQuantifier,
    FormalScalarResultKind, FormalScalarSelectItem, formal_query_expr_contains_analysis_error,
    query_expr_output_signature, scalar_expr_contains_subquery,
};

const SCALAR_SELECT_CERTIFICATE_CHUNK_SIZE: usize = 32;
const SCALAR_SELECT_CERTIFICATE_CHUNK_THRESHOLD: usize = 64;

// This registry is the Rust authority for every module imported directly by a
// generated proof. The ranks preserve the independently observable per-root
// import, object-check, and Makefile compilation orderings. Consumers define a
// small callback macro so this one declaration can drive both lowering and
// proof-stage policy without adding another module boundary.
#[doc(hidden)]
#[macro_export]
macro_rules! logos_trusted_rocq_import_registry {
    ($consumer:ident) => {
        $consumer! {
            roots: [
                (Sqlfs, "SQLFS"),
                (Logos, "Logos"),
                (LogosGenerated, "LogosGenerated"),
                (Stdlib, "Stdlib"),
            ],
            imports: [
                (Sqlfs, "SqlSyntax", Some(0), None, None),
                (Sqlfs, "GenericInstance", Some(1), None, None),
                (Sqlfs, "Values", Some(2), None, None),
                (Sqlfs, "SqlOutcome", Some(3), None, None),
                (Sqlfs, "SqlErrorSemantics", Some(4), None, None),
                (Sqlfs, "SqlListFacts", Some(5), None, None),
                (Sqlfs, "SqlQuerySyntax", Some(6), None, None),
                (Sqlfs, "SqlQuerySemantics", Some(7), None, None),
                (Sqlfs, "SqlQueryWellFormed", Some(8), None, None),
                (Sqlfs, "SqlBagAbstraction", Some(9), None, None),
                (Sqlfs, "SqlQueryFacts", Some(10), None, None),
                (Sqlfs, "SqlQueryContexts", Some(11), None, None),
                (Sqlfs, "FiniteBag", Some(12), None, None),
                (Sqlfs, "FiniteSet", Some(13), None, None),
                (Sqlfs, "Bool3", Some(14), None, None),
                (Sqlfs, "SchemaConstraints", Some(15), None, None),
                (Logos, "FormalSQL.TNullSyntax", Some(0), Some(0), Some(0)),
                (Logos, "FormalSQL.VerificationConditions", Some(1), Some(1), Some(2)),
                (Logos, "FormalSQL.SchemaCardinality", Some(2), Some(2), Some(3)),
                (Logos, "FormalSQL.QueryCardinality", Some(3), Some(3), Some(4)),
                (Logos, "FormalSQL.QueryTNullSyntax", Some(4), Some(4), Some(5)),
                (Logos, "FormalSQL.NumericFacts", Some(5), Some(5), Some(1)),
                (Logos, "FormalSQL.BitwiseFacts", Some(6), Some(6), Some(6)),
                (Logos, "FormalSQL.CardinalityCombinators", Some(7), Some(7), Some(7)),
                (Logos, "FormalSQL.IntegrityFacts", Some(8), Some(8), Some(8)),
                (Logos, "FormalSQL.ScalarPredicateFacts", Some(9), Some(9), Some(9)),
                (Logos, "FormalSQL.StringTemporalFacts", Some(10), Some(10), Some(10)),
                (Logos, "FormalSQL.NumericDerivedFacts", Some(11), Some(11), Some(11)),
                (Logos, "FormalSQL.GroupingRewriteFacts", Some(12), Some(12), Some(12)),
                (Logos, "FormalSQL.AggregateRuntimeFacts", Some(13), Some(13), Some(13)),
                (Logos, "FormalSQL.RelationalAlgebraFacts", Some(14), Some(14), Some(14)),
                (Logos, "FormalSQL.OuterJoinFilterFacts", Some(15), Some(15), Some(15)),
                (Logos, "FormalSQL.GroupedFilterOutcomeFacts", Some(16), Some(16), Some(16)),
                (Logos, "FormalSQL.SemijoinCompositionFacts", Some(17), Some(17), Some(17)),
                (Logos, "FormalSQL.NumericRegroupFacts", Some(18), Some(18), Some(18)),
                (Logos, "FormalSQL.OrderedQueryFacts", Some(19), Some(19), Some(19)),
                (Logos, "FormalSQL.OrderedObservationTransportFacts", Some(20), Some(20), Some(20)),
                (Logos, "FormalSQL.RenameTransportFacts", Some(21), Some(21), Some(21)),
                (Logos, "FormalSQL.PossibleOutcomeFacts", Some(22), Some(22), Some(22)),
                (Logos, "FormalSQL.ProofAgentFacade", Some(23), Some(23), Some(23)),
                (Logos, "FormalSQL.SubqueryFacts", Some(24), Some(24), Some(24)),
                (Logos, "FormalSQL.MembershipCompositionFacts", Some(25), Some(25), Some(25)),
                (Logos, "FormalSQL.WitnessFacts", Some(26), Some(26), Some(26)),
                (Logos, "FormalSQL.CountermodelFacts", Some(27), Some(27), Some(27)),
                (Logos, "FormalSQL.AggregateOutcomeBridgeFacts", Some(28), Some(28), Some(28)),
                (Logos, "FormalSQL.CorrelatedMembershipFacts", Some(29), Some(29), Some(29)),
                (Logos, "FormalSQL.MembershipJoinCompositionFacts", Some(30), Some(30), Some(30)),
                (Logos, "FormalSQL.FilterFkEliminationFacts", Some(31), Some(31), Some(31)),
                (Logos, "FormalSQL.QueryBindingSemantics", Some(32), Some(32), Some(32)),
                (LogosGenerated, "Schema", Some(0), None, None),
                (LogosGenerated, "Queries", Some(1), None, None),
                (LogosGenerated, "Witness", Some(2), None, None),
                (Stdlib, "String", Some(0), None, None),
                (Stdlib, "ZArith", Some(1), None, None),
                (Stdlib, "NArith", Some(2), None, None),
                (Stdlib, "List", Some(3), None, None),
                (Stdlib, "Lia", Some(4), None, None),
            ],
        }
    };
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TrustedRocqImportRoot {
    root: TrustedRocqRoot,
    qualifier: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TrustedRocqImport {
    root: TrustedRocqRoot,
    module: &'static str,
    proof_import_order: Option<usize>,
}

macro_rules! declare_emitter_trusted_rocq_imports {
    (
        roots: [$(($root:ident, $qualifier:literal)),* $(,)?],
        imports: [$(($import_root:ident, $module:literal, $proof_order:expr, $object_order:expr, $make_order:expr)),* $(,)?],
    ) => {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        enum TrustedRocqRoot {
            $($root),*
        }

        const TRUSTED_ROCQ_IMPORT_ROOTS: &[TrustedRocqImportRoot] = &[
            $(TrustedRocqImportRoot {
                root: TrustedRocqRoot::$root,
                qualifier: $qualifier,
            }),*
        ];

        const TRUSTED_ROCQ_IMPORTS: &[TrustedRocqImport] = &[
            $(TrustedRocqImport {
                root: TrustedRocqRoot::$import_root,
                module: $module,
                proof_import_order: $proof_order,
            }),*
        ];
    };
}

crate::logos_trusted_rocq_import_registry!(declare_emitter_trusted_rocq_imports);

fn ordered_direct_trusted_rocq_imports(root: TrustedRocqRoot) -> Vec<&'static str> {
    let mut imports = TRUSTED_ROCQ_IMPORTS
        .iter()
        .filter(|import| import.root == root)
        .filter_map(|import| Some((import.proof_import_order?, import.module)))
        .collect::<Vec<_>>();
    imports.sort_unstable_by_key(|(order, _)| *order);
    imports.into_iter().map(|(_, module)| module).collect()
}

pub(super) fn emit_trusted_proof_import_block() -> String {
    TRUSTED_ROCQ_IMPORT_ROOTS
        .iter()
        .map(|root| {
            format!(
                "From {} Require Import {}.",
                root.qualifier,
                ordered_direct_trusted_rocq_imports(root.root).join(" ")
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub(super) fn emit_rocq_create_schema(tables: &[FormalTable]) -> String {
    let mut expr = "init_db".to_owned();
    for table in tables {
        expr = format!(
            "create_table\n  ({})\n  (Rel {})\n  ({})",
            indent_rocq_nested_expr(&expr, 3),
            rocq_string_literal(&table.relation),
            emit_rocq_attribute_list(&table.attributes)
        );
    }
    expr
}

pub(super) fn emit_rocq_schema_module(
    schema_expr: &str,
    tables: &[FormalTable],
    sql_environment: SqlEnvironment,
) -> String {
    let schema_constraint_definitions = emit_rocq_schema_constraint_definitions(tables);
    let schema_constraints = emit_rocq_schema_constraints(tables);
    let schema_constraint_certificates = emit_rocq_schema_constraint_certificates(tables);
    format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance ValueCore ValueInteger ValueString Formula SchemaConstraints.
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.WitnessFacts.
From Stdlib Require Import String ZArith List Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition generated_sql_default_collation : string := {}.
Definition generated_sql_character_classification : string := {}.
Definition generated_sql_locale_provider : string := {}.
Definition generated_sql_server_encoding : string := {}.

{}

{}

Definition generated_schema_constraints : list table_constraint :=
{}.

{}

Definition generated_schema_conforms (db : db_state) : Prop :=
  database_conforms_schema
    generated_schema generated_schema_constraints db.
",
        rocq_string_literal(sql_environment.default_collation_label()),
        rocq_string_literal(sql_environment.character_classification_label()),
        rocq_string_literal(sql_environment.locale_provider_label()),
        rocq_string_literal(sql_environment.server_encoding_label()),
        emit_rocq_schema_definition("generated_schema", schema_expr),
        schema_constraint_definitions,
        indent_rocq_expr(&schema_constraints, 2),
        schema_constraint_certificates,
    )
}

fn generated_table_constraint_name(index: usize) -> String {
    format!("generated_table_constraint_{index}")
}

fn emit_rocq_schema_constraint_definitions(tables: &[FormalTable]) -> String {
    tables
        .iter()
        .enumerate()
        .map(|(index, table)| {
            format!(
                "Definition {} : table_constraint :=\n{}.",
                generated_table_constraint_name(index),
                indent_rocq_expr(&emit_rocq_table_constraint(table), 2),
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn emit_rocq_schema_constraints(tables: &[FormalTable]) -> String {
    let rendered = tables
        .iter()
        .enumerate()
        .map(|(index, _)| generated_table_constraint_name(index))
        .collect::<Vec<_>>();
    emit_rocq_list_expr(&rendered)
}

fn emit_rocq_forall_certificate_chain(lemmas: &[String]) -> String {
    let mut proof = String::new();
    for lemma in lemmas {
        proof.push_str(&format!("  constructor; [exact {lemma}|].\n"));
    }
    proof.push_str("  constructor.");
    proof
}

fn emit_rocq_schema_constraint_certificates(tables: &[FormalTable]) -> String {
    // Keep the generated constraint record opaque to downstream witness
    // certificates.  Projecting a field by unfolding a wide table declaration
    // can make Rocq repeatedly normalize the whole record (notably its long
    // NOT NULL list).  These tiny opaque equalities let the witness assembler
    // expose only the field that it is currently composing.
    let projection_lemmas = tables
        .iter()
        .enumerate()
        .flat_map(|(index, table)| {
            let constraint = generated_table_constraint_name(index);
            let primary_key = match &table.constraints.primary_key {
                None => "None".to_owned(),
                Some(attributes) => {
                    format!("Some ({})", emit_rocq_attribute_list(attributes))
                }
            };
            let unique_keys = table
                .constraints
                .unique
                .iter()
                .map(|constraint| emit_rocq_attribute_list(&constraint.columns))
                .collect::<Vec<_>>();
            let foreign_keys = table
                .constraints
                .foreign_keys
                .iter()
                .map(emit_rocq_foreign_key_constraint)
                .collect::<Vec<_>>();
            let checks = table
                .constraints
                .checks
                .iter()
                .map(|constraint| {
                    format!(
                        "CheckConstraint ({})",
                        emit_rocq_constraint_formula(&constraint.formula)
                    )
                })
                .collect::<Vec<_>>();
            let unique_indexes = table
                .constraints
                .unique_indexes
                .iter()
                .map(emit_rocq_unique_index_constraint)
                .collect::<Vec<_>>();
            [
                (
                    "primary_key",
                    "constraint_primary_key",
                    primary_key,
                ),
                (
                    "unique_keys",
                    "constraint_unique_keys",
                    emit_rocq_list_expr(&unique_keys),
                ),
                (
                    "foreign_keys",
                    "constraint_foreign_keys",
                    emit_rocq_list_expr(&foreign_keys),
                ),
                (
                    "checks",
                    "constraint_checks",
                    emit_rocq_list_expr(&checks),
                ),
                (
                    "unique_indexes",
                    "constraint_unique_indexes",
                    emit_rocq_list_expr(&unique_indexes),
                ),
            ]
            .into_iter()
            .map(move |(suffix, projection, value)| {
                format!(
                    "Lemma {constraint}_{suffix} :\n  {projection} {constraint} = ({value}).\nProof. reflexivity. Qed."
                )
            })
        })
        .collect::<Vec<_>>();
    let declaration_lemmas = tables
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let constraint = generated_table_constraint_name(index);
            let lemma = format!("{constraint}_declarations_well_formed");
            format!(
                "Lemma {lemma} :\n\
  table_constraint_declarations_well_formed\n\
    generated_schema_constraints {constraint}.\n\
Proof.\n\
  apply table_constraint_declarations_well_formedb_sound.\n\
  vm_compute.\n\
  reflexivity.\n\
Qed."
            )
        })
        .collect::<Vec<_>>();
    let lemma_names = (0..tables.len())
        .map(|index| {
            format!(
                "{}_declarations_well_formed",
                generated_table_constraint_name(index)
            )
        })
        .collect::<Vec<_>>();
    let aggregate = format!(
        "Lemma generated_schema_constraints_well_formed :\n\
  schema_constraints_well_formed generated_schema_constraints.\n\
Proof.\n\
  unfold schema_constraints_well_formed, generated_schema_constraints.\n{}\n\
Qed.",
        emit_rocq_forall_certificate_chain(&lemma_names)
    );
    projection_lemmas
        .into_iter()
        .chain(declaration_lemmas)
        .into_iter()
        .chain(std::iter::once(aggregate))
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn emit_rocq_table_constraint(table: &FormalTable) -> String {
    let primary_key = match &table.constraints.primary_key {
        None => "None".to_owned(),
        Some(attributes) => format!("Some ({})", emit_rocq_attribute_list(attributes)),
    };
    let unique_keys = table
        .constraints
        .unique
        .iter()
        .map(|constraint| emit_rocq_attribute_list(&constraint.columns))
        .collect::<Vec<_>>();
    let foreign_keys = table
        .constraints
        .foreign_keys
        .iter()
        .map(emit_rocq_foreign_key_constraint)
        .collect::<Vec<_>>();
    let checks = table
        .constraints
        .checks
        .iter()
        .map(|constraint| {
            format!(
                "CheckConstraint ({})",
                emit_rocq_constraint_formula(&constraint.formula)
            )
        })
        .collect::<Vec<_>>();
    let unique_indexes = table
        .constraints
        .unique_indexes
        .iter()
        .map(emit_rocq_unique_index_constraint)
        .collect::<Vec<_>>();
    format!(
        "TableConstraint\n  (Rel {})\n  ({})\n  ({primary_key})\n  ({})\n  ({})\n  ({})\n  ({})",
        rocq_string_literal(&table.relation),
        emit_rocq_attribute_list(&table.constraints.not_null),
        emit_rocq_list_expr(&unique_keys),
        emit_rocq_list_expr(&foreign_keys),
        emit_rocq_list_expr(&checks),
        emit_rocq_list_expr(&unique_indexes),
    )
}

fn emit_rocq_foreign_key_constraint(constraint: &FormalForeignKeyConstraint) -> String {
    format!(
        "ForeignKeyConstraint\n  ({})\n  (Rel {})\n  ({})",
        emit_rocq_attribute_list(&constraint.columns),
        rocq_string_literal(&constraint.referenced_relation),
        emit_rocq_attribute_list(&constraint.referenced_columns),
    )
}

fn emit_rocq_unique_index_constraint(constraint: &FormalUniqueIndexConstraint) -> String {
    let terms = constraint
        .terms
        .iter()
        .map(emit_rocq_constraint_function_term)
        .collect::<Vec<_>>();
    let predicate = match &constraint.predicate {
        None => "None".to_owned(),
        Some(predicate) => format!("Some ({})", emit_rocq_constraint_formula(predicate)),
    };
    format!(
        "UniqueIndexConstraint\n  ({})\n  ({predicate})",
        emit_rocq_list_expr(&terms),
    )
}

#[cfg(test)]
pub(super) fn emit_rocq_query_module(
    source: &FormalQueryExpr,
    target: &FormalQueryExpr,
) -> FormalQueryModule {
    try_emit_rocq_query_module(source, target)
        .expect("test Rocq emission requires complete ordered query output signatures")
}

#[cfg(test)]
pub(super) fn try_emit_rocq_query_module(
    source: &FormalQueryExpr,
    target: &FormalQueryExpr,
) -> Option<FormalQueryModule> {
    let source_signature = query_expr_output_signature(source)?;
    let target_signature = query_expr_output_signature(target)?;
    emit_rocq_query_program_module_with_signatures(
        &[(source, &source_signature)],
        &[(target, &target_signature)],
    )
}

#[cfg(test)]
pub(super) fn emit_rocq_query_module_with_signatures(
    source: &FormalQueryExpr,
    source_output_signature: &[FormalAttribute],
    target: &FormalQueryExpr,
    target_output_signature: &[FormalAttribute],
) -> FormalQueryModule {
    emit_rocq_query_program_module_with_signatures(
        &[(source, source_output_signature)],
        &[(target, target_output_signature)],
    )
    .expect("test Rocq emission requires exact supplied ordered query output signatures")
}

pub(super) fn emit_rocq_query_program_module_with_signatures(
    source: &[(&FormalQueryExpr, &[FormalAttribute])],
    target: &[(&FormalQueryExpr, &[FormalAttribute])],
) -> Option<FormalQueryModule> {
    validate_query_program_for_emission(source, target).ok()?;
    let source_exprs = source.iter().map(|(query, _)| *query).collect::<Vec<_>>();
    let target_exprs = target.iter().map(|(query, _)| *query).collect::<Vec<_>>();
    let readable = RocqQueryDefinitions::from_query_expr_program_pair(&source_exprs, &target_exprs);
    let shared_definitions = readable.emit_definitions();
    let shared_admissibility_certificates = readable.emit_admissibility_certificates();
    let source_side = emit_rocq_program_side(&readable, "source", source);
    let target_side = emit_rocq_program_side(&readable, "target", target);
    let mut statement_definitions = source_side.statement_definitions;
    statement_definitions.extend(target_side.statement_definitions);
    let rocq_module = format!(
        "\
From SQLFS Require Import FTuples FiniteSet FiniteBag FiniteCollection FlatData SqlSyntax GenericInstance Values ValueCore ValueNumeric ValueNumericTypmod ValueString SchemaConstraints SqlOutcome SqlOrder Formula SqlQuerySyntax SqlQuerySemantics SqlQueryWellFormed.
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.QueryTNullSyntax.
From LogosGenerated Require Import Schema.
From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* Each call is confined to one emitter-known, closed metadata side condition;
   recursive query admissibility is discharged compositionally below. *)
Ltac solve_generated_query_metadata :=
  first [
    intros;
    repeat match goal with
    | H : False |- _ => contradiction
    | H : _ /\\ _ |- _ => destruct H
    | H : _ \\/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ?left = ?right |- _ => first [subst left | subst right]
    end;
    solve [contradiction | reflexivity | congruence | tauto |
           eexists; reflexivity]
  | cbn;
    intros;
    repeat match goal with
    | H : False |- _ => contradiction
    | H : _ /\\ _ |- _ => destruct H
    | H : _ \\/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ?left = ?right |- _ => first [subst left | subst right]
    end;
    solve [contradiction | reflexivity | congruence | tauto |
           eexists; reflexivity]
  ].

(* This tactic is used only for one closed scalar-signature equality at a
   time.  Keep reduction local to the TNull type catalog: typed scalar
   certificates below traverse query and expression syntax compositionally. *)
Ltac solve_generated_scalar_type :=
  unfold TNullLeafHasType, TNullCallHasType, TNullPredicateHasTypes;
  cbn [scalar_expr_type
       TNullAggTermType TNullAggTermTypeFuel TNullAggTermTypesFuel
       TNullFunTermType TNullFunTermTypeFuel TNullFunTermTypesFuel
       TNullScalarOperatorOutputType TNullRequireArgumentTypes
       TNullTypeListEqb TNullTypeEqb TNullPredicateArgumentTypesValid
       TNullEqualityPairTypes TNullGenericOrderPairTypes TNullIntegralType
       TNullNumericKindType TNullNumericSourceType TNullCaseResultType
       TNullAggregateFunctionArgumentTypeValid
       TNullAggregateArgumentTypeValid TNullAggregateOutputType
       TNullAggregateFunctionOutputType];
  repeat split; reflexivity.

(* Query-free scalar trees are closed syntax. This bounded structural tactic
   proves their one canonical phase-and-type judgment without serializing a
   whitespace-heavy proof tree into every generated query certificate. *)
Ltac solve_generated_query_free_scalar_admissibility :=
  cbn [scalar_expr_admissible prop_forall];
  repeat split;
  first [match goal with
         | |- forall truth, _ => intros []; reflexivity
         end |
         left; reflexivity | right; reflexivity |
         solve_generated_scalar_type | solve_generated_query_metadata].

Ltac solve_generated_query_free_scalar_list_admissibility :=
  cbn [prop_forall fst snd];
  lazymatch goal with
  | |- True => constructor
  | |- _ /\\ _ => split;
      [ solve_generated_query_free_scalar_admissibility
      | solve_generated_query_free_scalar_list_admissibility ]
  end.

Ltac solve_generated_query_free_select_list_admissibility :=
  cbn [prop_forall fst snd firstn app];
  lazymatch goal with
  | |- True => constructor
  | |- (_ /\\ _) /\\ _ => split;
      [ split;
        [ solve_generated_query_free_scalar_admissibility
        | solve_generated_query_metadata ]
      | solve_generated_query_free_select_list_admissibility ]
  end.

{}

{}

{}

{}

{}

{}

{}

{}

{}
",
        shared_definitions,
        shared_admissibility_certificates,
        statement_definitions.join("\n\n"),
        source_side.program_definition,
        target_side.program_definition,
        source_side.signatures_definition,
        target_side.signatures_definition,
        source_side.program_admissibility_certificates,
        target_side.program_admissibility_certificates,
    );
    let mut shape_definitions = readable.shape_definitions();
    shape_definitions.extend(source_side.shape_definitions);
    shape_definitions.extend(target_side.shape_definitions);
    let definition_graph = FormalQueryDefinitionGraph {
        schema_version: 2,
        notation: "Constructor{compact-fields}(child,...); @identifier is an emitted Rocq definition reference; #role{compact-fields} is an intentionally opaque inline scalar/list argument"
            .to_owned(),
        opaque_helper_symbols: (0..readable.scalar_select_lists.len())
            .map(|index| format!("scalar_select_list_{index}"))
            .collect(),
        definitions: shape_definitions,
        source_statements: source_side.statement_symbols,
        target_statements: target_side.statement_symbols,
    };
    Some(FormalQueryModule {
        rocq_module,
        definition_graph,
    })
}

pub(super) type BoundProgramPart<'a> = (
    &'a FormalQueryExpr,
    &'a [FormalAttribute],
    &'a [FormalQueryBinding],
);

pub(crate) fn emit_rocq_bound_query_program_module_with_signatures(
    source: &[BoundProgramPart<'_>],
    target: &[BoundProgramPart<'_>],
) -> Option<FormalQueryModule> {
    validate_bound_query_program_for_emission(source, target).ok()?;

    let source_queries = bound_program_queries(source);
    let target_queries = bound_program_queries(target);
    let readable = RocqQueryDefinitions::from_query_expr_program_pair_with_schema(
        &source_queries,
        &target_queries,
        "generated_binding_schema",
    );
    let local_schema_count = source
        .iter()
        .chain(target)
        .map(|(_, _, bindings)| bindings.len())
        .sum();
    let local_schemas = emit_rocq_local_query_schemas(source, target);
    let shared_definitions = readable.emit_definitions();
    let shared_admissibility_certificates = readable.emit_admissibility_certificates();
    let source_side = emit_rocq_bound_program_side(&readable, "source", source, local_schema_count);
    let target_side = emit_rocq_bound_program_side(&readable, "target", target, local_schema_count);
    let mut statement_definitions = source_side.statement_definitions;
    statement_definitions.extend(target_side.statement_definitions);

    let rocq_module = format!(
        "\
From SQLFS Require Import FTuples FiniteSet FiniteBag FiniteCollection FlatData SqlSyntax GenericInstance Values ValueCore ValueNumeric ValueNumericTypmod ValueString SchemaConstraints SqlOutcome SqlOrder Formula SqlQuerySyntax SqlQuerySemantics SqlQueryWellFormed.
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.QueryTNullSyntax FormalSQL.QueryBindingSemantics.
From LogosGenerated Require Import Schema.
From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Ltac solve_generated_query_metadata :=
  first [
    intros;
    repeat match goal with
    | H : False |- _ => contradiction
    | H : _ /\\ _ |- _ => destruct H
    | H : _ \\/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ?left = ?right |- _ => first [subst left | subst right]
    end;
    solve [contradiction | reflexivity | congruence | tauto |
           eexists; reflexivity]
  | cbn;
    intros;
    repeat match goal with
    | H : False |- _ => contradiction
    | H : _ /\\ _ |- _ => destruct H
    | H : _ \\/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ?left = ?right |- _ => first [subst left | subst right]
    end;
    solve [contradiction | reflexivity | congruence | tauto |
           eexists; reflexivity]
  ].

(* Synthetic local relations are host-validated as distinct from every base
   relation.  Recheck that closed fact against the generated schema rather
   than asking the general metadata tactic to branch over a long relname
   disjunction. *)
Ltac solve_generated_local_schema_freshness :=
  unfold Schema.generated_schema;
  cbn;
  intros H;
  repeat match type of H with
  | _ \\/ _ => destruct H
  end;
  try contradiction;
  discriminate.

Ltac solve_generated_scalar_type :=
  unfold TNullLeafHasType, TNullCallHasType, TNullPredicateHasTypes;
  cbn [scalar_expr_type
       TNullAggTermType TNullAggTermTypeFuel TNullAggTermTypesFuel
       TNullFunTermType TNullFunTermTypeFuel TNullFunTermTypesFuel
       TNullScalarOperatorOutputType TNullRequireArgumentTypes
       TNullTypeListEqb TNullTypeEqb TNullPredicateArgumentTypesValid
       TNullEqualityPairTypes TNullGenericOrderPairTypes TNullIntegralType
       TNullNumericKindType TNullNumericSourceType TNullCaseResultType
       TNullAggregateFunctionArgumentTypeValid
       TNullAggregateArgumentTypeValid TNullAggregateOutputType
       TNullAggregateFunctionOutputType];
  repeat split; reflexivity.

Ltac solve_generated_query_free_scalar_admissibility :=
  cbn [scalar_expr_admissible prop_forall];
  repeat split;
  first [match goal with
         | |- forall truth, _ => intros []; reflexivity
         end |
         left; reflexivity | right; reflexivity |
         solve_generated_scalar_type | solve_generated_query_metadata].

Ltac solve_generated_query_free_scalar_list_admissibility :=
  cbn [prop_forall fst snd];
  lazymatch goal with
  | |- True => constructor
  | |- _ /\\ _ => split;
      [ solve_generated_query_free_scalar_admissibility
      | solve_generated_query_free_scalar_list_admissibility ]
  end.

Ltac solve_generated_query_free_select_list_admissibility :=
  cbn [prop_forall fst snd firstn app];
  lazymatch goal with
  | |- True => constructor
  | |- (_ /\\ _) /\\ _ => split;
      [ split;
        [ solve_generated_query_free_scalar_admissibility
        | solve_generated_query_metadata ]
      | solve_generated_query_free_select_list_admissibility ]
  end.

{local_schemas}

{shared_definitions}

{shared_admissibility_certificates}

{}

{}

{}

{}

{}

{}
",
        statement_definitions.join("\n\n"),
        source_side.program_definition,
        target_side.program_definition,
        source_side.signatures_definition,
        target_side.signatures_definition,
        format!(
            "{}\n\n{}",
            source_side.program_admissibility_certificates,
            target_side.program_admissibility_certificates
        ),
    );

    let mut shape_definitions = readable.shape_definitions();
    shape_definitions.extend(source_side.shape_definitions);
    shape_definitions.extend(target_side.shape_definitions);
    Some(FormalQueryModule {
        rocq_module,
        definition_graph: FormalQueryDefinitionGraph {
            schema_version: 2,
            notation: "Constructor{compact-fields}(child,...); @identifier is an emitted Rocq definition reference; #role{compact-fields} is an intentionally opaque inline scalar/list argument"
                .to_owned(),
            opaque_helper_symbols: (0..readable.scalar_select_lists.len())
                .map(|index| format!("scalar_select_list_{index}"))
                .collect(),
            definitions: shape_definitions,
            source_statements: source_side.statement_symbols,
            target_statements: target_side.statement_symbols,
        },
    })
}

fn bound_program_queries<'a>(program: &'a [BoundProgramPart<'a>]) -> Vec<&'a FormalQueryExpr> {
    program
        .iter()
        .flat_map(|(body, _, bindings)| {
            bindings
                .iter()
                .map(|binding| &binding.query_expr)
                .chain(std::iter::once(*body))
        })
        .collect()
}

fn validate_bound_query_program_for_emission(
    source: &[BoundProgramPart<'_>],
    target: &[BoundProgramPart<'_>],
) -> Result<(), String> {
    let mut local_relations = HashMap::new();
    for (side, statements) in [("source", source), ("target", target)] {
        for (statement_index, (_, _, bindings)) in statements.iter().enumerate() {
            for (binding_index, binding) in bindings.iter().enumerate() {
                if local_relations
                    .insert(
                        binding.relation.as_str(),
                        (
                            side,
                            statement_index,
                            binding_index,
                            binding.output_signature.as_slice(),
                        ),
                    )
                    .is_some()
                {
                    return Err(format!(
                        "local relation {:?} is not globally fresh",
                        binding.relation
                    ));
                }
            }
        }
    }

    for (side, statements) in [("source", source), ("target", target)] {
        for (statement_index, (body, output_signature, bindings)) in statements.iter().enumerate() {
            let mut boolean_sites = HashSet::new();
            if !bindings.is_empty() && matches!(body, FormalQueryExpr::Error { .. }) {
                return Err(format!(
                    "{side}[{statement_index}].body analysis error cannot follow query-local bindings"
                ));
            }
            validate_query_expr_scalar_operators(body)
                .map_err(|message| format!("{side}[{statement_index}].body: {message}"))?;
            validate_boolean_sites_into(body, &mut boolean_sites)
                .map_err(|message| format!("{side}[{statement_index}].body: {message}"))?;
            validate_local_query_references(body, &local_relations, side, statement_index, None)?;
            let expected = query_expr_output_signature(body).ok_or_else(|| {
                format!("{side}[{statement_index}].body has no exact output signature")
            })?;
            if expected != *output_signature {
                return Err(format!(
                    "{side}[{statement_index}].body output signature does not match its authoritative query expression"
                ));
            }
            let mut binding_ids = HashSet::new();
            for (binding_index, binding) in bindings.iter().enumerate() {
                if !binding_ids.insert(binding.id.as_str()) {
                    return Err(format!(
                        "{side}[{statement_index}] repeats binding id {:?}",
                        binding.id
                    ));
                }
                validate_query_expr_scalar_operators(&binding.query_expr).map_err(|message| {
                    format!("{side}[{statement_index}].bindings[{binding_index}]: {message}")
                })?;
                if formal_query_expr_contains_analysis_error(&binding.query_expr) {
                    return Err(format!(
                        "{side}[{statement_index}].bindings[{binding_index}] cannot contain an analysis-error relation"
                    ));
                }
                validate_boolean_sites_into(&binding.query_expr, &mut boolean_sites).map_err(
                    |message| {
                        format!("{side}[{statement_index}].bindings[{binding_index}]: {message}")
                    },
                )?;
                validate_local_query_references(
                    &binding.query_expr,
                    &local_relations,
                    side,
                    statement_index,
                    Some(binding_index),
                )?;
                let binding_outputs = query_expr_output_signature(&binding.query_expr)
                    .ok_or_else(|| {
                        format!(
                            "{side}[{statement_index}].bindings[{binding_index}] has no exact output signature"
                        )
                    })?;
                if binding_outputs != binding.output_signature {
                    return Err(format!(
                        "{side}[{statement_index}].bindings[{binding_index}] output signature mismatch"
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_local_query_references(
    query: &FormalQueryExpr,
    local_relations: &HashMap<&str, (&str, usize, usize, &[FormalAttribute])>,
    side: &str,
    statement_index: usize,
    binding_index: Option<usize>,
) -> Result<(), String> {
    for (relation, outputs) in query_table_relations(query) {
        let Some((owner_side, owner_statement, owner_binding, owner_outputs)) =
            local_relations.get(relation).copied()
        else {
            continue;
        };
        if owner_side != side || owner_statement != statement_index {
            return Err(format!(
                "{side}[{statement_index}] references query-local relation {relation:?} owned by {owner_side}[{owner_statement}]"
            ));
        }
        if outputs != owner_outputs {
            return Err(format!(
                "{side}[{statement_index}] references query-local relation {relation:?} with a non-authoritative ordered output signature"
            ));
        }
        if let Some(binding_index) = binding_index
            && owner_binding >= binding_index
        {
            return Err(format!(
                "{side}[{statement_index}].bindings[{binding_index}] references non-earlier query-local relation {relation:?} at binding index {owner_binding}"
            ));
        }
    }
    Ok(())
}

fn query_table_relations(query: &FormalQueryExpr) -> Vec<(&str, &[FormalAttribute])> {
    fn scalar<'a>(
        expression: &'a FormalScalarExpr,
        relations: &mut Vec<(&'a str, &'a [FormalAttribute])>,
    ) {
        match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => {}
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                for argument in args {
                    scalar(argument, relations);
                }
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                scalar(condition, relations);
                scalar(then_expr, relations);
                scalar(else_expr, relations);
            }
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => scalar(expression, relations),
            FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
                for operand in operands {
                    scalar(operand, relations);
                }
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. }
            | FormalScalarExpr::In { args, query } => {
                for argument in args {
                    scalar(argument, relations);
                }
                query_expr(query, relations);
            }
            FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
                query_expr(query, relations);
            }
        }
    }

    fn query_expr<'a>(
        query: &'a FormalQueryExpr,
        relations: &mut Vec<(&'a str, &'a [FormalAttribute])>,
    ) {
        match query {
            FormalQueryExpr::Table { relation, columns } => {
                relations.push((relation, columns.as_slice()));
            }
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple => {}
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                query_expr(left, relations);
                query_expr(right, relations);
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
                scalar(predicate, relations);
                for item in matched_select.iter().chain(left_select).chain(right_select) {
                    scalar(&item.expr, relations);
                }
                query_expr(left, relations);
                query_expr(right, relations);
            }
            FormalQueryExpr::Projection { select, input } => {
                for item in select {
                    scalar(&item.expr, relations);
                }
                query_expr(input, relations);
            }
            FormalQueryExpr::Selection { predicate, input } => {
                scalar(predicate, relations);
                query_expr(input, relations);
            }
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => {
                for item in select {
                    scalar(&item.expr, relations);
                }
                for expression in group_by {
                    scalar(expression, relations);
                }
                scalar(having, relations);
                query_expr(input, relations);
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                for grouping_set in grouping_sets {
                    for item in &grouping_set.select {
                        scalar(&item.expr, relations);
                    }
                    for expression in &grouping_set.group_by {
                        scalar(expression, relations);
                    }
                }
                query_expr(input, relations);
            }
            FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => query_expr(input, relations),
        }
    }

    let mut relations = Vec::new();
    query_expr(query, &mut relations);
    relations
}

fn emit_rocq_local_query_schemas(
    source: &[BoundProgramPart<'_>],
    target: &[BoundProgramPart<'_>],
) -> String {
    let schemas = source
        .iter()
        .chain(target)
        .flat_map(|(_, _, bindings)| bindings.iter())
        .map(|binding| {
            format!(
                "MakeLocalQuerySchema (Rel {}) ({})",
                rocq_string_literal(&binding.relation),
                emit_rocq_query_attribute_list(&binding.output_signature)
            )
        })
        .collect::<Vec<_>>();
    format!(
        "Definition generated_local_query_schemas : list LocalQuerySchema :=\n{}.\n\nDefinition generated_binding_schema : db_state :=\n  declare_local_query_schemas Schema.generated_schema generated_local_query_schemas.",
        indent_rocq_expr(&emit_rocq_list_expr(&schemas), 2)
    )
}

struct EmittedRocqBoundProgramSide {
    statement_definitions: Vec<String>,
    program_definition: String,
    signatures_definition: String,
    program_admissibility_certificates: String,
    shape_definitions: Vec<FormalQueryShapeDefinition>,
    statement_symbols: Vec<FormalQueryStatementSymbols>,
}

struct BoundBindingCertificate {
    binding_name: String,
    query_name: String,
    table_reference_count: usize,
}

fn emit_rocq_bound_program_side(
    readable: &RocqQueryDefinitions,
    side: &str,
    statements: &[BoundProgramPart<'_>],
    local_schema_count: usize,
) -> EmittedRocqBoundProgramSide {
    let singleton = statements.len() == 1;
    let mut definitions = Vec::new();
    let mut shape_definitions = Vec::new();
    let mut statement_symbols = Vec::new();
    let mut bound_query_names = Vec::new();
    let mut signature_names = Vec::new();
    let mut statement_admissibility_lemmas = Vec::new();

    for (statement_index, (body, output_signature, bindings)) in statements.iter().enumerate() {
        let suffix = if singleton {
            String::new()
        } else {
            format!("_{statement_index}")
        };
        let body_name = format!("{side}_query_expr{suffix}");
        let signature_name = format!("{side}_output_signature{suffix}");
        emit_bound_query_expr_definition(
            readable,
            &mut definitions,
            &mut shape_definitions,
            &body_name,
            body,
            output_signature,
        );

        let mut binding_names = Vec::new();
        let mut binding_certificates = Vec::new();
        for (binding_index, binding) in bindings.iter().enumerate() {
            let query_name = format!("{side}_query_binding_{statement_index}_{binding_index}_expr");
            emit_bound_query_expr_definition(
                readable,
                &mut definitions,
                &mut shape_definitions,
                &query_name,
                &binding.query_expr,
                &binding.output_signature,
            );
            let binding_name = format!("{side}_query_binding_{statement_index}_{binding_index}");
            definitions.push(format!(
                "Definition {binding_name} : LocalQueryBinding :=\n  MakeLocalQueryBinding\n    (Rel {})\n    ({})\n    ({query_name}).",
                rocq_string_literal(&binding.relation),
                emit_rocq_query_attribute_list(&binding.output_signature),
            ));
            binding_names.push(binding_name.clone());
            definitions.push(emit_local_query_binding_admissibility_certificate(
                &binding_name,
                &query_name,
            ));
            binding_certificates.push(BoundBindingCertificate {
                binding_name,
                query_name,
                table_reference_count: query_table_relations(&binding.query_expr).len(),
            });
        }

        let bound_name = format!("{side}_bound_query{suffix}");
        definitions.push(format!(
            "Definition {bound_name} : BoundQuery :=\n  MakeBoundQuery\n    ({})\n    ({body_name}).",
            emit_rocq_list_expr(&binding_names)
        ));
        let admissibility_lemma = format!("{bound_name}_admissible_generated_schema");
        definitions.push(emit_bound_query_admissibility_certificate(
            &bound_name,
            &admissibility_lemma,
            &body_name,
            query_table_relations(body).len(),
            &binding_certificates,
            local_schema_count,
        ));

        definitions.push(format!(
            "Definition {signature_name} : list (Tuple.attribute TNull) :=\n{}.",
            indent_rocq_expr(&emit_rocq_query_attribute_list(output_signature), 2)
        ));
        statement_symbols.push(FormalQueryStatementSymbols {
            statement_index: statement_index + 1,
            root_symbol: body_name.clone(),
            output_signature_symbol: signature_name.clone(),
        });
        bound_query_names.push(bound_name);
        signature_names.push(signature_name);
        statement_admissibility_lemmas.push(admissibility_lemma);
    }

    let program_definition = format!(
        "Definition {side}_bound_query_program : BoundQueryProgram :=\n  [{}].",
        bound_query_names.join("; ")
    );
    let signatures_definition = format!(
        "Definition {side}_program_output_signatures : list (list (Tuple.attribute TNull)) :=\n  [{}].",
        signature_names.join("; ")
    );
    let generated_steps = statement_admissibility_lemmas
        .iter()
        .map(|lemma| format!("apply {lemma}."))
        .collect::<Vec<_>>();
    let program_proof = rocq_conjunction_proof(vec![
        rocq_nodup_list_proof(
            statements
                .iter()
                .map(|(_, _, bindings)| bindings.len())
                .sum(),
        ),
        rocq_forall_list_proof(&generated_steps),
    ]);
    let program_admissibility_certificates = format!(
        "Lemma {side}_bound_query_program_admissible_generated_schema :\n  bound_query_program_admissible\n    Schema.generated_schema generated_local_query_schemas\n    {side}_bound_query_program.\nProof.\n  unfold {side}_bound_query_program, bound_query_program_admissible.\n  cbn [bound_query_program_binding_relations local_query_binding_relations\n    bound_query_bindings local_binding_relation].\n{}\nQed.\n\nLemma {side}_bound_query_program_admissible\n    (db : db_state) :\n  Schema.generated_schema_conforms db ->\n  bound_query_program_admissible\n    db generated_local_query_schemas\n    {side}_bound_query_program.\nProof.\n  intro Hschema.\n  eapply bound_query_program_admissible_database_schema_transport.\n  - exact Hschema.\n  - apply {side}_bound_query_program_admissible_generated_schema.\nQed.",
        indent_rocq_expr(&program_proof, 2)
    );

    EmittedRocqBoundProgramSide {
        statement_definitions: definitions,
        program_definition,
        signatures_definition,
        program_admissibility_certificates,
        shape_definitions,
        statement_symbols,
    }
}

fn emit_bound_query_expr_definition(
    readable: &RocqQueryDefinitions,
    definitions: &mut Vec<String>,
    shape_definitions: &mut Vec<FormalQueryShapeDefinition>,
    query_name: &str,
    query: &FormalQueryExpr,
    output_signature: &[FormalAttribute],
) {
    definitions.push(readable.emit_query_expr_definition(query_name, query));
    definitions.push(format!(
        "Definition {query_name}_expected_outputs :\n    list (Tuple.attribute TNull) :=\n{}.",
        indent_rocq_expr(&emit_rocq_query_attribute_list(output_signature), 2)
    ));
    definitions.push(readable.emit_query_expr_admissibility_certificate(
        query_name,
        query,
        QueryExprReferencePolicy::uniform(true),
    ));
    shape_definitions.push(FormalQueryShapeDefinition {
        symbol: query_name.to_owned(),
        kind: FormalQueryShapeKind::QueryExpr,
        tree: readable.shape_query_expr(query, true),
    });
}

fn emit_local_query_binding_admissibility_certificate(
    binding_name: &str,
    query_name: &str,
) -> String {
    format!(
        "Lemma {binding_name}_admissible_generated_schema :\n  local_query_binding_admissible\n    generated_binding_schema generated_local_query_schemas\n    {binding_name}.\nProof.\n  unfold local_query_binding_admissible, {binding_name},\n    local_query_binding_schema.\n  cbn [local_binding_relation local_binding_outputs local_binding_query].\n  split.\n  - solve_generated_query_metadata.\n  - split.\n    + exact (proj1 {query_name}_admissible_with_outputs_generated_schema).\n    + split.\n      * reflexivity.\n      * exact (proj2 {query_name}_admissible_with_outputs_generated_schema).\nQed."
    )
}

fn rocq_query_local_references_proof(table_reference_count: usize) -> String {
    let references = vec![rocq_metadata_proof(); table_reference_count];
    rocq_forall_list_proof(&references)
}

fn rocq_binding_dependencies_proof(bindings: &[BoundBindingCertificate]) -> String {
    if let Some((binding, rest)) = bindings.split_first() {
        rocq_focused_subproofs(
            "split.",
            &[
                rocq_query_local_references_proof(binding.table_reference_count),
                rocq_binding_dependencies_proof(rest),
            ],
        )
    } else {
        "constructor.".to_owned()
    }
}

fn emit_bound_query_admissibility_certificate(
    bound_name: &str,
    lemma_name: &str,
    body_name: &str,
    body_table_reference_count: usize,
    bindings: &[BoundBindingCertificate],
    local_schema_count: usize,
) -> String {
    let binding_steps = bindings
        .iter()
        .map(|binding| {
            format!(
                "apply {}_admissible_generated_schema.",
                binding.binding_name
            )
        })
        .collect::<Vec<_>>();
    let binding_names = bindings
        .iter()
        .map(|binding| binding.binding_name.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let query_names = bindings
        .iter()
        .map(|binding| binding.query_name.as_str())
        .chain(std::iter::once(body_name))
        .collect::<Vec<_>>()
        .join(" ");
    let local_references_proof = rocq_focused_subproofs(
        "split.",
        &[
            rocq_binding_dependencies_proof(bindings),
            rocq_query_local_references_proof(body_table_reference_count),
        ],
    );
    let site_proof = "unfold bound_query_boolean_sites.\n\
        apply boolean_sites_well_formedb_sound.\n\
        reflexivity."
        .to_owned();
    let proof = rocq_conjunction_proof(vec![
        rocq_nodup_list_proof(local_schema_count),
        format!(
            "unfold local_query_schemas_fresh.\n{}",
            rocq_forall_list_proof(&vec![
                "solve_generated_local_schema_freshness.".to_owned();
                local_schema_count
            ])
        ),
        rocq_nodup_list_proof(bindings.len()),
        rocq_forall_list_proof(&binding_steps),
        format!(
            "cbn [bound_query_local_references_well_formed\n  local_query_schema_relations local_query_binding_relations\n  local_query_binding_dependencies_well_formed query_local_references_allowed\n  query_expr_table_references scalar_expr_table_references\n  {binding_names} {query_names}].\n{local_references_proof}"
        ),
        rocq_metadata_proof(),
        site_proof,
        format!("exact (proj1 {body_name}_admissible_with_outputs_generated_schema)."),
    ]);
    format!(
        "Lemma {lemma_name} :\n  bound_query_admissible\n    Schema.generated_schema generated_local_query_schemas\n    {bound_name}.\nProof.\n  unfold bound_query_admissible, {bound_name}.\n  cbn [bound_query_bindings bound_query_body local_query_binding_relations\n    local_binding_relation {binding_names}].\n{}\nQed.",
        indent_rocq_expr(&proof, 2)
    )
}

fn validate_query_program_for_emission(
    source: &[(&FormalQueryExpr, &[FormalAttribute])],
    target: &[(&FormalQueryExpr, &[FormalAttribute])],
) -> Result<(), String> {
    for (side, statements) in [("source", source), ("target", target)] {
        for (index, (query, _)) in statements.iter().enumerate() {
            validate_query_expr_scalar_operators(query)
                .map_err(|message| format!("{side}[{index}]: {message}"))?;
            validate_boolean_sites(query)
                .map_err(|message| format!("{side}[{index}]: {message}"))?;
            let expected = query_expr_output_signature(query).ok_or_else(|| {
                format!("{side}[{index}]: query has no consistent ordered typed output signature")
            })?;
            let supplied = statements[index].1;
            if expected != supplied {
                return Err(format!(
                    "{side}[{index}]: supplied output signature does not exactly match the query's authoritative ordered signature"
                ));
            }
        }
    }
    Ok(())
}

/// Boolean-site paths are useful Rust diagnostics but expensive Rocq atoms.
/// Intern them injectively at the generated-module boundary. Since schedules
/// observe sites only through equality, this alpha-renaming preserves the
/// exact possible-outcome semantics while making closed uniqueness checks
/// operate on short strings.
fn compact_boolean_site_names(
    source: &[&FormalQueryExpr],
    target: &[&FormalQueryExpr],
) -> HashMap<String, String> {
    fn record(site: &str, names: &mut HashMap<String, String>) {
        if !names.contains_key(site) {
            names.insert(site.to_owned(), format!("b{}", names.len()));
        }
    }

    fn scalar(expression: &FormalScalarExpr, names: &mut HashMap<String, String>) {
        match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => {}
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                for argument in args {
                    scalar(argument, names);
                }
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                scalar(condition, names);
                scalar(then_expr, names);
                scalar(else_expr, names);
            }
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => scalar(expression, names),
            FormalScalarExpr::And {
                insertion_sites,
                operands,
            }
            | FormalScalarExpr::Or {
                insertion_sites,
                operands,
            } => {
                for row in insertion_sites {
                    for site in row {
                        record(site, names);
                    }
                }
                for operand in operands {
                    scalar(operand, names);
                }
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. }
            | FormalScalarExpr::In { args, query } => {
                for argument in args {
                    scalar(argument, names);
                }
                relational(query, names);
            }
            FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
                relational(query, names)
            }
        }
    }

    fn select(items: &[FormalScalarSelectItem], names: &mut HashMap<String, String>) {
        for item in items {
            scalar(&item.expr, names);
        }
    }

    fn relational(query: &FormalQueryExpr, names: &mut HashMap<String, String>) {
        match query {
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => {}
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                relational(left, names);
                relational(right, names);
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
                scalar(predicate, names);
                select(matched_select, names);
                select(left_select, names);
                select(right_select, names);
                relational(left, names);
                relational(right, names);
            }
            FormalQueryExpr::Projection {
                select: items,
                input,
            } => {
                select(items, names);
                relational(input, names);
            }
            FormalQueryExpr::Selection { predicate, input } => {
                scalar(predicate, names);
                relational(input, names);
            }
            FormalQueryExpr::Group {
                select: items,
                group_by,
                having,
                input,
            } => {
                select(items, names);
                for key in group_by {
                    scalar(key, names);
                }
                scalar(having, names);
                relational(input, names);
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                for grouping_set in grouping_sets {
                    select(&grouping_set.select, names);
                    for key in &grouping_set.group_by {
                        scalar(key, names);
                    }
                }
                relational(input, names);
            }
            FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => relational(input, names),
        }
    }

    let mut names = HashMap::new();
    for query in source.iter().chain(target) {
        relational(query, &mut names);
    }
    names
}

fn validate_boolean_sites(query: &FormalQueryExpr) -> Result<(), String> {
    validate_boolean_sites_into(query, &mut HashSet::new())
}

fn validate_boolean_sites_into<'a>(
    query: &'a FormalQueryExpr,
    sites: &mut HashSet<&'a str>,
) -> Result<(), String> {
    fn record_site<'a>(sites: &mut HashSet<&'a str>, site: &'a str) -> Result<(), String> {
        if site.is_empty() {
            return Err("Boolean evaluation site is empty".to_owned());
        }
        if !sites.insert(site) {
            return Err(format!(
                "Boolean evaluation site {site:?} is reused by distinct syntax nodes"
            ));
        }
        Ok(())
    }

    fn scalar<'a>(
        expression: &'a FormalScalarExpr,
        sites: &mut HashSet<&'a str>,
    ) -> Result<(), String> {
        match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => Ok(()),
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                for arg in args {
                    scalar(arg, sites)?;
                }
                Ok(())
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                scalar(condition, sites)?;
                scalar(then_expr, sites)?;
                scalar(else_expr, sites)
            }
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => scalar(expression, sites),
            FormalScalarExpr::And {
                insertion_sites,
                operands,
            }
            | FormalScalarExpr::Or {
                insertion_sites,
                operands,
            } => {
                if insertion_sites.len() != operands.len() {
                    return Err(
                        "Boolean insertion-site rows are not aligned with operands".to_owned()
                    );
                }
                for (index, row) in insertion_sites.iter().enumerate() {
                    if row.len() != index {
                        return Err(format!(
                            "Boolean insertion-site row {index} has length {}, expected {index}",
                            row.len()
                        ));
                    }
                    for site in row {
                        record_site(sites, site)?;
                    }
                }
                for operand in operands {
                    scalar(operand, sites)?;
                }
                Ok(())
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. }
            | FormalScalarExpr::In { args, query } => {
                for arg in args {
                    scalar(arg, sites)?;
                }
                query_expr(query, sites)
            }
            FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
                query_expr(query, sites)
            }
        }
    }

    fn query_expr<'a>(
        query: &'a FormalQueryExpr,
        sites: &mut HashSet<&'a str>,
    ) -> Result<(), String> {
        match query {
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => Ok(()),
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                query_expr(left, sites)?;
                query_expr(right, sites)
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
                scalar(predicate, sites)?;
                for item in matched_select.iter().chain(left_select).chain(right_select) {
                    scalar(&item.expr, sites)?;
                }
                query_expr(left, sites)?;
                query_expr(right, sites)
            }
            FormalQueryExpr::Projection { select, input } => {
                for item in select {
                    scalar(&item.expr, sites)?;
                }
                query_expr(input, sites)
            }
            FormalQueryExpr::Selection { predicate, input } => {
                scalar(predicate, sites)?;
                query_expr(input, sites)
            }
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => {
                for item in select {
                    scalar(&item.expr, sites)?;
                }
                for expression in group_by {
                    scalar(expression, sites)?;
                }
                scalar(having, sites)?;
                query_expr(input, sites)
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                for grouping_set in grouping_sets {
                    for item in &grouping_set.select {
                        scalar(&item.expr, sites)?;
                    }
                    for expression in &grouping_set.group_by {
                        scalar(expression, sites)?;
                    }
                }
                query_expr(input, sites)
            }
            FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => query_expr(input, sites),
        }
    }

    query_expr(query, sites)
}

struct EmittedRocqProgramSide {
    statement_definitions: Vec<String>,
    program_definition: String,
    signatures_definition: String,
    program_admissibility_certificates: String,
    shape_definitions: Vec<FormalQueryShapeDefinition>,
    statement_symbols: Vec<FormalQueryStatementSymbols>,
}

fn emit_rocq_program_side(
    readable: &RocqQueryDefinitions,
    side: &str,
    statements: &[(&FormalQueryExpr, &[FormalAttribute])],
) -> EmittedRocqProgramSide {
    let singleton = statements.len() == 1;
    let mut definitions = Vec::new();
    let mut shape_definitions = Vec::new();
    let mut statement_symbols = Vec::with_capacity(statements.len());
    let mut query_names = Vec::with_capacity(statements.len());
    let mut signature_names = Vec::with_capacity(statements.len());
    let mut statement_admissibility = Vec::with_capacity(statements.len());
    for (index, (query, output_signature)) in statements.iter().enumerate() {
        let suffix = if singleton {
            String::new()
        } else {
            format!("_{index}")
        };
        let query_name = format!("{side}_query_expr{suffix}");
        let signature_name = format!("{side}_output_signature{suffix}");
        definitions.push(readable.emit_query_expr_definition(&query_name, query));
        shape_definitions.push(FormalQueryShapeDefinition {
            symbol: query_name.clone(),
            kind: FormalQueryShapeKind::QueryExpr,
            tree: readable.shape_query_expr(query, true),
        });
        definitions.push(format!(
            "Definition {query_name}_expected_outputs :\n    list (Tuple.attribute TNull) :=\n{}.",
            indent_rocq_expr(&emit_rocq_query_attribute_list(output_signature), 2)
        ));
        definitions.push(format!(
            "Definition {signature_name} : list (Tuple.attribute TNull) :=\n{}.",
            indent_rocq_expr(&emit_rocq_query_attribute_list(output_signature), 2)
        ));
        definitions.push(readable.emit_query_expr_admissibility_certificate(
            &query_name,
            query,
            QueryExprReferencePolicy::uniform(true),
        ));
        definitions.push(emit_query_expr_schema_admissibility_certificate(
            &query_name,
        ));
        statement_symbols.push(FormalQueryStatementSymbols {
            statement_index: index + 1,
            root_symbol: query_name.clone(),
            output_signature_symbol: signature_name.clone(),
        });
        query_names.push(query_name);
        statement_admissibility.push(format!("{side}_query_expr{suffix}"));
        signature_names.push(signature_name);
    }
    let program_definition = format!(
        "Definition {side}_query_program : list QueryExpr :=\n  [{}].",
        query_names.join("; ")
    );
    let signatures_definition = format!(
        "Definition {side}_program_output_signatures : list (list (Tuple.attribute TNull)) :=\n  [{}].",
        signature_names.join("; ")
    );
    let program_admissibility_certificates =
        emit_query_program_admissibility_certificates(side, &statement_admissibility);
    EmittedRocqProgramSide {
        statement_definitions: definitions,
        program_definition,
        signatures_definition,
        program_admissibility_certificates,
        shape_definitions,
        statement_symbols,
    }
}

#[cfg(test)]
pub(super) fn emit_rocq_query_expr_proof_module() -> FormalProofModule {
    emit_rocq_query_expr_proof_module_for_mode(VerificationMode::SafeUnconditional)
}

pub(crate) fn emit_rocq_query_expr_proof_module_for_mode(
    verification_mode: VerificationMode,
) -> FormalProofModule {
    let equivalence_input = "Definition generated_equivalence_input :=
  (Schema.generated_schema,
   Schema.generated_schema_constraints,
   source_query_program,
   target_query_program).";
    let (query_equivalence, program_equivalence) = match verification_mode {
        VerificationMode::SafeUnconditional => {
            ("query_expr_possible_equiv", "query_program_possible_equiv")
        }
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => (
            "query_expr_possible_outcome_equiv",
            "query_program_possible_outcome_equiv",
        ),
    };
    let equivalence_goal = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Definition generated_equivalence_goal : Prop :=
    source_program_output_signatures =
      map query_expr_outputs
        (source_query_program) /\\
    target_program_output_signatures =
      map query_expr_outputs
        (target_query_program) /\\
    source_program_output_signatures = target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
      generated_query_program_admissible
        db (source_query_program) /\\
      generated_query_program_admissible
        db (target_query_program) /\\
      generated_query_program_equiv db
        (source_query_program)
        (target_query_program))."
                .to_owned()
        }
        VerificationMode::Conditional => "Definition generated_precondition_obligation
    (source : precondition_source)
    (condition : verification_condition) : Prop :=
  precondition_source_obligation
    Schema.generated_schema
    Schema.generated_schema_constraints
    source
    condition.

Definition generated_equivalence_goal
    (condition : verification_condition) : Prop :=
    source_program_output_signatures =
      map query_expr_outputs
        (source_query_program) /\\
    target_program_output_signatures =
      map query_expr_outputs
        (target_query_program) /\\
    source_program_output_signatures = target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
      verification_condition_holds db condition ->
      generated_query_program_admissible
        db (source_query_program) /\\
      generated_query_program_admissible
        db (target_query_program) /\\
      generated_query_program_equiv db
        (source_query_program)
        (target_query_program))."
            .to_owned(),
    };
    let equivalence_goal_intro = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Lemma generated_equivalence_goal_intro :
  (forall db,
    Schema.generated_schema_conforms db ->
    generated_query_program_equiv db
      (source_query_program)
      (target_query_program)) ->
  generated_equivalence_goal.
Proof.
intros Hcore.
split; [reflexivity|].
split; [reflexivity|].
split; [reflexivity|].
intros db Hschema.
split.
- apply source_query_program_admissible.
  exact Hschema.
- split.
  + apply target_query_program_admissible.
    exact Hschema.
  + exact (Hcore db Hschema).
Qed."
        }
        VerificationMode::Conditional => {
            "Lemma generated_equivalence_goal_intro :
  forall condition,
  (forall db,
    Schema.generated_schema_conforms db ->
    verification_condition_holds db condition ->
    generated_query_program_equiv db
      (source_query_program)
      (target_query_program)) ->
  generated_equivalence_goal condition.
Proof.
intros condition Hcore.
split; [reflexivity|].
split; [reflexivity|].
split; [reflexivity|].
intros db Hschema Hcondition.
split.
- apply source_query_program_admissible.
  exact Hschema.
- split.
  + apply target_query_program_admissible.
    exact Hschema.
  + exact (Hcore db Hschema Hcondition).
Qed."
        }
    };
    let verification_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Definition generated_countermodel_goal : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
      generated_query_program_admissible
        Witness.generated_witness_db
        (source_query_program) /\\
      generated_query_program_admissible
        Witness.generated_witness_db
        (target_query_program) /\\
      ~ generated_query_program_outcome_equiv Witness.generated_witness_db
          (source_query_program)
          (target_query_program).

Lemma generated_countermodel_goal_intro :
  Witness.generated_witness_available = true ->
    (
      ~ generated_query_program_outcome_equiv Witness.generated_witness_db
          (source_query_program)
          (target_query_program)) ->
    generated_countermodel_goal.
Proof.
intros Havailable Hseparation.
split; [exact Havailable|].
pose proof
  (Witness.generated_witness_schema_conforms Havailable) as Hschema.
split; [exact Hschema|].
split.
- apply source_query_program_admissible.
  exact Hschema.
- split.
  + apply target_query_program_admissible.
    exact Hschema.
  + exact (Hseparation).
Qed.

Definition generated_verification_goal
    (claim : verification_claim_kind) : Prop :=
  verification_claim_goal
    claim generated_equivalence_goal generated_countermodel_goal."
        }
        VerificationMode::Conditional => "",
    };
    let proof_hole = match verification_mode {
        VerificationMode::SafeUnconditional => {
            "(* LOGOS_PROOF_HOLE: define exactly one direct claim selector and
   prove the selected trusted statement:

     Definition generated_verification_claim :
       Logos.FormalSQL.VerificationConditions.verification_claim_kind :=
       Logos.FormalSQL.VerificationConditions.VerificationEquivalence.

     Theorem generated_queries_verified :
       generated_verification_goal generated_verification_claim.

   For equivalence, begin with [apply generated_equivalence_goal_intro].  The
   helper discharges generated signatures and both admissibility certificates;
   prove runtime safety on both sides and equality of every successful
   observation for every conforming database and every legal Boolean
   schedule.  Work at the possible-outcome boundary rather than selecting a
   fixed schedule; program equivalence advances pointwise through statements.

   If [Witness.generated_witness_available] computes to [true], Logos has
   frozen the validated PostgreSQL candidate as the read-only FormalSQL
   database [Witness.generated_witness_db].  To select the fully qualified
   [VerificationCountermodel] constructor, begin with
   [apply generated_countermodel_goal_intro; [reflexivity|]].  Do not rebuild
   a second database or re-prove schema conformance: prove only complete
   possible-outcome separation on that fixed witness, for every
   the generated query programs.  Finish the selected theorem with [Qed]. *)"
        }
        VerificationMode::OutcomeUnconditional => {
            "(* LOGOS_PROOF_HOLE: define exactly one direct claim selector and
   prove the selected trusted statement:

     Definition generated_verification_claim :
       Logos.FormalSQL.VerificationConditions.verification_claim_kind :=
       Logos.FormalSQL.VerificationConditions.VerificationEquivalence.

     Theorem generated_queries_verified :
       generated_verification_goal generated_verification_claim.

   For equivalence, begin with [apply generated_equivalence_goal_intro].  The
   helper discharges generated signatures and both admissibility certificates;
   prove existence of a legal outcome on each side and exact preservation of
   all successful results and SQL runtime-error categories for every conforming
   database.  When the queries are runtime-safe, the proof may instead
   establish [generated_safe_query_program_equiv] and lift it with
   [query_program_possible_equiv_implies_possible_outcome_equiv].  Safety must
   be proved in Rocq.

   If [Witness.generated_witness_available] computes to [true], Logos has
   frozen the validated PostgreSQL candidate as the read-only FormalSQL
   database [Witness.generated_witness_db].  To select the fully qualified
   [VerificationCountermodel] constructor, begin with
   [apply generated_countermodel_goal_intro; [reflexivity|]].  Do not rebuild
   a second database or re-prove schema conformance: prove only complete
   possible-outcome separation on that fixed witness, for every
   the generated query programs.  Finish the selected theorem with [Qed]. *)"
        }
        VerificationMode::Conditional => {
            "(* LOGOS_PROOF_HOLE: define exactly
     [generated_precondition :
        Logos.FormalSQL.VerificationConditions.verification_condition] and
     [generated_precondition_source :
        Logos.FormalSQL.VerificationConditions.precondition_source], then add
     and prove:

     Theorem generated_precondition_valid :
       generated_precondition_obligation
         generated_precondition_source generated_precondition.

     Theorem generated_queries_equivalent :
       generated_equivalence_goal generated_precondition.

   Finish both the provenance obligation and conditional outcome-equivalence
   theorem with [Qed].  Set the source to the fully qualified constructor
   [Logos.FormalSQL.VerificationConditions.PreconditionDerived] only when the
   original schema contract implies the condition; otherwise use
   [Logos.FormalSQL.VerificationConditions.PreconditionExternal] and prove that
   the strengthened input domain is satisfiable. *)"
        }
    };
    let trusted_imports = emit_trusted_proof_import_block();
    let rocq_module = format!(
        "\
{trusted_imports}
Open Scope string_scope.
Open Scope Z_scope.

Definition generated_value_is_null (v : value) : bool :=
  NullValues.is_null_value v.

Definition eval_generated_query_expr_outcome
    (db : db_state) (q : QueryExpr) :=
  @eval_query_expr_possible_outcome TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    generated_value_is_null
    nil
    q.

Definition generated_safe_query_expr_equiv
    (db : db_state)
    (q1 q2 : QueryExpr) : Prop :=
  @query_expr_possible_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    generated_value_is_null
    nil
    q1
    q2.

Definition generated_safe_query_program_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @query_program_possible_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    generated_value_is_null
    nil
    left
    right.

Definition generated_query_expr_equiv
    (db : db_state)
    (q1 q2 : QueryExpr) : Prop :=
  @{query_equivalence} TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    generated_value_is_null
    nil
    q1
    q2.

Definition generated_query_program_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @{program_equivalence} TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    generated_value_is_null
    nil
    left
    right.

Definition generated_query_program_outcome_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @query_program_possible_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    generated_value_is_null
    nil
    left
    right.

Definition generated_query_program_admissible
    (db : db_state) (program : list QueryExpr) : Prop :=
  Forall
    (TNullQueryExprAdmissible (@_basesort TNull db))
    program.

{equivalence_input}

{equivalence_goal}

{equivalence_goal_intro}

{verification_claim_contract}

{proof_hole}
"
    );
    FormalProofModule { rocq_module }
}

pub(crate) fn emit_rocq_bound_query_proof_module_for_mode(
    verification_mode: VerificationMode,
) -> FormalProofModule {
    let selected_equivalence = match verification_mode {
        VerificationMode::SafeUnconditional => "bound_query_program_possible_equiv",
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => {
            "bound_query_program_demand_safe_outcome_equiv"
        }
    };
    let equivalence_goal = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => format!(
            "Definition generated_equivalence_goal : Prop :=
    source_program_output_signatures =
      map bound_query_outputs
        (source_bound_query_program) /\\
    target_program_output_signatures =
      map bound_query_outputs
        (target_bound_query_program) /\\
    source_program_output_signatures = target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
      generated_query_program_admissible
        db (source_bound_query_program) /\\
      generated_query_program_admissible
        db (target_bound_query_program) /\\
      generated_query_program_equiv db
        (source_bound_query_program)
        (target_bound_query_program))."
        ),
        VerificationMode::Conditional => "Definition generated_precondition_obligation
    (source : precondition_source)
    (condition : verification_condition) : Prop :=
  precondition_source_obligation
    Schema.generated_schema
    Schema.generated_schema_constraints
    source
    condition.

Definition generated_equivalence_goal
    (condition : verification_condition) : Prop :=
    source_program_output_signatures =
      map bound_query_outputs
        (source_bound_query_program) /\\
    target_program_output_signatures =
      map bound_query_outputs
        (target_bound_query_program) /\\
    source_program_output_signatures = target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
      verification_condition_holds db condition ->
      generated_query_program_admissible
        db (source_bound_query_program) /\\
      generated_query_program_admissible
        db (target_bound_query_program) /\\
      generated_query_program_equiv db
        (source_bound_query_program)
        (target_bound_query_program))."
            .to_owned(),
    };
    let equivalence_goal_intro = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Lemma generated_equivalence_goal_intro :
  (forall db,
    Schema.generated_schema_conforms db ->
    generated_query_program_equiv db
      (source_bound_query_program)
      (target_bound_query_program)) ->
  generated_equivalence_goal.
Proof.
intros Hcore.
split; [reflexivity|].
split; [reflexivity|].
split; [reflexivity|].
intros db Hschema.
split.
- apply source_bound_query_program_admissible; exact Hschema.
- split.
  + apply target_bound_query_program_admissible; exact Hschema.
  + exact (Hcore db Hschema).
Qed."
        }
        VerificationMode::Conditional => {
            "Lemma generated_equivalence_goal_intro :
  forall condition,
  (forall db,
    Schema.generated_schema_conforms db ->
    verification_condition_holds db condition ->
    generated_query_program_equiv db
      (source_bound_query_program)
      (target_bound_query_program)) ->
  generated_equivalence_goal condition.
Proof.
intros condition Hcore.
split; [reflexivity|].
split; [reflexivity|].
split; [reflexivity|].
intros db Hschema Hcondition.
split.
- apply source_bound_query_program_admissible; exact Hschema.
- split.
  + apply target_bound_query_program_admissible; exact Hschema.
  + exact (Hcore db Hschema Hcondition).
Qed."
        }
    };
    let verification_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Definition generated_countermodel_goal : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
      generated_query_program_admissible
        Witness.generated_witness_db
        (source_bound_query_program) /\\
      generated_query_program_admissible
        Witness.generated_witness_db
        (target_bound_query_program) /\\
      generated_query_program_materialization_safe
        Witness.generated_witness_db
        (source_bound_query_program) /\\
      generated_query_program_materialization_safe
        Witness.generated_witness_db
        (target_bound_query_program) /\\
      ~ generated_query_program_outcome_equiv Witness.generated_witness_db
          (source_bound_query_program)
          (target_bound_query_program).

Lemma generated_countermodel_goal_intro :
  Witness.generated_witness_available = true ->
    (
      generated_query_program_materialization_safe Witness.generated_witness_db
        (source_bound_query_program)) ->
    (
      generated_query_program_materialization_safe Witness.generated_witness_db
        (target_bound_query_program)) ->
    (
      ~ generated_query_program_outcome_equiv Witness.generated_witness_db
          (source_bound_query_program)
          (target_bound_query_program)) ->
    generated_countermodel_goal.
Proof.
intros Havailable Hsource_safe Htarget_safe Hseparation.
split; [exact Havailable|].
pose proof
  (Witness.generated_witness_schema_conforms Havailable) as Hschema.
split; [exact Hschema|].
split.
- apply source_bound_query_program_admissible; exact Hschema.
- split.
  + apply target_bound_query_program_admissible; exact Hschema.
  + split.
    * exact (Hsource_safe).
    * split.
      -- exact (Htarget_safe).
      -- exact (Hseparation).
Qed.

Definition generated_verification_goal
    (claim : verification_claim_kind) : Prop :=
  verification_claim_goal
    claim generated_equivalence_goal generated_countermodel_goal."
        }
        VerificationMode::Conditional => "",
    };
    let proof_hole = match verification_mode {
        VerificationMode::SafeUnconditional => {
            "(* LOGOS_PROOF_HOLE: select equivalence or a validated countermodel
   exactly as in an ordinary generated problem.  For equivalence, start with
   [apply generated_equivalence_goal_intro].  Each local binding is evaluated
   once; repeated references observe arbitrary list representatives of that
   one materialized bag.  Finish the selected theorem with [Qed]. *)"
        }
        VerificationMode::OutcomeUnconditional => {
            "(* LOGOS_PROOF_HOLE: select equivalence or a validated countermodel.
   For equivalence, start with [apply generated_equivalence_goal_intro].  A
   safe proof may establish [generated_safe_query_program_equiv] and use
   [bound_query_program_possible_equiv_implies_demand_safe_outcome_equiv].
   Statements with local bindings must prove materialization safety because
   PostgreSQL may skip an undemanded CTE.  Unbound statements retain their
   exact successful and error outcomes without an extra safety premise. *)"
        }
        VerificationMode::Conditional => {
            "(* LOGOS_PROOF_HOLE: define [generated_precondition] and
   [generated_precondition_source], prove [generated_precondition_valid], and
   prove [generated_queries_equivalent : generated_equivalence_goal
   generated_precondition].  Finish both statements with [Qed]. *)"
        }
    };
    let trusted_imports = emit_trusted_proof_import_block();
    let rocq_module = format!(
        "\
{trusted_imports}
Open Scope string_scope.
Open Scope Z_scope.

Definition generated_safe_query_program_equiv
    (db : db_state) (left right : BoundQueryProgram) : Prop :=
  bound_query_program_possible_equiv
    db generated_local_query_schemas nil left right.

Definition generated_query_program_equiv
    (db : db_state) (left right : BoundQueryProgram) : Prop :=
  {selected_equivalence}
    db generated_local_query_schemas nil left right.

Definition generated_query_program_outcome_equiv
    (db : db_state) (left right : BoundQueryProgram) : Prop :=
  bound_query_program_possible_outcome_equiv
    db generated_local_query_schemas nil left right.

Definition generated_query_program_materialization_safe
    (db : db_state) (program : BoundQueryProgram) : Prop :=
  bound_query_program_materialization_safe
    db generated_local_query_schemas nil program.

Definition generated_query_program_admissible
    (db : db_state) (program : BoundQueryProgram) : Prop :=
  bound_query_program_admissible db generated_local_query_schemas program.

Definition generated_equivalence_input :=
  (Schema.generated_schema,
   Schema.generated_schema_constraints,
   generated_local_query_schemas,
   source_bound_query_program,
   target_bound_query_program).

{equivalence_goal}

{equivalence_goal_intro}

{verification_claim_contract}

{proof_hole}
"
    );
    FormalProofModule { rocq_module }
}

#[cfg(test)]
mod trusted_rocq_registry_tests {
    use super::*;

    fn import_modules<'a>(source: &'a str, qualifier: &str) -> Vec<&'a str> {
        let prefix = format!("From {qualifier} Require Import ");
        let imports = source
            .lines()
            .filter_map(|line| line.strip_prefix(&prefix))
            .collect::<Vec<_>>();
        assert_eq!(imports.len(), 1, "expected one direct {qualifier} import");
        imports[0]
            .strip_suffix('.')
            .expect("Rocq import terminator")
            .split_whitespace()
            .collect()
    }

    #[test]
    fn proof_emitters_derive_their_imports_from_the_trusted_registry() {
        let expected_block = emit_trusted_proof_import_block();
        for proof in [
            emit_rocq_query_expr_proof_module_for_mode(VerificationMode::SafeUnconditional),
            emit_rocq_query_expr_proof_module_for_mode(VerificationMode::OutcomeUnconditional),
            emit_rocq_query_expr_proof_module_for_mode(VerificationMode::Conditional),
        ] {
            assert!(proof.rocq_module.starts_with(&expected_block));
            assert!(!proof.rocq_module.contains("Import ListNotations."));
            for root in TRUSTED_ROCQ_IMPORT_ROOTS {
                assert_eq!(
                    import_modules(&proof.rocq_module, root.qualifier),
                    ordered_direct_trusted_rocq_imports(root.root),
                );
            }
        }
    }
}

fn emit_rocq_schema_definition(name: &str, schema_expr: &str) -> String {
    format!(
        "Definition {name} :=\n{}.",
        indent_rocq_expr(schema_expr, 2)
    )
}

fn rocq_focused_subproofs(tactic: &str, subproofs: &[String]) -> String {
    let mut proof = tactic.to_owned();
    for subproof in subproofs {
        proof.push_str("\n{\n");
        // Rocq focus braces do not depend on indentation. Keeping each nested
        // subproof at a fixed column prevents deep canonical scalar/query
        // trees from expanding quadratically in generated source whitespace.
        proof.push_str(subproof);
        proof.push_str("\n}");
    }
    proof
}

fn rocq_metadata_proof() -> String {
    // Structural certificates keep the goal local. Avoid `abstract` here:
    // inside a deeply focused proof it captures the surrounding evar context,
    // which can be far larger than the closed metadata fact being proved.
    "solve_generated_query_metadata.".to_owned()
}

fn rocq_closed_nonmembership_proof() -> String {
    "cbn.\n\
     unfold not.\n\
     intros.\n\
     repeat match goal with\n\
     | H : False |- _ => contradiction\n\
     | H : _ \\/ _ |- _ => destruct H\n\
     | H : ?left = ?right |- _ =>\n\
         first [subst left | subst right | discriminate H]\n\
     end."
        .to_owned()
}

fn rocq_conjunction_proof(mut conjuncts: Vec<String>) -> String {
    assert!(!conjuncts.is_empty());
    if conjuncts.len() == 1 {
        return conjuncts.remove(0);
    }
    let first = conjuncts.remove(0);
    let rest = rocq_conjunction_proof(conjuncts);
    rocq_focused_subproofs("split.", &[first, rest])
}

fn rocq_forall_list_proof(elements: &[String]) -> String {
    if let Some((first, rest)) = elements.split_first() {
        rocq_focused_subproofs(
            "constructor.",
            &[first.clone(), rocq_forall_list_proof(rest)],
        )
    } else {
        "constructor.".to_owned()
    }
}

fn rocq_append_chain(items: &[String]) -> String {
    match items {
        [] => "nil".to_owned(),
        [item] => item.clone(),
        [first, rest @ ..] => format!("{first} ++ ({})", rocq_append_chain(rest)),
    }
}

fn rocq_nodup_list_proof(element_count: usize) -> String {
    if element_count == 0 {
        "constructor.".to_owned()
    } else {
        rocq_focused_subproofs(
            "constructor.",
            &[
                rocq_closed_nonmembership_proof(),
                rocq_nodup_list_proof(element_count - 1),
            ],
        )
    }
}

fn rocq_window_outputs_all_diff_proof(item_count: usize) -> String {
    // ListFacts.all_diff is definitionally True for both [] and singleton lists.
    if item_count <= 1 {
        return "constructor.".to_owned();
    }
    rocq_focused_subproofs(
        "cbn [ListFacts.all_diff].\nsplit.",
        &[
            rocq_closed_nonmembership_proof(),
            rocq_window_outputs_all_diff_proof(item_count - 1),
        ],
    )
}

fn emit_query_expr_schema_admissibility_certificate(query_name: &str) -> String {
    format!(
        "Lemma {query_name}_admissible (db : db_state) :\n  Schema.generated_schema_conforms db ->\n  TNullQueryExprAdmissible (@_basesort TNull db)\n    {query_name}.\nProof.\n  intro Hschema.\n  apply (query_expr_admissible_database_schema_transport\n    Schema.generated_schema Schema.generated_schema_constraints db).\n  {{ exact Hschema. }}\n  {{ exact (proj1 {query_name}_admissible_with_outputs_generated_schema). }}\nQed."
    )
}

fn emit_query_program_admissibility_certificates(side: &str, statements: &[String]) -> String {
    let generated_steps = statements
        .iter()
        .map(|lemma| format!("exact (proj1 {lemma}_admissible_with_outputs_generated_schema)."))
        .collect::<Vec<_>>();
    let schema_steps = statements
        .iter()
        .map(|lemma| format!("apply ({lemma}_admissible db Hschema)."))
        .collect::<Vec<_>>();
    format!(
        "Lemma {side}_query_program_admissible_generated_schema :\n  Forall\n    (TNullQueryExprAdmissible\n      (@_basesort TNull Schema.generated_schema))\n    {side}_query_program.\nProof.\n  unfold {side}_query_program.\n{}\nQed.\n\nLemma {side}_query_program_admissible\n    (db : db_state) :\n  Schema.generated_schema_conforms db ->\n  Forall\n    (TNullQueryExprAdmissible (@_basesort TNull db))\n    {side}_query_program.\nProof.\n  intro Hschema.\n  unfold {side}_query_program.\n{}\nQed.",
        indent_rocq_expr(&rocq_forall_list_proof(&generated_steps), 2),
        indent_rocq_expr(&rocq_forall_list_proof(&schema_steps), 2),
    )
}

#[derive(Debug)]
struct RocqQueryDefinitions {
    admissibility_schema: String,
    boolean_site_names: HashMap<String, String>,
    scalar_select_lists: Vec<Vec<FormalScalarSelectItem>>,
    scalar_select_uses: Vec<(Vec<FormalScalarSelectItem>, ScalarPhase)>,
    scalar_expr_predicates: Vec<FormalScalarExpr>,
    scalar_expr_uses: Vec<(FormalScalarExpr, ScalarPhase)>,
    table_sorts: Vec<(String, Vec<FormalAttribute>)>,
    shared_query_exprs: Vec<FormalQueryExpr>,
}

#[derive(Clone, Copy)]
struct QueryExprReferencePolicy {
    query_exprs: bool,
    scalar_exprs: bool,
    scalar_select_lists: bool,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ScalarPhase {
    RowSelect,
    Select,
    Where,
    On,
    Having,
    GroupBy,
}

impl ScalarPhase {
    fn rocq_constructor(self) -> &'static str {
        match self {
            Self::RowSelect => "ScalarPhaseRowSelect",
            Self::Select => "ScalarPhaseSelect",
            Self::Where => "ScalarPhaseWhere",
            Self::On => "ScalarPhaseOn",
            Self::Having => "ScalarPhaseHaving",
            Self::GroupBy => "ScalarPhaseGroupBy",
        }
    }

    fn slug(self) -> &'static str {
        match self {
            Self::RowSelect => "row_select",
            Self::Select => "select",
            Self::Where => "where",
            Self::On => "on",
            Self::Having => "having",
            Self::GroupBy => "group_by",
        }
    }
}

impl QueryExprReferencePolicy {
    fn uniform(allow_refs: bool) -> Self {
        Self {
            query_exprs: allow_refs,
            scalar_exprs: allow_refs,
            scalar_select_lists: allow_refs,
        }
    }
}

impl RocqQueryDefinitions {
    fn from_query_expr_program_pair(
        source: &[&FormalQueryExpr],
        target: &[&FormalQueryExpr],
    ) -> Self {
        Self::from_query_expr_program_pair_with_schema(source, target, "Schema.generated_schema")
    }

    fn from_query_expr_program_pair_with_schema(
        source: &[&FormalQueryExpr],
        target: &[&FormalQueryExpr],
        admissibility_schema: &str,
    ) -> Self {
        let mut definitions = Self {
            admissibility_schema: admissibility_schema.to_owned(),
            boolean_site_names: compact_boolean_site_names(source, target),
            scalar_select_lists: Vec::new(),
            scalar_select_uses: Vec::new(),
            scalar_expr_predicates: Vec::new(),
            scalar_expr_uses: Vec::new(),
            table_sorts: Vec::new(),
            shared_query_exprs: Vec::new(),
        };
        for query in source.iter().chain(target) {
            definitions.collect_query_expr(query);
        }

        let mut query_expr_counts = HashMap::new();
        let mut query_expr_order = Vec::new();
        for query in source.iter().chain(target) {
            collect_query_expr_counts(query, &mut query_expr_counts, &mut query_expr_order);
        }
        definitions.shared_query_exprs =
            select_shared_query_exprs(query_expr_order, &query_expr_counts);
        definitions
    }

    fn collect_query_expr(&mut self, query: &FormalQueryExpr) {
        match query {
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple => {}
            FormalQueryExpr::Table { relation, columns } => {
                push_unique(&mut self.table_sorts, (relation.clone(), columns.clone()))
            }
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                self.collect_query_expr(left);
                self.collect_query_expr(right);
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
                push_unique(&mut self.scalar_expr_predicates, predicate.clone());
                push_unique(
                    &mut self.scalar_expr_uses,
                    (predicate.clone(), ScalarPhase::On),
                );
                self.collect_scalar_expr_queries(predicate);
                for select in [matched_select, left_select, right_select] {
                    for item in select {
                        self.collect_scalar_expr_queries(&item.expr);
                    }
                    push_unique(&mut self.scalar_select_lists, select.clone());
                    push_unique(
                        &mut self.scalar_select_uses,
                        (select.clone(), ScalarPhase::RowSelect),
                    );
                }
                self.collect_query_expr(left);
                self.collect_query_expr(right);
            }
            FormalQueryExpr::Projection { select, input } => {
                for item in select {
                    self.collect_scalar_expr_queries(&item.expr);
                }
                push_unique(&mut self.scalar_select_lists, select.clone());
                push_unique(
                    &mut self.scalar_select_uses,
                    (select.clone(), ScalarPhase::RowSelect),
                );
                self.collect_query_expr(input);
            }
            FormalQueryExpr::Selection { predicate, input } => {
                push_unique(&mut self.scalar_expr_predicates, predicate.clone());
                push_unique(
                    &mut self.scalar_expr_uses,
                    (predicate.clone(), ScalarPhase::Where),
                );
                self.collect_scalar_expr_queries(predicate);
                self.collect_query_expr(input);
            }
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => {
                for item in select {
                    self.collect_scalar_expr_queries(&item.expr);
                }
                push_unique(&mut self.scalar_select_lists, select.clone());
                push_unique(
                    &mut self.scalar_select_uses,
                    (select.clone(), ScalarPhase::Select),
                );
                for key in group_by {
                    self.collect_scalar_expr_queries(key);
                }
                push_unique(&mut self.scalar_expr_predicates, having.clone());
                push_unique(
                    &mut self.scalar_expr_uses,
                    (having.clone(), ScalarPhase::Having),
                );
                self.collect_scalar_expr_queries(having);
                self.collect_query_expr(input);
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                for grouping_set in grouping_sets {
                    for item in &grouping_set.select {
                        self.collect_scalar_expr_queries(&item.expr);
                    }
                    push_unique(&mut self.scalar_select_lists, grouping_set.select.clone());
                    push_unique(
                        &mut self.scalar_select_uses,
                        (grouping_set.select.clone(), ScalarPhase::Select),
                    );
                    for key in &grouping_set.group_by {
                        self.collect_scalar_expr_queries(key);
                    }
                }
                self.collect_query_expr(input);
            }
            FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => self.collect_query_expr(input),
        }
    }

    fn boolean_site_name<'a>(&'a self, site: &str) -> &'a str {
        self.boolean_site_names
            .get(site)
            .map(String::as_str)
            .expect("each emitted Boolean site has one compact module-local name")
    }

    fn emit_boolean_insertion_sites(&self, site_rows: &[Vec<String>]) -> String {
        emit_rocq_list_expr(
            &site_rows
                .iter()
                .map(|row| {
                    emit_rocq_list_expr(
                        &row.iter()
                            .map(|site| rocq_string_literal(self.boolean_site_name(site)))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }

    fn collect_scalar_expr_queries(&mut self, expression: &FormalScalarExpr) {
        match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => {}
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                for arg in args {
                    self.collect_scalar_expr_queries(arg);
                }
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                self.collect_scalar_expr_queries(condition);
                self.collect_scalar_expr_queries(then_expr);
                self.collect_scalar_expr_queries(else_expr);
            }
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => {
                self.collect_scalar_expr_queries(expression);
            }
            FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
                for operand in operands {
                    self.collect_scalar_expr_queries(operand);
                }
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. }
            | FormalScalarExpr::In { args, query } => {
                for arg in args {
                    self.collect_scalar_expr_queries(arg);
                }
                self.collect_query_expr(query);
            }
            FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
                self.collect_query_expr(query);
            }
        }
    }

    fn emit_definitions(&self) -> String {
        let mut definitions = Vec::new();
        let prefix_parents = self.scalar_select_list_prefix_parents();
        for index in self.scalar_select_list_emission_order() {
            let select = &self.scalar_select_lists[index];
            let body = if self.scalar_select_list_uses_chunks(index, &prefix_parents) {
                let chunk_symbols = select
                    .chunks(SCALAR_SELECT_CERTIFICATE_CHUNK_SIZE)
                    .enumerate()
                    .map(|(chunk_index, chunk)| {
                        let symbol = format!("scalar_select_list_{index}_chunk_{chunk_index}");
                        definitions.push(format!(
                            "Definition {symbol} :\n    list ((@scalar_expr TNull relname ScalarResultValue * Tuple.attribute TNull)%type) :=\n{}.",
                            indent_rocq_expr(&self.emit_scalar_select_list_inline(chunk), 2)
                        ));
                        symbol
                    })
                    .collect::<Vec<_>>();
                rocq_append_chain(&chunk_symbols)
            } else if let Some(parent) = prefix_parents[index] {
                format!(
                    "firstn ({}%nat) (scalar_select_list_{parent})",
                    select.len()
                )
            } else {
                self.emit_scalar_select_list_inline(select)
            };
            definitions.push(format!(
                "Definition scalar_select_list_{index} :\n    list ((@scalar_expr TNull relname ScalarResultValue * Tuple.attribute TNull)%type) :=\n{}.",
                indent_rocq_expr(&body, 2)
            ));
        }
        for (index, expression) in self.scalar_expr_predicates.iter().enumerate() {
            definitions.push(format!(
                "Definition scalar_expr_predicate_{index} :\n    @scalar_expr TNull relname ScalarResultBoolean :=\n{}.",
                indent_rocq_expr(&self.emit_scalar_expr(expression, false), 2)
            ));
        }
        for index in self.shared_query_expr_emission_order() {
            let query = &self.shared_query_exprs[index];
            definitions.push(format!(
                "Definition shared_query_expr_{index} : QueryExpr :=\n{}.",
                indent_rocq_expr(
                    &self.emit_query_expr_body(query, QueryExprReferencePolicy::uniform(true)),
                    2,
                )
            ));
            definitions.push(format!(
                "Definition shared_query_expr_{index}_expected_outputs :\n    list (Tuple.attribute TNull) :=\n{}.",
                indent_rocq_expr(
                    &format!("query_expr_outputs shared_query_expr_{index}"),
                    2,
                )
            ));
        }
        definitions.join("\n\n")
    }

    fn emit_admissibility_certificates(&self) -> String {
        let mut certificates = Vec::new();
        for (index, (relation, columns)) in self.table_sorts.iter().enumerate() {
            certificates.push(format!(
                "Lemma generated_table_sort_{index} :\n  @_basesort TNull {} (Rel {}) =S=\n  Fset.mk_set (Tuple.A TNull) ({}).\nProof.\n  {}\nQed.",
                self.admissibility_schema,
                rocq_string_literal(relation),
                emit_rocq_query_attribute_list(columns),
                rocq_metadata_proof(),
            ));
        }
        for (expression, phase) in &self.scalar_expr_uses {
            let index = self
                .scalar_expr_predicates
                .iter()
                .position(|candidate| candidate == expression)
                .expect("each scalar-expression use has one emitted definition");
            let symbol = format!("scalar_expr_predicate_{index}");
            certificates.push(
                self.emit_scalar_expr_admissibility_certificate(&symbol, expression, *phase, false),
            );
        }
        for use_index in self.scalar_select_use_emission_order() {
            let (select, phase) = &self.scalar_select_uses[use_index];
            let index = self
                .scalar_select_lists
                .iter()
                .position(|candidate| candidate == select)
                .expect("each scalar-select use has one emitted definition");
            certificates.push(
                self.emit_scalar_select_list_admissibility_certificate(index, select, *phase),
            );
        }
        for index in self.shared_query_expr_emission_order() {
            let query = &self.shared_query_exprs[index];
            let symbol = format!("shared_query_expr_{index}");
            certificates.push(self.emit_query_expr_body_admissibility_certificate(
                &symbol,
                query,
                // Scalar-expression certificates are emitted immediately above, so a
                // shared query can reuse their opaque proofs just as it
                // already reuses earlier shared-query certificates.  Expanding
                // the same predicate tree again here made generated
                // admissibility certificates quadratic in common nested-query
                // shapes without adding an independent obligation.
                QueryExprReferencePolicy::uniform(true),
            ));
        }
        certificates.join("\n\n")
    }

    fn emit_scalar_expr_admissibility_certificate(
        &self,
        symbol: &str,
        expression: &FormalScalarExpr,
        phase: ScalarPhase,
        allow_scalar_refs: bool,
    ) -> String {
        format!(
            "Lemma {symbol}_admissible_{}_generated_schema :\n  TNullScalarExprAdmissible\n    (@_basesort TNull {}) {} {symbol}.\nProof.\n  unfold TNullScalarExprAdmissible, {symbol}.\n{}\nQed.",
            phase.slug(),
            self.admissibility_schema,
            phase.rocq_constructor(),
            indent_rocq_expr(
                &rocq_focused_subproofs(
                    "split.",
                    &[
                        self.emit_scalar_expr_admissibility_proof(
                            expression,
                            phase,
                            allow_scalar_refs,
                        ),
                        rocq_focused_subproofs(
                            "split.",
                            &[
                                "reflexivity.".to_owned(),
                                "unfold scalar_expr_boolean_sites_well_formed.\n\
                                 apply boolean_sites_well_formedb_sound.\n\
                                 reflexivity."
                                    .to_owned(),
                            ],
                        ),
                    ],
                ),
                2,
            )
        )
    }

    fn emit_scalar_expr_admissibility_proof(
        &self,
        expression: &FormalScalarExpr,
        phase: ScalarPhase,
        allow_scalar_refs: bool,
    ) -> String {
        if allow_scalar_refs
            && expression.result_kind() == FormalScalarResultKind::Boolean
            && let Some(index) = self
                .scalar_expr_predicates
                .iter()
                .position(|candidate| candidate == expression)
        {
            return format!(
                "apply (scalar_expr_predicate_{index}_admissible_{}_generated_schema).",
                phase.slug()
            );
        }

        if !scalar_expr_contains_subquery(expression) {
            return "solve_generated_query_free_scalar_admissibility.".to_owned();
        }

        let scalar_arguments_proof = |arguments: &[FormalScalarExpr]| {
            rocq_forall_list_proof(
                &arguments
                    .iter()
                    .map(|argument| {
                        self.emit_scalar_expr_admissibility_proof(argument, phase, false)
                    })
                    .collect::<Vec<_>>(),
            )
        };
        let query_admissibility_proof = |query: &FormalQueryExpr| {
            rocq_focused_subproofs(
                "eapply query_expr_admissible_of_with_outputs.",
                &[self.emit_query_expr_child_admissibility_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                )],
            )
        };

        match expression {
            FormalScalarExpr::Leaf { .. } => {
                let phase_proof = if matches!(phase, ScalarPhase::Select | ScalarPhase::Having) {
                    "left; reflexivity.".to_owned()
                } else {
                    "right; reflexivity.".to_owned()
                };
                rocq_conjunction_proof(vec![phase_proof, "solve_generated_scalar_type.".to_owned()])
            }
            FormalScalarExpr::Call { args, .. } => rocq_conjunction_proof(vec![
                scalar_arguments_proof(args),
                "solve_generated_scalar_type.".to_owned(),
            ]),
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_admissibility_proof(condition, phase, false),
                self.emit_scalar_expr_admissibility_proof(then_expr, phase, false),
                self.emit_scalar_expr_admissibility_proof(else_expr, phase, false),
                rocq_metadata_proof(),
                rocq_metadata_proof(),
            ]),
            FormalScalarExpr::BooleanValue { expression } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_admissibility_proof(expression, phase, false),
                "intros truth; destruct truth; reflexivity.".to_owned(),
            ]),
            FormalScalarExpr::ValueBoolean { expression } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_admissibility_proof(expression, phase, false),
                "reflexivity.".to_owned(),
            ]),
            FormalScalarExpr::Not { expression } => {
                self.emit_scalar_expr_admissibility_proof(expression, phase, false)
            }
            FormalScalarExpr::Predicate { args, .. } => rocq_conjunction_proof(vec![
                scalar_arguments_proof(args),
                rocq_metadata_proof(),
                "solve_generated_scalar_type.".to_owned(),
            ]),
            FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
                rocq_conjunction_proof(vec![
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                    rocq_forall_list_proof(
                        &operands
                            .iter()
                            .map(|operand| {
                                self.emit_scalar_expr_admissibility_proof(operand, phase, false)
                            })
                            .collect::<Vec<_>>(),
                    ),
                ])
            }
            FormalScalarExpr::True => "constructor.".to_owned(),
            FormalScalarExpr::QuantifiedComparison { args, query, .. } => {
                rocq_conjunction_proof(vec![
                    rocq_metadata_proof(),
                    scalar_arguments_proof(args),
                    query_admissibility_proof(query),
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                    "solve_generated_scalar_type.".to_owned(),
                ])
            }
            FormalScalarExpr::In { args, query } => rocq_conjunction_proof(vec![
                rocq_metadata_proof(),
                scalar_arguments_proof(args),
                query_admissibility_proof(query),
                rocq_metadata_proof(),
                rocq_metadata_proof(),
                rocq_metadata_proof(),
            ]),
            FormalScalarExpr::Exists { query } => rocq_conjunction_proof(vec![
                rocq_metadata_proof(),
                query_admissibility_proof(query),
            ]),
            FormalScalarExpr::Subquery { query, .. } => rocq_conjunction_proof(vec![
                rocq_metadata_proof(),
                query_admissibility_proof(query),
                rocq_metadata_proof(),
                rocq_metadata_proof(),
                rocq_metadata_proof(),
            ]),
        }
    }

    fn emit_scalar_select_list_admissibility_proof(
        &self,
        select: &[FormalScalarSelectItem],
        phase: ScalarPhase,
        allow_refs: bool,
    ) -> String {
        if allow_refs
            && let Some(index) = self
                .scalar_select_lists
                .iter()
                .position(|candidate| candidate == select)
        {
            return format!(
                "apply (scalar_select_list_{index}_admissible_{}_generated_schema).",
                phase.slug()
            );
        }

        self.emit_scalar_select_list_admissibility_inline_proof(select, phase)
    }

    fn emit_scalar_select_list_admissibility_inline_proof(
        &self,
        select: &[FormalScalarSelectItem],
        phase: ScalarPhase,
    ) -> String {
        let proof = self.emit_scalar_select_list_admissibility_items_proof(select, phase);
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("{}\n{proof}", self.scalar_select_list_unfold(index)))
            .unwrap_or(proof)
    }

    fn emit_scalar_select_list_admissibility_items_proof(
        &self,
        select: &[FormalScalarSelectItem],
        phase: ScalarPhase,
    ) -> String {
        if select
            .iter()
            .all(|item| !scalar_expr_contains_subquery(&item.expr))
        {
            return "solve_generated_query_free_select_list_admissibility.".to_owned();
        }

        rocq_forall_list_proof(
            &select
                .iter()
                .map(|item| {
                    rocq_conjunction_proof(vec![
                        self.emit_scalar_expr_admissibility_proof(&item.expr, phase, false),
                        rocq_metadata_proof(),
                    ])
                })
                .collect::<Vec<_>>(),
        )
    }

    fn emit_named_scalar_select_list_admissibility_certificate(
        &self,
        lemma_symbol: &str,
        list_symbol: &str,
        phase: ScalarPhase,
        proof: &str,
    ) -> String {
        format!(
            "Lemma {lemma_symbol} :\n  prop_forall\n    (fun item =>\n      @scalar_expr_admissible TNull relname\n        (@_basesort TNull {})\n        TNullLeafHasType TNullCallHasType TNullPredicateHasTypes\n        type_int64 type_bool NullValues.is_null_value\n        {} ScalarResultValue (fst item) /\\\n      scalar_expr_type (fst item) =\n        Tuple.type_of_attribute TNull (snd item))\n    {list_symbol}.\nProof.\n{}\nQed.",
            self.admissibility_schema,
            phase.rocq_constructor(),
            indent_rocq_expr(proof, 2),
        )
    }

    fn emit_scalar_select_list_chunk_assembly_proof(
        &self,
        index: usize,
        chunk_count: usize,
        phase: ScalarPhase,
    ) -> String {
        fn assemble(
            index: usize,
            chunk_index: usize,
            chunk_count: usize,
            phase: ScalarPhase,
        ) -> String {
            let symbol = format!("scalar_select_list_{index}_chunk_{chunk_index}");
            let certificate = format!("{symbol}_admissible_{}_generated_schema", phase.slug());
            if chunk_index + 1 == chunk_count {
                return format!("exact ({certificate}).");
            }
            rocq_focused_subproofs(
                &format!("eapply (@prop_forall_app _ _ ({symbol}) _)."),
                &[
                    format!("exact ({certificate})."),
                    assemble(index, chunk_index + 1, chunk_count, phase),
                ],
            )
        }

        format!(
            "unfold scalar_select_list_{index}.\n{}",
            assemble(index, 0, chunk_count, phase)
        )
    }

    fn emit_scalar_select_list_admissibility_certificate(
        &self,
        index: usize,
        select: &[FormalScalarSelectItem],
        phase: ScalarPhase,
    ) -> String {
        let prefix_parents = self.scalar_select_list_prefix_parents();
        let mut certificates = Vec::new();
        let proof = if self.scalar_select_list_uses_chunks(index, &prefix_parents) {
            for (chunk_index, chunk) in select
                .chunks(SCALAR_SELECT_CERTIFICATE_CHUNK_SIZE)
                .enumerate()
            {
                let symbol = format!("scalar_select_list_{index}_chunk_{chunk_index}");
                let lemma = format!("{symbol}_admissible_{}_generated_schema", phase.slug());
                let chunk_proof = format!(
                    "unfold {symbol}.\n{}",
                    self.emit_scalar_select_list_admissibility_items_proof(chunk, phase)
                );
                certificates.push(
                    self.emit_named_scalar_select_list_admissibility_certificate(
                        &lemma,
                        &symbol,
                        phase,
                        &chunk_proof,
                    ),
                );
            }
            self.emit_scalar_select_list_chunk_assembly_proof(
                index,
                select.len().div_ceil(SCALAR_SELECT_CERTIFICATE_CHUNK_SIZE),
                phase,
            )
        } else if let Some(parent) = prefix_parents[index].filter(|parent| {
            let parent_select = &self.scalar_select_lists[*parent];
            self.scalar_select_uses
                .iter()
                .any(|(candidate, candidate_phase)| {
                    candidate == parent_select && *candidate_phase == phase
                })
        }) {
            format!(
                "unfold scalar_select_list_{index}.\neapply (@prop_forall_firstn\n  _ _ {}%nat (scalar_select_list_{parent})).\nexact (scalar_select_list_{parent}_admissible_{}_generated_schema).",
                select.len(),
                phase.slug()
            )
        } else {
            self.emit_scalar_select_list_admissibility_inline_proof(select, phase)
        };
        let lemma = format!(
            "scalar_select_list_{index}_admissible_{}_generated_schema",
            phase.slug()
        );
        certificates.push(
            self.emit_named_scalar_select_list_admissibility_certificate(
                &lemma,
                &format!("scalar_select_list_{index}"),
                phase,
                &proof,
            ),
        );
        certificates.join("\n\n")
    }

    fn emit_scalar_expr_list_admissibility_proof(
        &self,
        expressions: &[FormalScalarExpr],
        phase: ScalarPhase,
    ) -> String {
        if expressions
            .iter()
            .all(|expression| !scalar_expr_contains_subquery(expression))
        {
            return "solve_generated_query_free_scalar_list_admissibility.".to_owned();
        }
        rocq_forall_list_proof(
            &expressions
                .iter()
                .map(|expression| {
                    self.emit_scalar_expr_admissibility_proof(expression, phase, false)
                })
                .collect::<Vec<_>>(),
        )
    }

    fn emit_query_expr_admissibility_certificate(
        &self,
        symbol: &str,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        self.emit_query_expr_canonical_admissibility_certificate(
            symbol,
            query,
            self.emit_query_expr_admissibility_proof(query, reference_policy),
        )
    }

    fn emit_query_expr_body_admissibility_certificate(
        &self,
        symbol: &str,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        self.emit_query_expr_canonical_admissibility_certificate(
            symbol,
            query,
            self.emit_query_expr_body_admissibility_proof(query, reference_policy),
        )
    }

    fn emit_query_expr_canonical_admissibility_certificate(
        &self,
        symbol: &str,
        query: &FormalQueryExpr,
        admissibility_proof: String,
    ) -> String {
        let schema = &self.admissibility_schema;
        let analysis_error_proof = if matches!(query, FormalQueryExpr::Error { .. }) {
            "constructor."
        } else {
            "reflexivity."
        };
        format!(
            "Lemma {symbol}_admissible_with_outputs_generated_schema :\n  TNullQueryExprAdmissibleWithOutputs\n    (@_basesort TNull {schema})\n    {symbol} {symbol}_expected_outputs.\nProof.\n  unfold {symbol}, {symbol}_expected_outputs.\n  eapply TNullQueryExprAdmissibleWithOutputs_intro.\n  - {}\n  - {}\n  - unfold query_expr_boolean_sites_well_formed.\n    apply boolean_sites_well_formedb_sound.\n    reflexivity.\nQed.",
            admissibility_proof, analysis_error_proof,
        )
    }

    fn emit_join_projection_closed_metadata_proof(
        &self,
        property: &str,
        select_lists: &[&Vec<FormalScalarSelectItem>],
    ) -> String {
        let mut definitions = select_lists
            .iter()
            .filter_map(|select| {
                self.scalar_select_lists
                    .iter()
                    .position(|candidate| candidate == *select)
                    .map(|index| format!("scalar_select_list_{index}"))
            })
            .collect::<Vec<_>>();
        definitions.sort();
        definitions.dedup();

        let mut unfold = vec![property.to_owned()];
        if property == "query_join_projections_unique" {
            unfold.extend([
                "query_select_list_outputs_unique".to_owned(),
                "query_output_attributes_unique".to_owned(),
                "select_list_outputs".to_owned(),
            ]);
        }
        unfold.extend(definitions);
        format!("unfold {}.\n{}", unfold.join(", "), rocq_metadata_proof())
    }

    fn emit_join_projection_phase_admissibility_proof(
        &self,
        join_kind: FormalQueryJoinKind,
        matched_select: &[FormalScalarSelectItem],
        left_select: &[FormalScalarSelectItem],
        right_select: &[FormalScalarSelectItem],
        allow_select_refs: bool,
    ) -> String {
        let selected = match join_kind {
            FormalQueryJoinKind::Left => vec![matched_select, left_select],
            FormalQueryJoinKind::Right => vec![matched_select, right_select],
            FormalQueryJoinKind::Full => vec![matched_select, left_select, right_select],
            FormalQueryJoinKind::Semi | FormalQueryJoinKind::Anti => vec![left_select],
        };
        let proof = rocq_conjunction_proof(
            selected
                .into_iter()
                .map(|select| {
                    self.emit_scalar_select_list_admissibility_proof(
                        select,
                        ScalarPhase::RowSelect,
                        allow_select_refs,
                    )
                })
                .collect(),
        );
        proof
    }

    fn emit_window_items_admissibility_proof(&self, items: &[FormalWindowItem]) -> String {
        rocq_forall_list_proof(
            &items
                .iter()
                .map(|item| match &item.function {
                    FormalWindowFunction::RowNumber => rocq_metadata_proof(),
                    FormalWindowFunction::Aggregate { .. } => {
                        "unfold WindowAggregateItem, TNullLeafHasType; \
                         split; reflexivity."
                            .to_owned()
                    }
                    FormalWindowFunction::FullPartitionAggregate { .. } => {
                        "unfold WindowFullPartitionAggregateItem, TNullLeafHasType; \
                         split; reflexivity."
                            .to_owned()
                    }
                })
                .collect::<Vec<_>>(),
        )
    }

    fn emit_query_expr_admissibility_proof(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        if reference_policy.query_exprs
            && let Some(index) = self
                .shared_query_exprs
                .iter()
                .position(|candidate| candidate == query)
        {
            return rocq_focused_subproofs(
                "split.",
                &[
                    format!(
                        "exact (proj1 (proj1 (shared_query_expr_{index}_admissible_with_outputs_generated_schema)))."
                    ),
                    format!(
                        "exact (proj2 (shared_query_expr_{index}_admissible_with_outputs_generated_schema))."
                    ),
                ],
            );
        }
        self.emit_query_expr_body_admissibility_proof(query, reference_policy)
    }

    fn emit_query_expr_body_admissibility_proof(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        let structural =
            self.emit_query_expr_structural_admissibility_proof(query, reference_policy);
        rocq_focused_subproofs(
            "eapply query_expr_admissible_with_outputs_change.",
            &[structural, rocq_metadata_proof()],
        )
    }

    fn emit_query_expr_child_admissibility_proof(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        if reference_policy.query_exprs
            && let Some(index) = self
                .shared_query_exprs
                .iter()
                .position(|candidate| candidate == query)
        {
            return rocq_focused_subproofs(
                "split.",
                &[
                    format!(
                        "exact (proj1 (proj1 (shared_query_expr_{index}_admissible_with_outputs_generated_schema)))."
                    ),
                    format!(
                        "exact (proj2 (shared_query_expr_{index}_admissible_with_outputs_generated_schema))."
                    ),
                ],
            );
        }
        self.emit_query_expr_structural_admissibility_proof(query, reference_policy)
    }

    fn emit_query_expr_structural_admissibility_proof(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        let structural = match query {
            FormalQueryExpr::Error { .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_error.",
                &[rocq_metadata_proof()],
            ),
            FormalQueryExpr::Empty { .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_values.",
                &[rocq_metadata_proof(), rocq_metadata_proof()],
            ),
            FormalQueryExpr::EmptyTuple => {
                "apply query_expr_admissible_with_outputs_empty_tuple.".to_owned()
            }
            FormalQueryExpr::Table { relation, columns } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_table.",
                &[
                    rocq_metadata_proof(),
                    format!(
                        "apply {}.",
                        self.table_sort_certificate_name(relation, columns)
                    ),
                ],
            ),
            FormalQueryExpr::Set { left, right, .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_set.",
                &[
                    self.emit_query_expr_child_admissibility_proof(left, reference_policy),
                    self.emit_query_expr_child_admissibility_proof(right, reference_policy),
                    rocq_metadata_proof(),
                ],
            ),
            FormalQueryExpr::CrossJoin { left, right } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_cross_join.",
                &[
                    self.emit_query_expr_child_admissibility_proof(left, reference_policy),
                    self.emit_query_expr_child_admissibility_proof(right, reference_policy),
                    rocq_metadata_proof(),
                ],
            ),
            FormalQueryExpr::Join {
                join_kind,
                predicate,
                matched_select,
                left_select,
                right_select,
                left,
                right,
                ..
            } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_join.",
                &[
                    self.emit_scalar_expr_admissibility_proof(
                        predicate,
                        ScalarPhase::On,
                        reference_policy.scalar_exprs,
                    ),
                    self.emit_query_expr_child_admissibility_proof(left, reference_policy),
                    self.emit_query_expr_child_admissibility_proof(right, reference_policy),
                    self.emit_join_projection_closed_metadata_proof(
                        "query_join_projection_sorts_compatible",
                        &[matched_select, left_select, right_select],
                    ),
                    self.emit_join_projection_closed_metadata_proof(
                        "query_join_projections_unique",
                        &[matched_select, left_select, right_select],
                    ),
                    self.emit_join_projection_phase_admissibility_proof(
                        *join_kind,
                        matched_select,
                        left_select,
                        right_select,
                        reference_policy.scalar_select_lists,
                    ),
                ],
            ),
            FormalQueryExpr::Projection { select, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_project.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    self.emit_scalar_select_list_admissibility_proof(
                        select,
                        ScalarPhase::RowSelect,
                        reference_policy.scalar_select_lists,
                    ),
                ],
            ),
            FormalQueryExpr::Selection { predicate, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_filter.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    self.emit_scalar_expr_admissibility_proof(
                        predicate,
                        ScalarPhase::Where,
                        reference_policy.scalar_exprs,
                    ),
                ],
            ),
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_group.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    self.emit_scalar_select_list_admissibility_proof(
                        select,
                        ScalarPhase::Select,
                        reference_policy.scalar_select_lists,
                    ),
                    self.emit_scalar_expr_admissibility_proof(
                        having,
                        ScalarPhase::Having,
                        reference_policy.scalar_exprs,
                    ),
                    self.emit_scalar_expr_list_admissibility_proof(group_by, ScalarPhase::GroupBy),
                    rocq_metadata_proof(),
                ],
            ),
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_grouping_sets.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    self.emit_grouping_sets_well_formed_proof(grouping_sets),
                    self.emit_grouping_sets_admissibility_proof(
                        grouping_sets,
                        reference_policy.scalar_select_lists,
                    ),
                ],
            ),
            FormalQueryExpr::Rank {
                partition_keys,
                order_keys,
                input,
                ..
            } => rocq_focused_subproofs(
                "unfold RankExpr.\n\
                 eapply query_expr_admissible_with_outputs_rank.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    self.emit_sort_keys_in_outputs_proof(partition_keys),
                    self.emit_sort_keys_in_outputs_proof(order_keys),
                    rocq_focused_subproofs(
                        "eapply query_attribute_not_in_outputs.",
                        &[rocq_closed_nonmembership_proof()],
                    ),
                ],
            ),
            FormalQueryExpr::Window {
                partition_keys,
                order_keys,
                items,
                input,
            } => rocq_focused_subproofs(
                "unfold WindowExpr.\n\
                 eapply query_expr_admissible_with_outputs_window.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    self.emit_sort_keys_in_outputs_proof(partition_keys),
                    self.emit_sort_keys_in_outputs_proof(order_keys),
                    self.emit_window_items_fresh_proof(items),
                    self.emit_window_items_admissibility_proof(items),
                    rocq_focused_subproofs(
                        "eapply query_output_attributes_unique_from_all_diff.",
                        &[rocq_window_outputs_all_diff_proof(items.len())],
                    ),
                ],
            ),
            FormalQueryExpr::Distinct { input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_distinct.",
                &[self.emit_query_expr_child_admissibility_proof(input, reference_policy)],
            ),
            FormalQueryExpr::OrderBy { keys, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_order_by.",
                &[
                    self.emit_query_expr_child_admissibility_proof(input, reference_policy),
                    self.emit_sort_keys_in_outputs_proof(keys),
                ],
            ),
            FormalQueryExpr::Offset { input, .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_offset.",
                &[self.emit_query_expr_child_admissibility_proof(input, reference_policy)],
            ),
            FormalQueryExpr::Fetch { input, .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_fetch.",
                &[self.emit_query_expr_child_admissibility_proof(input, reference_policy)],
            ),
        };
        structural
    }

    fn shape_definitions(&self) -> Vec<FormalQueryShapeDefinition> {
        let mut definitions = Vec::new();
        for (index, expression) in self.scalar_expr_predicates.iter().enumerate() {
            definitions.push(FormalQueryShapeDefinition {
                symbol: format!("scalar_expr_predicate_{index}"),
                kind: FormalQueryShapeKind::ScalarExpr,
                tree: self.shape_scalar_expr(expression, false),
            });
        }
        for index in self.shared_query_expr_emission_order() {
            let query = &self.shared_query_exprs[index];
            definitions.push(FormalQueryShapeDefinition {
                symbol: format!("shared_query_expr_{index}"),
                kind: FormalQueryShapeKind::QueryExpr,
                tree: self.shape_query_expr_body(query, QueryExprReferencePolicy::uniform(true)),
            });
        }
        definitions
    }

    /// Keep the stable first-occurrence symbol indices while emitting exact
    /// structural dependencies before their containers. Rocq definitions
    /// cannot forward-reference a later definition, so textual emission order
    /// is a deterministic topological order rather than numeric symbol order.
    ///
    /// Dependencies are derived only from authoritative `FormalQueryExpr`
    /// equality and containment. Compact shape strings never participate in
    /// common-subexpression selection.
    fn shared_query_expr_emission_order(&self) -> Vec<usize> {
        fn visit(
            index: usize,
            queries: &[FormalQueryExpr],
            states: &mut [u8],
            order: &mut Vec<usize>,
        ) {
            match states[index] {
                2 => return,
                1 => {
                    // A finite owned syntax tree cannot contain itself as a
                    // proper subtree. Keep this assertion close to the CSE
                    // authority in case that representation ever changes.
                    unreachable!("shared QueryExpr proper-subtree dependency cycle")
                }
                _ => {}
            }
            states[index] = 1;
            for dependency in 0..queries.len() {
                if dependency != index
                    && proper_query_expr_subquery_occurrences(&queries[index], &queries[dependency])
                        > 0
                {
                    visit(dependency, queries, states, order);
                }
            }
            states[index] = 2;
            order.push(index);
        }

        let mut states = vec![0; self.shared_query_exprs.len()];
        let mut order = Vec::with_capacity(self.shared_query_exprs.len());
        for index in 0..self.shared_query_exprs.len() {
            visit(index, &self.shared_query_exprs, &mut states, &mut order);
        }
        order
    }

    /// Scalar select-list definitions may contain subqueries whose
    /// projections use another emitted scalar select list. Preserve stable
    /// first-occurrence symbol indices, but place nested lists and exact
    /// prefix parents before their users so Rocq never sees a forward
    /// reference.
    fn scalar_select_list_emission_order(&self) -> Vec<usize> {
        fn visit(
            index: usize,
            dependencies: &[Vec<usize>],
            states: &mut [u8],
            order: &mut Vec<usize>,
        ) {
            match states[index] {
                2 => return,
                1 => unreachable!("scalar select-list proper-subtree dependency cycle"),
                _ => {}
            }
            states[index] = 1;
            for &dependency in &dependencies[index] {
                visit(dependency, dependencies, states, order);
            }
            states[index] = 2;
            order.push(index);
        }

        let mut dependencies = self.scalar_select_list_nested_dependencies();
        for (index, parent) in self
            .scalar_select_list_prefix_parents()
            .into_iter()
            .enumerate()
        {
            if let Some(parent) = parent {
                dependencies[index].push(parent);
            }
        }
        let mut states = vec![0; self.scalar_select_lists.len()];
        let mut order = Vec::with_capacity(self.scalar_select_lists.len());
        for index in 0..self.scalar_select_lists.len() {
            visit(index, &dependencies, &mut states, &mut order);
        }
        order
    }

    fn scalar_select_list_nested_dependencies(&self) -> Vec<Vec<usize>> {
        self.scalar_select_lists
            .iter()
            .enumerate()
            .map(|(index, select)| {
                self.scalar_select_lists
                    .iter()
                    .enumerate()
                    .filter_map(|(dependency, candidate)| {
                        (dependency != index && scalar_select_list_contains_list(select, candidate))
                            .then_some(dependency)
                    })
                    .collect()
            })
            .collect()
    }

    /// Reuse only exact AST prefixes. Candidate edges are added to the
    /// authoritative nested-subquery dependency graph one at a time and are
    /// rejected if they would create a definition cycle.
    fn scalar_select_list_prefix_parents(&self) -> Vec<Option<usize>> {
        fn reaches(
            start: usize,
            target: usize,
            dependencies: &[Vec<usize>],
            visited: &mut [bool],
        ) -> bool {
            if start == target {
                return true;
            }
            if visited[start] {
                return false;
            }
            visited[start] = true;
            dependencies[start]
                .iter()
                .any(|dependency| reaches(*dependency, target, dependencies, visited))
        }

        let mut dependencies = self.scalar_select_list_nested_dependencies();
        let mut parents = vec![None; self.scalar_select_lists.len()];
        for (index, select) in self.scalar_select_lists.iter().enumerate() {
            if select.is_empty() {
                continue;
            }
            let mut candidates = self
                .scalar_select_lists
                .iter()
                .enumerate()
                .filter(|(parent, candidate)| {
                    *parent != index
                        && candidate.len() > select.len()
                        && candidate.starts_with(select)
                })
                .map(|(parent, candidate)| (candidate.len(), parent))
                .collect::<Vec<_>>();
            candidates.sort_unstable();
            if let Some((_, parent)) = candidates.into_iter().find(|(_, parent)| {
                !reaches(
                    *parent,
                    index,
                    &dependencies,
                    &mut vec![false; dependencies.len()],
                )
            }) {
                parents[index] = Some(parent);
                dependencies[index].push(parent);
            }
        }
        parents
    }

    fn scalar_select_list_uses_chunks(
        &self,
        index: usize,
        prefix_parents: &[Option<usize>],
    ) -> bool {
        prefix_parents[index].is_none()
            && self.scalar_select_lists[index].len() > SCALAR_SELECT_CERTIFICATE_CHUNK_THRESHOLD
    }

    fn scalar_select_list_unfold(&self, index: usize) -> String {
        let prefix_parents = self.scalar_select_list_prefix_parents();
        let mut symbols = Vec::new();
        let mut current = Some(index);
        while let Some(list_index) = current {
            symbols.push(format!("scalar_select_list_{list_index}"));
            if self.scalar_select_list_uses_chunks(list_index, &prefix_parents) {
                symbols.extend(
                    self.scalar_select_lists[list_index]
                        .chunks(SCALAR_SELECT_CERTIFICATE_CHUNK_SIZE)
                        .enumerate()
                        .map(|(chunk_index, _)| {
                            format!("scalar_select_list_{list_index}_chunk_{chunk_index}")
                        }),
                );
            }
            current = prefix_parents[list_index];
        }
        format!("unfold {}.", symbols.join(", "))
    }

    /// A prefix certificate may reuse a parent certificate only at the same
    /// scalar phase. Emit that parent first while retaining stable order for
    /// unrelated uses.
    fn scalar_select_use_emission_order(&self) -> Vec<usize> {
        fn visit(
            use_index: usize,
            uses: &[(Vec<FormalScalarSelectItem>, ScalarPhase)],
            lists: &[Vec<FormalScalarSelectItem>],
            prefix_parents: &[Option<usize>],
            states: &mut [u8],
            order: &mut Vec<usize>,
        ) {
            match states[use_index] {
                2 => return,
                1 => unreachable!("scalar select-list prefix certificate dependency cycle"),
                _ => {}
            }
            states[use_index] = 1;
            let (select, phase) = &uses[use_index];
            let list_index = lists
                .iter()
                .position(|candidate| candidate == select)
                .expect("each scalar-select use has one emitted definition");
            if let Some(parent) = prefix_parents[list_index]
                && let Some(parent_use) = uses.iter().position(|(candidate, candidate_phase)| {
                    candidate == &lists[parent] && candidate_phase == phase
                })
            {
                visit(parent_use, uses, lists, prefix_parents, states, order);
            }
            states[use_index] = 2;
            order.push(use_index);
        }

        let prefix_parents = self.scalar_select_list_prefix_parents();
        let mut states = vec![0; self.scalar_select_uses.len()];
        let mut order = Vec::with_capacity(self.scalar_select_uses.len());
        for use_index in 0..self.scalar_select_uses.len() {
            visit(
                use_index,
                &self.scalar_select_uses,
                &self.scalar_select_lists,
                &prefix_parents,
                &mut states,
                &mut order,
            );
        }
        order
    }

    fn shape_query_expr(&self, query: &FormalQueryExpr, allow_query_expr_refs: bool) -> String {
        self.shape_query_expr_with_policy(
            query,
            QueryExprReferencePolicy::uniform(allow_query_expr_refs),
        )
    }

    fn shape_query_expr_with_policy(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        if reference_policy.query_exprs
            && let Some(index) = self
                .shared_query_exprs
                .iter()
                .position(|candidate| candidate == query)
        {
            return shape_reference(&format!("shared_query_expr_{index}"));
        }

        self.shape_query_expr_body(query, reference_policy)
    }

    fn shape_query_expr_body(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        match query {
            FormalQueryExpr::Error { columns, error } => shape_node_with_fields(
                "QExpr_Error",
                &[format!("columns={}", columns.len())],
                &[emit_rocq_query_error(*error).to_owned()],
            ),
            FormalQueryExpr::Empty { columns } => shape_node_with_fields(
                "QExpr_Values",
                &[format!("columns={}", columns.len()), "rows=0".to_owned()],
                &[],
            ),
            FormalQueryExpr::EmptyTuple => shape_node_with_fields(
                "QExpr_Values",
                &["columns=0".to_owned(), "rows=1".to_owned()],
                &[],
            ),
            FormalQueryExpr::Table { columns, .. } => {
                shape_node_with_fields("QExpr_Table", &[format!("columns={}", columns.len())], &[])
            }
            FormalQueryExpr::Set { op, left, right } => shape_node(
                "QExpr_Set",
                &[
                    emit_rocq_set_op(*op).to_owned(),
                    self.shape_query_expr_with_policy(left, reference_policy),
                    self.shape_query_expr_with_policy(right, reference_policy),
                ],
            ),
            FormalQueryExpr::CrossJoin { left, right } => shape_node(
                "QExpr_CrossJoin",
                &[
                    self.shape_query_expr_with_policy(left, reference_policy),
                    self.shape_query_expr_with_policy(right, reference_policy),
                ],
            ),
            FormalQueryExpr::Join {
                join_kind,
                predicate,
                matched_select,
                left_select,
                right_select,
                left,
                right,
            } => shape_node(
                "QExpr_Join",
                &[
                    emit_rocq_query_join_kind(*join_kind).to_owned(),
                    self.shape_scalar_expr(predicate, reference_policy.scalar_exprs),
                    self.shape_scalar_select_list(matched_select),
                    self.shape_scalar_select_list(left_select),
                    self.shape_scalar_select_list(right_select),
                    self.shape_query_expr_with_policy(left, reference_policy),
                    self.shape_query_expr_with_policy(right, reference_policy),
                ],
            ),
            FormalQueryExpr::Projection { select, input } => shape_node(
                "QExpr_Project",
                &[
                    self.shape_scalar_select_list(select),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::Selection { predicate, input } => shape_node(
                "QExpr_Filter",
                &[
                    self.shape_scalar_expr(predicate, reference_policy.scalar_exprs),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => {
                let mut children = vec![self.shape_scalar_select_list(select)];
                children.extend(
                    group_by
                        .iter()
                        .map(|key| self.shape_scalar_expr(key, false)),
                );
                children.push(self.shape_scalar_expr(having, reference_policy.scalar_exprs));
                children.push(self.shape_query_expr_with_policy(input, reference_policy));
                shape_node_with_fields(
                    "QExpr_Group",
                    &[format!("keys={}", group_by.len())],
                    &children,
                )
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                let mut children = Vec::new();
                for grouping_set in grouping_sets {
                    children.push(self.shape_scalar_select_list(&grouping_set.select));
                    children.extend(
                        grouping_set
                            .group_by
                            .iter()
                            .map(|key| self.shape_scalar_expr(key, false)),
                    );
                }
                children.push(self.shape_query_expr_with_policy(input, reference_policy));
                shape_node_with_fields(
                    "QExpr_GroupingSets",
                    &[format!("sets={}", grouping_sets.len())],
                    &children,
                )
            }
            FormalQueryExpr::Rank {
                partition_keys,
                order_keys,
                input,
                ..
            } => shape_node_with_fields(
                "RankExpr",
                &[
                    format!("partition={}", partition_keys.len()),
                    format!("order={}", order_keys.len()),
                ],
                &[self.shape_query_expr_with_policy(input, reference_policy)],
            ),
            FormalQueryExpr::Window {
                partition_keys,
                order_keys,
                items,
                input,
            } => shape_node_with_fields(
                "WindowExpr",
                &[
                    format!("partition={}", partition_keys.len()),
                    format!("order={}", order_keys.len()),
                    format!("items={}", items.len()),
                ],
                &[self.shape_query_expr_with_policy(input, reference_policy)],
            ),
            FormalQueryExpr::Distinct { input } => shape_node(
                "QExpr_Distinct",
                &[self.shape_query_expr_with_policy(input, reference_policy)],
            ),
            FormalQueryExpr::OrderBy { keys, input } => shape_node_with_fields(
                "QExpr_OrderBy",
                &[format!("keys={}", keys.len())],
                &[self.shape_query_expr_with_policy(input, reference_policy)],
            ),
            FormalQueryExpr::Offset { count, input } => shape_node_with_fields(
                "QExpr_Offset",
                &[format!("count={count}")],
                &[self.shape_query_expr_with_policy(input, reference_policy)],
            ),
            FormalQueryExpr::Fetch { count, input } => shape_node_with_fields(
                "QExpr_Fetch",
                &[format!("count={count}")],
                &[self.shape_query_expr_with_policy(input, reference_policy)],
            ),
        }
    }

    fn shape_scalar_expr(&self, expression: &FormalScalarExpr, allow_scalar_refs: bool) -> String {
        if allow_scalar_refs
            && expression.result_kind() == FormalScalarResultKind::Boolean
            && let Some(index) = self
                .scalar_expr_predicates
                .iter()
                .position(|candidate| candidate == expression)
        {
            return shape_reference(&format!("scalar_expr_predicate_{index}"));
        }

        match expression {
            FormalScalarExpr::Leaf { result_ty, .. } => shape_node_with_fields(
                "SExpr_Leaf",
                &[format!("type={}", emit_rocq_value_type(*result_ty))],
                &["#aggregate-term".to_owned()],
            ),
            FormalScalarExpr::Call {
                result_ty,
                operator,
                args,
            } => shape_node_with_fields(
                "SExpr_Call",
                &[
                    format!("type={}", emit_rocq_value_type(*result_ty)),
                    format!(
                        "operator={}",
                        compact_skeleton_atom(&format!("{operator:?}"))
                    ),
                ],
                &args
                    .iter()
                    .map(|arg| self.shape_scalar_expr(arg, false))
                    .collect::<Vec<_>>(),
            ),
            FormalScalarExpr::Case {
                result_ty,
                condition,
                then_expr,
                else_expr,
            } => shape_node_with_fields(
                "SExpr_Case",
                &[format!("type={}", emit_rocq_value_type(*result_ty))],
                &[
                    self.shape_scalar_expr(condition, false),
                    self.shape_scalar_expr(then_expr, false),
                    self.shape_scalar_expr(else_expr, false),
                ],
            ),
            FormalScalarExpr::BooleanValue { expression } => shape_node(
                "SExpr_BoolValue",
                &[self.shape_scalar_expr(expression, false)],
            ),
            FormalScalarExpr::ValueBoolean { expression } => shape_node(
                "SExpr_ValueBool",
                &[self.shape_scalar_expr(expression, false)],
            ),
            FormalScalarExpr::Predicate { predicate, args } => shape_node_with_fields(
                "SExpr_Pred",
                &[format!("predicate={}", predicate.rocq_constructor())],
                &args
                    .iter()
                    .map(|arg| self.shape_scalar_expr(arg, false))
                    .collect::<Vec<_>>(),
            ),
            FormalScalarExpr::And {
                insertion_sites,
                operands,
            }
            | FormalScalarExpr::Or {
                insertion_sites,
                operands,
            } => {
                let operation = if matches!(expression, FormalScalarExpr::And { .. }) {
                    "And_F"
                } else {
                    "Or_F"
                };
                let mut children = vec![operation.to_owned()];
                children.extend(
                    operands
                        .iter()
                        .map(|operand| self.shape_scalar_expr(operand, false)),
                );
                let compact_sites = insertion_sites
                    .iter()
                    .map(|row| {
                        row.iter()
                            .map(|site| self.boolean_site_name(site))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                shape_node_with_fields(
                    "SExpr_ConjList",
                    &[format!("sites={compact_sites:?}")],
                    &children,
                )
            }
            FormalScalarExpr::Not { expression } => {
                shape_node("SExpr_Not", &[self.shape_scalar_expr(expression, false)])
            }
            FormalScalarExpr::True => "SExpr_True".to_owned(),
            FormalScalarExpr::QuantifiedComparison {
                quantifier,
                predicate,
                args,
                query,
            } => {
                let mut children = args
                    .iter()
                    .map(|arg| self.shape_scalar_expr(arg, false))
                    .collect::<Vec<_>>();
                children.push(self.shape_query_expr(query, false));
                shape_node_with_fields(
                    "SExpr_Quant",
                    &[
                        format!("quantifier={quantifier:?}"),
                        format!("predicate={}", predicate.rocq_constructor()),
                    ],
                    &children,
                )
            }
            FormalScalarExpr::In { args, query } => {
                let mut children = args
                    .iter()
                    .map(|arg| self.shape_scalar_expr(arg, false))
                    .collect::<Vec<_>>();
                children.push(self.shape_query_expr(query, false));
                shape_node("SExpr_In", &children)
            }
            FormalScalarExpr::Exists { query } => {
                shape_node("SExpr_Exists", &[self.shape_query_expr(query, false)])
            }
            FormalScalarExpr::Subquery {
                result_ty, query, ..
            } => shape_node_with_fields(
                "SExpr_Subquery",
                &[format!("type={}", emit_rocq_value_type(*result_ty))],
                &[self.shape_query_expr(query, false)],
            ),
        }
    }

    fn shape_scalar_select_list(&self, select: &[FormalScalarSelectItem]) -> String {
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| shape_reference(&format!("scalar_select_list_{index}")))
            .unwrap_or_else(|| format!("#scalar-select{{items={}}}", select.len()))
    }

    fn emit_query_expr_definition(&self, name: &str, query: &FormalQueryExpr) -> String {
        format!(
            "Definition {name} : QueryExpr :=\n{}.",
            indent_rocq_expr(&self.emit_query_expr(query, true), 2)
        )
    }

    fn emit_query_expr(&self, query: &FormalQueryExpr, allow_query_expr_refs: bool) -> String {
        self.emit_query_expr_with_policy(
            query,
            QueryExprReferencePolicy::uniform(allow_query_expr_refs),
        )
    }

    fn emit_query_expr_with_policy(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        if reference_policy.query_exprs
            && let Some(index) = self
                .shared_query_exprs
                .iter()
                .position(|candidate| candidate == query)
        {
            return format!("shared_query_expr_{index}");
        }

        self.emit_query_expr_body(query, reference_policy)
    }

    fn emit_query_expr_body(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        match query {
            FormalQueryExpr::Error { columns, error } => format!(
                "@QExpr_Error TNull relname ({}) ({})",
                emit_rocq_query_attribute_list(columns),
                emit_rocq_query_error(*error)
            ),
            FormalQueryExpr::Empty { columns } => format!(
                "@QExpr_Values TNull relname ({}) (Febag.empty (Fecol.CBag (Tuple.CTuple TNull)))",
                emit_rocq_query_attribute_list(columns)
            ),
            FormalQueryExpr::EmptyTuple =>
                "@QExpr_Values TNull relname [] (Febag.singleton (Fecol.CBag (Tuple.CTuple TNull)) (Tuple.empty_tuple TNull))".to_owned(),
            FormalQueryExpr::Table { relation, columns } => format!(
                "@QExpr_Table TNull relname ({}) (Rel {})",
                emit_rocq_query_attribute_list(columns),
                rocq_string_literal(relation)
            ),
            FormalQueryExpr::Set { op, left, right } => format!(
                "QExpr_Set {} ({}) ({})",
                emit_rocq_set_op(*op),
                self.emit_query_expr_with_policy(left, reference_policy),
                self.emit_query_expr_with_policy(right, reference_policy)
            ),
            FormalQueryExpr::CrossJoin { left, right } => format!(
                "QExpr_CrossJoin ({}) ({})",
                self.emit_query_expr_with_policy(left, reference_policy),
                self.emit_query_expr_with_policy(right, reference_policy)
            ),
            FormalQueryExpr::Join {
                join_kind,
                predicate,
                matched_select,
                left_select,
                right_select,
                left,
                right,
            } => format!(
                "QExpr_Join {} ({}) ({}) ({}) ({}) ({}) ({})",
                emit_rocq_query_join_kind(*join_kind),
                self.emit_scalar_expr(predicate, reference_policy.scalar_exprs),
                self.emit_scalar_select_list(matched_select),
                self.emit_scalar_select_list(left_select),
                self.emit_scalar_select_list(right_select),
                self.emit_query_expr_with_policy(left, reference_policy),
                self.emit_query_expr_with_policy(right, reference_policy)
            ),
            FormalQueryExpr::Projection { select, input } => format!(
                "QExpr_Project ({}) ({})",
                self.emit_scalar_select_list(select),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Selection { predicate, input } => format!(
                "QExpr_Filter ({}) ({})",
                self.emit_scalar_expr(predicate, reference_policy.scalar_exprs),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => format!(
                "QExpr_Group ({}) ({}) ({}) ({})",
                self.emit_scalar_select_list(select),
                self.emit_scalar_expr_list(group_by),
                self.emit_scalar_expr(having, reference_policy.scalar_exprs),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => format!(
                "QExpr_GroupingSets ({}) ({})",
                self.emit_grouping_sets(grouping_sets),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Rank {
                partition_keys,
                order_keys,
                rank_attribute,
                input,
            } => format!(
                "RankExpr ({}) ({}) ({}) ({})",
                emit_rocq_list(partition_keys, emit_rocq_sort_key),
                emit_rocq_list(order_keys, emit_rocq_sort_key),
                emit_rocq_attribute(rank_attribute.ty, &rank_attribute.name),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Window {
                partition_keys,
                order_keys,
                items,
                input,
            } => format!(
                "WindowExpr ({}) ({}) ({}) ({})",
                emit_rocq_list(partition_keys, emit_rocq_sort_key),
                emit_rocq_list(order_keys, emit_rocq_sort_key),
                emit_rocq_list(items, emit_rocq_window_item),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Distinct { input } => {
                format!(
                    "QExpr_Distinct ({})",
                    self.emit_query_expr_with_policy(input, reference_policy)
                )
            }
            FormalQueryExpr::OrderBy { keys, input } => format!(
                "QExpr_OrderBy ({}) ({})",
                emit_rocq_list(keys, emit_rocq_sort_key),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Offset { count, input } => {
                format!(
                    "QExpr_Offset ({}%nat) ({})",
                    count,
                    self.emit_query_expr_with_policy(input, reference_policy)
                )
            }
            FormalQueryExpr::Fetch { count, input } => {
                format!(
                    "QExpr_Fetch ({}%nat) ({})",
                    count,
                    self.emit_query_expr_with_policy(input, reference_policy)
                )
            }
        }
    }

    fn emit_grouping_sets(&self, grouping_sets: &[FormalGroupingSet]) -> String {
        let rendered = grouping_sets
            .iter()
            .map(|grouping_set| {
                format!(
                    "({}, {})",
                    self.emit_scalar_select_list(&grouping_set.select),
                    self.emit_scalar_expr_list(&grouping_set.group_by)
                )
            })
            .collect::<Vec<_>>();
        emit_rocq_list_expr(&rendered)
    }

    fn emit_grouping_sets_well_formed_proof(&self, grouping_sets: &[FormalGroupingSet]) -> String {
        let Some((_first, rest)) = grouping_sets.split_first() else {
            return rocq_metadata_proof();
        };
        let rest_proofs = rest
            .iter()
            .map(|_| rocq_conjunction_proof(vec![rocq_metadata_proof(), rocq_metadata_proof()]))
            .collect::<Vec<_>>();
        rocq_focused_subproofs(
            "cbn [query_grouping_sets_well_formed].\nsplit.",
            &[rocq_metadata_proof(), rocq_forall_list_proof(&rest_proofs)],
        )
    }

    fn emit_grouping_sets_admissibility_proof(
        &self,
        grouping_sets: &[FormalGroupingSet],
        allow_select_refs: bool,
    ) -> String {
        let grouping_set_proofs = grouping_sets
            .iter()
            .map(|grouping_set| {
                rocq_conjunction_proof(vec![
                    self.emit_scalar_select_list_admissibility_proof(
                        &grouping_set.select,
                        ScalarPhase::Select,
                        allow_select_refs,
                    ),
                    self.emit_scalar_expr_list_admissibility_proof(
                        &grouping_set.group_by,
                        ScalarPhase::GroupBy,
                    ),
                    rocq_metadata_proof(),
                ])
            })
            .collect::<Vec<_>>();
        rocq_forall_list_proof(&grouping_set_proofs)
    }

    fn emit_sort_keys_in_outputs_proof(&self, keys: &[FormalSortKey]) -> String {
        let key_proofs = keys
            .iter()
            .map(|_| rocq_metadata_proof())
            .collect::<Vec<_>>();
        rocq_focused_subproofs(
            "eapply query_sort_keys_in_outputs.",
            &[rocq_forall_list_proof(&key_proofs)],
        )
    }

    fn emit_window_items_fresh_proof(&self, items: &[FormalWindowItem]) -> String {
        let item_proofs = items
            .iter()
            .map(|_| {
                rocq_focused_subproofs(
                    "eapply query_attribute_not_in_outputs.",
                    &[rocq_closed_nonmembership_proof()],
                )
            })
            .collect::<Vec<_>>();
        rocq_forall_list_proof(&item_proofs)
    }

    fn emit_scalar_expr(&self, expression: &FormalScalarExpr, allow_scalar_refs: bool) -> String {
        if allow_scalar_refs
            && expression.result_kind() == FormalScalarResultKind::Boolean
            && let Some(index) = self
                .scalar_expr_predicates
                .iter()
                .position(|candidate| candidate == expression)
        {
            return format!("scalar_expr_predicate_{index}");
        }

        match expression {
            FormalScalarExpr::Leaf { result_ty, term } => format!(
                "@SExpr_Leaf TNull relname {} ({})",
                emit_rocq_value_type(*result_ty),
                emit_rocq_aggregate_term(term)
            ),
            FormalScalarExpr::Call {
                result_ty,
                operator,
                args,
            } => format!(
                "@SExpr_Call TNull relname {} ({}) ({})",
                emit_rocq_value_type(*result_ty),
                emit_rocq_scalar_operator(*operator),
                self.emit_scalar_expr_list(args)
            ),
            FormalScalarExpr::Case {
                result_ty,
                condition,
                then_expr,
                else_expr,
            } => format!(
                "@SExpr_Case TNull relname {} ({}) ({}) ({})",
                emit_rocq_value_type(*result_ty),
                self.emit_scalar_expr(condition, false),
                self.emit_scalar_expr(then_expr, false),
                self.emit_scalar_expr(else_expr, false)
            ),
            FormalScalarExpr::BooleanValue { expression } => format!(
                "@SExpr_BoolValue TNull relname type_bool NullValues.bool3_to_value_bool ({})",
                self.emit_scalar_expr(expression, false)
            ),
            FormalScalarExpr::ValueBoolean { expression } => format!(
                "@SExpr_ValueBool TNull relname NullValues.value_bool_to_bool3 ({})",
                self.emit_scalar_expr(expression, false)
            ),
            FormalScalarExpr::Predicate { predicate, args } => format!(
                "@SExpr_Pred TNull relname ({} : FTuples.Tuple.predicate TNull) ({})",
                predicate.rocq_constructor(),
                self.emit_scalar_expr_list(args)
            ),
            FormalScalarExpr::And {
                insertion_sites,
                operands,
            } => format!(
                "@SExpr_ConjList TNull relname ({}) And_F ({})",
                self.emit_boolean_insertion_sites(insertion_sites),
                self.emit_scalar_expr_list(operands)
            ),
            FormalScalarExpr::Or {
                insertion_sites,
                operands,
            } => format!(
                "@SExpr_ConjList TNull relname ({}) Or_F ({})",
                self.emit_boolean_insertion_sites(insertion_sites),
                self.emit_scalar_expr_list(operands)
            ),
            FormalScalarExpr::Not { expression } => {
                format!(
                    "@SExpr_Not TNull relname ({})",
                    self.emit_scalar_expr(expression, false)
                )
            }
            FormalScalarExpr::True => "@SExpr_True TNull relname".to_owned(),
            FormalScalarExpr::QuantifiedComparison {
                quantifier,
                predicate,
                args,
                query,
            } => format!(
                "@SExpr_Quant TNull relname {} ({} : FTuples.Tuple.predicate TNull) ({}) ({})",
                emit_rocq_scalar_quantifier(*quantifier),
                predicate.rocq_constructor(),
                self.emit_scalar_expr_list(args),
                self.emit_query_expr(query, false)
            ),
            FormalScalarExpr::In { args, query } => format!(
                "@SExpr_In TNull relname ({}) ({})",
                self.emit_scalar_expr_list(args),
                self.emit_query_expr(query, false)
            ),
            FormalScalarExpr::Exists { query } => {
                format!(
                    "@SExpr_Exists TNull relname ({})",
                    self.emit_query_expr(query, false)
                )
            }
            FormalScalarExpr::Subquery { result_ty, query } => format!(
                "@SExpr_Subquery TNull relname {} ({}) ({})",
                emit_rocq_value_type(*result_ty),
                emit_rocq_value("NULL", Some(*result_ty)),
                self.emit_query_expr(query, false)
            ),
        }
    }

    fn emit_scalar_expr_list(&self, expressions: &[FormalScalarExpr]) -> String {
        emit_rocq_list_expr(
            &expressions
                .iter()
                .map(|expression| self.emit_scalar_expr(expression, false))
                .collect::<Vec<_>>(),
        )
    }

    fn table_sort_certificate_name(&self, relation: &str, columns: &[FormalAttribute]) -> String {
        let index = self
            .table_sorts
            .iter()
            .position(|(candidate_relation, candidate_columns)| {
                candidate_relation == relation && candidate_columns == columns
            })
            .expect("every emitted table has one deterministic sort witness");
        format!("generated_table_sort_{index}")
    }

    fn emit_scalar_select_list(&self, select: &[FormalScalarSelectItem]) -> String {
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("scalar_select_list_{index}"))
            .unwrap_or_else(|| self.emit_scalar_select_list_inline(select))
    }

    fn emit_scalar_select_list_inline(&self, select: &[FormalScalarSelectItem]) -> String {
        emit_rocq_list_expr(
            &select
                .iter()
                .map(|item| {
                    format!(
                        "({}, {})",
                        self.emit_scalar_expr(&item.expr, false),
                        emit_rocq_attribute(item.alias_ty, &item.alias)
                    )
                })
                .collect::<Vec<_>>(),
        )
    }
}

/// Compact skeleton fields cannot contain structural delimiters because the
/// proof-stage parser must distinguish them from child nodes. Preserve every
/// debug-variant token while replacing punctuation used by nested Rust enum
/// formatting (for example `Multiply(Numeric)`) with an inert separator.
fn compact_skeleton_atom(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || matches!(character, '_' | '-' | ' ') {
                character
            } else {
                ':'
            }
        })
        .collect()
}

fn shape_reference(symbol: &str) -> String {
    format!("@{symbol}")
}

fn shape_node(constructor: &str, children: &[String]) -> String {
    shape_node_with_fields(constructor, &[], children)
}

fn shape_node_with_fields(constructor: &str, fields: &[String], children: &[String]) -> String {
    let mut shape = constructor.to_owned();
    if !fields.is_empty() {
        shape.push('{');
        shape.push_str(&fields.join(";"));
        shape.push('}');
    }
    if !children.is_empty() {
        shape.push('(');
        shape.push_str(&children.join(","));
        shape.push(')');
    }
    shape
}

fn push_unique<T: PartialEq>(items: &mut Vec<T>, item: T) {
    if !items.iter().any(|candidate| candidate == &item) {
        items.push(item);
    }
}

fn collect_query_expr_counts(
    query: &FormalQueryExpr,
    counts: &mut HashMap<FormalQueryExpr, usize>,
    order: &mut Vec<FormalQueryExpr>,
) {
    let count = counts.entry(query.clone()).or_insert_with(|| {
        order.push(query.clone());
        0
    });
    *count += 1;

    match query {
        FormalQueryExpr::Set { left, right, .. } | FormalQueryExpr::CrossJoin { left, right } => {
            collect_query_expr_counts(left, counts, order);
            collect_query_expr_counts(right, counts, order);
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
            collect_scalar_expr_query_counts(predicate, counts, order);
            for item in matched_select.iter().chain(left_select).chain(right_select) {
                collect_scalar_expr_query_counts(&item.expr, counts, order);
            }
            collect_query_expr_counts(left, counts, order);
            collect_query_expr_counts(right, counts, order);
        }
        FormalQueryExpr::Projection { select, input } => {
            for item in select {
                collect_scalar_expr_query_counts(&item.expr, counts, order);
            }
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::Selection { predicate, input } => {
            collect_scalar_expr_query_counts(predicate, counts, order);
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::Group {
            select,
            group_by,
            having,
            input,
        } => {
            for item in select {
                collect_scalar_expr_query_counts(&item.expr, counts, order);
            }
            for key in group_by {
                collect_scalar_expr_query_counts(key, counts, order);
            }
            collect_scalar_expr_query_counts(having, counts, order);
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::GroupingSets {
            grouping_sets,
            input,
        } => {
            for grouping_set in grouping_sets {
                for item in &grouping_set.select {
                    collect_scalar_expr_query_counts(&item.expr, counts, order);
                }
                for key in &grouping_set.group_by {
                    collect_scalar_expr_query_counts(key, counts, order);
                }
            }
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::Rank { input, .. } | FormalQueryExpr::Window { input, .. } => {
            collect_query_expr_counts(input, counts, order)
        }
        FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => collect_query_expr_counts(input, counts, order),
        FormalQueryExpr::Error { .. }
        | FormalQueryExpr::Empty { .. }
        | FormalQueryExpr::EmptyTuple
        | FormalQueryExpr::Table { .. } => {}
    }
}

fn collect_scalar_expr_query_counts(
    expression: &FormalScalarExpr,
    counts: &mut HashMap<FormalQueryExpr, usize>,
    order: &mut Vec<FormalQueryExpr>,
) {
    match expression {
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => {}
        FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
            for arg in args {
                collect_scalar_expr_query_counts(arg, counts, order);
            }
        }
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            collect_scalar_expr_query_counts(condition, counts, order);
            collect_scalar_expr_query_counts(then_expr, counts, order);
            collect_scalar_expr_query_counts(else_expr, counts, order);
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => {
            collect_scalar_expr_query_counts(expression, counts, order)
        }
        FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
            for operand in operands {
                collect_scalar_expr_query_counts(operand, counts, order);
            }
        }
        FormalScalarExpr::QuantifiedComparison { args, query, .. }
        | FormalScalarExpr::In { args, query } => {
            for arg in args {
                collect_scalar_expr_query_counts(arg, counts, order);
            }
            collect_query_expr_counts(query, counts, order);
        }
        FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
            collect_query_expr_counts(query, counts, order)
        }
    }
}

fn scalar_select_list_contains_list(
    container: &[FormalScalarSelectItem],
    needle: &[FormalScalarSelectItem],
) -> bool {
    container
        .iter()
        .any(|item| scalar_expr_contains_scalar_select_list(&item.expr, needle))
}

fn scalar_expr_contains_scalar_select_list(
    expression: &FormalScalarExpr,
    needle: &[FormalScalarSelectItem],
) -> bool {
    match expression {
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => false,
        FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => args
            .iter()
            .any(|argument| scalar_expr_contains_scalar_select_list(argument, needle)),
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            scalar_expr_contains_scalar_select_list(condition, needle)
                || scalar_expr_contains_scalar_select_list(then_expr, needle)
                || scalar_expr_contains_scalar_select_list(else_expr, needle)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => {
            scalar_expr_contains_scalar_select_list(expression, needle)
        }
        FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => operands
            .iter()
            .any(|operand| scalar_expr_contains_scalar_select_list(operand, needle)),
        FormalScalarExpr::QuantifiedComparison { args, query, .. }
        | FormalScalarExpr::In { args, query } => {
            args.iter()
                .any(|argument| scalar_expr_contains_scalar_select_list(argument, needle))
                || query_expr_contains_scalar_select_list(query, needle)
        }
        FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
            query_expr_contains_scalar_select_list(query, needle)
        }
    }
}

fn query_expr_contains_scalar_select_list(
    query: &FormalQueryExpr,
    needle: &[FormalScalarSelectItem],
) -> bool {
    match query {
        FormalQueryExpr::Error { .. }
        | FormalQueryExpr::Empty { .. }
        | FormalQueryExpr::EmptyTuple
        | FormalQueryExpr::Table { .. } => false,
        FormalQueryExpr::Set { left, right, .. } | FormalQueryExpr::CrossJoin { left, right } => {
            query_expr_contains_scalar_select_list(left, needle)
                || query_expr_contains_scalar_select_list(right, needle)
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
            scalar_expr_contains_scalar_select_list(predicate, needle)
                || [matched_select, left_select, right_select]
                    .into_iter()
                    .any(|select| {
                        select == needle || scalar_select_list_contains_list(select, needle)
                    })
                || query_expr_contains_scalar_select_list(left, needle)
                || query_expr_contains_scalar_select_list(right, needle)
        }
        FormalQueryExpr::Projection { select, input } => {
            select == needle
                || scalar_select_list_contains_list(select, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::Selection { predicate, input } => {
            scalar_expr_contains_scalar_select_list(predicate, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::Group {
            select,
            group_by,
            having,
            input,
        } => {
            select == needle
                || scalar_select_list_contains_list(select, needle)
                || group_by
                    .iter()
                    .any(|key| scalar_expr_contains_scalar_select_list(key, needle))
                || scalar_expr_contains_scalar_select_list(having, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::GroupingSets {
            grouping_sets,
            input,
        } => {
            grouping_sets.iter().any(|grouping_set| {
                grouping_set.select == needle
                    || scalar_select_list_contains_list(&grouping_set.select, needle)
                    || grouping_set
                        .group_by
                        .iter()
                        .any(|key| scalar_expr_contains_scalar_select_list(key, needle))
            }) || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::Rank { input, .. }
        | FormalQueryExpr::Window { input, .. }
        | FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => {
            query_expr_contains_scalar_select_list(input, needle)
        }
    }
}

fn select_shared_query_exprs(
    query_order: Vec<FormalQueryExpr>,
    query_counts: &HashMap<FormalQueryExpr, usize>,
) -> Vec<FormalQueryExpr> {
    let candidates = query_order
        .into_iter()
        .filter(|query| {
            query_counts.get(query).copied().unwrap_or_default() > 1
                && !matches!(
                    query,
                    FormalQueryExpr::Error { .. }
                        | FormalQueryExpr::Empty { .. }
                        | FormalQueryExpr::EmptyTuple
                        | FormalQueryExpr::Table { .. }
                )
        })
        .collect::<Vec<_>>();

    candidates
        .iter()
        .filter(|query| {
            let total = query_counts.get(*query).copied().unwrap_or_default();
            let covered_by_larger_shared_queries = candidates
                .iter()
                .filter(|container| *container != *query)
                .map(|container| {
                    query_counts.get(container).copied().unwrap_or_default()
                        * proper_query_expr_subquery_occurrences(container, query)
                })
                .sum::<usize>();
            total > covered_by_larger_shared_queries
        })
        .cloned()
        .collect()
}

fn proper_query_expr_subquery_occurrences(
    container: &FormalQueryExpr,
    needle: &FormalQueryExpr,
) -> usize {
    match container {
        FormalQueryExpr::Set { left, right, .. } | FormalQueryExpr::CrossJoin { left, right } => {
            query_expr_occurrences(left, needle) + query_expr_occurrences(right, needle)
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
            query_expr_occurrences(left, needle)
                + query_expr_occurrences(right, needle)
                + scalar_expr_query_occurrences(predicate, needle)
                + matched_select
                    .iter()
                    .chain(left_select)
                    .chain(right_select)
                    .map(|item| scalar_expr_query_occurrences(&item.expr, needle))
                    .sum::<usize>()
        }
        FormalQueryExpr::Projection { select, input } => {
            query_expr_occurrences(input, needle)
                + select
                    .iter()
                    .map(|item| scalar_expr_query_occurrences(&item.expr, needle))
                    .sum::<usize>()
        }
        FormalQueryExpr::Selection { predicate, input } => {
            query_expr_occurrences(input, needle) + scalar_expr_query_occurrences(predicate, needle)
        }
        FormalQueryExpr::Group {
            select,
            group_by,
            having,
            input,
        } => {
            query_expr_occurrences(input, needle)
                + scalar_expr_query_occurrences(having, needle)
                + group_by
                    .iter()
                    .map(|key| scalar_expr_query_occurrences(key, needle))
                    .sum::<usize>()
                + select
                    .iter()
                    .map(|item| scalar_expr_query_occurrences(&item.expr, needle))
                    .sum::<usize>()
        }
        FormalQueryExpr::GroupingSets {
            grouping_sets,
            input,
        } => {
            query_expr_occurrences(input, needle)
                + grouping_sets
                    .iter()
                    .map(|grouping_set| {
                        grouping_set
                            .select
                            .iter()
                            .map(|item| scalar_expr_query_occurrences(&item.expr, needle))
                            .sum::<usize>()
                            + grouping_set
                                .group_by
                                .iter()
                                .map(|key| scalar_expr_query_occurrences(key, needle))
                                .sum::<usize>()
                    })
                    .sum::<usize>()
        }
        FormalQueryExpr::Rank { input, .. } | FormalQueryExpr::Window { input, .. } => {
            query_expr_occurrences(input, needle)
        }
        FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => query_expr_occurrences(input, needle),
        FormalQueryExpr::Error { .. }
        | FormalQueryExpr::Empty { .. }
        | FormalQueryExpr::EmptyTuple
        | FormalQueryExpr::Table { .. } => 0,
    }
}

fn query_expr_occurrences(query: &FormalQueryExpr, needle: &FormalQueryExpr) -> usize {
    usize::from(query == needle) + proper_query_expr_subquery_occurrences(query, needle)
}

fn scalar_expr_query_occurrences(expression: &FormalScalarExpr, needle: &FormalQueryExpr) -> usize {
    match expression {
        FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => 0,
        FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => args
            .iter()
            .map(|arg| scalar_expr_query_occurrences(arg, needle))
            .sum(),
        FormalScalarExpr::Case {
            condition,
            then_expr,
            else_expr,
            ..
        } => {
            scalar_expr_query_occurrences(condition, needle)
                + scalar_expr_query_occurrences(then_expr, needle)
                + scalar_expr_query_occurrences(else_expr, needle)
        }
        FormalScalarExpr::BooleanValue { expression }
        | FormalScalarExpr::ValueBoolean { expression }
        | FormalScalarExpr::Not { expression } => scalar_expr_query_occurrences(expression, needle),
        FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => operands
            .iter()
            .map(|operand| scalar_expr_query_occurrences(operand, needle))
            .sum(),
        FormalScalarExpr::QuantifiedComparison { args, query, .. }
        | FormalScalarExpr::In { args, query } => {
            query_expr_occurrences(query, needle)
                + args
                    .iter()
                    .map(|arg| scalar_expr_query_occurrences(arg, needle))
                    .sum::<usize>()
        }
        FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => {
            query_expr_occurrences(query, needle)
        }
    }
}

fn emit_rocq_set_op(op: FormalSetOp) -> &'static str {
    match op {
        FormalSetOp::Union => "Union",
        FormalSetOp::Inter => "Inter",
        FormalSetOp::Diff => "Diff",
    }
}

fn emit_rocq_scalar_quantifier(quantifier: FormalScalarQuantifier) -> &'static str {
    match quantifier {
        FormalScalarQuantifier::Forall => "Forall_F",
        FormalScalarQuantifier::Exists => "Exists_F",
    }
}

fn emit_rocq_value_type(ty: FormalAttributeType) -> &'static str {
    match ty {
        FormalAttributeType::String { .. } => "type_string",
        FormalAttributeType::Z => "type_Z",
        FormalAttributeType::Int32 => "type_int32",
        FormalAttributeType::Int64 => "type_int64",
        FormalAttributeType::Bool => "type_bool",
        FormalAttributeType::Float => "type_float",
        FormalAttributeType::Double => "type_double",
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. } => "type_numeric",
        FormalAttributeType::Date => "type_date",
        FormalAttributeType::Time => "type_time",
        FormalAttributeType::Timestamp { .. } => "type_timestamp",
        FormalAttributeType::Timestamptz { .. } => "type_timestamptz",
    }
}

fn emit_rocq_query_join_kind(kind: FormalQueryJoinKind) -> &'static str {
    match kind {
        FormalQueryJoinKind::Left => "QueryJoinLeft",
        FormalQueryJoinKind::Right => "QueryJoinRight",
        FormalQueryJoinKind::Full => "QueryJoinFull",
        FormalQueryJoinKind::Semi => "QueryJoinSemi",
        FormalQueryJoinKind::Anti => "QueryJoinAnti",
    }
}

fn emit_rocq_query_error(error: FormalQueryError) -> &'static str {
    match error {
        FormalQueryError::AmbiguousColumn => "AmbiguousColumn",
        FormalQueryError::UndefinedColumn => "UndefinedColumn",
        FormalQueryError::UndefinedFunction => "UndefinedFunction",
        FormalQueryError::InvalidTextRepresentation => "DataException InvalidTextRepresentation",
    }
}

fn emit_rocq_sort_key(key: &FormalSortKey) -> String {
    format!(
        "{} ({})",
        emit_rocq_sort_key_constructor(key.direction, key.null_direction),
        emit_rocq_attribute(key.attribute_ty, &key.attribute_name)
    )
}

fn emit_rocq_window_item(item: &FormalWindowItem) -> String {
    let output = emit_rocq_attribute(item.output.ty, &item.output.name);
    match &item.function {
        FormalWindowFunction::RowNumber => format!("WindowRowNumberItem ({output})"),
        FormalWindowFunction::Aggregate { term } => format!(
            "WindowAggregateItem ({output}) ({})",
            emit_rocq_aggregate_term(term)
        ),
        FormalWindowFunction::FullPartitionAggregate { term } => format!(
            "WindowFullPartitionAggregateItem ({output}) ({})",
            emit_rocq_aggregate_term(term)
        ),
    }
}

fn emit_rocq_sort_key_constructor(
    direction: FormalSortDirection,
    null_direction: FormalNullDirection,
) -> &'static str {
    match (direction, null_direction) {
        (FormalSortDirection::Asc, FormalNullDirection::First) => "SortAscNullsFirst",
        (FormalSortDirection::Asc, FormalNullDirection::Last) => "SortAscNullsLast",
        (FormalSortDirection::Desc, FormalNullDirection::First) => "SortDescNullsFirst",
        (FormalSortDirection::Desc, FormalNullDirection::Last) => "SortDescNullsLast",
    }
}

fn emit_rocq_aggregate_term(term: &FormalAggregateTerm) -> String {
    match term {
        FormalAggregateTerm::Expr { term } => match term {
            FormalFunctionTerm::Attribute { name, ty } => {
                if let Some(dot_constructor) = dot_constructor(*ty) {
                    emit_rocq_named_helper(dot_constructor, name, *ty)
                } else {
                    format!("AExpr ({})", emit_rocq_function_term(term))
                }
            }
            FormalFunctionTerm::Constant { raw, ty } => emit_rocq_constant_aggregate(raw, *ty),
            _ => format!("AExpr ({})", emit_rocq_function_term(term)),
        },
        FormalAggregateTerm::Aggregate {
            function,
            quantifier,
            arg,
        } => format!(
            "AAggregate {} {} ({})",
            emit_rocq_aggregate_function(*function),
            emit_rocq_aggregate_quantifier(*quantifier),
            emit_rocq_function_term(arg)
        ),
        FormalAggregateTerm::CountStar => "ACountStar".to_owned(),
        FormalAggregateTerm::ScalarCall { operator, args } => format!(
            "AScalarCall ({}) ({})",
            emit_rocq_scalar_operator(*operator),
            emit_rocq_list(args, emit_rocq_aggregate_term)
        ),
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => format!(
            "AScalarCall ScalarCase ({})",
            emit_rocq_list(
                &case_function_args(branches, else_expr),
                emit_rocq_aggregate_term
            )
        ),
    }
}

fn emit_rocq_aggregate_quantifier(quantifier: FormalAggregateQuantifier) -> &'static str {
    match quantifier {
        FormalAggregateQuantifier::All => "AggregateAll",
        FormalAggregateQuantifier::Distinct => "AggregateDistinct",
    }
}

fn emit_rocq_aggregate_function(function: FormalAggregateFunction) -> String {
    let constructor = match function {
        FormalAggregateFunction::Count => "AggregateCount",
        FormalAggregateFunction::SumZ => "AggregateSumZ",
        FormalAggregateFunction::SumInt32 => "AggregateSumInt32",
        FormalAggregateFunction::SumInt64Numeric => "AggregateSumInt64Numeric",
        FormalAggregateFunction::SumFloat => "AggregateSumFloat",
        FormalAggregateFunction::SumDouble => "AggregateSumDouble",
        FormalAggregateFunction::SumNumeric => "AggregateSumNumeric",
        FormalAggregateFunction::BitAndInt32 => "AggregateBitAndInt32",
        FormalAggregateFunction::BitOrInt32 => "AggregateBitOrInt32",
        FormalAggregateFunction::BitAndInt64 => "AggregateBitAndInt64",
        FormalAggregateFunction::BitOrInt64 => "AggregateBitOrInt64",
        FormalAggregateFunction::MaxZ => "AggregateMaxZ",
        FormalAggregateFunction::MaxInt32 => "AggregateMaxInt32",
        FormalAggregateFunction::MaxInt64 => "AggregateMaxInt64",
        FormalAggregateFunction::MaxFloat => "AggregateMaxFloat",
        FormalAggregateFunction::MaxDouble => "AggregateMaxDouble",
        FormalAggregateFunction::MaxNumeric => "AggregateMaxNumeric",
        FormalAggregateFunction::MaxString => "AggregateMaxString",
        FormalAggregateFunction::MinZ => "AggregateMinZ",
        FormalAggregateFunction::MinInt32 => "AggregateMinInt32",
        FormalAggregateFunction::MinInt64 => "AggregateMinInt64",
        FormalAggregateFunction::MinFloat => "AggregateMinFloat",
        FormalAggregateFunction::MinDouble => "AggregateMinDouble",
        FormalAggregateFunction::MinNumeric => "AggregateMinNumeric",
        FormalAggregateFunction::SingleValueInt32 => "AggregateSingleValueInt32",
        FormalAggregateFunction::AverageZ => "AggregateAverageZ",
        FormalAggregateFunction::AverageInt32Numeric => "AggregateAverageInt32Numeric",
        FormalAggregateFunction::NumericDisplayScale(aggregate) => {
            let aggregate = match aggregate {
                FormalNumericAggregate::AverageInt32 => "NumericAverageInt32",
                FormalNumericAggregate::StddevSampleInt32 => "NumericStddevSampleInt32",
            };
            return format!("(AggregateNumericDisplayScale {aggregate})");
        }
        FormalAggregateFunction::AverageInt64Numeric => "AggregateAverageInt64Numeric",
        FormalAggregateFunction::VariancePopulationInt32 => "AggregateVariancePopulationInt32",
        FormalAggregateFunction::VarianceSampleInt32 => "AggregateVarianceSampleInt32",
        FormalAggregateFunction::StddevPopulationInt32 => "AggregateStddevPopulationInt32",
        FormalAggregateFunction::StddevSampleInt32 => "AggregateStddevSampleInt32",
        FormalAggregateFunction::StddevSampleNumericFixed { precision, scale } => {
            return format!("(AggregateStddevSampleNumericFixed ({precision})%Z ({scale})%Z)");
        }
        FormalAggregateFunction::AverageFloat => "AggregateAverageFloat",
        FormalAggregateFunction::AverageDouble => "AggregateAverageDouble",
        FormalAggregateFunction::AverageNumericFixed { precision, scale } => {
            return format!("(AggregateAverageNumericFixed ({precision})%Z ({scale})%Z)");
        }
        FormalAggregateFunction::AverageNumericAtScale { scale } => {
            return format!("(AggregateAverageNumericAtScale ({scale})%Z)");
        }
    };
    constructor.to_owned()
}

fn case_function_args(
    branches: &[FormalCaseBranch],
    else_expr: &FormalAggregateTerm,
) -> Vec<FormalAggregateTerm> {
    let mut args = Vec::with_capacity(branches.len() * 2 + 1);
    for branch in branches {
        args.push(branch.when.clone());
        args.push(branch.then_expr.clone());
    }
    args.push(else_expr.clone());
    args
}

fn emit_rocq_function_term(term: &FormalFunctionTerm) -> String {
    match term {
        FormalFunctionTerm::Constant { raw, ty } => emit_rocq_constant_function(raw, *ty),
        FormalFunctionTerm::Attribute { name, ty } => {
            format!("Dot ({})", emit_rocq_attribute(*ty, name))
        }
        FormalFunctionTerm::ScalarCall { operator, args } => format!(
            "ScalarCall ({}) ({})",
            emit_rocq_scalar_operator(*operator),
            emit_rocq_list(args, emit_rocq_function_term)
        ),
    }
}

fn emit_rocq_constraint_integer_value(
    raw: &str,
    ty: Option<FormalAttributeType>,
) -> Option<String> {
    let trimmed = raw.trim();
    if !is_integer_literal(trimmed) {
        return None;
    }
    match ty {
        Some(FormalAttributeType::Int32) => Some(format!(
            "Value_int32 (Some (Int32 ({trimmed})%Z ltac:(unfold int32_min, int32_max; lia)))"
        )),
        Some(FormalAttributeType::Int64) => Some(format!(
            "Value_int64 (Some (Int64 ({trimmed})%Z ltac:(unfold int64_min, int64_max; lia)))"
        )),
        _ => None,
    }
}

// Schema constraints have already passed Rust-side literal range validation.
// Emit their fixed-width integer constants with an explicit payload proof so
// closed witness reflection never has to reduce the proof-driven
// [int32_checked]/[int64_checked] constructors.
fn emit_rocq_constraint_function_term(term: &FormalFunctionTerm) -> String {
    match term {
        FormalFunctionTerm::Constant { raw, ty } => {
            if let Some(value) = emit_rocq_constraint_integer_value(raw, *ty) {
                format!("Constant ({value})")
            } else {
                emit_rocq_constant_function(raw, *ty)
            }
        }
        FormalFunctionTerm::Attribute { name, ty } => {
            format!("Dot ({})", emit_rocq_attribute(*ty, name))
        }
        FormalFunctionTerm::ScalarCall { operator, args } => format!(
            "ScalarCall ({}) ({})",
            emit_rocq_scalar_operator(*operator),
            emit_rocq_list(args, emit_rocq_constraint_function_term)
        ),
    }
}

fn emit_rocq_constraint_aggregate_term(term: &FormalAggregateTerm) -> String {
    match term {
        FormalAggregateTerm::Expr { term } => match term {
            FormalFunctionTerm::Attribute { name, ty } => {
                if let Some(dot_constructor) = dot_constructor(*ty) {
                    emit_rocq_named_helper(dot_constructor, name, *ty)
                } else {
                    format!("AExpr ({})", emit_rocq_constraint_function_term(term))
                }
            }
            _ => format!("AExpr ({})", emit_rocq_constraint_function_term(term)),
        },
        FormalAggregateTerm::Aggregate {
            function,
            quantifier,
            arg,
        } => format!(
            "AAggregate {} {} ({})",
            emit_rocq_aggregate_function(*function),
            emit_rocq_aggregate_quantifier(*quantifier),
            emit_rocq_constraint_function_term(arg)
        ),
        FormalAggregateTerm::CountStar => "ACountStar".to_owned(),
        FormalAggregateTerm::ScalarCall { operator, args } => format!(
            "AScalarCall ({}) ({})",
            emit_rocq_scalar_operator(*operator),
            emit_rocq_list(args, emit_rocq_constraint_aggregate_term)
        ),
        FormalAggregateTerm::Case {
            branches,
            else_expr,
        } => format!(
            "AScalarCall ScalarCase ({})",
            emit_rocq_list(
                &case_function_args(branches, else_expr),
                emit_rocq_constraint_aggregate_term
            )
        ),
    }
}

fn emit_rocq_scalar_operator(operator: ScalarOperator) -> String {
    match operator {
        ScalarOperator::PredicateValue(predicate) => {
            format!("ScalarPredicateValue {}", predicate.rocq_constructor())
        }
        ScalarOperator::Boolean(ScalarBooleanOperator::And) => "ScalarBoolean ScalarAnd".to_owned(),
        ScalarOperator::Boolean(ScalarBooleanOperator::Or) => "ScalarBoolean ScalarOr".to_owned(),
        ScalarOperator::Boolean(ScalarBooleanOperator::Not) => "ScalarBoolean ScalarNot".to_owned(),
        ScalarOperator::Case => "ScalarCase".to_owned(),
        ScalarOperator::StringCase(ScalarStringCase::Upper) => {
            "ScalarStringCase ScalarUpper".to_owned()
        }
        ScalarOperator::StringCase(ScalarStringCase::Lower) => {
            "ScalarStringCase ScalarLower".to_owned()
        }
        ScalarOperator::ExtractDate(ScalarDatePart::Year) => {
            "ScalarExtractDate ScalarYear".to_owned()
        }
        ScalarOperator::ExtractDate(ScalarDatePart::Month) => {
            "ScalarExtractDate ScalarMonth".to_owned()
        }
        ScalarOperator::Cast(cast) => emit_rocq_scalar_cast(cast),
        ScalarOperator::Add(kind) => {
            format!("ScalarAdd Scalar{}", rocq_scalar_numeric_kind_suffix(kind))
        }
        ScalarOperator::Subtract(kind) => {
            format!(
                "ScalarSubtract Scalar{}",
                rocq_scalar_numeric_kind_suffix(kind)
            )
        }
        ScalarOperator::Multiply(kind) => {
            format!(
                "ScalarMultiply Scalar{}",
                rocq_scalar_numeric_kind_suffix(kind)
            )
        }
        ScalarOperator::Divide(kind) => format!(
            "ScalarDivide Scalar{}",
            rocq_scalar_numeric_kind_suffix(kind)
        ),
        ScalarOperator::Negate(kind) => {
            format!(
                "ScalarNegate Scalar{}",
                rocq_scalar_numeric_kind_suffix(kind)
            )
        }
        ScalarOperator::NumericDivideResultScale => "ScalarNumericDivideResultScale".to_owned(),
        ScalarOperator::NumericDivideTypmod => "ScalarNumericDivideTypmod".to_owned(),
        ScalarOperator::PowerHalfInt64ToInt32 => "ScalarPowerHalfInt64ToInt32".to_owned(),
        ScalarOperator::StringConcat => "ScalarStringConcat".to_owned(),
        ScalarOperator::SubstringNonnegative => "ScalarSubstringNonnegative".to_owned(),
        ScalarOperator::TimestampAdd(unit) => format!(
            "ScalarTimestampAdd {}",
            match unit {
                ScalarTimestampUnit::Microsecond => "ScalarTimestampMicrosecond",
                ScalarTimestampUnit::Second => "ScalarTimestampSecond",
                ScalarTimestampUnit::Minute => "ScalarTimestampMinute",
                ScalarTimestampUnit::Hour => "ScalarTimestampHour",
                ScalarTimestampUnit::Day => "ScalarTimestampDay",
                ScalarTimestampUnit::Month => "ScalarTimestampMonth",
                ScalarTimestampUnit::Year => "ScalarTimestampYear",
            }
        ),
    }
}

fn rocq_scalar_numeric_kind_suffix(kind: ScalarNumericKind) -> &'static str {
    match kind {
        ScalarNumericKind::Int32 => "Int32",
        ScalarNumericKind::Int64 => "Int64",
        ScalarNumericKind::Float => "Float",
        ScalarNumericKind::Double => "Double",
        ScalarNumericKind::Numeric => "Numeric",
    }
}

fn emit_rocq_scalar_cast(cast: ScalarCast) -> String {
    match cast {
        ScalarCast::Identity => "ScalarCast ScalarCastIdentity".to_owned(),
        ScalarCast::ToNumeric(source) => format!(
            "ScalarCast (ScalarCastToNumeric {})",
            emit_rocq_scalar_numeric_source(source)
        ),
        ScalarCast::ToNumericTypmod(source) => format!(
            "ScalarCast (ScalarCastToNumericTypmod {})",
            emit_rocq_scalar_numeric_source(source)
        ),
        ScalarCast::Int32ToDouble => "ScalarCast ScalarCastInt32ToDouble".to_owned(),
        ScalarCast::Int32ToInt64 => "ScalarCast ScalarCastInt32ToInt64".to_owned(),
        ScalarCast::Int64ToInt32 => "ScalarCast ScalarCastInt64ToInt32".to_owned(),
        ScalarCast::NumericToInt32 => "ScalarCast ScalarCastNumericToInt32".to_owned(),
        ScalarCast::StringToInt32 => "ScalarCast ScalarCastStringToInt32".to_owned(),
        ScalarCast::StringToInt64 => "ScalarCast ScalarCastStringToInt64".to_owned(),
        ScalarCast::DateToTimestamp => "ScalarCast ScalarCastDateToTimestamp".to_owned(),
        ScalarCast::TimestampToDate => "ScalarCast ScalarCastTimestampToDate".to_owned(),
        ScalarCast::StringExplicit => "ScalarCast ScalarCastStringExplicit".to_owned(),
        ScalarCast::StringImplicit => "ScalarCast ScalarCoerceStringImplicit".to_owned(),
    }
}

fn emit_rocq_scalar_numeric_source(source: ScalarNumericSource) -> &'static str {
    match source {
        ScalarNumericSource::Z => "ScalarSourceZ",
        ScalarNumericSource::Int32 => "ScalarSourceInt32",
        ScalarNumericSource::Int64 => "ScalarSourceInt64",
        ScalarNumericSource::Numeric => "ScalarSourceNumeric",
    }
}

fn emit_rocq_constraint_formula(formula: &FormalConstraintFormula) -> String {
    match formula {
        FormalConstraintFormula::True => "@Sql_True TNull constraint_query".to_owned(),
        FormalConstraintFormula::False => {
            "@Sql_Not TNull constraint_query (@Sql_True TNull constraint_query)".to_owned()
        }
        FormalConstraintFormula::Predicate { predicate, args } => format!(
            "@Sql_Pred TNull constraint_query {} ({})",
            predicate.rocq_constructor(),
            emit_rocq_list(args, emit_rocq_constraint_aggregate_term)
        ),
        FormalConstraintFormula::And { left, right } => emit_rocq_call(
            "@Sql_Conj TNull constraint_query And_F",
            &[
                emit_rocq_constraint_formula(left),
                emit_rocq_constraint_formula(right),
            ],
        ),
        FormalConstraintFormula::Or { left, right } => emit_rocq_call(
            "@Sql_Conj TNull constraint_query Or_F",
            &[
                emit_rocq_constraint_formula(left),
                emit_rocq_constraint_formula(right),
            ],
        ),
        FormalConstraintFormula::Not { formula } => {
            format!(
                "@Sql_Not TNull constraint_query ({})",
                emit_rocq_constraint_formula(formula)
            )
        }
    }
}

fn emit_rocq_call(function: &str, args: &[String]) -> String {
    let single_line = format!(
        "{} {}",
        function,
        args.iter()
            .map(|arg| format!("({arg})"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    if single_line.len() <= 72 && !args.iter().any(|arg| arg.contains('\n')) {
        return single_line;
    }

    let mut lines = vec![function.to_owned()];
    for arg in args {
        lines.push(format!("  ({})", indent_rocq_expr(arg, 2).trim_start()));
    }
    lines.join("\n")
}

fn emit_rocq_attribute(ty: FormalAttributeType, name: &str) -> String {
    let helper = match ty {
        FormalAttributeType::Z => "AttrZ",
        FormalAttributeType::Int32 => "AttrInt32",
        FormalAttributeType::Int64 => "AttrInt64",
        FormalAttributeType::String { .. } => "AttrString",
        FormalAttributeType::Bool => "AttrBool",
        FormalAttributeType::Float => "AttrFloat",
        FormalAttributeType::Double => "AttrDouble",
        FormalAttributeType::Numeric => "AttrNumeric",
        FormalAttributeType::Decimal { .. } => "AttrDecimal",
        FormalAttributeType::Date => "AttrDate",
        FormalAttributeType::Time => "AttrTime",
        FormalAttributeType::Timestamp { .. } => "AttrTimestamp",
        FormalAttributeType::Timestamptz { .. } => "AttrTimestamptz",
    };
    emit_rocq_named_helper(helper, name, ty)
}

fn emit_rocq_query_attribute_list(attributes: &[FormalAttribute]) -> String {
    let rendered = attributes
        .iter()
        .map(|attribute| emit_rocq_attribute(attribute.ty, &attribute.name))
        .collect::<Vec<_>>();
    emit_rocq_list_expr(&rendered)
}

fn emit_rocq_schema_attribute(ty: FormalAttributeType, name: &str) -> String {
    match ty {
        FormalAttributeType::Z => format!("Attr_Z {}", rocq_string_literal(name)),
        FormalAttributeType::Int32 => format!("Attr_int32 {}", rocq_string_literal(name)),
        FormalAttributeType::Int64 => format!("Attr_int64 {}", rocq_string_literal(name)),
        FormalAttributeType::String { typmod } => format!(
            "Attr_string {} {}",
            rocq_string_literal(name),
            emit_rocq_string_typmod(typmod)
        ),
        FormalAttributeType::Bool => format!("Attr_bool {}", rocq_string_literal(name)),
        FormalAttributeType::Float => format!("Attr_float {}", rocq_string_literal(name)),
        FormalAttributeType::Double => format!("Attr_double {}", rocq_string_literal(name)),
        FormalAttributeType::Numeric => format!("Attr_numeric {}", rocq_string_literal(name)),
        FormalAttributeType::Decimal { precision, scale } => {
            format!(
                "Attr_decimal {} {precision} {scale}",
                rocq_string_literal(name)
            )
        }
        FormalAttributeType::Date => format!("Attr_date {}", rocq_string_literal(name)),
        FormalAttributeType::Time => format!("Attr_time {}", rocq_string_literal(name)),
        FormalAttributeType::Timestamp { precision } => format!(
            "Attr_timestamp {} {}",
            rocq_string_literal(name),
            timestamp_precision(precision)
        ),
        FormalAttributeType::Timestamptz { precision } => format!(
            "Attr_timestamptz {} {}",
            rocq_string_literal(name),
            timestamp_precision(precision)
        ),
    }
}

fn emit_rocq_string_typmod(typmod: SqlStringType) -> String {
    match typmod {
        SqlStringType::Text => "StringText".to_owned(),
        SqlStringType::Varchar { length: None } => "StringVarchar".to_owned(),
        SqlStringType::Varchar {
            length: Some(length),
        } => format!("(StringVarcharN {length})"),
        SqlStringType::Char { length } => format!("(StringChar {length})"),
        SqlStringType::Bpchar => "StringBpchar".to_owned(),
    }
}

fn emit_rocq_named_helper(helper: &str, name: &str, ty: FormalAttributeType) -> String {
    match ty {
        FormalAttributeType::String { typmod } => format!(
            "{helper} {} {}",
            rocq_string_literal(name),
            emit_rocq_string_typmod(typmod)
        ),
        FormalAttributeType::Decimal { precision, scale } => {
            format!("{helper} {} {precision} {scale}", rocq_string_literal(name))
        }
        FormalAttributeType::Timestamp { precision }
        | FormalAttributeType::Timestamptz { precision } => {
            format!(
                "{helper} {} {}",
                rocq_string_literal(name),
                timestamp_precision(precision)
            )
        }
        _ => format!("{helper} {}", rocq_string_literal(name)),
    }
}

fn dot_constructor(attribute_ty: FormalAttributeType) -> Option<&'static str> {
    match attribute_ty {
        FormalAttributeType::Z => Some("DotZ"),
        FormalAttributeType::Int32 => Some("DotInt32"),
        FormalAttributeType::Int64 => Some("DotInt64"),
        FormalAttributeType::String { .. } => Some("DotString"),
        FormalAttributeType::Bool => Some("DotBool"),
        FormalAttributeType::Float => Some("DotFloat"),
        FormalAttributeType::Double => Some("DotDouble"),
        FormalAttributeType::Numeric => Some("DotNumeric"),
        FormalAttributeType::Decimal { .. } => Some("DotDecimal"),
        FormalAttributeType::Date => Some("DotDate"),
        FormalAttributeType::Time => Some("DotTime"),
        FormalAttributeType::Timestamp { .. } => Some("DotTimestamp"),
        FormalAttributeType::Timestamptz { .. } => Some("DotTimestamptz"),
    }
}

fn emit_rocq_constant_aggregate(raw: &str, ty: Option<FormalAttributeType>) -> String {
    let trimmed = raw.trim();
    if trimmed.eq_ignore_ascii_case("null") {
        return match ty {
            Some(FormalAttributeType::Z) => "NullZ".to_owned(),
            Some(FormalAttributeType::Int32) => "NullInt32".to_owned(),
            Some(FormalAttributeType::Int64) => "NullInt64".to_owned(),
            Some(FormalAttributeType::String { typmod }) => {
                format!("NullString {}", emit_rocq_string_typmod(typmod))
            }
            None => "NullString StringText".to_owned(),
            Some(FormalAttributeType::Bool) => "NullBool".to_owned(),
            Some(FormalAttributeType::Float) => "NullFloat".to_owned(),
            Some(FormalAttributeType::Double) => "NullDouble".to_owned(),
            Some(FormalAttributeType::Numeric) => "NullNumeric".to_owned(),
            Some(FormalAttributeType::Decimal { .. }) => "NullDecimal".to_owned(),
            Some(FormalAttributeType::Date) => "NullDate".to_owned(),
            Some(FormalAttributeType::Time) => "NullTime".to_owned(),
            Some(FormalAttributeType::Timestamp { .. }) => "NullTimestamp".to_owned(),
            Some(FormalAttributeType::Timestamptz { .. }) => "NullTimestamptz".to_owned(),
        };
    }
    if trimmed.eq_ignore_ascii_case("true") {
        return "CstBool true".to_owned();
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return "CstBool false".to_owned();
    }
    if let Some(bits) = float_literal_bits_for_type(trimmed, ty.as_ref()) {
        return match ty {
            Some(FormalAttributeType::Float) => format!("CstFloatBits ({bits})"),
            Some(FormalAttributeType::Double) => format!("CstDoubleBits ({bits})"),
            _ => unreachable!("float_literal_bits_for_type only accepts FLOAT/DOUBLE"),
        };
    }
    if matches!(ty, Some(FormalAttributeType::Date))
        && let Some(days) = parse_date_literal(trimmed)
    {
        return format!("CstDate ({days})");
    }
    if matches!(ty, Some(FormalAttributeType::Time))
        && let Some(micros) = parse_time_literal(trimmed)
    {
        return format!("CstTime ({micros})");
    }
    if let Some(FormalAttributeType::Timestamp { precision }) = ty
        && let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision))
    {
        return format!("CstTimestamp ({micros})");
    }
    if let Some(FormalAttributeType::Timestamptz { precision }) = ty
        && let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision))
    {
        return format!("CstTimestamptz ({micros})");
    }
    if matches!(ty, Some(FormalAttributeType::Numeric)) {
        if let Some((coeff, scale)) = parse_decimal_literal(trimmed) {
            return format!("CstNumeric ({coeff}) ({scale})");
        }
        panic!("unsupported NUMERIC aggregate literal reached Rocq emitter: {trimmed}");
    }
    if matches!(ty, Some(FormalAttributeType::Decimal { .. })) {
        if let Some((coeff, precision, scale)) = decimal_literal_for_type(trimmed, ty.as_ref()) {
            return format!("CstDecimal ({precision}) ({scale}) ({coeff})");
        }
        panic!("unsupported DECIMAL aggregate literal reached Rocq emitter: {trimmed}");
    }
    if matches!(ty, Some(FormalAttributeType::Int32)) && is_integer_literal(trimmed) {
        return format!("CstInt32 ({trimmed})");
    }
    if matches!(ty, Some(FormalAttributeType::Int64)) && is_integer_literal(trimmed) {
        return format!("CstInt64 ({trimmed})");
    }
    if let Some(unquoted) = sql_string_literal_content(trimmed) {
        return format!(
            "CstString {} {}",
            emit_rocq_string_typmod(string_typmod_or_text(ty.as_ref())),
            rocq_string_literal(&unquoted)
        );
    }
    if is_integer_literal(trimmed) {
        return format!("CstZ ({trimmed})");
    }
    format!(
        "CstString {} {}",
        emit_rocq_string_typmod(string_typmod_or_text(ty.as_ref())),
        rocq_string_literal(trimmed)
    )
}

fn emit_rocq_constant_function(raw: &str, ty: Option<FormalAttributeType>) -> String {
    format!("Constant ({})", emit_rocq_value(raw, ty))
}

fn emit_rocq_value(raw: &str, ty: Option<FormalAttributeType>) -> String {
    let trimmed = raw.trim();
    if trimmed.eq_ignore_ascii_case("null") {
        return match ty {
            Some(FormalAttributeType::Z) => "Value_Z None".to_owned(),
            Some(FormalAttributeType::Int32) => "Value_int32 None".to_owned(),
            Some(FormalAttributeType::Int64) => "Value_int64 None".to_owned(),
            Some(FormalAttributeType::String { typmod }) => format!(
                "Value_string (StringValue {} None)",
                emit_rocq_string_typmod(typmod)
            ),
            None => "Value_string (StringValue StringText None)".to_owned(),
            Some(FormalAttributeType::Bool) => "Value_bool None".to_owned(),
            Some(FormalAttributeType::Float) => "Value_float None".to_owned(),
            Some(FormalAttributeType::Double) => "Value_double None".to_owned(),
            Some(FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. }) => {
                "Value_numeric None".to_owned()
            }
            Some(FormalAttributeType::Date) => "Value_date None".to_owned(),
            Some(FormalAttributeType::Time) => "Value_time None".to_owned(),
            Some(FormalAttributeType::Timestamp { .. }) => "Value_timestamp None".to_owned(),
            Some(FormalAttributeType::Timestamptz { .. }) => "Value_timestamptz None".to_owned(),
        };
    }
    if trimmed.eq_ignore_ascii_case("true") {
        return "Value_bool (Some true)".to_owned();
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return "Value_bool (Some false)".to_owned();
    }
    if let Some(bits) = float_literal_bits_for_type(trimmed, ty.as_ref()) {
        return match ty {
            Some(FormalAttributeType::Float) => {
                format!("Value_float (Some (Float32OfBits ({bits})))")
            }
            Some(FormalAttributeType::Double) => {
                format!("Value_double (Some (Float64OfBits ({bits})))")
            }
            _ => unreachable!("float_literal_bits_for_type only accepts FLOAT/DOUBLE"),
        };
    }
    if matches!(ty, Some(FormalAttributeType::Date))
        && let Some(days) = parse_date_literal(trimmed)
    {
        return format!("Value_date (Some ({days})%Z)");
    }
    if matches!(ty, Some(FormalAttributeType::Time))
        && let Some(micros) = parse_time_literal(trimmed)
    {
        return format!("Value_time (Some ({micros})%Z)");
    }
    if let Some(FormalAttributeType::Timestamp { precision }) = ty
        && let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision))
    {
        return format!("Value_timestamp (Some ({micros})%Z)");
    }
    if let Some(FormalAttributeType::Timestamptz { precision }) = ty
        && let Some(micros) = parse_timestamp_literal(trimmed, timestamp_precision(precision))
    {
        return format!("Value_timestamptz (Some ({micros})%Z)");
    }
    if matches!(ty, Some(FormalAttributeType::Numeric)) {
        if let Some((coeff, scale)) = parse_decimal_literal(trimmed) {
            return format!("Value_numeric (Some (numeric_of_scaled ({coeff}) ({scale})))");
        }
        panic!("unsupported NUMERIC value literal reached Rocq emitter: {trimmed}");
    }
    if matches!(ty, Some(FormalAttributeType::Decimal { .. })) {
        if let Some((coeff, precision, scale)) = decimal_literal_for_type(trimmed, ty.as_ref()) {
            return format!(
                "Value_numeric (numeric_of_scaled_with_typmod ({precision}) ({scale}) ({coeff}))"
            );
        }
        panic!("unsupported DECIMAL value literal reached Rocq emitter: {trimmed}");
    }
    if matches!(ty, Some(FormalAttributeType::Int32)) && is_integer_literal(trimmed) {
        return format!("Value_int32 (int32_checked ({trimmed})%Z)");
    }
    if matches!(ty, Some(FormalAttributeType::Int64)) && is_integer_literal(trimmed) {
        return format!("Value_int64 (int64_checked ({trimmed})%Z)");
    }
    if let Some(unquoted) = sql_string_literal_content(trimmed) {
        let typmod = emit_rocq_string_typmod(string_typmod_or_text(ty.as_ref()));
        return format!(
            "Value_string (StringValue {typmod} (Some (string_explicit_cast {typmod} {})))",
            rocq_string_literal(&unquoted)
        );
    }
    if is_integer_literal(trimmed) {
        return format!("Value_Z (Some ({trimmed})%Z)");
    }
    let typmod = emit_rocq_string_typmod(string_typmod_or_text(ty.as_ref()));
    format!(
        "Value_string (StringValue {typmod} (Some (string_explicit_cast {typmod} {})))",
        rocq_string_literal(trimmed)
    )
}

fn string_typmod_or_text(ty: Option<&FormalAttributeType>) -> SqlStringType {
    match ty {
        Some(FormalAttributeType::String { typmod }) => *typmod,
        _ => SqlStringType::Text,
    }
}

pub(super) fn parse_decimal_literal(raw: &str) -> Option<(String, u32)> {
    let trimmed = raw.trim();
    if trimmed.is_empty() || trimmed.contains(['e', 'E']) {
        return None;
    }
    let (negative, body) = match trimmed.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, trimmed.strip_prefix('+').unwrap_or(trimmed)),
    };
    let (whole, fractional) = body.split_once('.').unwrap_or((body, ""));
    if whole.is_empty() && fractional.is_empty() {
        return None;
    }
    if !whole.chars().all(|c| c.is_ascii_digit()) || !fractional.chars().all(|c| c.is_ascii_digit())
    {
        return None;
    }
    let mut digits = format!("{whole}{fractional}");
    if digits.is_empty() {
        return None;
    }
    while digits.len() > 1 && digits.starts_with('0') {
        digits.remove(0);
    }
    if negative && digits != "0" {
        digits.insert(0, '-');
    }
    Some((digits, fractional.len().try_into().ok()?))
}

pub(super) fn numeric_literal_fits_postgres_runtime(raw: &str) -> bool {
    const MAX_INTEGER_DIGITS: usize = 131_072;
    const MAX_FRACTIONAL_DIGITS: u32 = 16_383;

    let Some((coeff, scale)) = parse_decimal_literal(raw) else {
        return false;
    };
    if scale > MAX_FRACTIONAL_DIGITS {
        return false;
    }
    let digits = coeff.strip_prefix('-').unwrap_or(&coeff);
    let integer_digits = if digits == "0" {
        0
    } else {
        digits.len().saturating_sub(scale as usize)
    };
    integer_digits <= MAX_INTEGER_DIGITS
}

pub(super) fn float_literal_bits_for_type(
    raw: &str,
    ty: Option<&FormalAttributeType>,
) -> Option<u64> {
    let value = finite_sql_float_literal_text(raw)?;
    match ty {
        Some(FormalAttributeType::Float) => {
            let parsed = value.parse::<f32>().ok()?;
            parsed.is_finite().then_some(parsed.to_bits() as u64)
        }
        Some(FormalAttributeType::Double) => {
            let parsed = value.parse::<f64>().ok()?;
            parsed.is_finite().then_some(parsed.to_bits())
        }
        _ => None,
    }
}

fn finite_sql_float_literal_text(raw: &str) -> Option<String> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    let value = value.trim();
    if !is_sql_finite_float_literal(value) {
        return None;
    }
    Some(value.to_owned())
}

fn is_sql_finite_float_literal(value: &str) -> bool {
    let mut chars = value.chars().peekable();
    if matches!(chars.peek(), Some('+') | Some('-')) {
        chars.next();
    }

    let mut saw_digit = false;
    while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
        saw_digit = true;
        chars.next();
    }

    if matches!(chars.peek(), Some('.')) {
        chars.next();
        while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            saw_digit = true;
            chars.next();
        }
    }

    if !saw_digit {
        return false;
    }

    if matches!(chars.peek(), Some('e') | Some('E')) {
        chars.next();
        if matches!(chars.peek(), Some('+') | Some('-')) {
            chars.next();
        }
        let mut saw_exponent_digit = false;
        while chars.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            saw_exponent_digit = true;
            chars.next();
        }
        if !saw_exponent_digit {
            return false;
        }
    }

    chars.next().is_none()
}

pub(super) fn decimal_literal_for_type(
    raw: &str,
    ty: Option<&FormalAttributeType>,
) -> Option<(String, u32, u32)> {
    let (coeff, literal_scale) = parse_decimal_literal(raw)?;
    let Some(FormalAttributeType::Decimal {
        precision,
        scale: target_scale,
    }) = ty
    else {
        return None;
    };
    let coerced = if literal_scale > *target_scale {
        round_decimal_coeff_to_scale(&coeff, literal_scale, *target_scale)?
    } else {
        let padding = target_scale - literal_scale;
        if padding == 0 {
            coeff
        } else {
            format!("{coeff}{}", "0".repeat(padding as usize))
        }
    };
    if !decimal_literal_fits_precision(&coerced, *target_scale, Some(*precision)) {
        return None;
    }
    Some((coerced, *precision, *target_scale))
}

fn decimal_literal_fits_precision(coeff: &str, scale: u32, precision: Option<u32>) -> bool {
    let Some(precision) = precision else {
        return false;
    };
    if precision == 0 || precision > 1000 || scale > 1000 {
        return false;
    }
    let digits = coeff.trim_start_matches('-').trim_start_matches('0');
    digits.len() <= precision as usize
}

fn round_decimal_coeff_to_scale(
    coeff: &str,
    literal_scale: u32,
    target_scale: u32,
) -> Option<String> {
    let drop_digits = literal_scale.checked_sub(target_scale)?;
    let divisor = 10_i128.checked_pow(drop_digits)?;
    let value = coeff.parse::<i128>().ok()?;
    let quotient = value / divisor;
    let remainder = value % divisor;
    let rounded = if remainder.abs().checked_mul(2)? >= divisor {
        quotient + if value.is_negative() { -1 } else { 1 }
    } else {
        quotient
    };
    Some(rounded.to_string())
}

fn emit_rocq_list<T>(items: &[T], emit: fn(&T) -> String) -> String {
    let rendered = items.iter().map(emit).collect::<Vec<_>>();
    emit_rocq_list_expr(&rendered)
}

fn emit_rocq_list_expr(items: &[String]) -> String {
    if items.is_empty() {
        return "[]".to_owned();
    }
    let single_line = format!("[{}]", items.join("; "));
    if !items.iter().any(|item| item.contains('\n')) {
        return single_line;
    }

    let mut lines = Vec::with_capacity(items.len() + 2);
    lines.push("[".to_owned());
    for (index, item) in items.iter().enumerate() {
        let suffix = if index + 1 == items.len() { "" } else { ";" };
        lines.push(format!("{item}{suffix}"));
    }
    lines.push("]".to_owned());
    lines.join("\n")
}

fn emit_rocq_attribute_list(attributes: &[FormalAttribute]) -> String {
    if attributes.is_empty() {
        return "nil".to_owned();
    }
    let mut rendered = attributes
        .iter()
        .map(|attribute| emit_rocq_schema_attribute(attribute.ty, &attribute.name))
        .collect::<Vec<_>>();
    rendered.push("nil".to_owned());
    rendered.join(" :: ")
}

fn indent_rocq_expr(expr: &str, spaces: usize) -> String {
    let padding = " ".repeat(spaces);
    expr.lines()
        .map(|line| format!("{padding}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
        .to_owned()
}

fn indent_rocq_nested_expr(expr: &str, spaces: usize) -> String {
    indent_rocq_expr(expr, spaces).trim_start().to_owned()
}

fn rocq_string_literal(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

pub(super) fn parse_date_literal(raw: &str) -> Option<i64> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    if let Ok(days) = value.parse::<i64>() {
        return valid_postgres_date_days(days).then_some(days);
    }
    parse_date_text(&value)
}

fn parse_date_text(value: &str) -> Option<i64> {
    let (year, month, day) = parse_ymd(value)?;
    if !(1..=5_874_897).contains(&year) {
        return None;
    }
    let days = days_from_civil(year, month, day);
    valid_postgres_date_days(days).then_some(days)
}

pub(super) fn date_literal_conforms_to_day(raw: &str) -> bool {
    parse_date_literal(raw).is_some()
}

/// Parse the deliberately small, exact subset of PostgreSQL string-to-DATE
/// input syntax accepted by lowering. Unlike `parse_date_literal`, this never
/// interprets a quoted integer as Calcite's normalized days-since-epoch
/// carrier.
pub(super) fn parse_source_date_cast_literal(raw: &str) -> Option<i64> {
    let value = sql_string_literal_content(raw)?;
    source_date_text_is_unambiguous(&value).then_some(())?;
    parse_date_text(&value)
}

fn parse_time_literal(raw: &str) -> Option<i64> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    if let Ok(micros) = value.parse::<i64>() {
        return valid_day_time_micros(micros).then_some(micros);
    }
    parse_time_text(&value)
}

fn parse_time_text(value: &str) -> Option<i64> {
    let (hour, minute, second, micros) = parse_hms(value)?;
    if !valid_sql_time(hour, minute, second, micros) {
        return None;
    }
    Some(hour * MICROS_PER_HOUR + minute * MICROS_PER_MINUTE + second * MICROS_PER_SECOND + micros)
}

pub(super) fn time_literal_conforms_to_day(raw: &str) -> bool {
    parse_time_literal(raw).is_some()
}

/// Parse supported PostgreSQL source text without accepting the unquoted
/// microsecond encoding used internally by Calcite/FormalSQL artifacts.
pub(super) fn parse_source_time_cast_literal(raw: &str) -> Option<i64> {
    let value = sql_string_literal_content(raw)?;
    parse_time_text(&value)
}

pub(super) fn timestamp_literal_conforms_to_precision(raw: &str, precision: u32) -> bool {
    parse_timestamp_literal(raw, precision).is_some()
}

pub(super) fn parse_source_timestamp_cast_literal(raw: &str, precision: u32) -> Option<i64> {
    let value = sql_string_literal_content(raw)?;
    source_timestamp_text_is_unambiguous(&value).then_some(())?;
    parse_timestamp_text(&value, precision)
}

pub(super) fn timestamptz_literal_to_utc_micros(
    raw: &str,
    precision: u32,
    sql_time_zone: &SqlTimeZone,
) -> Option<i64> {
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    let (timestamp_text, literal_offset) = split_timestamp_offset(&value)?;
    let local_micros = parse_timestamp_literal(timestamp_text, precision)?;
    let utc_micros = if let Some(literal_offset) = literal_offset {
        local_micros.checked_sub(literal_offset)?
    } else {
        // The embedded chrono-tz database is not attested to equal the
        // PostgreSQL server's tzdata version.  A local wall time is therefore
        // authoritative only under UTC/a fixed session offset; a literal
        // numeric offset remains self-contained under every session zone.
        sql_time_zone.has_fixed_offset_authority().then_some(())?;
        sql_time_zone.local_timestamp_micros_to_utc_instant(local_micros)?
    };
    timestamp_micros_with_precision(utc_micros, precision)
}

pub(super) fn source_timestamptz_cast_to_utc_micros(
    raw: &str,
    precision: u32,
    sql_time_zone: &SqlTimeZone,
) -> Option<i64> {
    let value = sql_string_literal_content(raw)?;
    let (timestamp_text, literal_offset) = split_timestamp_offset(&value)?;
    source_timestamp_text_is_unambiguous(timestamp_text).then_some(())?;
    let local_micros = parse_timestamp_text(timestamp_text, precision)?;
    let utc_micros = if let Some(literal_offset) = literal_offset {
        local_micros.checked_sub(literal_offset)?
    } else {
        sql_time_zone.has_fixed_offset_authority().then_some(())?;
        sql_time_zone.local_timestamp_micros_to_utc_instant(local_micros)?
    };
    timestamp_micros_with_precision(utc_micros, precision)
}

fn parse_timestamp_literal(raw: &str, precision: u32) -> Option<i64> {
    if precision > 6 {
        return None;
    }
    let value = sql_string_literal_content(raw).unwrap_or_else(|| raw.trim().to_owned());
    if let Ok(micros) = value.parse::<i64>() {
        return timestamp_micros_with_precision(micros, precision);
    }
    parse_timestamp_text(&value, precision)
}

fn parse_timestamp_text(value: &str, precision: u32) -> Option<i64> {
    let (date_part, time_part) = value
        .split_once(' ')
        .or_else(|| value.split_once('T'))
        .unwrap_or((value, "00:00:00"));
    let (year, month, day) = parse_ymd(date_part)?;
    if !(1..=294_276).contains(&year) {
        return None;
    }
    let (hour, minute, second, micros) = parse_hms(time_part)?;
    if !valid_time(hour, minute, second, micros) {
        return None;
    }
    let timestamp = days_from_civil(year, month, day)
        .checked_mul(MICROS_PER_DAY)?
        .checked_add(hour * MICROS_PER_HOUR)?
        .checked_add(minute * MICROS_PER_MINUTE)?
        .checked_add(second * MICROS_PER_SECOND)?
        .checked_add(micros)?;
    timestamp_micros_with_precision(timestamp, precision)
}

fn source_timestamp_text_is_unambiguous(value: &str) -> bool {
    let date_part = value
        .split_once(' ')
        .or_else(|| value.split_once('T'))
        .map_or(value, |(date, _)| date);
    source_date_text_is_unambiguous(date_part)
}

fn source_date_text_is_unambiguous(value: &str) -> bool {
    // PostgreSQL interprets a leading field of one or two digits according to
    // the session DateStyle and then applies its two-digit-year adjustment.
    // The campaign does not encode DateStyle, so accept only the unambiguous
    // YMD subset whose leading year has at least three decimal digits.
    value
        .split('-')
        .next()
        .is_some_and(|year| year.len() >= 3 && year.chars().all(|ch| ch.is_ascii_digit()))
}

fn split_timestamp_offset(value: &str) -> Option<(&str, Option<i64>)> {
    let value = value.trim();
    if let Some(timestamp) = value.strip_suffix('Z').or_else(|| value.strip_suffix('z')) {
        return Some((timestamp.trim_end(), Some(0)));
    }
    let search_start = value
        .find([' ', 'T'])
        .map(|index| index + 1)
        .unwrap_or(value.len());
    let offset_start = value[search_start..]
        .rfind(['+', '-'])
        .map(|index| search_start + index);
    match offset_start {
        Some(index) => {
            let timestamp = value[..index].trim_end();
            let offset = parse_timestamp_offset(&value[index..])?;
            Some((timestamp, Some(offset)))
        }
        None => Some((value, None)),
    }
}

fn parse_timestamp_offset(value: &str) -> Option<i64> {
    let value = value.trim();
    let sign = if value.starts_with('+') {
        1
    } else if value.starts_with('-') {
        -1
    } else {
        return None;
    };
    let body = &value[1..];
    let (hour_text, minute_text) = body.split_once(':').unwrap_or((body, "0"));
    let hours = hour_text.parse::<i64>().ok()?;
    let minutes = minute_text.parse::<i64>().ok()?;
    // PostgreSQL's numeric time-zone displacement is bounded by
    // MAX_TZDISP_HOUR (15), independently of the ordinary time-of-day hour
    // range.  In particular +15:59 is accepted while +16:00 is rejected.
    if !(0..=15).contains(&hours) || !(0..=59).contains(&minutes) {
        return None;
    }
    Some(sign * (hours * MICROS_PER_HOUR + minutes * MICROS_PER_MINUTE))
}

fn timestamp_micros_with_precision(micros: i64, precision: u32) -> Option<i64> {
    if precision > MAX_TIMESTAMP_PRECISION || !valid_postgres_timestamp_micros(micros) {
        return None;
    }
    let factor = 10_i64.pow(MAX_TIMESTAMP_PRECISION - precision);
    if micros.rem_euclid(factor) == 0 {
        Some(micros)
    } else {
        None
    }
}

fn parse_ymd(value: &str) -> Option<(i64, i64, i64)> {
    let mut parts = value.split('-');
    let year = parts.next()?.parse::<i64>().ok()?;
    let month = parts.next()?.parse::<i64>().ok()?;
    let day = parts.next()?.parse::<i64>().ok()?;
    if parts.next().is_some() || !valid_ymd(year, month, day) {
        return None;
    }
    Some((year, month, day))
}

fn parse_hms(value: &str) -> Option<(i64, i64, i64, i64)> {
    let mut parts = value.split(':');
    let hour = parts.next()?.parse::<i64>().ok()?;
    let minute = parts.next()?.parse::<i64>().ok()?;
    let second_part = parts.next()?;
    if parts.next().is_some() {
        return None;
    }
    let (second_text, fraction_text) = second_part.split_once('.').unwrap_or((second_part, ""));
    let second = second_text.parse::<i64>().ok()?;
    let micros = if fraction_text.is_empty() {
        0
    } else if fraction_text.len() <= 6 && fraction_text.chars().all(|ch| ch.is_ascii_digit()) {
        let padded = format!("{fraction_text:0<6}");
        padded.parse::<i64>().ok()?
    } else {
        return None;
    };
    Some((hour, minute, second, micros))
}

fn valid_time(hour: i64, minute: i64, second: i64, micros: i64) -> bool {
    (0..=23).contains(&hour)
        && (0..=59).contains(&minute)
        && (0..=59).contains(&second)
        && (0..=999_999).contains(&micros)
}

fn valid_sql_time(hour: i64, minute: i64, second: i64, micros: i64) -> bool {
    valid_time(hour, minute, second, micros)
        || (hour == 24 && minute == 0 && second == 0 && micros == 0)
}

fn valid_day_time_micros(micros: i64) -> bool {
    (0..=MICROS_PER_DAY).contains(&micros)
}

const MICROS_PER_SECOND: i64 = 1_000_000;
const MICROS_PER_MINUTE: i64 = 60 * MICROS_PER_SECOND;
const MICROS_PER_HOUR: i64 = 60 * MICROS_PER_MINUTE;
const MICROS_PER_DAY: i64 = 24 * MICROS_PER_HOUR;
const POSTGRES_DATE_MIN_DAYS_UNIX_EPOCH: i64 = -2_440_588;
const POSTGRES_DATE_END_DAYS_UNIX_EPOCH: i64 = 2_145_042_906;
const POSTGRES_TIMESTAMP_MIN_MICROS_UNIX_EPOCH: i64 = -210_866_803_200_000_000;

pub(super) fn valid_postgres_date_days(days: i64) -> bool {
    (POSTGRES_DATE_MIN_DAYS_UNIX_EPOCH..POSTGRES_DATE_END_DAYS_UNIX_EPOCH).contains(&days)
}

fn valid_postgres_timestamp_micros(micros: i64) -> bool {
    // PostgreSQL's exclusive absolute upper bound is 9_224_318_016_000_000_000
    // in Unix-epoch microseconds, above i64::MAX. This carrier therefore only
    // needs the lower-bound check and conservatively cannot encode that high tail.
    micros >= POSTGRES_TIMESTAMP_MIN_MICROS_UNIX_EPOCH
}

fn valid_ymd(year: i64, month: i64, day: i64) -> bool {
    (1..=12).contains(&month) && (1..=days_in_month(year, month)).contains(&day)
}

fn is_leap_year(year: i64) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

fn days_in_month(year: i64, month: i64) -> i64 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => 0,
    }
}

fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let yoe = year - era * 400;
    let mp = if month > 2 { month - 3 } else { month + 9 };
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}
