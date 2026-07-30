use std::collections::HashMap;

use super::*;
use crate::core::VerificationMode;
use crate::core::syntax::{
    FormalQueryDefinitionGraph, FormalQueryShapeDefinition, FormalQueryShapeKind,
    FormalQueryStatementSymbols, FormalRowMapAdapter, FormalScalarExpr, FormalScalarQuantifier,
    FormalScalarResultKind, FormalScalarSelectItem, formula_expr_requires_numeric_exp_model,
    query_expr_output_signature, scalar_expr_requires_numeric_exp_model,
};

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
                (Logos, "FormalSQL.ProofAgentFacade", Some(22), Some(22), Some(22)),
                (Logos, "FormalSQL.SubqueryFacts", Some(23), Some(23), Some(23)),
                (Logos, "FormalSQL.MembershipCompositionFacts", Some(24), Some(24), Some(24)),
                (Logos, "FormalSQL.WitnessFacts", Some(25), Some(25), Some(25)),
                (Logos, "FormalSQL.CountermodelFacts", Some(26), Some(26), Some(26)),
                (Logos, "FormalSQL.AggregateOutcomeBridgeFacts", Some(27), Some(27), Some(27)),
                (Logos, "FormalSQL.CorrelatedMembershipFacts", Some(28), Some(28), Some(28)),
                (Logos, "FormalSQL.MembershipJoinCompositionFacts", Some(29), Some(29), Some(29)),
                (Logos, "FormalSQL.FilterFkEliminationFacts", Some(30), Some(30), Some(30)),
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
    let schema_constraints = emit_rocq_schema_constraints(tables);
    format!(
        "\
From SQLFS Require Import SqlSyntax GenericInstance ValueCore ValueInteger ValueString Formula SchemaConstraints.
From Logos Require Import FormalSQL.TNullSyntax.
From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition generated_sql_default_collation : string := {}.
Definition generated_sql_character_classification : string := {}.
Definition generated_sql_locale_provider : string := {}.
Definition generated_sql_server_encoding : string := {}.

{}

Definition generated_schema_constraints : list table_constraint :=
{}.

Definition generated_schema_conforms (db : db_state) : Prop :=
  database_conforms_schema
    generated_schema generated_schema_constraints db.
",
        rocq_string_literal(sql_environment.default_collation_label()),
        rocq_string_literal(sql_environment.character_classification_label()),
        rocq_string_literal(sql_environment.locale_provider_label()),
        rocq_string_literal(sql_environment.server_encoding_label()),
        emit_rocq_schema_definition("generated_schema", schema_expr),
        indent_rocq_expr(&schema_constraints, 2)
    )
}

fn emit_rocq_schema_constraints(tables: &[FormalTable]) -> String {
    let rendered = tables
        .iter()
        .map(emit_rocq_table_constraint)
        .collect::<Vec<_>>();
    emit_rocq_list_expr(&rendered)
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
        .map(emit_rocq_function_term)
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
    solve [contradiction | reflexivity | congruence | tauto]
  | cbn;
    intros;
    repeat match goal with
    | H : False |- _ => contradiction
    | H : _ /\\ _ |- _ => destruct H
    | H : _ \\/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ?left = ?right |- _ => first [subst left | subst right]
    end;
    solve [contradiction | reflexivity | congruence | tauto]
  ].

(* This tactic is used only for one closed scalar-signature equality at a
   time.  Keep reduction local to the TNull type catalog: native scalar
   certificates below traverse query and expression syntax compositionally. *)
Ltac solve_generated_scalar_type :=
  cbn [TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
       TNullAggTermType TNullAggTermTypeFuel TNullAggTermTypesFuel
       TNullFunTermType TNullFunTermTypeFuel TNullFunTermTypesFuel
       TNullScalarOperatorOutputType TNullRequireArgumentTypes
       TNullTypeListEqb TNullTypeEqb TNullPredicateArgumentTypesValid
       TNullEqualityPairTypes TNullGenericOrderPairTypes TNullIntegralType
       TNullNumericKindType TNullNumericSourceType TNullCaseResultType
       TNullAggregateFunctionArgumentTypeValid
       TNullAggregateArgumentTypeValid TNullAggregateOutputType
       TNullAggregateFunctionOutputType];
  reflexivity.

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
        opaque_helper_symbols: (0..readable.select_lists.len())
            .map(|index| format!("select_list_{index}"))
            .chain(
                (0..readable.scalar_select_lists.len())
                    .map(|index| format!("scalar_select_list_{index}")),
            )
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

fn validate_query_program_for_emission(
    source: &[(&FormalQueryExpr, &[FormalAttribute])],
    target: &[(&FormalQueryExpr, &[FormalAttribute])],
) -> Result<(), String> {
    for (side, statements) in [("source", source), ("target", target)] {
        for (index, (query, _)) in statements.iter().enumerate() {
            validate_query_expr_scalar_operators(query)
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
            query.requires_numeric_exp_model(),
        ));
        statement_symbols.push(FormalQueryStatementSymbols {
            statement_index: index + 1,
            root_symbol: query_name.clone(),
            output_signature_symbol: signature_name.clone(),
            requires_numeric_exp_model: query.requires_numeric_exp_model(),
        });
        query_names.push(if query.requires_numeric_exp_model() {
            format!("{query_name} generated_numeric_exp_model")
        } else {
            query_name
        });
        statement_admissibility.push((
            format!("{side}_query_expr{suffix}_admissible"),
            query.requires_numeric_exp_model(),
        ));
        signature_names.push(signature_name);
    }
    let program_definition = format!(
        "Definition {side}_query_program (generated_numeric_exp_model : NumericExpModel) : list QueryExpr :=\n  [{}].",
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
    let equivalence_input = "Definition generated_equivalence_input
    (generated_numeric_exp_model : NumericExpModel) :=
  (Schema.generated_schema,
   Schema.generated_schema_constraints,
   source_query_program generated_numeric_exp_model,
   target_query_program generated_numeric_exp_model).";
    let (query_equivalence, program_equivalence) = match verification_mode {
        VerificationMode::SafeUnconditional => ("query_expr_equiv", "query_program_equiv"),
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => {
            ("query_expr_outcome_equiv", "query_program_outcome_equiv")
        }
    };
    let equivalence_goal = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Definition generated_equivalence_goal : Prop :=
  forall generated_numeric_exp_model : NumericExpModel,
    source_program_output_signatures =
      map query_expr_outputs
        (source_query_program generated_numeric_exp_model) /\\
    target_program_output_signatures =
      map query_expr_outputs
        (target_query_program generated_numeric_exp_model) /\\
    source_program_output_signatures = target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
      generated_query_program_admissible
        db (source_query_program generated_numeric_exp_model) /\\
      generated_query_program_admissible
        db (target_query_program generated_numeric_exp_model) /\\
      generated_query_program_equiv db
        (source_query_program generated_numeric_exp_model)
        (target_query_program generated_numeric_exp_model))."
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
  forall generated_numeric_exp_model : NumericExpModel,
    source_program_output_signatures =
      map query_expr_outputs
        (source_query_program generated_numeric_exp_model) /\\
    target_program_output_signatures =
      map query_expr_outputs
        (target_query_program generated_numeric_exp_model) /\\
    source_program_output_signatures = target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
      verification_condition_holds db condition ->
      generated_query_program_admissible
        db (source_query_program generated_numeric_exp_model) /\\
      generated_query_program_admissible
        db (target_query_program generated_numeric_exp_model) /\\
      generated_query_program_equiv db
        (source_query_program generated_numeric_exp_model)
        (target_query_program generated_numeric_exp_model))."
            .to_owned(),
    };
    let equivalence_goal_intro = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Lemma generated_equivalence_goal_intro :
  (forall generated_numeric_exp_model db,
    Schema.generated_schema_conforms db ->
    generated_query_program_equiv db
      (source_query_program generated_numeric_exp_model)
      (target_query_program generated_numeric_exp_model)) ->
  generated_equivalence_goal.
Proof.
intros Hcore generated_numeric_exp_model.
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
  + exact (Hcore generated_numeric_exp_model db Hschema).
Qed."
        }
        VerificationMode::Conditional => {
            "Lemma generated_equivalence_goal_intro :
  forall condition,
  (forall generated_numeric_exp_model db,
    Schema.generated_schema_conforms db ->
    verification_condition_holds db condition ->
    generated_query_program_equiv db
      (source_query_program generated_numeric_exp_model)
      (target_query_program generated_numeric_exp_model)) ->
  generated_equivalence_goal condition.
Proof.
intros condition Hcore generated_numeric_exp_model.
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
  + exact (Hcore generated_numeric_exp_model db Hschema Hcondition).
Qed."
        }
    };
    let verification_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "Definition generated_countermodel_goal : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
  forall generated_numeric_exp_model : NumericExpModel,
      generated_query_program_admissible
        Witness.generated_witness_db
        (source_query_program generated_numeric_exp_model) /\\
      generated_query_program_admissible
        Witness.generated_witness_db
        (target_query_program generated_numeric_exp_model) /\\
      ~ generated_query_program_outcome_equiv Witness.generated_witness_db
          (source_query_program generated_numeric_exp_model)
          (target_query_program generated_numeric_exp_model).

Lemma generated_countermodel_goal_intro :
  Witness.generated_witness_available = true ->
    (forall generated_numeric_exp_model : NumericExpModel,
      ~ generated_query_program_outcome_equiv Witness.generated_witness_db
          (source_query_program generated_numeric_exp_model)
          (target_query_program generated_numeric_exp_model)) ->
    generated_countermodel_goal.
Proof.
intros Havailable Hseparation.
split; [exact Havailable|].
pose proof
  (Witness.generated_witness_schema_conforms Havailable) as Hschema.
split; [exact Hschema|].
intro generated_numeric_exp_model.
split.
- apply source_query_program_admissible.
  exact Hschema.
- split.
  + apply target_query_program_admissible.
    exact Hschema.
  + exact (Hseparation generated_numeric_exp_model).
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
   observation for every conforming database.  Use
   [query_expr_equiv_of_ordered_observations] for a general exact
   query-expression obligation and [query_program_equiv_cons] to advance
   through statements.

   If [Witness.generated_witness_available] computes to [true], Logos has
   frozen the validated PostgreSQL candidate as the read-only FormalSQL
   database [Witness.generated_witness_db].  To select the fully qualified
   [VerificationCountermodel] constructor, begin with
   [apply generated_countermodel_goal_intro; [reflexivity|]].  Do not rebuild
   a second database or re-prove schema conformance: prove only complete
   possible-outcome separation on that fixed witness, for every
   [NumericExpModel].  Finish the selected theorem with [Qed]. *)"
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
   [query_program_equiv_implies_outcome_equiv].  Safety must be proved in Rocq.

   If [Witness.generated_witness_available] computes to [true], Logos has
   frozen the validated PostgreSQL candidate as the read-only FormalSQL
   database [Witness.generated_witness_db].  To select the fully qualified
   [VerificationCountermodel] constructor, begin with
   [apply generated_countermodel_goal_intro; [reflexivity|]].  Do not rebuild
   a second database or re-prove schema conformance: prove only complete
   possible-outcome separation on that fixed witness, for every
   [NumericExpModel].  Finish the selected theorem with [Qed]. *)"
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
  @eval_query_expr_outcome TNull relname
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
  @query_expr_equiv TNull relname
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
  @query_program_equiv TNull relname
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
  @query_program_outcome_equiv TNull relname
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
    (@query_expr_admissible TNull relname (@_basesort TNull db))
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
        proof.push_str(&indent_rocq_expr(subproof, 2));
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

fn rocq_closed_attribute_nonmembership_proof() -> String {
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

fn rocq_cbn_only_proof(definition: &str, proof: String) -> String {
    format!("cbn [{definition}].\n{proof}")
}

fn rocq_window_outputs_all_diff_proof(item_count: usize) -> String {
    // ListFacts.all_diff is definitionally True for both [] and singleton lists.
    if item_count <= 1 {
        return "constructor.".to_owned();
    }
    rocq_focused_subproofs(
        "cbn [ListFacts.all_diff].\nsplit.",
        &[
            rocq_closed_attribute_nonmembership_proof(),
            rocq_window_outputs_all_diff_proof(item_count - 1),
        ],
    )
}

fn emit_query_expr_schema_admissibility_certificate(
    query_name: &str,
    requires_numeric_exp_model: bool,
) -> String {
    let model_binder = if requires_numeric_exp_model {
        "\n    (generated_numeric_exp_model : NumericExpModel)"
    } else {
        ""
    };
    let model_argument = if requires_numeric_exp_model {
        " generated_numeric_exp_model"
    } else {
        ""
    };
    format!(
        "Lemma {query_name}_admissible{model_binder} (db : db_state) :\n  Schema.generated_schema_conforms db ->\n  @query_expr_admissible TNull relname (@_basesort TNull db)\n    ({query_name}{model_argument}).\nProof.\n  intro Hschema.\n  apply (query_expr_admissible_database_schema_transport\n    Schema.generated_schema Schema.generated_schema_constraints db).\n  {{ exact Hschema. }}\n  {{ apply {query_name}_admissible_generated_schema. }}\nQed."
    )
}

fn emit_query_program_admissibility_certificates(
    side: &str,
    statements: &[(String, bool)],
) -> String {
    let generated_steps = statements
        .iter()
        .map(|(lemma, requires_model)| {
            let model_argument = if *requires_model {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            format!("apply ({lemma}_generated_schema{model_argument}).")
        })
        .collect::<Vec<_>>();
    let schema_steps = statements
        .iter()
        .map(|(lemma, requires_model)| {
            let model_argument = if *requires_model {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            format!("apply ({lemma}{model_argument} db Hschema).")
        })
        .collect::<Vec<_>>();
    format!(
        "Lemma {side}_query_program_admissible_generated_schema\n    (generated_numeric_exp_model : NumericExpModel) :\n  Forall\n    (@query_expr_admissible TNull relname\n      (@_basesort TNull Schema.generated_schema))\n    ({side}_query_program generated_numeric_exp_model).\nProof.\n  unfold {side}_query_program.\n{}\nQed.\n\nLemma {side}_query_program_admissible\n    (generated_numeric_exp_model : NumericExpModel) (db : db_state) :\n  Schema.generated_schema_conforms db ->\n  Forall\n    (@query_expr_admissible TNull relname (@_basesort TNull db))\n    ({side}_query_program generated_numeric_exp_model).\nProof.\n  intro Hschema.\n  unfold {side}_query_program.\n{}\nQed.",
        indent_rocq_expr(&rocq_forall_list_proof(&generated_steps), 2),
        indent_rocq_expr(&rocq_forall_list_proof(&schema_steps), 2),
    )
}

#[derive(Debug, Default)]
struct RocqQueryDefinitions {
    select_lists: Vec<Vec<FormalSelectItem>>,
    scalar_select_lists: Vec<Vec<FormalScalarSelectItem>>,
    formula_expr_predicates: Vec<FormalFormulaExpr>,
    formula_expr_uses: Vec<(FormalFormulaExpr, ScalarPhase)>,
    scalar_expr_predicates: Vec<FormalScalarExpr>,
    scalar_expr_uses: Vec<(FormalScalarExpr, ScalarPhase)>,
    table_sorts: Vec<(String, Vec<FormalAttribute>)>,
    shared_query_exprs: Vec<FormalQueryExpr>,
}

#[derive(Clone, Copy)]
struct QueryExprReferencePolicy {
    query_exprs: bool,
    formula_exprs: bool,
    scalar_exprs: bool,
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
            formula_exprs: allow_refs,
            scalar_exprs: allow_refs,
        }
    }
}

impl RocqQueryDefinitions {
    fn from_query_expr_program_pair(
        source: &[&FormalQueryExpr],
        target: &[&FormalQueryExpr],
    ) -> Self {
        let mut definitions = Self::default();
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
                push_unique(&mut self.formula_expr_predicates, predicate.clone());
                push_unique(
                    &mut self.formula_expr_uses,
                    (predicate.clone(), ScalarPhase::On),
                );
                self.collect_formula_expr_queries(predicate, ScalarPhase::On);
                push_unique(&mut self.select_lists, matched_select.clone());
                push_unique(&mut self.select_lists, left_select.clone());
                push_unique(&mut self.select_lists, right_select.clone());
                self.collect_query_expr(left);
                self.collect_query_expr(right);
            }
            FormalQueryExpr::Projection { select, input } => {
                push_unique(&mut self.select_lists, select.clone());
                self.collect_query_expr(input);
            }
            FormalQueryExpr::ScalarProjection { select, input } => {
                push_unique(&mut self.scalar_select_lists, select.clone());
                for item in select {
                    self.collect_scalar_expr_queries(&item.expr);
                }
                self.collect_query_expr(input);
            }
            FormalQueryExpr::RowMap { input, .. } => self.collect_query_expr(input),
            FormalQueryExpr::Selection { predicate, input } => {
                push_unique(&mut self.formula_expr_predicates, predicate.clone());
                push_unique(
                    &mut self.formula_expr_uses,
                    (predicate.clone(), ScalarPhase::Where),
                );
                self.collect_formula_expr_queries(predicate, ScalarPhase::Where);
                self.collect_query_expr(input);
            }
            FormalQueryExpr::ScalarSelection { predicate, input } => {
                push_unique(&mut self.scalar_expr_predicates, predicate.clone());
                push_unique(
                    &mut self.scalar_expr_uses,
                    (predicate.clone(), ScalarPhase::Where),
                );
                self.collect_scalar_expr_queries(predicate);
                self.collect_query_expr(input);
            }
            FormalQueryExpr::ScalarGroup {
                select,
                group_by,
                having,
                input,
            } => {
                push_unique(&mut self.scalar_select_lists, select.clone());
                for item in select {
                    self.collect_scalar_expr_queries(&item.expr);
                }
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
            FormalQueryExpr::Group {
                select,
                having,
                input,
                ..
            } => {
                push_unique(&mut self.select_lists, select.clone());
                if !matches!(having, FormalFormulaExpr::True) {
                    push_unique(&mut self.formula_expr_predicates, having.clone());
                    push_unique(
                        &mut self.formula_expr_uses,
                        (having.clone(), ScalarPhase::Having),
                    );
                }
                self.collect_formula_expr_queries(having, ScalarPhase::Having);
                self.collect_query_expr(input);
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                for grouping_set in grouping_sets {
                    push_unique(&mut self.select_lists, grouping_set.select.clone());
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

    fn collect_formula_expr_queries(&mut self, formula: &FormalFormulaExpr, phase: ScalarPhase) {
        match formula {
            FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
                self.collect_formula_expr_queries(left, phase);
                self.collect_formula_expr_queries(right, phase);
            }
            FormalFormulaExpr::Not { formula } => {
                self.collect_formula_expr_queries(formula, phase);
            }
            FormalFormulaExpr::In { query, .. }
            | FormalFormulaExpr::QuantifiedComparison { query, .. }
            | FormalFormulaExpr::Exists { query } => self.collect_query_expr(query),
            FormalFormulaExpr::Scalar { expression } => {
                push_unique(
                    &mut self.scalar_expr_predicates,
                    expression.as_ref().clone(),
                );
                push_unique(
                    &mut self.scalar_expr_uses,
                    (expression.as_ref().clone(), phase),
                );
                self.collect_scalar_expr_queries(expression);
            }
            FormalFormulaExpr::True
            | FormalFormulaExpr::False
            | FormalFormulaExpr::Predicate { .. } => {}
        }
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
            FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
                self.collect_scalar_expr_queries(left);
                self.collect_scalar_expr_queries(right);
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
        for (index, select) in self.select_lists.iter().enumerate() {
            definitions.push(format!(
                "Definition select_list_{index} : SelectListT :=\n{}.",
                indent_rocq_expr(&emit_rocq_select_list(select), 2)
            ));
        }
        for index in self.scalar_select_list_emission_order() {
            let select = &self.scalar_select_lists[index];
            let model_parameter = if scalar_select_requires_numeric_exp_model(select) {
                " (generated_numeric_exp_model : NumericExpModel)"
            } else {
                ""
            };
            definitions.push(format!(
                "Definition scalar_select_list_{index}{model_parameter} :\n    list ((@scalar_expr TNull relname ScalarResultValue * Tuple.attribute TNull)%type) :=\n{}.",
                indent_rocq_expr(&self.emit_scalar_select_list_inline(select), 2)
            ));
        }
        for (index, expression) in self.scalar_expr_predicates.iter().enumerate() {
            let model_parameter = if scalar_expr_requires_numeric_exp_model(expression) {
                " (generated_numeric_exp_model : NumericExpModel)"
            } else {
                ""
            };
            definitions.push(format!(
                "Definition scalar_expr_predicate_{index}{model_parameter} :\n    @scalar_expr TNull relname ScalarResultBoolean :=\n{}.",
                indent_rocq_expr(&self.emit_scalar_expr(expression, false), 2)
            ));
        }
        for (index, predicate) in self.formula_expr_predicates.iter().enumerate() {
            let model_parameter = if formula_expr_requires_numeric_exp_model(predicate) {
                " (generated_numeric_exp_model : NumericExpModel)"
            } else {
                ""
            };
            definitions.push(format!(
                "Definition formula_expr_predicate_{index}{model_parameter} : FormulaExpr :=\n{}.",
                indent_rocq_expr(&self.emit_formula_expr(predicate, false), 2)
            ));
        }
        for index in self.shared_query_expr_emission_order() {
            let query = &self.shared_query_exprs[index];
            let model_parameter = if query.requires_numeric_exp_model() {
                " (generated_numeric_exp_model : NumericExpModel)"
            } else {
                ""
            };
            definitions.push(format!(
                "Definition shared_query_expr_{index}{model_parameter} : QueryExpr :=\n{}.",
                indent_rocq_expr(
                    &self.emit_query_expr_body(query, QueryExprReferencePolicy::uniform(true)),
                    2,
                )
            ));
            definitions.push(format!(
                "Definition shared_query_expr_{index}_expected_outputs :\n    list (Tuple.attribute TNull) :=\n{}.",
                indent_rocq_expr(&self.emit_query_expr_expected_outputs(query, false), 2)
            ));
        }
        definitions.join("\n\n")
    }

    fn emit_admissibility_certificates(&self) -> String {
        let mut certificates = Vec::new();
        for (index, (relation, columns)) in self.table_sorts.iter().enumerate() {
            certificates.push(format!(
                "Lemma generated_table_sort_{index} :\n  @_basesort TNull Schema.generated_schema (Rel {}) =S=\n  Fset.mk_set (Tuple.A TNull) ({}).\nProof.\n  {}\nQed.",
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
        for (formula, phase) in &self.formula_expr_uses {
            let index = self
                .formula_expr_predicates
                .iter()
                .position(|candidate| candidate == formula)
                .expect("each formula use has one emitted definition");
            let symbol = format!("formula_expr_predicate_{index}");
            certificates.push(
                self.emit_formula_expr_admissibility_certificate(&symbol, formula, *phase, false),
            );
        }
        for index in self.shared_query_expr_emission_order() {
            let query = &self.shared_query_exprs[index];
            let symbol = format!("shared_query_expr_{index}");
            certificates.push(self.emit_query_expr_body_admissibility_certificate(
                &symbol,
                query,
                // Formula certificates are emitted immediately above, so a
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

    fn emit_formula_expr_admissibility_certificate(
        &self,
        symbol: &str,
        formula: &FormalFormulaExpr,
        phase: ScalarPhase,
        allow_formula_refs: bool,
    ) -> String {
        let requires_model = formula_expr_requires_numeric_exp_model(formula);
        let model_binder = if requires_model {
            "\n    (generated_numeric_exp_model : NumericExpModel)"
        } else {
            ""
        };
        let model_argument = if requires_model {
            " generated_numeric_exp_model"
        } else {
            ""
        };
        format!(
            "Lemma {symbol}_admissible_{}_generated_schema{model_binder} :\n  @formula_expr_admissible_at TNull relname\n    (@_basesort TNull Schema.generated_schema) {}\n    ({symbol}{model_argument}).\nProof.\n  unfold {symbol}.\n{}\nQed.",
            phase.slug(),
            phase.rocq_constructor(),
            indent_rocq_expr(
                &self.emit_formula_expr_admissibility_proof(formula, phase, allow_formula_refs,),
                2,
            )
        )
    }

    fn emit_formula_expr_admissibility_proof(
        &self,
        formula: &FormalFormulaExpr,
        phase: ScalarPhase,
        allow_formula_refs: bool,
    ) -> String {
        if allow_formula_refs
            && let Some(index) = self
                .formula_expr_predicates
                .iter()
                .position(|candidate| candidate == formula)
        {
            let model_argument = if formula_expr_requires_numeric_exp_model(formula) {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!(
                "apply (formula_expr_predicate_{index}_admissible_{}_generated_schema{model_argument}).",
                phase.slug()
            );
        }

        match formula {
            FormalFormulaExpr::True => "constructor.".to_owned(),
            FormalFormulaExpr::False => "constructor.".to_owned(),
            FormalFormulaExpr::Predicate { .. } => rocq_metadata_proof(),
            FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
                rocq_conjunction_proof(vec![
                    self.emit_formula_expr_admissibility_proof(left, phase, false),
                    self.emit_formula_expr_admissibility_proof(right, phase, false),
                ])
            }
            FormalFormulaExpr::Not { formula } => rocq_focused_subproofs(
                &format!(
                    "eapply formula_expr_not_admissible_at with (phase := {}).",
                    phase.rocq_constructor()
                ),
                &[self.emit_formula_expr_admissibility_proof(formula, phase, false)],
            ),
            FormalFormulaExpr::QuantifiedComparison { query, .. } => rocq_focused_subproofs(
                &format!(
                    "eapply formula_expr_quant_admissible_at_from_outputs with (phase := {}).",
                    phase.rocq_constructor()
                ),
                &[
                    self.emit_query_expr_admissibility_proof(
                        query,
                        QueryExprReferencePolicy::uniform(false),
                    ),
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                    rocq_metadata_proof(),
                ],
            ),
            FormalFormulaExpr::In { query, .. } => rocq_focused_subproofs(
                &format!(
                    "eapply formula_expr_in_admissible_at_from_outputs with (phase := {}).",
                    phase.rocq_constructor()
                ),
                &[
                    self.emit_query_expr_admissibility_proof(
                        query,
                        QueryExprReferencePolicy::uniform(false),
                    ),
                    rocq_metadata_proof(),
                    self.emit_query_in_positionally_aligned_proof(),
                ],
            ),
            FormalFormulaExpr::Exists { query } => rocq_focused_subproofs(
                &format!(
                    "eapply formula_expr_exists_admissible_at_from_outputs with (phase := {}).",
                    phase.rocq_constructor()
                ),
                &[self.emit_query_expr_admissibility_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                )],
            ),
            FormalFormulaExpr::Scalar { expression } => rocq_focused_subproofs(
                &format!(
                    "eapply formula_expr_scalar_admissible_at with (phase := {}).",
                    phase.rocq_constructor()
                ),
                &[self.emit_scalar_expr_admissibility_proof(expression, phase, false)],
            ),
        }
    }

    fn emit_scalar_expr_admissibility_certificate(
        &self,
        symbol: &str,
        expression: &FormalScalarExpr,
        phase: ScalarPhase,
        allow_scalar_refs: bool,
    ) -> String {
        let requires_model = scalar_expr_requires_numeric_exp_model(expression);
        let model_binder = if requires_model {
            "\n    (generated_numeric_exp_model : NumericExpModel)"
        } else {
            ""
        };
        let model_argument = if requires_model {
            " generated_numeric_exp_model"
        } else {
            ""
        };
        format!(
            "Lemma {symbol}_admissible_{}_generated_schema{model_binder} :\n  @scalar_expr_admissible TNull relname\n    (@_basesort TNull Schema.generated_schema) {} ScalarResultBoolean\n    ({symbol}{model_argument}).\nProof.\n  unfold {symbol}.\n{}\nQed.",
            phase.slug(),
            phase.rocq_constructor(),
            indent_rocq_expr(
                &self.emit_scalar_expr_admissibility_proof(expression, phase, allow_scalar_refs,),
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
            let model_argument = if scalar_expr_requires_numeric_exp_model(expression) {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!(
                "apply (scalar_expr_predicate_{index}_admissible_{}_generated_schema{model_argument}).",
                phase.slug()
            );
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
                &[self.emit_query_expr_admissibility_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                )],
            )
        };

        match expression {
            FormalScalarExpr::Leaf { .. } => {
                if matches!(phase, ScalarPhase::Select | ScalarPhase::Having) {
                    "left; reflexivity.".to_owned()
                } else {
                    "right; reflexivity.".to_owned()
                }
            }
            FormalScalarExpr::Call { args, .. } => scalar_arguments_proof(args),
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
            FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => {
                self.emit_scalar_expr_admissibility_proof(expression, phase, false)
            }
            FormalScalarExpr::Predicate { args, .. } => {
                rocq_conjunction_proof(vec![scalar_arguments_proof(args), rocq_metadata_proof()])
            }
            FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
                rocq_conjunction_proof(vec![
                    self.emit_scalar_expr_admissibility_proof(left, phase, false),
                    self.emit_scalar_expr_admissibility_proof(right, phase, false),
                ])
            }
            FormalScalarExpr::True => "constructor.".to_owned(),
            FormalScalarExpr::QuantifiedComparison { args, query, .. } => {
                rocq_conjunction_proof(vec![
                    rocq_metadata_proof(),
                    scalar_arguments_proof(args),
                    query_admissibility_proof(query),
                    rocq_metadata_proof(),
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
            ]),
        }
    }

    fn emit_scalar_select_list_admissibility_proof(
        &self,
        select: &[FormalScalarSelectItem],
        phase: ScalarPhase,
    ) -> String {
        let item_proofs = select
            .iter()
            .map(|item| {
                rocq_conjunction_proof(vec![
                    self.emit_scalar_expr_admissibility_proof(&item.expr, phase, false),
                    rocq_metadata_proof(),
                ])
            })
            .collect::<Vec<_>>();
        let proof = rocq_forall_list_proof(&item_proofs);
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("unfold scalar_select_list_{index}.\n{proof}"))
            .unwrap_or(proof)
    }

    fn emit_query_expr_admissibility_certificate(
        &self,
        symbol: &str,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        self.emit_query_expr_typed_admissibility_certificate(
            symbol,
            query,
            self.emit_query_expr_admissibility_proof(query, reference_policy),
            self.emit_query_expr_scalar_witnesses_proof(query, reference_policy),
            self.emit_query_expr_scalar_types_proof(query, reference_policy),
        )
    }

    fn emit_query_expr_body_admissibility_certificate(
        &self,
        symbol: &str,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        self.emit_query_expr_typed_admissibility_certificate(
            symbol,
            query,
            self.emit_query_expr_body_admissibility_proof(query, reference_policy),
            self.emit_query_expr_body_scalar_witnesses_proof(query, reference_policy),
            self.emit_query_expr_body_scalar_types_proof(query, reference_policy),
        )
    }

    fn emit_query_expr_typed_admissibility_certificate(
        &self,
        symbol: &str,
        query: &FormalQueryExpr,
        structural_proof: String,
        scalar_witnesses_proof: String,
        scalar_types_proof: String,
    ) -> String {
        let requires_model = query.requires_numeric_exp_model();
        let model_binder = if requires_model {
            "\n    (generated_numeric_exp_model : NumericExpModel)"
        } else {
            ""
        };
        let model_argument = if requires_model {
            " generated_numeric_exp_model"
        } else {
            ""
        };
        let certificate = format!(
            "Lemma {symbol}_native_scalar_witnesses_valid_generated_schema{model_binder} :\n  @query_expr_scalar_witnesses_valid TNull relname\n    NullValues.is_null_value ({symbol}{model_argument}).\nProof.\n  unfold {symbol}.\n{}\nQed.\n\nLemma {symbol}_native_scalar_types_valid_generated_schema{model_binder} :\n  @query_expr_scalar_types_valid TNull relname\n    TNullLeafHasType TNullCallHasType TNullPredicateHasTypes type_int64 type_bool\n    ({symbol}{model_argument}).\nProof.\n  unfold {symbol}.\n{}\nQed.\n\nLemma {symbol}_typed_native_scalar_admissible_with_outputs_generated_schema{model_binder} :\n  TNullQueryExprTypedNativeScalarAdmissibleWithOutputs\n    (@_basesort TNull Schema.generated_schema)\n    ({symbol}{model_argument}) {symbol}_expected_outputs.\nProof.\n  assert (Hstructural :\n    @query_expr_admissible_with_outputs TNull relname\n      (@_basesort TNull Schema.generated_schema)\n      ({symbol}{model_argument}) {symbol}_expected_outputs).\n  {{\n    unfold {symbol}, {symbol}_expected_outputs.\n{}\n  }}\n  unfold TNullQueryExprTypedNativeScalarAdmissibleWithOutputs,\n    TNullQueryExprTypedNativeScalarAdmissible,\n    query_expr_typed_native_scalar_admissible,\n    query_expr_native_scalar_admissible.\n  split.\n  {{\n    split.\n    {{\n      split.\n      {{ exact (proj1 Hstructural). }}\n      {{ apply {symbol}_native_scalar_witnesses_valid_generated_schema. }}\n    }}\n    {{ apply {symbol}_native_scalar_types_valid_generated_schema. }}\n  }}\n  {{ exact (proj2 Hstructural). }}\nQed.\n\nLemma {symbol}_admissible_with_outputs_generated_schema{model_binder} :\n  @query_expr_admissible_with_outputs TNull relname\n    (@_basesort TNull Schema.generated_schema)\n    ({symbol}{model_argument}) {symbol}_expected_outputs.\nProof.\n  apply TNullQueryExprTypedNativeScalarAdmissibleWithOutputs_is_admissible.\n  exact ({symbol}_typed_native_scalar_admissible_with_outputs_generated_schema{model_argument}).\nQed.\n\nLemma {symbol}_admissible_generated_schema{model_binder} :\n  @query_expr_admissible TNull relname\n    (@_basesort TNull Schema.generated_schema)\n    ({symbol}{model_argument}).\nProof.\n  exact (proj1 ({symbol}_admissible_with_outputs_generated_schema{model_argument})).\nQed.\n\nLemma {symbol}_outputs_generated_schema{model_binder} :\n  query_expr_outputs ({symbol}{model_argument}) = {symbol}_expected_outputs.\nProof.\n  exact (proj2 ({symbol}_admissible_with_outputs_generated_schema{model_argument})).\nQed.",
            indent_rocq_expr(&scalar_witnesses_proof, 2),
            indent_rocq_expr(&scalar_types_proof, 2),
            indent_rocq_expr(&structural_proof, 4),
        );
        certificate.replace(
            &format!(
                "      {{ apply {symbol}_native_scalar_witnesses_valid_generated_schema. }}"
            ),
            &format!(
                "      {{\n        split.\n        {{ apply {symbol}_native_scalar_witnesses_valid_generated_schema. }}\n        {{ reflexivity. }}\n      }}"
            ),
        )
    }

    fn emit_query_expr_scalar_witnesses_proof(
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
            let model_argument = if query.requires_numeric_exp_model() {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!(
                "apply (shared_query_expr_{index}_native_scalar_witnesses_valid_generated_schema{model_argument})."
            );
        }
        self.emit_query_expr_body_scalar_witnesses_proof(query, reference_policy)
    }

    fn emit_query_expr_body_scalar_witnesses_proof(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        let proof = match query {
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => "constructor.".to_owned(),
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => rocq_conjunction_proof(vec![
                self.emit_query_expr_scalar_witnesses_proof(left, reference_policy),
                self.emit_query_expr_scalar_witnesses_proof(right, reference_policy),
            ]),
            FormalQueryExpr::Join {
                predicate,
                left,
                right,
                ..
            } => rocq_conjunction_proof(vec![
                self.emit_formula_expr_scalar_witnesses_proof(
                    predicate,
                    reference_policy.formula_exprs,
                ),
                self.emit_query_expr_scalar_witnesses_proof(left, reference_policy),
                self.emit_query_expr_scalar_witnesses_proof(right, reference_policy),
            ]),
            FormalQueryExpr::Projection { input, .. }
            | FormalQueryExpr::RowMap { input, .. }
            | FormalQueryExpr::GroupingSets { input, .. }
            | FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => {
                self.emit_query_expr_scalar_witnesses_proof(input, reference_policy)
            }
            FormalQueryExpr::ScalarProjection { select, input } => rocq_conjunction_proof(vec![
                self.emit_scalar_select_list_witnesses_proof(select),
                self.emit_query_expr_scalar_witnesses_proof(input, reference_policy),
            ]),
            FormalQueryExpr::Selection { predicate, input } => rocq_conjunction_proof(vec![
                self.emit_formula_expr_scalar_witnesses_proof(
                    predicate,
                    reference_policy.formula_exprs,
                ),
                self.emit_query_expr_scalar_witnesses_proof(input, reference_policy),
            ]),
            FormalQueryExpr::ScalarSelection { predicate, input } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_witnesses_proof(predicate, reference_policy.scalar_exprs),
                self.emit_query_expr_scalar_witnesses_proof(input, reference_policy),
            ]),
            FormalQueryExpr::Group { having, input, .. } => rocq_conjunction_proof(vec![
                self.emit_formula_expr_scalar_witnesses_proof(
                    having,
                    reference_policy.formula_exprs,
                ),
                self.emit_query_expr_scalar_witnesses_proof(input, reference_policy),
            ]),
            FormalQueryExpr::ScalarGroup {
                select,
                group_by,
                having,
                input,
            } => rocq_conjunction_proof(vec![
                self.emit_scalar_select_list_witnesses_proof(select),
                rocq_forall_list_proof(
                    &group_by
                        .iter()
                        .map(|key| self.emit_scalar_expr_witnesses_proof(key, false))
                        .collect::<Vec<_>>(),
                ),
                self.emit_scalar_expr_witnesses_proof(having, reference_policy.scalar_exprs),
                self.emit_query_expr_scalar_witnesses_proof(input, reference_policy),
            ]),
        };
        rocq_cbn_only_proof("query_expr_scalar_witnesses_valid", proof)
    }

    fn emit_formula_expr_scalar_witnesses_proof(
        &self,
        formula: &FormalFormulaExpr,
        allow_formula_refs: bool,
    ) -> String {
        if allow_formula_refs
            && let Some(index) = self
                .formula_expr_predicates
                .iter()
                .position(|candidate| candidate == formula)
        {
            return format!(
                "unfold formula_expr_predicate_{index}.\n{}",
                self.emit_formula_expr_scalar_witnesses_proof(formula, false)
            );
        }
        let proof = match formula {
            FormalFormulaExpr::True
            | FormalFormulaExpr::False
            | FormalFormulaExpr::Predicate { .. } => "constructor.".to_owned(),
            FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
                rocq_conjunction_proof(vec![
                    self.emit_formula_expr_scalar_witnesses_proof(left, false),
                    self.emit_formula_expr_scalar_witnesses_proof(right, false),
                ])
            }
            FormalFormulaExpr::Not { formula } => {
                self.emit_formula_expr_scalar_witnesses_proof(formula, false)
            }
            FormalFormulaExpr::In { query, .. }
            | FormalFormulaExpr::QuantifiedComparison { query, .. }
            | FormalFormulaExpr::Exists { query } => self.emit_query_expr_scalar_witnesses_proof(
                query,
                QueryExprReferencePolicy::uniform(false),
            ),
            FormalFormulaExpr::Scalar { expression } => {
                self.emit_scalar_expr_witnesses_proof(expression, false)
            }
        };
        rocq_cbn_only_proof("formula_expr_scalar_witnesses_valid", proof)
    }

    fn emit_scalar_expr_witnesses_proof(
        &self,
        expression: &FormalScalarExpr,
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
                "unfold scalar_expr_predicate_{index}.\n{}",
                self.emit_scalar_expr_witnesses_proof(expression, false)
            );
        }
        let argument_proof = |arguments: &[FormalScalarExpr]| {
            rocq_forall_list_proof(
                &arguments
                    .iter()
                    .map(|argument| self.emit_scalar_expr_witnesses_proof(argument, false))
                    .collect::<Vec<_>>(),
            )
        };
        let proof = match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => "constructor.".to_owned(),
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                argument_proof(args)
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_witnesses_proof(condition, false),
                self.emit_scalar_expr_witnesses_proof(then_expr, false),
                self.emit_scalar_expr_witnesses_proof(else_expr, false),
            ]),
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => {
                self.emit_scalar_expr_witnesses_proof(expression, false)
            }
            FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
                rocq_conjunction_proof(vec![
                    self.emit_scalar_expr_witnesses_proof(left, false),
                    self.emit_scalar_expr_witnesses_proof(right, false),
                ])
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. }
            | FormalScalarExpr::In { args, query } => rocq_conjunction_proof(vec![
                argument_proof(args),
                self.emit_query_expr_scalar_witnesses_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                ),
            ]),
            FormalScalarExpr::Exists { query } => self.emit_query_expr_scalar_witnesses_proof(
                query,
                QueryExprReferencePolicy::uniform(false),
            ),
            FormalScalarExpr::Subquery { query, .. } => rocq_conjunction_proof(vec![
                "reflexivity.".to_owned(),
                self.emit_query_expr_scalar_witnesses_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                ),
            ]),
        };
        rocq_cbn_only_proof("scalar_expr_witnesses_valid", proof)
    }

    fn emit_scalar_select_list_witnesses_proof(&self, select: &[FormalScalarSelectItem]) -> String {
        let proof = rocq_forall_list_proof(
            &select
                .iter()
                .map(|item| self.emit_scalar_expr_witnesses_proof(&item.expr, false))
                .collect::<Vec<_>>(),
        );
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("unfold scalar_select_list_{index}.\n{proof}"))
            .unwrap_or(proof)
    }

    fn emit_query_expr_scalar_types_proof(
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
            let model_argument = if query.requires_numeric_exp_model() {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!(
                "apply (shared_query_expr_{index}_native_scalar_types_valid_generated_schema{model_argument})."
            );
        }
        self.emit_query_expr_body_scalar_types_proof(query, reference_policy)
    }

    fn emit_query_expr_body_scalar_types_proof(
        &self,
        query: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        let proof = match query {
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => "constructor.".to_owned(),
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => rocq_conjunction_proof(vec![
                self.emit_query_expr_scalar_types_proof(left, reference_policy),
                self.emit_query_expr_scalar_types_proof(right, reference_policy),
            ]),
            FormalQueryExpr::Join {
                join_kind,
                predicate,
                matched_select,
                left_select,
                right_select,
                left,
                right,
                ..
            } => rocq_conjunction_proof(vec![
                self.emit_formula_expr_scalar_types_proof(
                    predicate,
                    reference_policy.formula_exprs,
                ),
                self.emit_join_select_lists_types_proof(
                    *join_kind,
                    matched_select,
                    left_select,
                    right_select,
                ),
                self.emit_query_expr_scalar_types_proof(left, reference_policy),
                self.emit_query_expr_scalar_types_proof(right, reference_policy),
            ]),
            FormalQueryExpr::Projection { select, input } => rocq_conjunction_proof(vec![
                self.emit_select_list_types_proof(select),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::RowMap { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => {
                self.emit_query_expr_scalar_types_proof(input, reference_policy)
            }
            FormalQueryExpr::ScalarProjection { select, input } => rocq_conjunction_proof(vec![
                self.emit_scalar_select_list_types_proof(select),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::Selection { predicate, input } => rocq_conjunction_proof(vec![
                self.emit_formula_expr_scalar_types_proof(
                    predicate,
                    reference_policy.formula_exprs,
                ),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::ScalarSelection { predicate, input } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_types_proof(predicate, reference_policy.scalar_exprs),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => rocq_conjunction_proof(vec![
                self.emit_select_list_types_proof(select),
                self.emit_aggregate_terms_existential_types_proof(group_by),
                self.emit_formula_expr_scalar_types_proof(having, reference_policy.formula_exprs),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => rocq_conjunction_proof(vec![
                self.emit_grouping_sets_scalar_types_proof(grouping_sets),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::Rank { input, .. } => rocq_conjunction_proof(vec![
                "reflexivity.".to_owned(),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::Window { items, input, .. } => rocq_conjunction_proof(vec![
                self.emit_window_items_scalar_types_proof(items),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
            FormalQueryExpr::ScalarGroup {
                select,
                group_by,
                having,
                input,
            } => rocq_conjunction_proof(vec![
                self.emit_scalar_select_list_types_proof(select),
                rocq_forall_list_proof(
                    &group_by
                        .iter()
                        .map(|key| self.emit_scalar_expr_types_proof(key, false))
                        .collect::<Vec<_>>(),
                ),
                self.emit_scalar_expr_types_proof(having, reference_policy.scalar_exprs),
                self.emit_query_expr_scalar_types_proof(input, reference_policy),
            ]),
        };
        rocq_cbn_only_proof("query_expr_scalar_types_valid", proof)
    }

    fn emit_select_list_types_proof(&self, select: &[FormalSelectItem]) -> String {
        let proof = rocq_cbn_only_proof(
            "query_select_list_scalar_types_valid",
            rocq_forall_list_proof(
                &select
                    .iter()
                    .map(|_| "solve_generated_scalar_type.".to_owned())
                    .collect::<Vec<_>>(),
            ),
        );
        self.select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("unfold select_list_{index}.\n{proof}"))
            .unwrap_or(proof)
    }

    fn emit_select_list_phase_admissibility_proof(
        &self,
        select: &[FormalSelectItem],
        phase: ScalarPhase,
    ) -> String {
        let item_proof = if matches!(phase, ScalarPhase::Select | ScalarPhase::Having) {
            "left; reflexivity."
        } else {
            "right; reflexivity."
        };
        let proof = rocq_forall_list_proof(
            &select
                .iter()
                .map(|_| item_proof.to_owned())
                .collect::<Vec<_>>(),
        );
        self.select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| {
                format!(
                    "unfold select_list_{index}, SelectList, \
                     select_list_phase_admissible.\n{proof}"
                )
            })
            .unwrap_or_else(|| format!("unfold SelectList, select_list_phase_admissible.\n{proof}"))
    }

    fn emit_join_projection_closed_metadata_proof(
        &self,
        property: &str,
        select_lists: &[&Vec<FormalSelectItem>],
    ) -> String {
        let mut definitions = select_lists
            .iter()
            .filter_map(|select| {
                self.select_lists
                    .iter()
                    .position(|candidate| candidate == *select)
                    .map(|index| format!("select_list_{index}"))
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
        matched_select: &[FormalSelectItem],
        left_select: &[FormalSelectItem],
        right_select: &[FormalSelectItem],
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
                    self.emit_select_list_phase_admissibility_proof(select, ScalarPhase::RowSelect)
                })
                .collect(),
        );
        format!("unfold query_join_projections_phase_admissible.\n{proof}")
    }

    fn emit_aggregate_terms_phase_admissibility_proof(
        &self,
        terms: &[FormalAggregateTerm],
        phase: ScalarPhase,
    ) -> String {
        let term_proof = if matches!(phase, ScalarPhase::Select | ScalarPhase::Having) {
            "left; reflexivity."
        } else {
            "right; reflexivity."
        };
        rocq_forall_list_proof(
            &terms
                .iter()
                .map(|_| term_proof.to_owned())
                .collect::<Vec<_>>(),
        )
    }

    fn emit_aggregate_terms_existential_types_proof(
        &self,
        terms: &[FormalAggregateTerm],
    ) -> String {
        rocq_cbn_only_proof(
            "query_aggterms_scalar_types_valid",
            rocq_forall_list_proof(
                &terms
                    .iter()
                    .map(|_| "eexists; solve_generated_scalar_type.".to_owned())
                    .collect::<Vec<_>>(),
            ),
        )
    }

    fn emit_join_select_lists_types_proof(
        &self,
        join_kind: FormalQueryJoinKind,
        matched_select: &[FormalSelectItem],
        left_select: &[FormalSelectItem],
        right_select: &[FormalSelectItem],
    ) -> String {
        let proof = match join_kind {
            FormalQueryJoinKind::Left => rocq_conjunction_proof(vec![
                self.emit_select_list_types_proof(matched_select),
                self.emit_select_list_types_proof(left_select),
            ]),
            FormalQueryJoinKind::Right => rocq_conjunction_proof(vec![
                self.emit_select_list_types_proof(matched_select),
                self.emit_select_list_types_proof(right_select),
            ]),
            FormalQueryJoinKind::Full => rocq_conjunction_proof(vec![
                self.emit_select_list_types_proof(matched_select),
                self.emit_select_list_types_proof(left_select),
                self.emit_select_list_types_proof(right_select),
            ]),
            FormalQueryJoinKind::Semi | FormalQueryJoinKind::Anti => {
                self.emit_select_list_types_proof(left_select)
            }
        };
        rocq_cbn_only_proof("query_join_scalar_types_valid", proof)
    }

    fn emit_grouping_sets_scalar_types_proof(&self, grouping_sets: &[FormalGroupingSet]) -> String {
        rocq_cbn_only_proof(
            "query_grouping_sets_scalar_types_valid",
            rocq_forall_list_proof(
                &grouping_sets
                    .iter()
                    .map(|grouping_set| {
                        rocq_conjunction_proof(vec![
                            self.emit_select_list_types_proof(&grouping_set.select),
                            self.emit_aggregate_terms_existential_types_proof(
                                &grouping_set.group_by,
                            ),
                        ])
                    })
                    .collect::<Vec<_>>(),
            ),
        )
    }

    fn emit_window_items_scalar_types_proof(&self, items: &[FormalWindowItem]) -> String {
        rocq_forall_list_proof(
            &items
                .iter()
                .map(|item| {
                    rocq_cbn_only_proof(
                        "query_window_item_scalar_types_valid",
                        match &item.function {
                            FormalWindowFunction::RowNumber => "reflexivity.".to_owned(),
                            FormalWindowFunction::Aggregate { .. }
                            | FormalWindowFunction::FullPartitionAggregate { .. } => {
                                "solve_generated_scalar_type.".to_owned()
                            }
                        },
                    )
                })
                .collect::<Vec<_>>(),
        )
    }

    fn emit_formula_expr_scalar_types_proof(
        &self,
        formula: &FormalFormulaExpr,
        allow_formula_refs: bool,
    ) -> String {
        if allow_formula_refs
            && let Some(index) = self
                .formula_expr_predicates
                .iter()
                .position(|candidate| candidate == formula)
        {
            return format!(
                "unfold formula_expr_predicate_{index}.\n{}",
                self.emit_formula_expr_scalar_types_proof(formula, false)
            );
        }
        let existential_predicate_proof = |arguments: &[FormalAggregateTerm]| {
            rocq_focused_subproofs(
                "eexists.\nsplit.",
                &[
                    rocq_forall_list_proof(
                        &arguments
                            .iter()
                            .map(|_| "solve_generated_scalar_type.".to_owned())
                            .collect::<Vec<_>>(),
                    ),
                    "solve_generated_scalar_type.".to_owned(),
                ],
            )
        };
        let proof = match formula {
            FormalFormulaExpr::True | FormalFormulaExpr::False => "constructor.".to_owned(),
            FormalFormulaExpr::Predicate { args, .. } => existential_predicate_proof(args),
            FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
                rocq_conjunction_proof(vec![
                    self.emit_formula_expr_scalar_types_proof(left, false),
                    self.emit_formula_expr_scalar_types_proof(right, false),
                ])
            }
            FormalFormulaExpr::Not { formula } => {
                self.emit_formula_expr_scalar_types_proof(formula, false)
            }
            FormalFormulaExpr::QuantifiedComparison { args, query, .. } => {
                rocq_conjunction_proof(vec![
                    existential_predicate_proof(args),
                    self.emit_query_expr_scalar_types_proof(
                        query,
                        QueryExprReferencePolicy::uniform(false),
                    ),
                ])
            }
            FormalFormulaExpr::In { select, query } => rocq_conjunction_proof(vec![
                rocq_forall_list_proof(
                    &select
                        .iter()
                        .map(|_| "solve_generated_scalar_type.".to_owned())
                        .collect::<Vec<_>>(),
                ),
                self.emit_query_expr_scalar_types_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                ),
            ]),
            FormalFormulaExpr::Exists { query } => self.emit_query_expr_scalar_types_proof(
                query,
                QueryExprReferencePolicy::uniform(false),
            ),
            FormalFormulaExpr::Scalar { expression } => {
                self.emit_scalar_expr_types_proof(expression, false)
            }
        };
        rocq_cbn_only_proof("formula_expr_scalar_types_valid", proof)
    }

    fn emit_scalar_expr_types_proof(
        &self,
        expression: &FormalScalarExpr,
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
                "unfold scalar_expr_predicate_{index}.\n{}",
                self.emit_scalar_expr_types_proof(expression, false)
            );
        }
        let argument_proof = |arguments: &[FormalScalarExpr]| {
            rocq_forall_list_proof(
                &arguments
                    .iter()
                    .map(|argument| self.emit_scalar_expr_types_proof(argument, false))
                    .collect::<Vec<_>>(),
            )
        };
        let proof = match expression {
            FormalScalarExpr::Leaf { .. } => "solve_generated_scalar_type.".to_owned(),
            FormalScalarExpr::Call { args, .. } => rocq_conjunction_proof(vec![
                argument_proof(args),
                "solve_generated_scalar_type.".to_owned(),
            ]),
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_types_proof(condition, false),
                self.emit_scalar_expr_types_proof(then_expr, false),
                self.emit_scalar_expr_types_proof(else_expr, false),
            ]),
            FormalScalarExpr::BooleanValue { expression } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_types_proof(expression, false),
                "intros truth; destruct truth; reflexivity.".to_owned(),
            ]),
            FormalScalarExpr::ValueBoolean { expression } => rocq_conjunction_proof(vec![
                self.emit_scalar_expr_types_proof(expression, false),
                "reflexivity.".to_owned(),
            ]),
            FormalScalarExpr::Predicate { args, .. } => rocq_conjunction_proof(vec![
                argument_proof(args),
                "solve_generated_scalar_type.".to_owned(),
            ]),
            FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
                rocq_conjunction_proof(vec![
                    self.emit_scalar_expr_types_proof(left, false),
                    self.emit_scalar_expr_types_proof(right, false),
                ])
            }
            FormalScalarExpr::Not { expression } => {
                self.emit_scalar_expr_types_proof(expression, false)
            }
            FormalScalarExpr::True => "constructor.".to_owned(),
            FormalScalarExpr::QuantifiedComparison { args, query, .. } => {
                rocq_conjunction_proof(vec![
                    argument_proof(args),
                    "solve_generated_scalar_type.".to_owned(),
                    self.emit_query_expr_scalar_types_proof(
                        query,
                        QueryExprReferencePolicy::uniform(false),
                    ),
                ])
            }
            FormalScalarExpr::In { args, query } => rocq_conjunction_proof(vec![
                argument_proof(args),
                self.emit_query_expr_scalar_types_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                ),
            ]),
            FormalScalarExpr::Exists { query } | FormalScalarExpr::Subquery { query, .. } => self
                .emit_query_expr_scalar_types_proof(
                    query,
                    QueryExprReferencePolicy::uniform(false),
                ),
        };
        rocq_cbn_only_proof("scalar_expr_types_valid", proof)
    }

    fn emit_scalar_select_list_types_proof(&self, select: &[FormalScalarSelectItem]) -> String {
        let proof = rocq_forall_list_proof(
            &select
                .iter()
                .map(|item| self.emit_scalar_expr_types_proof(&item.expr, false))
                .collect::<Vec<_>>(),
        );
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("unfold scalar_select_list_{index}.\n{proof}"))
            .unwrap_or(proof)
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
            let model_argument = if query.requires_numeric_exp_model() {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!(
                "apply (shared_query_expr_{index}_admissible_with_outputs_generated_schema{model_argument})."
            );
        }
        self.emit_query_expr_body_admissibility_proof(query, reference_policy)
    }

    fn emit_query_expr_body_admissibility_proof(
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
                    self.emit_query_expr_admissibility_proof(left, reference_policy),
                    self.emit_query_expr_admissibility_proof(right, reference_policy),
                    rocq_metadata_proof(),
                ],
            ),
            FormalQueryExpr::CrossJoin { left, right } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_cross_join.",
                &[
                    self.emit_query_expr_admissibility_proof(left, reference_policy),
                    self.emit_query_expr_admissibility_proof(right, reference_policy),
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
                    self.emit_formula_expr_admissibility_proof(
                        predicate,
                        ScalarPhase::On,
                        reference_policy.formula_exprs,
                    ),
                    self.emit_query_expr_admissibility_proof(left, reference_policy),
                    self.emit_query_expr_admissibility_proof(right, reference_policy),
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
                    ),
                ],
            ),
            FormalQueryExpr::Projection { select, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_project.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    self.emit_select_list_phase_admissibility_proof(select, ScalarPhase::RowSelect),
                ],
            ),
            FormalQueryExpr::ScalarProjection { select, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_scalar_project.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    self.emit_scalar_select_list_admissibility_proof(
                        select,
                        ScalarPhase::RowSelect,
                    ),
                ],
            ),
            FormalQueryExpr::RowMap { input, .. } => rocq_focused_subproofs(
                "unfold NumericExpRowMapExpr, RowMapExpr.\n\
                 eapply query_expr_admissible_with_outputs_row_map.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    "apply NumericExpRowAdapter_well_sorted.".to_owned(),
                ],
            ),
            FormalQueryExpr::Selection { predicate, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_filter.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_formula_expr_admissibility_proof(
                        predicate,
                        ScalarPhase::Where,
                        reference_policy.formula_exprs,
                    ),
                ],
            ),
            FormalQueryExpr::ScalarSelection { predicate, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_scalar_filter.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_scalar_expr_admissibility_proof(
                        predicate,
                        ScalarPhase::Where,
                        reference_policy.scalar_exprs,
                    ),
                ],
            ),
            FormalQueryExpr::ScalarGroup {
                select,
                group_by,
                having,
                input,
            } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_scalar_group.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    rocq_metadata_proof(),
                    self.emit_scalar_select_list_admissibility_proof(select, ScalarPhase::Select),
                    self.emit_scalar_expr_admissibility_proof(
                        having,
                        ScalarPhase::Having,
                        reference_policy.scalar_exprs,
                    ),
                    rocq_forall_list_proof(
                        &group_by
                            .iter()
                            .map(|key| {
                                self.emit_scalar_expr_admissibility_proof(
                                    key,
                                    ScalarPhase::GroupBy,
                                    false,
                                )
                            })
                            .collect::<Vec<_>>(),
                    ),
                    rocq_metadata_proof(),
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
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_formula_expr_admissibility_proof(
                        having,
                        ScalarPhase::Having,
                        reference_policy.formula_exprs,
                    ),
                    rocq_metadata_proof(),
                    self.emit_select_list_phase_admissibility_proof(select, ScalarPhase::Select),
                    self.emit_aggregate_terms_phase_admissibility_proof(
                        group_by,
                        ScalarPhase::GroupBy,
                    ),
                ],
            ),
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_grouping_sets.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_grouping_sets_well_formed_proof(grouping_sets),
                    self.emit_grouping_sets_phase_admissibility_proof(grouping_sets),
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
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_sort_keys_in_outputs_proof(partition_keys),
                    self.emit_sort_keys_in_outputs_proof(order_keys),
                    rocq_focused_subproofs(
                        "eapply query_attribute_not_in_outputs.",
                        &[rocq_closed_attribute_nonmembership_proof()],
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
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_sort_keys_in_outputs_proof(partition_keys),
                    self.emit_sort_keys_in_outputs_proof(order_keys),
                    self.emit_window_items_fresh_proof(items),
                    rocq_focused_subproofs(
                        "eapply query_output_attributes_unique_from_all_diff.",
                        &[rocq_window_outputs_all_diff_proof(items.len())],
                    ),
                ],
            ),
            FormalQueryExpr::Distinct { input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_distinct.",
                &[self.emit_query_expr_admissibility_proof(input, reference_policy)],
            ),
            FormalQueryExpr::OrderBy { keys, input } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_order_by.",
                &[
                    self.emit_query_expr_admissibility_proof(input, reference_policy),
                    self.emit_sort_keys_in_outputs_proof(keys),
                ],
            ),
            FormalQueryExpr::Offset { input, .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_offset.",
                &[self.emit_query_expr_admissibility_proof(input, reference_policy)],
            ),
            FormalQueryExpr::Fetch { input, .. } => rocq_focused_subproofs(
                "eapply query_expr_admissible_with_outputs_fetch.",
                &[self.emit_query_expr_admissibility_proof(input, reference_policy)],
            ),
        };
        rocq_focused_subproofs(
            "eapply query_expr_admissible_with_outputs_change.",
            &[structural, rocq_metadata_proof()],
        )
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
        for (index, predicate) in self.formula_expr_predicates.iter().enumerate() {
            definitions.push(FormalQueryShapeDefinition {
                symbol: format!("formula_expr_predicate_{index}"),
                kind: FormalQueryShapeKind::FormulaExpr,
                tree: self.shape_formula_expr(predicate, false),
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

    /// Scalar select-list definitions may contain native subqueries whose
    /// projections use another emitted scalar select list. Preserve stable
    /// first-occurrence symbol indices, but place those nested list
    /// definitions before their containers so Rocq never sees a forward
    /// reference.
    fn scalar_select_list_emission_order(&self) -> Vec<usize> {
        fn visit(
            index: usize,
            lists: &[Vec<FormalScalarSelectItem>],
            states: &mut [u8],
            order: &mut Vec<usize>,
        ) {
            match states[index] {
                2 => return,
                1 => unreachable!("scalar select-list proper-subtree dependency cycle"),
                _ => {}
            }
            states[index] = 1;
            for dependency in 0..lists.len() {
                if dependency != index
                    && scalar_select_list_contains_list(&lists[index], &lists[dependency])
                {
                    visit(dependency, lists, states, order);
                }
            }
            states[index] = 2;
            order.push(index);
        }

        let mut states = vec![0; self.scalar_select_lists.len()];
        let mut order = Vec::with_capacity(self.scalar_select_lists.len());
        for index in 0..self.scalar_select_lists.len() {
            visit(index, &self.scalar_select_lists, &mut states, &mut order);
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
                    self.shape_formula_expr(predicate, reference_policy.formula_exprs),
                    self.shape_select_list(matched_select),
                    self.shape_select_list(left_select),
                    self.shape_select_list(right_select),
                    self.shape_query_expr_with_policy(left, reference_policy),
                    self.shape_query_expr_with_policy(right, reference_policy),
                ],
            ),
            FormalQueryExpr::Projection { select, input } => shape_node(
                "QExpr_Project",
                &[
                    self.shape_select_list(select),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::ScalarProjection { select, input } => shape_node(
                "QExpr_ScalarProject",
                &[
                    self.shape_scalar_select_list(select),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::RowMap { adapter, input } => match adapter {
                FormalRowMapAdapter::NumericExp { passthrough, .. } => shape_node_with_fields(
                    "NumericExpRowMapExpr",
                    &[format!("passthrough={}", passthrough.len())],
                    &[self.shape_query_expr_with_policy(input, reference_policy)],
                ),
            },
            FormalQueryExpr::Selection { predicate, input } => shape_node(
                "QExpr_Filter",
                &[
                    self.shape_formula_expr(predicate, reference_policy.formula_exprs),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::ScalarSelection { predicate, input } => shape_node(
                "QExpr_ScalarFilter",
                &[
                    self.shape_scalar_expr(predicate, reference_policy.scalar_exprs),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::ScalarGroup {
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
                    "QExpr_ScalarGroup",
                    &[format!("keys={}", group_by.len())],
                    &children,
                )
            }
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => shape_node_with_fields(
                "QExpr_Group",
                &[format!("keys={}", group_by.len())],
                &[
                    self.shape_select_list(select),
                    self.shape_formula_expr(having, reference_policy.formula_exprs),
                    self.shape_query_expr_with_policy(input, reference_policy),
                ],
            ),
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                let mut children = grouping_sets
                    .iter()
                    .map(|grouping_set| self.shape_select_list(&grouping_set.select))
                    .collect::<Vec<_>>();
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

    fn shape_formula_expr(&self, formula: &FormalFormulaExpr, allow_formula_refs: bool) -> String {
        if allow_formula_refs
            && let Some(index) = self
                .formula_expr_predicates
                .iter()
                .position(|candidate| candidate == formula)
        {
            return shape_reference(&format!("formula_expr_predicate_{index}"));
        }

        match formula {
            FormalFormulaExpr::True => "FExpr_True".to_owned(),
            FormalFormulaExpr::False => shape_node("FExpr_Not", &["FExpr_True".to_owned()]),
            FormalFormulaExpr::Predicate { predicate, args } => shape_node_with_fields(
                "FExpr_Pred",
                &[format!("args={}", args.len())],
                &[predicate.rocq_constructor().to_owned()],
            ),
            FormalFormulaExpr::And { left, right } => shape_node(
                "FExpr_Conj",
                &[
                    "And_F".to_owned(),
                    self.shape_formula_expr(left, false),
                    self.shape_formula_expr(right, false),
                ],
            ),
            FormalFormulaExpr::Or { left, right } => shape_node(
                "FExpr_Conj",
                &[
                    "Or_F".to_owned(),
                    self.shape_formula_expr(left, false),
                    self.shape_formula_expr(right, false),
                ],
            ),
            FormalFormulaExpr::Not { formula } => {
                shape_node("FExpr_Not", &[self.shape_formula_expr(formula, false)])
            }
            FormalFormulaExpr::In { select, query } => shape_node_with_fields(
                "FExpr_In",
                &[format!("select={}", select.len())],
                &[self.shape_query_expr(query, false)],
            ),
            FormalFormulaExpr::QuantifiedComparison {
                predicate,
                args,
                query,
            } => shape_node_with_fields(
                "FExpr_Quant",
                &[format!("args={}", args.len())],
                &[
                    "Exists_F".to_owned(),
                    predicate.rocq_constructor().to_owned(),
                    self.shape_query_expr(query, false),
                ],
            ),
            FormalFormulaExpr::Exists { query } => {
                shape_node("FExpr_Exists", &[self.shape_query_expr(query, false)])
            }
            FormalFormulaExpr::Scalar { expression } => shape_node(
                "FExpr_Scalar",
                &[self.shape_scalar_expr(expression, allow_formula_refs)],
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
                    format!("operator={operator:?}"),
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
            FormalScalarExpr::And { left, right } => shape_node(
                "SExpr_Conj",
                &[
                    "And_F".to_owned(),
                    self.shape_scalar_expr(left, false),
                    self.shape_scalar_expr(right, false),
                ],
            ),
            FormalScalarExpr::Or { left, right } => shape_node(
                "SExpr_Conj",
                &[
                    "Or_F".to_owned(),
                    self.shape_scalar_expr(left, false),
                    self.shape_scalar_expr(right, false),
                ],
            ),
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

    fn shape_select_list(&self, select: &[FormalSelectItem]) -> String {
        self.select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| shape_reference(&format!("select_list_{index}")))
            .unwrap_or_else(|| format!("#select{{items={}}}", select.len()))
    }

    fn shape_scalar_select_list(&self, select: &[FormalScalarSelectItem]) -> String {
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| shape_reference(&format!("scalar_select_list_{index}")))
            .unwrap_or_else(|| format!("#scalar-select{{items={}}}", select.len()))
    }

    fn emit_query_expr_definition(&self, name: &str, query: &FormalQueryExpr) -> String {
        let model_parameter = if query.requires_numeric_exp_model() {
            " (generated_numeric_exp_model : NumericExpModel)"
        } else {
            ""
        };
        format!(
            "Definition {name}{model_parameter} : QueryExpr :=\n{}.",
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
            let model_argument = if query.requires_numeric_exp_model() {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!("shared_query_expr_{index}{model_argument}");
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
                self.emit_formula_expr(predicate, reference_policy.formula_exprs),
                self.emit_select_list(matched_select),
                self.emit_select_list(left_select),
                self.emit_select_list(right_select),
                self.emit_query_expr_with_policy(left, reference_policy),
                self.emit_query_expr_with_policy(right, reference_policy)
            ),
            FormalQueryExpr::Projection { select, input } => format!(
                "QExpr_Project ({}) ({})",
                self.emit_select_list(select),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::ScalarProjection { select, input } => format!(
                "QExpr_ScalarProject ({}) ({})",
                self.emit_scalar_select_list(select),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::RowMap { adapter, input } => {
                self.emit_row_map(adapter, input, reference_policy)
            }
            FormalQueryExpr::Selection { predicate, input } => format!(
                "QExpr_Filter ({}) ({})",
                self.emit_formula_expr(predicate, reference_policy.formula_exprs),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::ScalarSelection { predicate, input } => format!(
                "QExpr_ScalarFilter ({}) ({})",
                self.emit_scalar_expr(predicate, reference_policy.scalar_exprs),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::ScalarGroup {
                select,
                group_by,
                having,
                input,
            } => format!(
                "QExpr_ScalarGroup ({}) ({}) ({}) ({})",
                self.emit_scalar_select_list(select),
                self.emit_scalar_expr_list(group_by),
                self.emit_scalar_expr(having, reference_policy.scalar_exprs),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
            } => format!(
                "QExpr_Group ({}) ({}) ({}) ({})",
                self.emit_select_list(select),
                emit_rocq_list(group_by, emit_rocq_aggregate_term),
                self.emit_formula_expr(having, reference_policy.formula_exprs),
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

    fn emit_row_map(
        &self,
        adapter: &FormalRowMapAdapter,
        input: &FormalQueryExpr,
        reference_policy: QueryExprReferencePolicy,
    ) -> String {
        match adapter {
            FormalRowMapAdapter::NumericExp {
                passthrough,
                avg_value,
                avg_dscale,
                output_numeric,
                output_dscale,
            } => format!(
                "NumericExpRowMapExpr ({}) ({}) ({}) ({}) ({}) generated_numeric_exp_model ({})",
                emit_rocq_query_attribute_list(passthrough),
                emit_rocq_attribute(avg_value.ty, &avg_value.name),
                emit_rocq_attribute(avg_dscale.ty, &avg_dscale.name),
                emit_rocq_attribute(output_numeric.ty, &output_numeric.name),
                emit_rocq_attribute(output_dscale.ty, &output_dscale.name),
                self.emit_query_expr_with_policy(input, reference_policy)
            ),
        }
    }

    fn emit_grouping_sets(&self, grouping_sets: &[FormalGroupingSet]) -> String {
        let rendered = grouping_sets
            .iter()
            .map(|grouping_set| {
                format!(
                    "({}, {})",
                    self.emit_select_list(&grouping_set.select),
                    emit_rocq_list(&grouping_set.group_by, emit_rocq_aggregate_term)
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

    fn emit_grouping_sets_phase_admissibility_proof(
        &self,
        grouping_sets: &[FormalGroupingSet],
    ) -> String {
        let grouping_set_proofs = grouping_sets
            .iter()
            .map(|grouping_set| {
                rocq_conjunction_proof(vec![
                    self.emit_select_list_phase_admissibility_proof(
                        &grouping_set.select,
                        ScalarPhase::Select,
                    ),
                    self.emit_aggregate_terms_phase_admissibility_proof(
                        &grouping_set.group_by,
                        ScalarPhase::GroupBy,
                    ),
                ])
            })
            .collect::<Vec<_>>();
        format!(
            "unfold query_grouping_sets_phase_admissible.\n{}",
            rocq_forall_list_proof(&grouping_set_proofs)
        )
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
                    &[rocq_closed_attribute_nonmembership_proof()],
                )
            })
            .collect::<Vec<_>>();
        rocq_forall_list_proof(&item_proofs)
    }

    fn emit_query_in_positionally_aligned_proof(&self) -> String {
        rocq_focused_subproofs(
            "cbn [query_in_positionally_aligned].\nsplit.",
            &[
                rocq_metadata_proof(),
                rocq_conjunction_proof(vec![rocq_metadata_proof(), rocq_metadata_proof()]),
            ],
        )
    }

    fn emit_formula_expr(&self, formula: &FormalFormulaExpr, allow_formula_refs: bool) -> String {
        if allow_formula_refs
            && let Some(index) = self
                .formula_expr_predicates
                .iter()
                .position(|candidate| candidate == formula)
        {
            let model_argument = if formula_expr_requires_numeric_exp_model(formula) {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!("formula_expr_predicate_{index}{model_argument}");
        }

        match formula {
            FormalFormulaExpr::True => "FExpr_True".to_owned(),
            FormalFormulaExpr::False => "FExpr_Not FExpr_True".to_owned(),
            FormalFormulaExpr::Predicate { predicate, args } => format!(
                "FExpr_Pred ({} : FTuples.Tuple.predicate TNull) ({})",
                predicate.rocq_constructor(),
                emit_rocq_list(args, emit_rocq_aggregate_term)
            ),
            FormalFormulaExpr::And { left, right } => format!(
                "FExpr_Conj And_F ({}) ({})",
                self.emit_formula_expr(left, false),
                self.emit_formula_expr(right, false)
            ),
            FormalFormulaExpr::Or { left, right } => format!(
                "FExpr_Conj Or_F ({}) ({})",
                self.emit_formula_expr(left, false),
                self.emit_formula_expr(right, false)
            ),
            FormalFormulaExpr::Not { formula } => {
                format!("FExpr_Not ({})", self.emit_formula_expr(formula, false))
            }
            FormalFormulaExpr::In { select, query } => format!(
                "FExpr_In ({}) ({})",
                emit_rocq_list(select, emit_rocq_select_item),
                self.emit_query_expr(query, false)
            ),
            FormalFormulaExpr::QuantifiedComparison {
                predicate,
                args,
                query,
            } => format!(
                "FExpr_Quant Exists_F ({} : FTuples.Tuple.predicate TNull) ({}) ({})",
                predicate.rocq_constructor(),
                emit_rocq_list(args, emit_rocq_aggregate_term),
                self.emit_query_expr(query, false)
            ),
            FormalFormulaExpr::Exists { query } => {
                format!("FExpr_Exists ({})", self.emit_query_expr(query, false))
            }
            FormalFormulaExpr::Scalar { expression } => format!(
                "FExpr_Scalar ({})",
                self.emit_scalar_expr(expression, allow_formula_refs)
            ),
        }
    }

    fn emit_scalar_expr(&self, expression: &FormalScalarExpr, allow_scalar_refs: bool) -> String {
        if allow_scalar_refs
            && expression.result_kind() == FormalScalarResultKind::Boolean
            && let Some(index) = self
                .scalar_expr_predicates
                .iter()
                .position(|candidate| candidate == expression)
        {
            let model_argument = if scalar_expr_requires_numeric_exp_model(expression) {
                " generated_numeric_exp_model"
            } else {
                ""
            };
            return format!("scalar_expr_predicate_{index}{model_argument}");
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
            FormalScalarExpr::And { left, right } => format!(
                "@SExpr_Conj TNull relname And_F ({}) ({})",
                self.emit_scalar_expr(left, false),
                self.emit_scalar_expr(right, false)
            ),
            FormalScalarExpr::Or { left, right } => format!(
                "@SExpr_Conj TNull relname Or_F ({}) ({})",
                self.emit_scalar_expr(left, false),
                self.emit_scalar_expr(right, false)
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

    fn emit_query_expr_expected_outputs(
        &self,
        query: &FormalQueryExpr,
        allow_query_expr_refs: bool,
    ) -> String {
        if allow_query_expr_refs
            && let Some(index) = self
                .shared_query_exprs
                .iter()
                .position(|candidate| candidate == query)
        {
            return format!("shared_query_expr_{index}_expected_outputs");
        }

        let outputs = query_expr_output_signature(query)
            .expect("validated Rocq emission has a complete exact-query output signature");
        emit_rocq_query_attribute_list(&outputs)
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

    fn emit_select_list(&self, select: &[FormalSelectItem]) -> String {
        self.select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| format!("select_list_{index}"))
            .unwrap_or_else(|| emit_rocq_select_list(select))
    }

    fn emit_scalar_select_list(&self, select: &[FormalScalarSelectItem]) -> String {
        self.scalar_select_lists
            .iter()
            .position(|candidate| candidate == select)
            .map(|index| {
                let model_argument = if scalar_select_requires_numeric_exp_model(select) {
                    " generated_numeric_exp_model"
                } else {
                    ""
                };
                format!("scalar_select_list_{index}{model_argument}")
            })
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
            left,
            right,
            ..
        } => {
            collect_formula_expr_query_counts(predicate, counts, order);
            collect_query_expr_counts(left, counts, order);
            collect_query_expr_counts(right, counts, order);
        }
        FormalQueryExpr::Selection {
            predicate, input, ..
        } => {
            collect_formula_expr_query_counts(predicate, counts, order);
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::ScalarProjection { select, input } => {
            for item in select {
                collect_scalar_expr_query_counts(&item.expr, counts, order);
            }
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::ScalarSelection { predicate, input } => {
            collect_scalar_expr_query_counts(predicate, counts, order);
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::ScalarGroup {
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
        FormalQueryExpr::Group { having, input, .. } => {
            collect_formula_expr_query_counts(having, counts, order);
            collect_query_expr_counts(input, counts, order);
        }
        FormalQueryExpr::GroupingSets { input, .. }
        | FormalQueryExpr::Rank { input, .. }
        | FormalQueryExpr::Window { input, .. } => collect_query_expr_counts(input, counts, order),
        FormalQueryExpr::Projection { input, .. }
        | FormalQueryExpr::RowMap { input, .. }
        | FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => collect_query_expr_counts(input, counts, order),
        FormalQueryExpr::Error { .. }
        | FormalQueryExpr::Empty { .. }
        | FormalQueryExpr::EmptyTuple
        | FormalQueryExpr::Table { .. } => {}
    }
}

fn collect_formula_expr_query_counts(
    formula: &FormalFormulaExpr,
    counts: &mut HashMap<FormalQueryExpr, usize>,
    order: &mut Vec<FormalQueryExpr>,
) {
    match formula {
        FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
            collect_formula_expr_query_counts(left, counts, order);
            collect_formula_expr_query_counts(right, counts, order);
        }
        FormalFormulaExpr::Not { formula } => {
            collect_formula_expr_query_counts(formula, counts, order)
        }
        FormalFormulaExpr::In { query, .. }
        | FormalFormulaExpr::QuantifiedComparison { query, .. }
        | FormalFormulaExpr::Exists { query } => collect_query_expr_counts(query, counts, order),
        FormalFormulaExpr::Scalar { expression } => {
            collect_scalar_expr_query_counts(expression, counts, order)
        }
        FormalFormulaExpr::True
        | FormalFormulaExpr::False
        | FormalFormulaExpr::Predicate { .. } => {}
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
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            collect_scalar_expr_query_counts(left, counts, order);
            collect_scalar_expr_query_counts(right, counts, order);
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
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            scalar_expr_contains_scalar_select_list(left, needle)
                || scalar_expr_contains_scalar_select_list(right, needle)
        }
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

fn formula_expr_contains_scalar_select_list(
    formula: &FormalFormulaExpr,
    needle: &[FormalScalarSelectItem],
) -> bool {
    match formula {
        FormalFormulaExpr::True
        | FormalFormulaExpr::False
        | FormalFormulaExpr::Predicate { .. } => false,
        FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
            formula_expr_contains_scalar_select_list(left, needle)
                || formula_expr_contains_scalar_select_list(right, needle)
        }
        FormalFormulaExpr::Not { formula } => {
            formula_expr_contains_scalar_select_list(formula, needle)
        }
        FormalFormulaExpr::In { query, .. }
        | FormalFormulaExpr::QuantifiedComparison { query, .. }
        | FormalFormulaExpr::Exists { query } => {
            query_expr_contains_scalar_select_list(query, needle)
        }
        FormalFormulaExpr::Scalar { expression } => {
            scalar_expr_contains_scalar_select_list(expression, needle)
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
            left,
            right,
            ..
        } => {
            formula_expr_contains_scalar_select_list(predicate, needle)
                || query_expr_contains_scalar_select_list(left, needle)
                || query_expr_contains_scalar_select_list(right, needle)
        }
        FormalQueryExpr::Projection { input, .. }
        | FormalQueryExpr::RowMap { input, .. }
        | FormalQueryExpr::GroupingSets { input, .. }
        | FormalQueryExpr::Rank { input, .. }
        | FormalQueryExpr::Window { input, .. }
        | FormalQueryExpr::Distinct { input }
        | FormalQueryExpr::OrderBy { input, .. }
        | FormalQueryExpr::Offset { input, .. }
        | FormalQueryExpr::Fetch { input, .. } => {
            query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::ScalarProjection { select, input } => {
            select == needle
                || scalar_select_list_contains_list(select, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::Selection { predicate, input } => {
            formula_expr_contains_scalar_select_list(predicate, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::ScalarSelection { predicate, input } => {
            scalar_expr_contains_scalar_select_list(predicate, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::Group { having, input, .. } => {
            formula_expr_contains_scalar_select_list(having, needle)
                || query_expr_contains_scalar_select_list(input, needle)
        }
        FormalQueryExpr::ScalarGroup {
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
            left,
            right,
            ..
        } => {
            query_expr_occurrences(left, needle)
                + query_expr_occurrences(right, needle)
                + formula_expr_query_occurrences(predicate, needle)
        }
        FormalQueryExpr::Selection {
            predicate, input, ..
        } => {
            query_expr_occurrences(input, needle)
                + formula_expr_query_occurrences(predicate, needle)
        }
        FormalQueryExpr::ScalarProjection { select, input } => {
            query_expr_occurrences(input, needle)
                + select
                    .iter()
                    .map(|item| scalar_expr_query_occurrences(&item.expr, needle))
                    .sum::<usize>()
        }
        FormalQueryExpr::ScalarSelection { predicate, input } => {
            query_expr_occurrences(input, needle) + scalar_expr_query_occurrences(predicate, needle)
        }
        FormalQueryExpr::ScalarGroup {
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
        FormalQueryExpr::Group { having, input, .. } => {
            query_expr_occurrences(input, needle) + formula_expr_query_occurrences(having, needle)
        }
        FormalQueryExpr::GroupingSets { input, .. }
        | FormalQueryExpr::Rank { input, .. }
        | FormalQueryExpr::Window { input, .. } => query_expr_occurrences(input, needle),
        FormalQueryExpr::Projection { input, .. }
        | FormalQueryExpr::RowMap { input, .. }
        | FormalQueryExpr::Distinct { input }
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

fn formula_expr_query_occurrences(formula: &FormalFormulaExpr, needle: &FormalQueryExpr) -> usize {
    match formula {
        FormalFormulaExpr::And { left, right } | FormalFormulaExpr::Or { left, right } => {
            formula_expr_query_occurrences(left, needle)
                + formula_expr_query_occurrences(right, needle)
        }
        FormalFormulaExpr::Not { formula } => formula_expr_query_occurrences(formula, needle),
        FormalFormulaExpr::In { query, .. }
        | FormalFormulaExpr::QuantifiedComparison { query, .. }
        | FormalFormulaExpr::Exists { query } => query_expr_occurrences(query, needle),
        FormalFormulaExpr::Scalar { expression } => {
            scalar_expr_query_occurrences(expression, needle)
        }
        FormalFormulaExpr::True
        | FormalFormulaExpr::False
        | FormalFormulaExpr::Predicate { .. } => 0,
    }
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
        FormalScalarExpr::And { left, right } | FormalScalarExpr::Or { left, right } => {
            scalar_expr_query_occurrences(left, needle)
                + scalar_expr_query_occurrences(right, needle)
        }
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

fn scalar_select_requires_numeric_exp_model(select: &[FormalScalarSelectItem]) -> bool {
    select
        .iter()
        .any(|item| scalar_expr_requires_numeric_exp_model(&item.expr))
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

fn column_ref_constructor(attribute_ty: FormalAttributeType) -> &'static str {
    match attribute_ty {
        FormalAttributeType::Z => "ZColumn",
        FormalAttributeType::Int32 => "Int32Column",
        FormalAttributeType::Int64 => "Int64Column",
        FormalAttributeType::String { .. } => "StringColumn",
        FormalAttributeType::Bool => "BoolColumn",
        FormalAttributeType::Float => "FloatColumn",
        FormalAttributeType::Double => "DoubleColumn",
        FormalAttributeType::Numeric => "NumericColumn",
        FormalAttributeType::Decimal { .. } => "DecimalColumn",
        FormalAttributeType::Date => "DateColumn",
        FormalAttributeType::Time => "TimeColumn",
        FormalAttributeType::Timestamp { .. } => "TimestampColumn",
        FormalAttributeType::Timestamptz { .. } => "TimestamptzColumn",
    }
}

fn emit_rocq_select_list(select: &[FormalSelectItem]) -> String {
    let columns = select
        .iter()
        .map(identity_select_column)
        .collect::<Option<Vec<_>>>();
    if let Some(columns) = columns {
        return format!("SelectColumns {}", emit_rocq_list_expr(&columns));
    }
    format!(
        "SelectList {}",
        emit_rocq_list(select, emit_rocq_select_item)
    )
}

fn emit_rocq_select_item(item: &FormalSelectItem) -> String {
    if let FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::Attribute { name, ty },
    } = &item.expr
        && name == &item.alias
        && attribute_types_emit_equivalent(*ty, item.alias_ty)
        && let Some(select_constructor) = identity_select_constructor(*ty)
    {
        return emit_rocq_named_helper(select_constructor, name, *ty);
    }
    format!(
        "SelectAs ({}) ({})",
        emit_rocq_aggregate_term(&item.expr),
        emit_rocq_attribute(item.alias_ty, &item.alias)
    )
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
            emit_rocq_list(args, emit_rocq_aggregate_term)
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

fn identity_select_constructor(attribute_ty: FormalAttributeType) -> Option<&'static str> {
    match attribute_ty {
        FormalAttributeType::Z => Some("SelectZ"),
        FormalAttributeType::Int32 => Some("SelectInt32"),
        FormalAttributeType::Int64 => Some("SelectInt64"),
        FormalAttributeType::String { .. } => Some("SelectString"),
        FormalAttributeType::Bool => Some("SelectBool"),
        FormalAttributeType::Float => Some("SelectFloat"),
        FormalAttributeType::Double => Some("SelectDouble"),
        FormalAttributeType::Numeric => Some("SelectNumeric"),
        FormalAttributeType::Decimal { .. } => Some("SelectDecimal"),
        FormalAttributeType::Date => Some("SelectDate"),
        FormalAttributeType::Time => Some("SelectTime"),
        FormalAttributeType::Timestamp { .. } => Some("SelectTimestamp"),
        FormalAttributeType::Timestamptz { .. } => Some("SelectTimestamptz"),
    }
}

fn attribute_types_emit_equivalent(left: FormalAttributeType, right: FormalAttributeType) -> bool {
    match (left, right) {
        (
            FormalAttributeType::Timestamp { precision: left },
            FormalAttributeType::Timestamp { precision: right },
        ) => timestamp_precision(left) == timestamp_precision(right),
        (
            FormalAttributeType::Timestamptz { precision: left },
            FormalAttributeType::Timestamptz { precision: right },
        ) => timestamp_precision(left) == timestamp_precision(right),
        _ => left == right,
    }
}

fn identity_select_column(item: &FormalSelectItem) -> Option<String> {
    let FormalAggregateTerm::Expr {
        term: FormalFunctionTerm::Attribute { name, ty },
    } = &item.expr
    else {
        return None;
    };
    if name != &item.alias || !attribute_types_emit_equivalent(*ty, item.alias_ty) {
        return None;
    }
    Some(emit_rocq_named_helper(
        column_ref_constructor(*ty),
        name,
        *ty,
    ))
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
    if items.len() <= 3 && single_line.len() <= 88 && !items.iter().any(|item| item.contains('\n'))
    {
        return single_line;
    }

    let mut lines = Vec::with_capacity(items.len() + 2);
    lines.push("[".to_owned());
    for (index, item) in items.iter().enumerate() {
        let suffix = if index + 1 == items.len() { "" } else { ";" };
        let item = indent_rocq_expr(item, 2);
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
