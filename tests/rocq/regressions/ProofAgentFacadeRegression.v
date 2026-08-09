(******************************************************************************)
(** Semantic regressions for the canonical proof-agent facade.                 **)
(******************************************************************************)

From SQLFS Require Import FiniteBag FiniteCollection FTuples GenericInstance
  SqlOrder SqlOutcome SqlQuerySemantics SqlQuerySyntax SqlQueryWellFormed Values.
From Logos.FormalSQL Require Import TNullSyntax ProofAgentFacade.
From Stdlib Require Import List String ZArith.

Import ListNotations.
Import Tuple.
Open Scope string_scope.
Open Scope Z_scope.

Definition facade_schedule (_ : boolean_site) : boolean_evaluation_order :=
  BooleanLeftFirst.

Definition facade_value_expression : TNullScalarValueExpr :=
  @SExpr_Leaf TNull relname type_Z (CstZ 1).

Definition facade_boolean_expression : TNullScalarBooleanExpr :=
  @SExpr_True TNull relname.

Definition facade_output : TNullAttribute := AttrZ "facade_output".

Definition facade_select : TNullQuerySelectList :=
  [(facade_value_expression, facade_output)].

Definition facade_input : TNullQueryExpr :=
  @QExpr_Values TNull relname nil
    (Febag.empty (Fecol.CBag (CTuple TNull))).

(** Every query operator consumes the one typed scalar surface. *)
Definition facade_project : TNullQueryExpr :=
  QExpr_Project facade_select facade_input.

Definition facade_filter : TNullQueryExpr :=
  QExpr_Filter facade_boolean_expression facade_input.

Definition facade_group : TNullQueryExpr :=
  QExpr_Group facade_select [facade_value_expression]
    facade_boolean_expression facade_input.

Definition facade_join : TNullQueryExpr :=
  QExpr_Join QueryJoinInner facade_boolean_expression
    facade_select facade_select facade_select facade_input facade_input.

Definition facade_grouping_sets : TNullQueryExpr :=
  QExpr_GroupingSets [(facade_select, [facade_value_expression])]
    facade_input.

Section OutcomeAndAdmission.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variable outputs : list TNullAttribute.
Variable error : sql_runtime_error.
Hypothesis outputs_unique : query_output_attributes_unique TNull outputs.

Example canonical_tnull_admission_uses_the_single_hook :
  TNullQueryExprAdmissible (@_basesort TNull db)
    (@QExpr_Error TNull relname outputs error).
Proof.
  cbn [TNullQueryExprAdmissible query_expr_admissible].
  repeat split; try exact outputs_unique; constructor.
Qed.

Example exact_error_outcome_remains_public :
  TNullQueryExprOutcome db env
    (QExpr_Error outputs error) (SqlError error).
Proof.
  unfold TNullQueryExprOutcome, eval_query_expr_outcome_in_env.
  exists facade_schedule; constructor.
Qed.

End OutcomeAndAdmission.

Section OrderedAndBagObservations.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variable query : TNullQueryExpr.
Variable rows : list TNullRow.

Hypothesis exact_rows :
  TNullQueryExprOutcome db env query (SqlSuccess rows).

Example ordered_success_maps_to_the_proved_bag_observation :
  TNullQuerySuccessBag db env query (TNullRowsBag rows).
Proof.
  now apply tnull_query_success_outcome_is_success_bag.
Qed.

(** The exact ordered relation is not replaced by its bag abstraction. *)
Check TNullRowsObservationEq.
Check TNullBagEq.

End OrderedAndBagObservations.

Section OutcomeSeparation.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables left right : TNullQueryExpr.
Variable error : sql_runtime_error.

Hypothesis left_error :
  TNullQueryExprOutcome db env left (SqlError error).
Hypothesis right_no_error :
  ~ TNullQueryExprOutcome db env right (SqlError error).

Example exact_error_separation_refutes_outcome_equivalence :
  ~ TNullQueryExprOutcomeEq db env left right.
Proof.
  apply tnull_query_expr_outcome_separation_sound.
  now apply OutcomeSeparationLeftError with (error := error).
Qed.

End OutcomeSeparation.

Section TransparentTactic.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables left right : TNullQueryExpr.
Variable keys : list (sort_key TNull).

Hypothesis core_outcomes : TNullQueryExprOutcomeEq db env left right.

Example logos_lifts_only_transparent_ordered_shells :
  TNullQueryExprOutcomeEq db env
    (QExpr_Distinct (QExpr_OrderBy keys (QExpr_Fetch 2 left)))
    (QExpr_Distinct (QExpr_OrderBy keys (QExpr_Fetch 2 right))).
Proof.
  unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
  logos.
Qed.

End TransparentTactic.

(** Success-only safety mode and error-preserving mode remain separate. *)
Check query_expr_equiv_in_env.
Check query_expr_outcome_equiv_in_env.
