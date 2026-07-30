From SQLFS Require Import
  ATerms Bool3 FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  OrderedSet SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax
  Values.
From Logos.FormalSQL Require Import AggregateOutcomeBridgeFacts.
From Stdlib Require Import List ZArith.

Import ListNotations.
Import NullValues.

Open Scope Z_scope.

(** Equal cardinality, rather than row type or row equality, is the complete
    COUNT-star value and overflow observation. *)
Theorem count_star_equal_cardinality_interface : forall left right,
  List.length left = List.length right ->
  interp_aggregate AggregateCountStar left =
    interp_aggregate AggregateCountStar right /\
  aggregate_local_runtime_error AggregateCountStar left =
    aggregate_local_runtime_error AggregateCountStar right.
Proof.
  apply count_star_value_local_error_exact_of_equal_length.
Qed.

(** COUNT(ALL expr) retains duplicate multiplicity.  Explicit child safety
    and non-NULL values make it agree with COUNT-star, including overflow. *)
Example count_star_count_all_nonnull_runtime_interface :
  interp_aggregate AggregateCountStar
    (observation_values
      [(None, Value_bool (Some true)); (None, Value_Z None)]) =
  interp_aggregate (AggregateCall AggregateCount AggregateAll)
    (observation_values
      [(None, Value_Z (Some 7)); (None, Value_Z (Some 7))]) /\
  interp_aggregate_runtime_error AggregateCountStar
    [(None, Value_bool (Some true)); (None, Value_Z None)] =
  interp_aggregate_runtime_error
    (AggregateCall AggregateCount AggregateAll)
    [(None, Value_Z (Some 7)); (None, Value_Z (Some 7))].
Proof.
  apply count_star_count_all_nonnull_value_runtime_error_exact.
  - reflexivity.
  - repeat constructor; reflexivity.
Qed.

Section GenericPredicateOutcomeInterface.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

(** This wrapper applies the formula/HAVING seam in both outcome directions;
    equal successful values alone are not enough without equal first errors. *)
Example predicate_argument_observation_outcome_interface :
  forall left_env right_env predicate left_arguments right_arguments,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      left_arguments =
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      right_arguments ->
    map (@Interp.interp_aggterm T left_env) left_arguments =
    map (@Interp.interp_aggterm T right_env) right_arguments ->
    forall outcome,
      @eval_formula_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_env (FExpr_Pred predicate left_arguments) outcome <->
      @eval_formula_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_env (FExpr_Pred predicate right_arguments) outcome.
Proof.
  intros; eapply formula_pred_outcome_equiv_of_argument_observations;
    eassumption.
Qed.

End GenericPredicateOutcomeInterface.

Section CountStarGroupOutcomeInterface.

Context {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A TNull).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple TNull)).

(** This wrapper applies the complete TRUE-HAVING Forall2 lift.  Its success
    relation remains semantic permutation, while equal-length group pairing
    preserves COUNT overflow and first-error behavior. *)
Example count_star_true_groups_outcome_interface :
  forall left_env right_env left_group_terms right_group_terms
      left_groups right_groups output,
    Forall2
      (fun left_group right_group =>
        List.length left_group = List.length right_group)
      left_groups right_groups ->
    (exists outcome,
      @eval_groups_outcome TNull relname basesort instance unknown3
        interp_scalar_operator_runtime_error interp_aggregate_runtime_error
        is_null_value left_env (tnull_count_star_select_list output)
        left_group_terms FExpr_True left_groups outcome) ->
    outcome_relation_equiv (Oeset.permut (Tuple.OTuple TNull))
      (@eval_groups_outcome TNull relname basesort instance unknown3
        interp_scalar_operator_runtime_error interp_aggregate_runtime_error
        is_null_value left_env (tnull_count_star_select_list output)
        left_group_terms FExpr_True left_groups)
      (@eval_groups_outcome TNull relname basesort instance unknown3
        interp_scalar_operator_runtime_error interp_aggregate_runtime_error
        is_null_value right_env (tnull_count_star_select_list output)
        right_group_terms FExpr_True right_groups).
Proof.
  intros; eapply tnull_count_star_groups_true_outcome_equiv_of_Forall2_length;
    eassumption.
Qed.

End CountStarGroupOutcomeInterface.

(** The remaining checks exercise the syntax/HAVING and group-scheduler
    routing surfaces without fixing a schema, relation, or column. *)
Check formula_pred_outcome_equiv_of_argument_observations.
Check aggterm_observation_at.
Check tnull_group_count_star_projection_eq_of_equal_length.
Check tnull_count_star_group_observation_equiv_of_equal_length.
Check tnull_count_star_groups_outcome_equiv_of_Forall2_observations.
Check tnull_count_star_groups_true_outcome_equiv_of_Forall2_length.

Print Assumptions tnull_group_count_star_value_runtime_exact.
Print Assumptions count_star_value_local_error_exact_of_equal_length.
Print Assumptions count_star_value_runtime_error_exact_of_equal_observation_length.
Print Assumptions count_star_count_all_nonnull_value_local_error_exact.
Print Assumptions count_star_count_all_nonnull_value_runtime_error_exact.
Print Assumptions formula_pred_outcome_equiv_of_argument_observations.
Print Assumptions tnull_count_star_groups_outcome_equiv_of_Forall2_observations.
Print Assumptions tnull_count_star_groups_true_outcome_equiv_of_Forall2_length.
