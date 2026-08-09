(******************************************************************************)
(** Generic regression for extensional, error-preserving WHERE transport.    **)
(******************************************************************************)

From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet Formula OrderedSet
  SqlBagAbstraction SqlErrorSemantics SqlOutcome SqlQuerySemantics
  SqlQuerySyntax.
From Logos.FormalSQL Require Import GroupedFilterOutcomeFacts.

Import Tuple.

Section FilterExtensionalOutcomeRegression.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T ->
  list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T ->
  list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation filter_observation :=
  (@filter_scalar_observation_equiv_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Theorem ordered_filter_scheduler_regression :
  forall left_env left_predicate left_rows
      right_env right_predicate right_rows,
    ordered_rows_equiv T left_rows right_rows ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_observation
        (env_t T left_env left_row) left_predicate
        (env_t T right_env right_row) right_predicate) ->
    (exists outcome,
      eval_filter_rows left_env left_predicate left_rows outcome) ->
    outcome_relation_equiv (ordered_rows_equiv T)
      (eval_filter_rows left_env left_predicate left_rows)
      (eval_filter_rows right_env right_predicate right_rows).
Proof.
intros; now eapply eval_filter_rows_ordered_outcome_congr.
Qed.

Theorem query_filter_extensional_regression :
  forall env left_predicate right_predicate left_input right_input,
    query_outcome_equiv env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_observation
        (env_t T env left_row) left_predicate
        (env_t T env right_row) right_predicate) ->
    (exists outcome,
      eval_query env (QExpr_Filter left_predicate left_input) outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_predicate left_input)
      (QExpr_Filter right_predicate right_input).
Proof.
intros; now eapply query_expr_filter_outcome_congr_extensional.
Qed.

End FilterExtensionalOutcomeRegression.

Print Assumptions filter_scalar_observation_equiv_at_sym.
Print Assumptions eval_filter_rows_ordered_outcome_congr_forward.
Print Assumptions eval_filter_rows_ordered_outcome_congr.
Print Assumptions query_expr_filter_outcome_congr_extensional_forward.
Print Assumptions query_expr_filter_outcome_congr_extensional.
