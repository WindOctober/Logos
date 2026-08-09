(******************************************************************************)
(** Closed-group NUMERIC SUM observation and regrouping regressions.         **)
(******************************************************************************)

From Stdlib Require Import List Sorting.Permutation.
From SQLFS Require Import
  Env FiniteSet FTerms FTuples GenericInstance SqlErrorSemantics
  SqlOutcome SqlQuerySemantics Values.
From Logos.FormalSQL Require Import
  AggregateRuntimeFacts NumericRegroupFacts TNullSyntax.

Import ListNotations.
Import NullValues.
Import Tuple.

Section GenericDirectColumnArgumentObservation.

Context {T : Tuple.Rcd}.

Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.

(** This regression intentionally quantifies over the tuple model and the
    aggregate value.  Its conclusion is only the selected argument schedule,
    so it supplies no permutation congruence for FLOAT/DOUBLE SUM or AVG. *)
Theorem closed_group_direct_column_argument_observations_regression :
  forall group_terms group aggregate attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels T row)
      group ->
    Permutation
      (closed_group_direct_column_argument_observations
        symbol_runtime_error group_terms group aggregate attribute)
      (map (fun row => (None, dot T row attribute)) group).
Proof.
  exact
    (@closed_group_direct_column_argument_observations_permutation_rows
      T symbol_runtime_error).
Qed.

End GenericDirectColumnArgumentObservation.

Theorem closed_group_sum_numeric_dot_observations_regression :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Permutation
      (tnull_closed_group_sum_numeric_dot_argument_observations
        group_terms group attribute)
      (map (fun row => (None, dot TNull row attribute)) group).
Proof.
exact
  (@tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows).
Qed.

Theorem closed_group_sum_numeric_dot_value_runtime_regression :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Interp.interp_aggterm TNull
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
      interp_sum_numeric (map (fun row => dot TNull row attribute) group) /\
    @eval_aggterm_aggregate_runtime_error TNull
      interp_scalar_operator_runtime_error
      interp_aggregate_runtime_error
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
      sum_numeric_runtime_error
        (map (fun row => dot TNull row attribute) group).
Proof.
exact (@tnull_closed_group_sum_numeric_dot_value_runtime_exact).
Qed.

Print Assumptions
  tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows.
Print Assumptions tnull_closed_group_sum_numeric_dot_value_runtime_exact.
Print Assumptions
  closed_group_direct_column_argument_observations_permutation_rows.
Print Assumptions
  closed_group_direct_column_argument_observations_regression.
