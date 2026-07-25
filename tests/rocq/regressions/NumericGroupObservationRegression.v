(******************************************************************************)
(** Closed-group NUMERIC SUM observation and regrouping regressions.         **)
(******************************************************************************)

From Stdlib Require Import List Sorting.Permutation.
From SQLFS Require Import
  Env FiniteSet FTerms FTuples GenericInstance SqlErrorSemantics
  SqlQuerySemantics Values.
From Logos.FormalSQL Require Import NumericRegroupFacts TNullSyntax.

Import ListNotations.
Import NullValues.
Import Tuple.

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

Theorem closed_group_sum_numeric_dot_outer_sum_regression :
  forall grouping_env rows group_terms attribute,
    group_terms <> nil ->
    Forall
      (fun row =>
        attribute inS labels TNull row /\
        is_numeric_value (dot TNull row attribute) = true)
      rows ->
    let groups := @query_make_groups TNull grouping_env rows group_terms in
    let grouped_sums :=
      map
        (fun group =>
          Interp.interp_aggterm TNull
            (Env.env_g TNull nil
              (@Env.Group_By TNull group_terms) group)
            (tnull_sum_numeric_dot_term attribute))
        groups in
    interp_sum_numeric grouped_sums =
      interp_sum_numeric
        (map (fun row => dot TNull row attribute) rows) /\
    sum_numeric_runtime_error grouped_sums =
      sum_numeric_runtime_error
        (map (fun row => dot TNull row attribute) rows).
Proof.
exact
  (@query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact).
Qed.

Print Assumptions
  tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows.
Print Assumptions tnull_closed_group_sum_numeric_dot_value_runtime_exact.
Print Assumptions
  query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact.
