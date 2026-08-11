(******************************************************************************)
(** Exact nullable-NUMERIC singleton and regrouping runtime regressions.     **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import Values ValueNumeric.
From Logos.FormalSQL Require Import NumericRegroupFacts.

Check fixed_decimal_sum_runtime_safe_of_cardinality.
Check fixed_decimal_avg_runtime_safe_of_cardinality.

Import ListNotations.
Import NullValues.

Example numeric_sum_singleton_null_regression :
  interp_sum_numeric [Value_numeric None] = Value_numeric None.
Proof.
apply interp_sum_numeric_singleton.
Qed.

Example numeric_sum_singleton_nan_regression :
  interp_sum_numeric [Value_numeric (Some NumericNaN)] =
    Value_numeric (Some NumericNaN).
Proof.
apply interp_sum_numeric_singleton.
Qed.

Example numeric_sum_singleton_runtime_nan_regression :
  sum_numeric_runtime_error [Value_numeric (Some NumericNaN)] =
    numeric_result_runtime_error NumericNaN.
Proof.
apply sum_numeric_runtime_error_singleton.
Qed.

Theorem numeric_sum_regroup_value_runtime_regression :
  forall groups subtotals,
    Forall
      (fun observations => forallb is_numeric_value observations = true)
      groups ->
    forallb is_numeric_value subtotals = true ->
    numeric_values subtotals =
      flat_map
        (fun numbers =>
          match fold_left numeric_sum_option_add numbers None with
          | Some total => [total]
          | None => []
          end)
        (map numeric_values groups) ->
    interp_sum_numeric subtotals = interp_sum_numeric (concat groups) /\
    sum_numeric_runtime_error subtotals =
      sum_numeric_runtime_error (concat groups).
Proof.
intros; now apply interp_sum_numeric_regroup_value_runtime_exact.
Qed.

Print Assumptions interp_sum_numeric_singleton.
Print Assumptions sum_numeric_runtime_error_singleton.
Print Assumptions interp_sum_numeric_regroup_value_runtime_exact.
