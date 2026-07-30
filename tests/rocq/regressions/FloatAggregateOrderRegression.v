From SQLFS Require Import Values.
From Logos.FormalSQL Require Import GroupedFilterOutcomeFacts.
From Stdlib Require Import List.

Import ListNotations.

(** IEEE-754 addition is not invariant under input permutation.  Therefore the
    concrete SUM and AVG interpreters cannot satisfy an unconditional bag-fold
    congruence for REAL or DOUBLE PRECISION. *)
Example float_sum_depends_on_representative_order :
  exists first second third,
    NullValues.interp_sum_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some second);
       NullValues.Value_float (Some third)] <>
    NullValues.interp_sum_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some third);
       NullValues.Value_float (Some second)].
Proof.
destruct float32_add_order_sensitive as
  [first [second [third Horder]]].
exists first, second, third.
unfold NullValues.interp_sum_float; cbn.
intro Hequal; injection Hequal as Hequal; now apply Horder.
Qed.

Example float_average_depends_on_representative_order :
  exists first second third,
    NullValues.interp_avg_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some second);
       NullValues.Value_float (Some third)] <>
    NullValues.interp_avg_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some third);
       NullValues.Value_float (Some second)].
Proof.
destruct float32_average_order_sensitive as
  [first [second [third Horder]]].
exists first, second, third.
unfold NullValues.interp_avg_float, NullValues.interp_avg_float64_values; cbn.
intro Hequal; injection Hequal as Hequal; now apply Horder.
Qed.

Example double_sum_depends_on_representative_order :
  exists first second third,
    NullValues.interp_sum_double
      [NullValues.Value_double (Some first);
       NullValues.Value_double (Some second);
       NullValues.Value_double (Some third)] <>
    NullValues.interp_sum_double
      [NullValues.Value_double (Some first);
       NullValues.Value_double (Some third);
       NullValues.Value_double (Some second)].
Proof.
destruct float64_add_order_sensitive as
  [first [second [third Horder]]].
exists first, second, third.
unfold NullValues.interp_sum_double; cbn.
intro Hequal; injection Hequal as Hequal; now apply Horder.
Qed.

Example double_average_depends_on_representative_order :
  exists first second third,
    NullValues.interp_avg_double
      [NullValues.Value_double (Some first);
       NullValues.Value_double (Some second);
       NullValues.Value_double (Some third)] <>
    NullValues.interp_avg_double
      [NullValues.Value_double (Some first);
       NullValues.Value_double (Some third);
       NullValues.Value_double (Some second)].
Proof.
destruct float64_average_order_sensitive as
  [first [second [third Horder]]].
exists first, second, third.
unfold NullValues.interp_avg_double, NullValues.interp_avg_float64_values; cbn.
intro Hequal; injection Hequal as Hequal; now apply Horder.
Qed.

(** The grouping API consequently requires stability as a premise instead of
    exporting a universal aggregate-permutation theorem. *)
Check group_projection_permutation_stable.
Check eval_group_bag_global_true_success_bag_unique_if_stable.

Print Assumptions float_sum_depends_on_representative_order.
Print Assumptions float_average_depends_on_representative_order.
Print Assumptions double_sum_depends_on_representative_order.
Print Assumptions double_average_depends_on_representative_order.
