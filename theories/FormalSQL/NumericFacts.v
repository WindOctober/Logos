From SQLFS Require Import Bool3 OrderedSet SqlOutcome SqlSyntax
  SqlErrorSemantics GenericInstance Values ValueNumeric ValueNumericTypmod.
From Logos.FormalSQL Require Import TNullSyntax.
From Stdlib Require Import Lia List QArith Qcanon Ring Sorting.Permutation String ZArith.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Import NullValues.

(** Logical aggregate state uses exact mathematical cardinalities rather than
    executor field widths.  Its additive transitions commute, so the ordered
    query semantics still admits bag-theory permutation proofs. *)

Lemma numeric_avg_scale_transition_commutes : forall scale state left right,
  numeric_avg_scale_transition scale
    (numeric_avg_scale_transition scale state left)
    right =
  numeric_avg_scale_transition scale
    (numeric_avg_scale_transition scale state right)
    left.
Proof.
  intros scale [finite_count nan_count pos_inf_count neg_inf_count sum_coeff]
    left right.
  destruct left as [|left| |]; destruct right as [|right| |];
    cbv [numeric_avg_scale_transition numeric_avg_finite_count
      numeric_avg_nan_count numeric_avg_pos_inf_count
      numeric_avg_neg_inf_count numeric_avg_sum_coeff].
  all: try reflexivity.
  replace
    (sum_coeff + numeric_finite_rounded_coeff left scale +
      numeric_finite_rounded_coeff right scale)
    with
    (sum_coeff + numeric_finite_rounded_coeff right scale +
      numeric_finite_rounded_coeff left scale) by ring.
  reflexivity.
Qed.

Lemma numeric_sum_transition_commutes : forall state left right,
  numeric_sum_transition
    (numeric_sum_transition state left) right =
  numeric_sum_transition
    (numeric_sum_transition state right) left.
Proof.
  intros [finite_count nan_count pos_inf_count neg_inf_count accumulator]
    left right.
  destruct left as [|left| |]; destruct right as [|right| |];
    cbv [numeric_sum_transition numeric_sum_finite_count
      numeric_sum_nan_count numeric_sum_pos_inf_count
      numeric_sum_neg_inf_count numeric_sum_finite_accumulator].
  all: try reflexivity.
  f_equal.
  rewrite <- !Qcplus_assoc.
  now rewrite (Qcplus_comm left right).
Qed.

Lemma fold_left_permutation_of_commuting_steps :
  forall (state item : Type) (step : state -> item -> state),
    (forall current left right,
      step (step current left) right = step (step current right) left) ->
    forall left right initial,
      Permutation left right ->
      fold_left step left initial = fold_left step right initial.
Proof.
  intros state item step Hcomm left right initial Hperm.
  revert initial.
  induction Hperm as
    [|value left right Hperm IH|left right rest|left middle right _ IH1 _ IH2];
    intro initial; cbn.
  - reflexivity.
  - apply IH.
  - now rewrite Hcomm.
  - rewrite IH1; apply IH2.
Qed.

Lemma numeric_scale_stats_transition_commutes : forall scale state left right,
  numeric_scale_stats_transition scale
    (numeric_scale_stats_transition scale state left) right =
  numeric_scale_stats_transition scale
    (numeric_scale_stats_transition scale state right) left.
Proof.
  intros scale [finite_count [special_count [sum_coeff sum_square_coeff]]]
    left right.
  destruct left as [|left| |]; destruct right as [|right| |];
    unfold numeric_scale_stats_transition.
  all: repeat match goal with
    | |- (_, _) = (_, _) => apply injective_projections; cbn
    end; ring.
Qed.

Lemma numeric_scale_stats_fold_permutation : forall scale left right initial,
  Permutation left right ->
  fold_left (numeric_scale_stats_transition scale) left initial =
  fold_left (numeric_scale_stats_transition scale) right initial.
Proof.
  intros scale left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    numeric_scale_stats_state numeric
    (numeric_scale_stats_transition scale)
    (numeric_scale_stats_transition_commutes scale)
    left right initial Hperm).
Qed.

Lemma numeric_avg_scale_fold_permutation : forall scale left right initial,
  Permutation left right ->
  fold_left (numeric_avg_scale_transition scale)
    left initial =
  fold_left (numeric_avg_scale_transition scale)
    right initial.
Proof.
  intros scale left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    numeric_avg_scale_state numeric
    (numeric_avg_scale_transition scale)
    (numeric_avg_scale_transition_commutes scale)
    left right initial Hperm).
Qed.

Lemma numeric_sum_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left numeric_sum_transition left initial =
  fold_left numeric_sum_transition right initial.
Proof.
  intros left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    numeric_sum_state numeric
    numeric_sum_transition
    numeric_sum_transition_commutes left right initial Hperm).
Qed.

Lemma int32_avg_transition_commutes : forall state left right,
  int32_avg_transition (int32_avg_transition state left) right =
  int32_avg_transition (int32_avg_transition state right) left.
Proof.
  intros [count sum] left right.
  cbn [int32_avg_transition].
  f_equal; ring.
Qed.

Lemma int64_avg_transition_commutes : forall state left right,
  int64_avg_transition (int64_avg_transition state left) right =
  int64_avg_transition (int64_avg_transition state right) left.
Proof.
  intros [count sum] left right.
  cbn [int64_avg_transition].
  f_equal.
  replace (sum + int64_value left + int64_value right)
    with (sum + int64_value right + int64_value left) by ring.
  reflexivity.
Qed.

Lemma integer_stats_transition_commutes : forall state left right,
  integer_stats_transition (integer_stats_transition state left) right =
  integer_stats_transition (integer_stats_transition state right) left.
Proof.
  intros [count [sum sum_squares]] left right.
  cbn [integer_stats_transition].
  repeat match goal with
  | |- (_, _) = (_, _) => apply injective_projections; cbn
  end; ring.
Qed.

Lemma int32_sum_transition_commutes : forall state left right,
  (state + int32_value left) + int32_value right =
  (state + int32_value right) + int32_value left.
Proof. intros; ring. Qed.

Lemma int32_sum_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left (fun state next => state + int32_value next) left initial =
  fold_left (fun state next => state + int32_value next) right initial.
Proof.
  intros left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    Z int32 (fun state next => state + int32_value next)
    int32_sum_transition_commutes left right initial Hperm).
Qed.

Lemma int32_avg_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left int32_avg_transition left initial =
  fold_left int32_avg_transition right initial.
Proof.
  intros left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    (Z * Z)%type int32 int32_avg_transition
    int32_avg_transition_commutes left right initial Hperm).
Qed.

Lemma int64_avg_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left int64_avg_transition left initial =
  fold_left int64_avg_transition right initial.
Proof.
  intros left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    (Z * Z)%type int64 int64_avg_transition
    int64_avg_transition_commutes left right initial Hperm).
Qed.

Lemma integer_stats_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left integer_stats_transition left initial =
  fold_left integer_stats_transition right initial.
Proof.
  intros left right initial Hperm.
  exact (fold_left_permutation_of_commuting_steps
    integer_stats_state Z integer_stats_transition
    integer_stats_transition_commutes left right initial Hperm).
Qed.

Definition int32_value_projection (value : value) : list int32 :=
  match value with
  | Value_int32 (Some integer) => integer :: nil
  | _ => nil
  end.

Definition int64_value_projection (value : value) : list int64 :=
  match value with
  | Value_int64 (Some integer) => integer :: nil
  | _ => nil
  end.

Definition numeric_value_projection (value : value) : list numeric :=
  match value with
  | Value_numeric (Some number) => number :: nil
  | _ => nil
  end.

Lemma int32_values_as_flat_map : forall values,
  int32_values values = flat_map int32_value_projection values.
Proof.
  induction values as [|value values IH]; cbn; [reflexivity|].
  destruct value; cbn; try exact IH.
  destruct o; cbn; now rewrite IH.
Qed.

Lemma int64_values_as_flat_map : forall values,
  int64_values values = flat_map int64_value_projection values.
Proof.
  induction values as [|value values IH]; cbn; [reflexivity|].
  destruct value; cbn; try exact IH.
  destruct o; cbn; now rewrite IH.
Qed.

Lemma numeric_values_as_flat_map : forall values,
  numeric_values values = flat_map numeric_value_projection values.
Proof.
  induction values as [|value values IH]; cbn; [reflexivity|].
  destruct value; cbn; try exact IH.
  destruct o; cbn; now rewrite IH.
Qed.

Lemma int32_values_permutation : forall left right,
  Permutation left right ->
  Permutation (int32_values left) (int32_values right).
Proof.
  intros left right Hperm; rewrite !int32_values_as_flat_map.
  now apply Permutation_flat_map.
Qed.

Lemma int64_values_permutation : forall left right,
  Permutation left right ->
  Permutation (int64_values left) (int64_values right).
Proof.
  intros left right Hperm; rewrite !int64_values_as_flat_map.
  now apply Permutation_flat_map.
Qed.

Lemma numeric_values_permutation : forall left right,
  Permutation left right ->
  Permutation (numeric_values left) (numeric_values right).
Proof.
  intros left right Hperm; rewrite !numeric_values_as_flat_map.
  now apply Permutation_flat_map.
Qed.

Lemma forallb_permutation : forall (A : Type) (predicate : A -> bool) left right,
  Permutation left right -> forallb predicate left = forallb predicate right.
Proof.
  intros A predicate left right Hperm.
  induction Hperm; cbn.
  - reflexivity.
  - now rewrite IHHperm.
  - destruct (predicate x), (predicate y), (forallb predicate l); reflexivity.
  - now rewrite IHHperm1, IHHperm2.
Qed.

Lemma interp_sum_int32_as_int64_permutation : forall left right,
  Permutation left right ->
  interp_sum_int32_as_int64 left = interp_sum_int32_as_int64 right.
Proof.
  intros left right Hperm.
  unfold interp_sum_int32_as_int64.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  pose proof (int32_values_permutation left right Hperm) as Hvalues.
  destruct (int32_values left) as [|left_head left_tail] eqn:Hleft.
  - apply Permutation_nil in Hvalues; now rewrite Hvalues.
  - destruct (int32_values right) as [|right_head right_tail] eqn:Hright.
    + symmetry in Hvalues; apply Permutation_nil in Hvalues; discriminate.
    + rewrite (int32_sum_fold_permutation _ _ _ Hvalues); reflexivity.
Qed.

Lemma sum_int32_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_int32_runtime_error left = sum_int32_runtime_error right.
Proof.
  intros left right Hperm.
  unfold sum_int32_runtime_error.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  pose proof (int32_values_permutation left right Hperm) as Hvalues.
  destruct (int32_values left) as [|left_head left_tail] eqn:Hleft.
  - apply Permutation_nil in Hvalues; now rewrite Hvalues.
  - destruct (int32_values right) as [|right_head right_tail] eqn:Hright.
    + symmetry in Hvalues; apply Permutation_nil in Hvalues; discriminate.
    + rewrite (int32_sum_fold_permutation _ _ _ Hvalues); reflexivity.
Qed.

Lemma interp_avg_int32_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_avg_int32_as_numeric left = interp_avg_int32_as_numeric right.
Proof.
  intros left right Hperm.
  unfold interp_avg_int32_as_numeric.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  pose proof (int32_values_permutation left right Hperm) as Hvalues.
  destruct (int32_values left) as [|left_head left_tail] eqn:Hleft.
  - apply Permutation_nil in Hvalues; now rewrite Hvalues.
  - destruct (int32_values right) as [|right_head right_tail] eqn:Hright.
    + symmetry in Hvalues; apply Permutation_nil in Hvalues; discriminate.
    + rewrite (int32_avg_fold_permutation _ _ _ Hvalues); reflexivity.
Qed.

Lemma numeric_div_by_Z_success_has_scale :
  forall sum count average,
    numeric_div_by_Z (numeric_of_Z sum) count = Some average ->
    exists scale,
      numeric_pg_div_scale
        (numeric_of_Z sum) 0 (numeric_of_Z count) 0 = Some scale.
Proof.
intros sum count average Hdivision.
unfold numeric_div_by_Z, numeric_div_at_scales, numeric_of_Z in Hdivision.
destruct
  (numeric_eqb (NumericFinite (Q2Qc (inject_Z count))) numeric_zero)
  eqn:Hzero; [discriminate|].
destruct
  (numeric_pg_div_scale
    (NumericFinite (Q2Qc (inject_Z sum))) 0
    (NumericFinite (Q2Qc (inject_Z count))) 0)
  as [scale |] eqn:Hscale; [exists scale; exact Hscale | discriminate].
Qed.

(** The value and display-scale aggregate slots are two projections of the
    same PostgreSQL AVG(int4) finalization.  This includes an all-NULL group,
    whose filtered int4 stream is empty and whose two projections are NULL. *)
Lemma interp_avg_int32_value_dscale_coherent :
  forall observations,
    forallb is_int32_value observations = true ->
    match int32_avg_numeric_with_scale (int32_values observations) with
    | None =>
        interp_avg_int32_as_numeric observations = Value_numeric None /\
        interp_numeric_aggregate_display_scale
          NumericAverageInt32 observations = Value_Z None
    | Some (average, scale) =>
        interp_avg_int32_as_numeric observations =
          Value_numeric (Some average) /\
        interp_numeric_aggregate_display_scale
          NumericAverageInt32 observations = Value_Z (Some scale)
    end.
Proof.
intros observations Htyped.
unfold interp_avg_int32_as_numeric,
  interp_numeric_aggregate_display_scale,
  int32_numeric_aggregate_with_scale.
rewrite Htyped.
destruct (int32_values observations) as [| first rest] eqn:Hintegers.
- cbn [int32_avg_numeric_with_scale]; split; reflexivity.
-
unfold int32_avg_numeric_with_scale.
remember
  (fold_left int32_avg_transition (first :: rest) (0, 0))
  as state eqn:Hstate.
destruct state as [count sum].
destruct (count =? 0) eqn:Hcount; [split; reflexivity|].
unfold numeric_div_by_Z.
destruct
  (numeric_pg_div_scale
    (numeric_of_Z sum) 0 (numeric_of_Z count) 0)
  as [scale |] eqn:Hscale;
destruct
  (numeric_div_at_scales
    (numeric_of_Z sum) 0 (numeric_of_Z count) 0)
  as [average |] eqn:Hdivision.
+ split; reflexivity.
+ split; reflexivity.
+ destruct
    (numeric_div_by_Z_success_has_scale sum count average Hdivision)
    as [scale Hscale'].
  rewrite Hscale in Hscale'; discriminate.
+ split; reflexivity.
Qed.

Lemma interp_avg_int64_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_avg_int64_as_numeric left = interp_avg_int64_as_numeric right.
Proof.
  intros left right Hperm.
  unfold interp_avg_int64_as_numeric.
  rewrite (forallb_permutation value is_int64_value left right Hperm).
  destruct (forallb is_int64_value right); [|reflexivity].
  pose proof (int64_values_permutation left right Hperm) as Hvalues.
  destruct (int64_values left) as [|left_head left_tail] eqn:Hleft.
  - apply Permutation_nil in Hvalues; now rewrite Hvalues.
  - destruct (int64_values right) as [|right_head right_tail] eqn:Hright.
    + symmetry in Hvalues; apply Permutation_nil in Hvalues; discriminate.
    + rewrite (int64_avg_fold_permutation _ _ _ Hvalues); reflexivity.
Qed.

Lemma interp_sum_int64_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_sum_int64_as_numeric left = interp_sum_int64_as_numeric right.
Proof.
  intros left right Hperm.
  unfold interp_sum_int64_as_numeric.
  rewrite (forallb_permutation value is_int64_value left right Hperm).
  destruct (forallb is_int64_value right); [|reflexivity].
  pose proof (int64_values_permutation left right Hperm) as Hvalues.
  now rewrite (int64_avg_fold_permutation _ _ _ Hvalues).
Qed.

Lemma sum_int64_numeric_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_int64_numeric_runtime_error left =
  sum_int64_numeric_runtime_error right.
Proof.
  intros left right Hperm.
  unfold sum_int64_numeric_runtime_error.
  rewrite (forallb_permutation value is_int64_value left right Hperm).
  destruct (forallb is_int64_value right); [|reflexivity].
  pose proof (int64_values_permutation left right Hperm) as Hvalues.
  now rewrite (int64_avg_fold_permutation _ _ _ Hvalues).
Qed.

Lemma interp_sum_numeric_permutation : forall left right,
  Permutation left right ->
  interp_sum_numeric left = interp_sum_numeric right.
Proof.
  intros left right Hperm.
  unfold interp_sum_numeric.
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  now rewrite (numeric_sum_fold_permutation _ _ _ Hnumbers).
Qed.

Lemma sum_numeric_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_numeric_runtime_error left = sum_numeric_runtime_error right.
Proof.
  intros left right Hperm.
  unfold sum_numeric_runtime_error.
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  now rewrite (numeric_sum_fold_permutation _ _ _ Hnumbers).
Qed.

Lemma interp_integer_statistic_permutation : forall left right variance sample,
  Permutation left right ->
  interp_integer_statistic left variance sample =
  interp_integer_statistic right variance sample.
Proof.
  intros left right variance sample Hperm.
  unfold interp_integer_statistic.
  now rewrite (integer_stats_fold_permutation _ _ _ Hperm).
Qed.

Lemma interp_var_pop_int32_permutation : forall left right,
  Permutation left right ->
  interp_var_pop_int32 left = interp_var_pop_int32 right.
Proof.
  intros left right Hperm; unfold interp_var_pop_int32.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  apply interp_integer_statistic_permutation, Permutation_map,
    int32_values_permutation; exact Hperm.
Qed.

Lemma interp_var_samp_int32_permutation : forall left right,
  Permutation left right ->
  interp_var_samp_int32 left = interp_var_samp_int32 right.
Proof.
  intros left right Hperm; unfold interp_var_samp_int32.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  apply interp_integer_statistic_permutation, Permutation_map,
    int32_values_permutation; exact Hperm.
Qed.

Lemma interp_stddev_pop_int32_permutation : forall left right,
  Permutation left right ->
  interp_stddev_pop_int32 left = interp_stddev_pop_int32 right.
Proof.
  intros left right Hperm; unfold interp_stddev_pop_int32.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  apply interp_integer_statistic_permutation, Permutation_map,
    int32_values_permutation; exact Hperm.
Qed.

Lemma interp_stddev_samp_int32_permutation : forall left right,
  Permutation left right ->
  interp_stddev_samp_int32 left = interp_stddev_samp_int32 right.
Proof.
  intros left right Hperm; unfold interp_stddev_samp_int32.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  apply interp_integer_statistic_permutation, Permutation_map,
    int32_values_permutation; exact Hperm.
Qed.

Lemma int32_avg_numeric_with_scale_permutation : forall left right,
  Permutation left right ->
  int32_avg_numeric_with_scale left = int32_avg_numeric_with_scale right.
Proof.
  intros left right Hperm; unfold int32_avg_numeric_with_scale.
  destruct left as [|left_head left_tail].
  - apply Permutation_nil in Hperm; now rewrite Hperm.
  - destruct right as [|right_head right_tail].
    + symmetry in Hperm; apply Permutation_nil in Hperm; discriminate.
    + now rewrite (int32_avg_fold_permutation _ _ _ Hperm).
Qed.

Lemma int32_stddev_samp_numeric_with_scale_permutation : forall left right,
  Permutation left right ->
  int32_stddev_samp_numeric_with_scale left =
  int32_stddev_samp_numeric_with_scale right.
Proof.
  intros left right Hperm; unfold int32_stddev_samp_numeric_with_scale.
  now rewrite (integer_stats_fold_permutation
    (map int32_value left) (map int32_value right) (0, (0, 0))
    (Permutation_map int32_value Hperm)).
Qed.

Lemma int32_numeric_aggregate_with_scale_permutation :
  forall aggregate left right,
  Permutation left right ->
  int32_numeric_aggregate_with_scale aggregate left =
  int32_numeric_aggregate_with_scale aggregate right.
Proof.
  intros aggregate left right Hperm; destruct aggregate; cbn.
  - now apply int32_avg_numeric_with_scale_permutation.
  - now apply int32_stddev_samp_numeric_with_scale_permutation.
Qed.

Lemma interp_numeric_aggregate_display_scale_permutation :
  forall aggregate left right,
  Permutation left right ->
  interp_numeric_aggregate_display_scale aggregate left =
  interp_numeric_aggregate_display_scale aggregate right.
Proof.
  intros aggregate left right Hperm.
  unfold interp_numeric_aggregate_display_scale.
  rewrite (forallb_permutation value is_int32_value left right Hperm).
  destruct (forallb is_int32_value right); [|reflexivity].
  now rewrite (int32_numeric_aggregate_with_scale_permutation aggregate
    (int32_values left) (int32_values right)
    (int32_values_permutation left right Hperm)).
Qed.

Lemma interp_stddev_samp_numeric_fixed_permutation :
  forall precision scale left right,
  Permutation left right ->
  interp_stddev_samp_numeric_fixed precision scale left =
  interp_stddev_samp_numeric_fixed precision scale right.
Proof.
  intros precision scale left right Hperm.
  unfold interp_stddev_samp_numeric_fixed.
  destruct (numeric_typmod_valid_bool precision scale); [|reflexivity].
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  rewrite (forallb_permutation numeric
    (numeric_conforms_typmod_bool precision scale)
    (numeric_values left) (numeric_values right) Hnumbers).
  destruct (forallb (numeric_conforms_typmod_bool precision scale)
    (numeric_values right)); [|reflexivity].
  now rewrite (numeric_scale_stats_fold_permutation
    scale (numeric_values left) (numeric_values right)
    numeric_scale_stats_initial Hnumbers).
Qed.

Lemma interp_avg_numeric_fixed_permutation : forall precision scale left right,
  Permutation left right ->
  interp_avg_numeric_fixed precision scale left =
  interp_avg_numeric_fixed precision scale right.
Proof.
  intros precision scale left right Hperm.
  unfold interp_avg_numeric_fixed.
  destruct (numeric_typmod_valid_bool precision scale); [|reflexivity].
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  rewrite (forallb_permutation numeric
    (numeric_conforms_typmod_bool precision scale)
    (numeric_values left) (numeric_values right) Hnumbers).
  destruct (forallb (numeric_conforms_typmod_bool precision scale)
    (numeric_values right)); [|reflexivity].
  now rewrite (numeric_avg_scale_fold_permutation
    scale (numeric_values left) (numeric_values right)
    numeric_avg_scale_initial Hnumbers).
Qed.

Lemma avg_numeric_fixed_runtime_error_permutation :
  forall precision scale left right,
  Permutation left right ->
  avg_numeric_fixed_runtime_error precision scale left =
  avg_numeric_fixed_runtime_error precision scale right.
Proof.
  intros precision scale left right Hperm.
  unfold avg_numeric_fixed_runtime_error.
  destruct (numeric_typmod_valid_bool precision scale); [|reflexivity].
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  rewrite (forallb_permutation numeric
    (numeric_conforms_typmod_bool precision scale)
    (numeric_values left) (numeric_values right) Hnumbers).
  destruct (forallb (numeric_conforms_typmod_bool precision scale)
    (numeric_values right)); [|reflexivity].
  now rewrite (numeric_avg_scale_fold_permutation
    scale (numeric_values left) (numeric_values right)
    numeric_avg_scale_initial Hnumbers).
Qed.

Lemma stddev_samp_numeric_fixed_runtime_error_permutation :
  forall precision scale left right,
  Permutation left right ->
  stddev_samp_numeric_fixed_runtime_error precision scale left =
  stddev_samp_numeric_fixed_runtime_error precision scale right.
Proof.
  intros precision scale left right Hperm.
  unfold stddev_samp_numeric_fixed_runtime_error.
  destruct (numeric_typmod_valid_bool precision scale); [|reflexivity].
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  rewrite (forallb_permutation numeric
    (numeric_conforms_typmod_bool precision scale)
    (numeric_values left) (numeric_values right) Hnumbers).
  destruct (forallb (numeric_conforms_typmod_bool precision scale)
    (numeric_values right)); [|reflexivity].
  now rewrite (numeric_scale_stats_fold_permutation
    scale (numeric_values left) (numeric_values right)
    numeric_scale_stats_initial Hnumbers).
Qed.

Lemma interp_avg_numeric_at_scale_permutation : forall scale left right,
  Permutation left right ->
  interp_avg_numeric_at_scale scale left = interp_avg_numeric_at_scale scale right.
Proof.
  intros scale left right Hperm.
  unfold interp_avg_numeric_at_scale.
  destruct (numeric_display_scale_valid_bool scale); [|reflexivity].
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  now rewrite (numeric_avg_scale_fold_permutation
    scale (numeric_values left) (numeric_values right)
    numeric_avg_scale_initial Hnumbers).
Qed.

Lemma avg_numeric_at_scale_runtime_error_permutation : forall scale left right,
  Permutation left right ->
  avg_numeric_at_scale_runtime_error scale left =
  avg_numeric_at_scale_runtime_error scale right.
Proof.
  intros scale left right Hperm.
  unfold avg_numeric_at_scale_runtime_error.
  destruct (numeric_display_scale_valid_bool scale); [|reflexivity].
  rewrite (forallb_permutation value is_numeric_value left right Hperm).
  destruct (forallb is_numeric_value right); [|reflexivity].
  pose proof (numeric_values_permutation left right Hperm) as Hnumbers.
  now rewrite (numeric_avg_scale_fold_permutation
    scale (numeric_values left) (numeric_values right)
    numeric_avg_scale_initial Hnumbers).
Qed.

(** The DISTINCT interpreter keeps the last occurrence of each value.  Its
    output order can therefore change when the input enumeration changes, but
    it denotes the same duplicate-free bag. *)
Lemma distinct_values_membership : forall value values,
  In value (distinct_values values) <-> In value values.
Proof.
  intros value values; induction values as [|head tail IH]; cbn.
  - reflexivity.
  - destruct (Oset.mem_bool OVal head tail) eqn:Hhead.
    + rewrite IH; split.
      * now right.
      * intros [Heq | Hin]; [subst|exact Hin].
        now apply Oset.mem_bool_true_iff in Hhead.
    + cbn; now rewrite IH.
Qed.

Lemma distinct_values_nodup : forall values, NoDup (distinct_values values).
Proof.
  induction values as [|head tail IH]; cbn; [constructor|].
  destruct (Oset.mem_bool OVal head tail) eqn:Hhead; [exact IH|].
  constructor; [|exact IH].
  intro Hin; apply (proj1 (distinct_values_membership head tail)) in Hin.
  pose proof (proj2 (Oset.mem_bool_true_iff OVal head tail) Hin) as Hmember.
  congruence.
Qed.

Lemma distinct_values_permutation : forall left right,
  Permutation left right ->
  Permutation (distinct_values left) (distinct_values right).
Proof.
  intros left right Hperm.
  apply NoDup_Permutation.
  - apply distinct_values_nodup.
  - apply distinct_values_nodup.
  - intro value; rewrite !distinct_values_membership.
    split; intro Hin.
    + eapply Permutation_in; eauto.
    + eapply Permutation_in; [symmetry; exact Hperm|exact Hin].
Qed.

Lemma exact_sum_aggregate_permutation :
  forall function left right,
    In function
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
Proof.
  intros function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  - now apply interp_sum_int32_as_int64_permutation.
  - apply interp_sum_int32_as_int64_permutation.
    now apply distinct_values_permutation.
  - now apply interp_sum_int64_as_numeric_permutation.
  - apply interp_sum_int64_as_numeric_permutation.
    now apply distinct_values_permutation.
  - now apply interp_sum_numeric_permutation.
  - apply interp_sum_numeric_permutation.
    now apply distinct_values_permutation.
Qed.

Lemma exact_sum_runtime_error_permutation :
  forall function left right,
    In function
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
Proof.
  intros function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  - now apply sum_int32_runtime_error_permutation.
  - apply sum_int32_runtime_error_permutation.
    now apply distinct_values_permutation.
  - now apply sum_int64_numeric_runtime_error_permutation.
  - apply sum_int64_numeric_runtime_error_permutation.
    now apply distinct_values_permutation.
  - now apply sum_numeric_runtime_error_permutation.
  - apply sum_numeric_runtime_error_permutation.
    now apply distinct_values_permutation.
Qed.

Lemma fixed_numeric_aggregate_permutation :
  forall precision scale function left right,
    In function
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
Proof.
  intros precision scale function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  - now apply interp_stddev_samp_numeric_fixed_permutation.
  - apply interp_stddev_samp_numeric_fixed_permutation.
    now apply distinct_values_permutation.
  - now apply interp_avg_numeric_fixed_permutation.
  - apply interp_avg_numeric_fixed_permutation.
    now apply distinct_values_permutation.
Qed.

Lemma fixed_numeric_aggregate_runtime_error_permutation :
  forall precision scale function left right,
    In function
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
Proof.
  intros precision scale function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  - now apply stddev_samp_numeric_fixed_runtime_error_permutation.
  - apply stddev_samp_numeric_fixed_runtime_error_permutation.
    now apply distinct_values_permutation.
  - now apply avg_numeric_fixed_runtime_error_permutation.
  - apply avg_numeric_fixed_runtime_error_permutation.
    now apply distinct_values_permutation.
Qed.

Lemma numeric_average_at_scale_aggregate_permutation :
  forall scale function left right,
    In function
      [Aggregate (AggregateAverageNumericAtScale scale);
       DistinctAggregate (AggregateAverageNumericAtScale scale)] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
Proof.
  intros scale function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  - now apply interp_avg_numeric_at_scale_permutation.
  - apply interp_avg_numeric_at_scale_permutation.
    now apply distinct_values_permutation.
Qed.

Lemma numeric_average_at_scale_runtime_error_permutation :
  forall scale function left right,
    In function
      [Aggregate (AggregateAverageNumericAtScale scale);
       DistinctAggregate (AggregateAverageNumericAtScale scale)] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
Proof.
  intros scale function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  - now apply avg_numeric_at_scale_runtime_error_permutation.
  - apply avg_numeric_at_scale_runtime_error_permutation.
    now apply distinct_values_permutation.
Qed.

Lemma integral_numeric_aggregate_permutation :
  forall function left right,
    In function
      [Aggregate AggregateAverageInt32Numeric;
       DistinctAggregate AggregateAverageInt32Numeric;
       Aggregate (AggregateNumericDisplayScale NumericAverageInt32);
       Aggregate (AggregateNumericDisplayScale NumericStddevSampleInt32);
       Aggregate AggregateAverageInt64Numeric;
       DistinctAggregate AggregateAverageInt64Numeric;
       Aggregate AggregateVariancePopulationInt32;
       DistinctAggregate AggregateVariancePopulationInt32;
       Aggregate AggregateVarianceSampleInt32;
       DistinctAggregate AggregateVarianceSampleInt32;
       Aggregate AggregateStddevPopulationInt32;
       DistinctAggregate AggregateStddevPopulationInt32;
       Aggregate AggregateStddevSampleInt32;
       DistinctAggregate AggregateStddevSampleInt32] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
Proof.
  intros function left right Hfunction Hperm.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function; cbn|]); try contradiction.
  all: try apply interp_avg_int32_as_numeric_permutation.
  all: try apply interp_numeric_aggregate_display_scale_permutation.
  all: try apply interp_avg_int64_as_numeric_permutation.
  all: try apply interp_var_pop_int32_permutation.
  all: try apply interp_var_samp_int32_permutation.
  all: try apply interp_stddev_pop_int32_permutation.
  all: try apply interp_stddev_samp_int32_permutation.
  all: try exact Hperm.
  all: try (apply distinct_values_permutation; exact Hperm).
Qed.

Theorem numeric_integer_stddev_samp_with_scale_forgets_scale :
  forall count sum sum_squares,
    (match numeric_integer_stddev_samp_with_scale count sum sum_squares with
     | Some (value, _) => Some value
     | None => None
     end) =
    numeric_integer_statistic count sum sum_squares false true.
Proof.
  intros count sum sum_squares.
  unfold numeric_integer_stddev_samp_with_scale,
    numeric_integer_statistic.
  destruct (count =? 0); [reflexivity|].
  destruct (count <=? 1); [reflexivity|].
  destruct (count * sum_squares - sum * sum <=? 0); [reflexivity|].
  destruct (numeric_pg_div_scale
    (numeric_of_Z (count * sum_squares - sum * sum)) 0
    (numeric_of_Z (count * (count - 1))) 0) as [scale|];
    [|reflexivity].
  destruct (numeric_div_at_scales
    (numeric_of_Z (count * sum_squares - sum * sum)) 0
    (numeric_of_Z (count * (count - 1))) 0) as [variance|];
    [|reflexivity].
  now destruct (numeric_sqrt_at_scale variance scale).
Qed.

(** Exact logical-state certificates.  Counts grow with the finite input list;
    no proof or semantic branch depends on a fixed-width executor field. *)

Lemma int32_avg_fold_count_exact : forall values count sum,
  fst (fold_left int32_avg_transition values (count, sum)) =
    count + Z.of_nat (List.length values).
Proof.
  induction values as [|next values IH]; intros count sum; cbn.
  - lia.
  - rewrite IH; cbn [int32_avg_transition]; lia.
Qed.

Lemma int64_avg_fold_count_exact : forall values count sum,
  fst (fold_left int64_avg_transition values (count, sum)) =
    count + Z.of_nat (List.length values).
Proof.
  induction values as [|next values IH]; intros count sum; cbn.
  - lia.
  - rewrite IH; cbn [int64_avg_transition]; lia.
Qed.

Lemma integer_stats_fold_count_exact : forall values count sum sum_squares,
  fst (fold_left integer_stats_transition values
    (count, (sum, sum_squares))) =
    count + Z.of_nat (List.length values).
Proof.
  induction values as [|next values IH];
    intros count sum sum_squares; cbn.
  - lia.
  - rewrite IH; cbn [integer_stats_transition]; lia.
Qed.

Lemma numeric_avg_scale_transition_total_count_exact :
  forall scale state next,
    numeric_avg_scale_total_count
      (numeric_avg_scale_transition scale state next) =
    numeric_avg_scale_total_count state + 1.
Proof.
  intros scale [finite_count nan_count pos_inf_count neg_inf_count sum_coeff]
    next.
  destruct next; cbv [numeric_avg_scale_transition
    numeric_avg_scale_total_count numeric_agg_total_count
    numeric_avg_finite_count numeric_avg_nan_count
    numeric_avg_pos_inf_count numeric_avg_neg_inf_count
    numeric_avg_sum_coeff]; ring.
Qed.

Lemma numeric_avg_scale_fold_total_count_exact : forall scale values state,
  numeric_avg_scale_total_count
    (fold_left (numeric_avg_scale_transition scale) values state) =
  numeric_avg_scale_total_count state + Z.of_nat (List.length values).
Proof.
  intros scale values; induction values as [|next values IH]; intro state; cbn.
  - lia.
  - rewrite IH, numeric_avg_scale_transition_total_count_exact; cbn; lia.
Qed.

Lemma numeric_sum_transition_total_count_exact : forall state next,
  numeric_sum_total_count (numeric_sum_transition state next) =
    numeric_sum_total_count state + 1.
Proof.
  intros [finite_count nan_count pos_inf_count neg_inf_count accumulator]
    next.
  destruct next; cbv [numeric_sum_transition numeric_sum_total_count
    numeric_agg_total_count numeric_sum_finite_count numeric_sum_nan_count
    numeric_sum_pos_inf_count numeric_sum_neg_inf_count
    numeric_sum_finite_accumulator]; ring.
Qed.

Lemma numeric_sum_fold_total_count_exact : forall values state,
  numeric_sum_total_count (fold_left numeric_sum_transition values state) =
    numeric_sum_total_count state + Z.of_nat (List.length values).
Proof.
  intro values; induction values as [|next values IH]; intro state; cbn.
  - lia.
  - rewrite IH, numeric_sum_transition_total_count_exact; cbn; lia.
Qed.

Lemma numeric_scale_stats_transition_total_count_exact :
  forall scale state next,
    numeric_scale_stats_total_count
      (numeric_scale_stats_transition scale state next) =
    numeric_scale_stats_total_count state + 1.
Proof.
  intros scale [finite_count [special_count [sum_coeff sum_square_coeff]]]
    next.
  destruct next; cbn [numeric_scale_stats_transition
    numeric_scale_stats_total_count]; ring.
Qed.

Lemma numeric_scale_stats_fold_total_count_exact : forall scale values state,
  numeric_scale_stats_total_count
    (fold_left (numeric_scale_stats_transition scale) values state) =
  numeric_scale_stats_total_count state + Z.of_nat (List.length values).
Proof.
  intros scale values; induction values as [|next values IH]; intro state; cbn.
  - lia.
  - rewrite IH, numeric_scale_stats_transition_total_count_exact; cbn; lia.
Qed.

Theorem integral_average_runtime_error_totality_certificate : forall values,
  avg_int32_numeric_runtime_error values = None /\
  avg_int64_numeric_runtime_error values = None.
Proof. intro values; split; reflexivity. Qed.

Theorem numeric_aggregate_display_scale_runtime_error_totality_certificate :
  forall aggregate values,
  numeric_aggregate_display_scale_runtime_error aggregate values = None.
Proof. reflexivity. Qed.

Theorem integer_statistic_runtime_error_totality_certificate : forall values,
  integer_statistic_runtime_error values = None.
Proof. reflexivity. Qed.

(** Core facts for canonical finite NUMERIC values, PostgreSQL infinities and
    NaN, and DECIMAL(p,s) typmods.  Unconstrained table values remain a
    frontend boundary because their per-value display scale is not carried by
    [Value_numeric]. *)

Lemma numeric_compare_refl :
  forall value,
    numeric_compare value value = Eq.
Proof.
intro value.
exact (Oset.compare_eq_refl Onumeric value).
Qed.

Lemma numeric_eqb_refl :
  forall value,
    numeric_eqb value value = true.
Proof.
intro value.
unfold numeric_eqb.
rewrite numeric_compare_refl.
reflexivity.
Qed.

Lemma numeric_cast_typmod_result :
  forall value precision scale result,
    numeric_cast_typmod value precision scale = Some result ->
    result = numeric_round_to_scale value scale.
Proof.
intros value precision scale result Hcast.
unfold numeric_cast_typmod in Hcast.
destruct (numeric_fits_typmod_bool value precision scale); try discriminate.
now inversion Hcast.
Qed.

(** A database value conforming to any DECIMAL(p,s) attribute is already the
    exact scale-[s] coefficient used by [numeric_avg_scale_transition].  This
    is the schema-side justification for sharing one parameterized aggregate
    semantics across all fixed DECIMAL typmods. *)
Lemma numeric_avg_fixed_attested_finite_exact :
  forall precision scale q,
    numeric_cast_typmod (NumericFinite q) precision scale =
      Some (NumericFinite q) ->
    numeric_of_scaled (numeric_finite_rounded_coeff q scale) scale =
      NumericFinite q.
Proof.
intros precision scale q Hconforms.
pose proof (numeric_cast_typmod_result
  (NumericFinite q) precision scale (NumericFinite q) Hconforms) as Hround.
cbn [numeric_round_to_scale numeric_rounded_coeff] in Hround.
now symmetry.
Qed.

(** Expression-derived scale provenance uses the same semantic obligation as
    a constrained DECIMAL column: a finite value fixed by rounding at the
    attested scale has the corresponding exact scaled coefficient. *)
Lemma numeric_avg_attested_scale_finite_exact :
  forall scale q,
    numeric_round_to_scale (NumericFinite q) scale = NumericFinite q ->
    numeric_of_scaled (numeric_finite_rounded_coeff q scale) scale =
      NumericFinite q.
Proof.
intros scale q Hround.
cbn [numeric_round_to_scale numeric_rounded_coeff] in Hround.
now symmetry.
Qed.

Lemma finite_numeric_div_by_zero :
  forall value,
    numeric_div_at_scales (NumericFinite value) 0 numeric_zero 0 = None.
Proof.
intro value.
unfold numeric_div_at_scales.
rewrite numeric_eqb_refl.
reflexivity.
Qed.

Lemma numeric_to_int32_checked_result_in_range :
  forall value result,
    numeric_to_int32_checked value = Some result ->
    int32_min <= int32_value result <= int32_max.
Proof.
intros value [result Hrange] Hchecked.
exact Hrange.
Qed.

(** Finite division is defined whenever both canonical rationals have a
    finite-decimal representation and the divisor is nonzero.  The explicit
    decimal-parts hypotheses expose the representation invariant consumed by
    PostgreSQL's [select_div_scale]; DECIMAL conformance supplies exactly this
    invariant after typmod rounding. *)
Lemma finite_decimal_numeric_division_total :
  forall left right left_scale right_scale
    left_coeff left_decimal_scale right_coeff right_decimal_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_decimal_parts (NumericFinite left) =
      Some (left_coeff, left_decimal_scale) ->
    numeric_decimal_parts (NumericFinite right) =
      Some (right_coeff, right_decimal_scale) ->
    exists result,
      numeric_div_at_scales
        (NumericFinite left) left_scale
        (NumericFinite right) right_scale = Some result.
Proof.
intros left right left_scale right_scale
  left_coeff left_decimal_scale right_coeff right_decimal_scale
  Hnonzero Hleft Hright.
unfold numeric_div_at_scales.
rewrite Hnonzero.
unfold numeric_pg_div_scale.
rewrite Hleft, Hright.
eexists; reflexivity.
Qed.

Lemma numeric_positive_is_nonzero :
  forall value,
    numeric_compare numeric_zero value = Lt ->
    numeric_eqb value numeric_zero = false.
Proof.
intros value Hpositive.
pose proof (Oset.compare_lt_gt Onumeric numeric_zero value) as Hreverse.
change
  (numeric_compare numeric_zero value =
    CompOpp (numeric_compare value numeric_zero)) in Hreverse.
rewrite Hpositive in Hreverse.
unfold numeric_eqb.
destruct (numeric_compare value numeric_zero); cbn in Hreverse;
  try discriminate; reflexivity.
Qed.

(** Once a successful finite division result is known to fit PostgreSQL's
    NUMERIC implementation limits, the runtime-error layer adds no error.
    This bridge keeps the distinction
    between mathematical totality and the server's NUMERIC representation limits
    explicit. *)
Lemma finite_numeric_division_runtime_error_none :
  forall left right left_scale right_scale result,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result ->
    numeric_runtime_fits_bool result = true ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      None.
Proof.
intros left right left_scale right_scale result
  Hnonzero Hleft_scale Hright_scale Hdivision Hfits.
cbn [numeric_div_runtime_error numeric_is_nan].
rewrite Hnonzero, Hleft_scale, Hright_scale, Hdivision.
unfold numeric_result_runtime_error.
now rewrite Hfits.
Qed.

Lemma numeric_positive_from_integer_lower_bound :
  forall lower value,
    1 <= lower ->
    (numeric_compare (numeric_of_Z lower) value = Lt \/
     numeric_compare (numeric_of_Z lower) value = Eq) ->
    numeric_compare numeric_zero value = Lt.
Proof.
intros lower value Hlower Hbound.
assert
  (numeric_compare numeric_zero (numeric_of_Z lower) = Lt)
  as Hzero_lower.
{
  cbn [numeric_compare numeric_zero numeric_of_Z].
  apply (proj1 (Qclt_alt _ _)).
  unfold Qclt, Q2Qc; cbn [this].
  apply (proj2 (Qred_lt _ _)).
  replace 0%Q with (inject_Z 0) by reflexivity.
  rewrite <- Zlt_Qlt.
  lia.
}
destruct Hbound as [Hstrict | Hequal].
- exact (Oset.compare_lt_trans Onumeric
    numeric_zero (numeric_of_Z lower) value Hzero_lower Hstrict).
- exact (Oset.compare_lt_eq_trans Onumeric
    numeric_zero (numeric_of_Z lower) value Hzero_lower Hequal).
Qed.
