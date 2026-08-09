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

Definition z_value_projection (value : value) : list Z :=
  match value with
  | Value_Z (Some integer) => integer :: nil
  | _ => nil
  end.

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

Lemma z_values_as_flat_map : forall values,
  z_values values = flat_map z_value_projection values.
Proof.
  induction values as [|value values IH]; cbn; [reflexivity|].
  destruct value; cbn; try exact IH.
  destruct o; cbn; now rewrite IH.
Qed.

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

Lemma z_values_permutation : forall left right,
  Permutation left right ->
  Permutation (z_values left) (z_values right).
Proof.
  intros left right Hperm; rewrite !z_values_as_flat_map.
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

(** A nonempty fold of a commutative semigroup is independent of the input
    permutation.  This is the common algebraic core of exact MIN/MAX. *)
Lemma fold_nonempty_permutation : forall (A : Type) (operation : A -> A -> A),
  (forall left right, operation left right = operation right left) ->
  (forall first second third,
    operation (operation first second) third =
    operation first (operation second third)) ->
  forall left right,
    Permutation left right ->
    fold_nonempty operation left = fold_nonempty operation right.
Proof.
  intros A operation Hcomm Hassoc left right Hperm.
  induction Hperm; cbn [fold_nonempty].
  - reflexivity.
  - destruct l, l'; cbn [fold_nonempty] in *; try discriminate.
    + reflexivity.
    + f_equal.
      eapply fold_left_permutation_of_commuting_steps; [|exact Hperm].
      intros current first second.
      rewrite !Hassoc, (Hcomm first second); reflexivity.
  - change
      (Some (fold_left operation l (operation y x)) =
       Some (fold_left operation l (operation x y))).
    now rewrite (Hcomm y x).
  - now rewrite IHHperm1, IHHperm2.
Qed.

(** Generic min/max over an ordered carrier.  The order is used only to prove
    the algebraic laws; aggregate evaluation remains the concrete PostgreSQL
    operation supplied by each value domain. *)
Definition ordered_minimum {A : Type} (order : Oset.Rcd A) left right :=
  match Oset.compare order left right with Gt => right | Eq | Lt => left end.

Definition ordered_maximum {A : Type} (order : Oset.Rcd A) left right :=
  match Oset.compare order left right with Lt => right | Eq | Gt => left end.

Lemma ordered_minimum_commutative : forall (A : Type) (order : Oset.Rcd A),
  forall left right,
    ordered_minimum order left right = ordered_minimum order right left.
Proof.
  intros A order left right; unfold ordered_minimum.
  rewrite (Oset.compare_lt_gt order right left).
  destruct (Oset.compare order left right) eqn:Hcompare; cbn.
  - apply (proj1 (Oset.compare_eq_iff order left right)) in Hcompare.
    now subst right.
  - reflexivity.
  - reflexivity.
Qed.

Lemma ordered_minimum_associative : forall (A : Type) (order : Oset.Rcd A),
  forall first second third,
    ordered_minimum order (ordered_minimum order first second) third =
    ordered_minimum order first (ordered_minimum order second third).
Proof.
  intros A order first second third.
  unfold ordered_minimum at 1 3.
  destruct (Oset.compare order first second) eqn:Hfirst_second.
  - apply (proj1 (Oset.compare_eq_iff order first second)) in Hfirst_second.
    subst second; unfold ordered_minimum.
    rewrite Oset.compare_eq_refl.
    destruct (Oset.compare order first third) eqn:Hfirst_third; cbn;
      rewrite ?Oset.compare_eq_refl, ?Hfirst_third; reflexivity.
  - destruct (Oset.compare order second third) eqn:Hsecond_third.
    + apply (proj1 (Oset.compare_eq_iff order second third)) in Hsecond_third.
      subst third; unfold ordered_minimum.
      now rewrite Hfirst_second, Oset.compare_eq_refl, Hfirst_second.
    + assert (Hfirst_third : Oset.compare order first third = Lt).
      { eapply Oset.compare_lt_trans; eassumption. }
      unfold ordered_minimum; now rewrite Hfirst_second, Hsecond_third,
        Hfirst_third, Hfirst_second.
    + unfold ordered_minimum; now rewrite Hfirst_second, Hsecond_third.
  - destruct (Oset.compare order second third) eqn:Hsecond_third.
    + apply (proj1 (Oset.compare_eq_iff order second third)) in Hsecond_third.
      subst third; unfold ordered_minimum.
      now rewrite Hfirst_second, Oset.compare_eq_refl, Hfirst_second.
    + unfold ordered_minimum.
      now rewrite Hfirst_second, Hsecond_third, Hfirst_second.
    + assert (Hthird_first : Oset.compare order third first = Lt).
      {
        pose proof Hfirst_second as Hsecond_first.
        pose proof Hsecond_third as Hthird_second.
        rewrite Oset.compare_lt_gt, CompOpp_iff in Hsecond_first.
        rewrite Oset.compare_lt_gt, CompOpp_iff in Hthird_second.
        eapply Oset.compare_lt_trans; eassumption.
      }
      pose proof (Oset.compare_lt_gt order first third) as Hfirst_third.
      rewrite Hthird_first in Hfirst_third; cbn in Hfirst_third.
      unfold ordered_minimum.
      now rewrite Hfirst_second, Hsecond_third, Hfirst_third.
Qed.

Lemma ordered_maximum_commutative : forall (A : Type) (order : Oset.Rcd A),
  forall left right,
    ordered_maximum order left right = ordered_maximum order right left.
Proof.
  intros A order left right; unfold ordered_maximum.
  rewrite (Oset.compare_lt_gt order right left).
  destruct (Oset.compare order left right) eqn:Hcompare; cbn.
  - apply (proj1 (Oset.compare_eq_iff order left right)) in Hcompare.
    now subst right.
  - reflexivity.
  - reflexivity.
Qed.

Lemma ordered_maximum_associative : forall (A : Type) (order : Oset.Rcd A),
  forall first second third,
    ordered_maximum order (ordered_maximum order first second) third =
    ordered_maximum order first (ordered_maximum order second third).
Proof.
  intros A order first second third.
  unfold ordered_maximum at 1 3.
  destruct (Oset.compare order first second) eqn:Hfirst_second.
  - apply (proj1 (Oset.compare_eq_iff order first second)) in Hfirst_second.
    subst second; unfold ordered_maximum.
    rewrite Oset.compare_eq_refl.
    destruct (Oset.compare order first third) eqn:Hfirst_third; cbn;
      rewrite ?Oset.compare_eq_refl, ?Hfirst_third; reflexivity.
  - destruct (Oset.compare order second third) eqn:Hsecond_third.
    + apply (proj1 (Oset.compare_eq_iff order second third)) in Hsecond_third.
      subst third; unfold ordered_maximum.
      repeat first [rewrite Hfirst_second | rewrite Oset.compare_eq_refl].
      reflexivity.
    + assert (Hfirst_third : Oset.compare order first third = Lt).
      { eapply Oset.compare_lt_trans; eassumption. }
      unfold ordered_maximum.
      repeat first [rewrite Hfirst_second | rewrite Hsecond_third |
        rewrite Hfirst_third].
      reflexivity.
    + unfold ordered_maximum.
      repeat first [rewrite Hfirst_second | rewrite Hsecond_third].
      reflexivity.
  - destruct (Oset.compare order second third) eqn:Hsecond_third.
    + apply (proj1 (Oset.compare_eq_iff order second third)) in Hsecond_third.
      subst third; unfold ordered_maximum.
      repeat first [rewrite Hfirst_second | rewrite Oset.compare_eq_refl].
      reflexivity.
    + unfold ordered_maximum.
      repeat first [rewrite Hfirst_second | rewrite Hsecond_third].
      reflexivity.
    + assert (Hthird_first : Oset.compare order third first = Lt).
      {
        pose proof Hfirst_second as Hsecond_first.
        pose proof Hsecond_third as Hthird_second.
        rewrite Oset.compare_lt_gt, CompOpp_iff in Hsecond_first.
        rewrite Oset.compare_lt_gt, CompOpp_iff in Hthird_second.
        eapply Oset.compare_lt_trans; eassumption.
      }
      pose proof (Oset.compare_lt_gt order first third) as Hfirst_third.
      rewrite Hthird_first in Hfirst_third; cbn in Hfirst_third.
      unfold ordered_maximum.
      repeat first [rewrite Hfirst_second | rewrite Hsecond_third |
        rewrite Hfirst_third].
      reflexivity.
Qed.

Lemma numeric_minimum_is_ordered_minimum : forall left right,
  numeric_min left right = ordered_minimum Onumeric left right.
Proof. reflexivity. Qed.

Lemma numeric_maximum_is_ordered_maximum : forall left right,
  numeric_max left right = ordered_maximum Onumeric left right.
Proof. reflexivity. Qed.

Lemma numeric_min_commutative : forall left right,
  numeric_min left right = numeric_min right left.
Proof.
  intros left right; rewrite !numeric_minimum_is_ordered_minimum.
  apply ordered_minimum_commutative.
Qed.

Lemma numeric_min_associative : forall first second third,
  numeric_min (numeric_min first second) third =
    numeric_min first (numeric_min second third).
Proof.
  intros first second third; rewrite !numeric_minimum_is_ordered_minimum.
  apply ordered_minimum_associative.
Qed.

Lemma numeric_max_commutative : forall left right,
  numeric_max left right = numeric_max right left.
Proof.
  intros left right; rewrite !numeric_maximum_is_ordered_maximum.
  apply ordered_maximum_commutative.
Qed.

Lemma numeric_max_associative : forall first second third,
  numeric_max (numeric_max first second) third =
    numeric_max first (numeric_max second third).
Proof.
  intros first second third; rewrite !numeric_maximum_is_ordered_maximum.
  apply ordered_maximum_associative.
Qed.

Lemma checked_fold_nonempty_permutation :
  forall (A B : Type) (predicate : value -> bool)
    (extract : list value -> list A) (operation : A -> A -> A)
    (wrap : option A -> B) left right,
    Permutation left right ->
    Permutation (extract left) (extract right) ->
    (forall first second, operation first second = operation second first) ->
    (forall first second third,
      operation (operation first second) third =
      operation first (operation second third)) ->
    (if forallb predicate left
     then wrap (fold_nonempty operation (extract left))
     else wrap None) =
    (if forallb predicate right
     then wrap (fold_nonempty operation (extract right))
     else wrap None).
Proof.
  intros A B predicate extract operation wrap left right Hvalues Hextract
    Hcomm Hassoc.
  rewrite (forallb_permutation value predicate left right Hvalues).
  destruct (forallb predicate right); [|reflexivity].
  f_equal; now apply fold_nonempty_permutation.
Qed.

Lemma interp_min_z_permutation : forall left right,
  Permutation left right -> interp_min_z left = interp_min_z right.
Proof.
  intros left right Hperm; unfold interp_min_z.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply z_values_permutation.
  - apply Z.min_comm.
  - symmetry; apply Z.min_assoc.
Qed.

Lemma interp_max_z_permutation : forall left right,
  Permutation left right -> interp_max_z left = interp_max_z right.
Proof.
  intros left right Hperm; unfold interp_max_z.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply z_values_permutation.
  - apply Z.max_comm.
  - symmetry; apply Z.max_assoc.
Qed.

Lemma interp_min_int32_permutation : forall left right,
  Permutation left right -> interp_min_int32 left = interp_min_int32 right.
Proof.
  intros left right Hperm; unfold interp_min_int32.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply int32_values_permutation.
  - apply int32_minimum_commutative.
  - apply int32_minimum_associative.
Qed.

Lemma interp_max_int32_permutation : forall left right,
  Permutation left right -> interp_max_int32 left = interp_max_int32 right.
Proof.
  intros left right Hperm; unfold interp_max_int32.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply int32_values_permutation.
  - apply int32_maximum_commutative.
  - apply int32_maximum_associative.
Qed.

Lemma interp_min_int64_permutation : forall left right,
  Permutation left right -> interp_min_int64 left = interp_min_int64 right.
Proof.
  intros left right Hperm; unfold interp_min_int64.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply int64_values_permutation.
  - apply int64_minimum_commutative.
  - apply int64_minimum_associative.
Qed.

Lemma interp_max_int64_permutation : forall left right,
  Permutation left right -> interp_max_int64 left = interp_max_int64 right.
Proof.
  intros left right Hperm; unfold interp_max_int64.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply int64_values_permutation.
  - apply int64_maximum_commutative.
  - apply int64_maximum_associative.
Qed.

Lemma interp_min_numeric_permutation : forall left right,
  Permutation left right -> interp_min_numeric left = interp_min_numeric right.
Proof.
  intros left right Hperm; unfold interp_min_numeric.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply numeric_values_permutation.
  - apply numeric_min_commutative.
  - apply numeric_min_associative.
Qed.

Lemma interp_max_numeric_permutation : forall left right,
  Permutation left right -> interp_max_numeric left = interp_max_numeric right.
Proof.
  intros left right Hperm; unfold interp_max_numeric.
  eapply checked_fold_nonempty_permutation; try eassumption.
  - now apply numeric_values_permutation.
  - apply numeric_max_commutative.
  - apply numeric_max_associative.
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

Lemma integer_stats_fold_interval_invariant :
  forall (values : list Z) lower upper count sum sum_squares,
    0 <= lower ->
    count * lower <= sum ->
    sum_squares <= upper * sum ->
    Forall (fun value => lower <= value <= upper) values ->
    let '(final_count, (final_sum, final_sum_squares)) :=
      fold_left integer_stats_transition values
        (count, (sum, sum_squares)) in
    final_count * lower <= final_sum /\
    final_sum_squares <= upper * final_sum.
Proof.
  induction values as [|value values IH];
    intros lower upper count sum sum_squares
      Hlower Hsum Hsquares Hvalues.
  - cbn; tauto.
  - inversion Hvalues as [|? ? Hvalue Htail]; subst.
    cbn [integer_stats_transition].
    apply IH; try assumption.
    + nia.
    + destruct Hvalue as [Hvalue_lower Hvalue_upper].
      assert (0 <= value) by lia.
      assert (value * value <= upper * value) by nia.
      nia.
Qed.

Lemma integer_stats_initial_interval_bounds :
  forall (values : list Z) lower upper final_count final_sum
      final_sum_squares,
    0 <= lower ->
    Forall (fun value => lower <= value <= upper) values ->
    fold_left integer_stats_transition values (0, (0, 0)) =
      (final_count, (final_sum, final_sum_squares)) ->
    final_count * lower <= final_sum /\
    final_sum_squares <= upper * final_sum.
Proof.
  intros values lower upper final_count final_sum final_sum_squares
    Hlower Hvalues Hfold.
  assert (Hzero : 0 <= upper * 0) by nia.
  pose proof
    (integer_stats_fold_interval_invariant values lower upper 0 0 0
      Hlower (Z.le_refl 0) Hzero Hvalues) as Hbounds.
  rewrite Hfold in Hbounds.
  exact Hbounds.
Qed.

Lemma bounded_integer_stats_sum_positive :
  forall (values : list Z) lower upper count sum sum_squares,
    0 < lower ->
    Forall (fun value => lower <= value <= upper) values ->
    fold_left integer_stats_transition values (0, (0, 0)) =
      (count, (sum, sum_squares)) ->
    1 <= count ->
    0 < sum.
Proof.
  intros values lower upper count sum sum_squares
    Hlower Hvalues Hfold Hcount.
  destruct
    (integer_stats_initial_interval_bounds values lower upper
      count sum sum_squares)
    as [Hsum Hsquares]; try lia; try assumption.
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

Lemma numeric_compare_eq_iff :
  forall left right,
    numeric_compare left right = Eq <-> left = right.
Proof.
intros left right.
exact (Oset.compare_eq_iff Onumeric left right).
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

Lemma numeric_eqb_true_iff :
  forall left right,
    numeric_eqb left right = true <-> left = right.
Proof.
intros left right.
change (Oset.eq_bool Onumeric left right = true <-> left = right).
apply Oset.eq_bool_true_iff.
Qed.

Lemma numeric_eqb_false_iff :
  forall left right,
    numeric_eqb left right = false <-> left <> right.
Proof.
intros left right; split.
- intros Hequal Hsame; subst right.
  rewrite numeric_eqb_refl in Hequal; discriminate.
- intro Hdistinct.
  destruct (numeric_eqb left right) eqn:Hequal; [|reflexivity].
  apply numeric_eqb_true_iff in Hequal; contradiction.
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

(** PostgreSQL's integer rounding primitive differs from the exact quotient
    by at most one half.  Keeping the certificate in doubled integer form
    avoids introducing an inexact real carrier and makes the tie-away rule
    explicit. *)
Lemma numeric_round_quot_nonnegative_half_ulp :
  forall numerator denominator,
    0 <= numerator ->
    0 < denominator ->
    2 * numerator - denominator <=
      2 * numeric_round_quot numerator denominator * denominator <=
    2 * numerator + denominator.
Proof.
intros numerator denominator Hnumerator Hdenominator.
assert (Hdenominator_nonzero : denominator <> 0) by lia.
pose proof
  (Z.quot_rem numerator denominator Hdenominator_nonzero) as Hdecompose.
pose proof
  (Z.rem_nonneg numerator denominator Hdenominator_nonzero Hnumerator)
  as Hremainder_nonnegative.
pose proof
  (Z.rem_bound_abs numerator denominator Hdenominator_nonzero)
  as Hremainder_bound.
rewrite (Z.abs_eq (Z.rem numerator denominator) Hremainder_nonnegative),
  (Z.abs_eq denominator (Z.lt_le_incl _ _ Hdenominator))
  in Hremainder_bound.
unfold numeric_round_quot.
rewrite (Z.abs_eq (Z.rem numerator denominator) Hremainder_nonnegative),
  (Z.abs_eq denominator (Z.lt_le_incl _ _ Hdenominator)).
assert (Hproduct_nonnegative : 0 <= numerator * denominator) by nia.
rewrite (proj2 (Z.ltb_ge (numerator * denominator) 0)
  Hproduct_nonnegative).
destruct (2 * Z.rem numerator denominator >=? denominator)%Z
  eqn:Hround.
- apply Z.geb_le in Hround; nia.
- rewrite Z.geb_leb in Hround.
  apply Z.leb_gt in Hround; nia.
Qed.

(** A display scale selected by PostgreSQL's division rule is always inside
    the runtime scale domain.  Value range remains a separate result check. *)
Lemma numeric_pg_div_scale_display_valid :
  forall left left_scale right right_scale result_scale,
    numeric_pg_div_scale left left_scale right right_scale =
      Some result_scale ->
    numeric_display_scale_valid_bool result_scale = true.
Proof.
intros left left_scale right right_scale result_scale Hscale.
unfold numeric_pg_div_scale in Hscale.
destruct (numeric_decimal_parts left) as [[left_coeff left_decimal_scale]|];
  [|discriminate].
destruct (numeric_decimal_parts right) as [[right_coeff right_decimal_scale]|];
  [|discriminate].
inversion Hscale; subst result_scale; clear Hscale.
unfold numeric_display_scale_valid_bool,
  postgres_numeric_max_fractional_digits,
  postgres_numeric_max_display_scale,
  postgres_numeric_min_display_scale.
apply andb_true_iff; split; apply Z.leb_le.
- apply Z.min_glb; [apply Z.le_max_r|lia].
- pose proof (Z.le_min_r
    (Z.max
      (Z.max
        (Z.max
          (postgres_numeric_min_sig_digits -
           (if numeric_pg_first_digit left_coeff left_decimal_scale <=?
               numeric_pg_first_digit right_coeff right_decimal_scale
            then numeric_pg_weight left_coeff left_decimal_scale -
                 numeric_pg_weight right_coeff right_decimal_scale - 1
            else numeric_pg_weight left_coeff left_decimal_scale -
                 numeric_pg_weight right_coeff right_decimal_scale) *
             postgres_numeric_dec_digits)
          left_scale) right_scale) 0) 1000) as Hupper.
  lia.
Qed.

Local Opaque Qred.

(** Cross multiplication is sound for canonical fixed-point values at any
    two nonnegative display scales. *)
Lemma numeric_of_scaled_compare_lt :
  forall left_coeff left_scale right_coeff right_scale,
    0 <= left_scale ->
    0 <= right_scale ->
    left_coeff * Z.pow 10 right_scale <
      right_coeff * Z.pow 10 left_scale ->
    numeric_compare
      (numeric_of_scaled left_coeff left_scale)
      (numeric_of_scaled right_coeff right_scale) = Lt.
Proof.
intros left_coeff left_scale right_coeff right_scale
  Hleft_scale Hright_scale Hcross.
unfold numeric_of_scaled.
rewrite (proj2 (Z.leb_le 0 left_scale) Hleft_scale),
  (proj2 (Z.leb_le 0 right_scale) Hright_scale).
cbn [numeric_compare].
apply (proj1 (Qclt_alt _ _)).
unfold Qclt, Qcdiv, Qcmult, Qcinv.
simpl; rewrite !Qred_correct.
change
  ((inject_Z left_coeff / inject_Z (10 ^ left_scale)) <
   (inject_Z right_coeff / inject_Z (10 ^ right_scale)))%Q.
assert (Hleft_factor : (0 < inject_Z (10 ^ left_scale))%Q).
{
  replace 0%Q with (inject_Z 0) by reflexivity.
  rewrite <- Zlt_Qlt.
  apply Z.pow_pos_nonneg; lia.
}
assert (Hright_factor : (0 < inject_Z (10 ^ right_scale))%Q).
{
  replace 0%Q with (inject_Z 0) by reflexivity.
  rewrite <- Zlt_Qlt.
  apply Z.pow_pos_nonneg; lia.
}
apply Qlt_shift_div_r; [exact Hleft_factor|].
setoid_replace
  ((inject_Z right_coeff / inject_Z (10 ^ right_scale)) *
    inject_Z (10 ^ left_scale))%Q
  with
  ((inject_Z right_coeff * inject_Z (10 ^ left_scale)) /
    inject_Z (10 ^ right_scale))%Q
  by (unfold Qdiv; ring).
apply Qlt_shift_div_l; [exact Hright_factor|].
rewrite <- !inject_Z_mult, <- Zlt_Qlt.
exact Hcross.
Qed.

(** The exact half-unit certificate for the fixed-point coefficient emitted
    by finite NUMERIC rounding.  The premise says that the scaled rational is
    nonnegative; signed rounding needs a corresponding two-sided treatment
    and is intentionally not inferred here. *)
Lemma numeric_round_to_scale_nonnegative_half_ulp :
  forall q scale,
    let scaled := this (Qcmult q (numeric_scale_factor scale)) in
    0 <= Qnum scaled ->
    let coefficient :=
      numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)) in
    numeric_round_to_scale (NumericFinite q) scale =
      numeric_of_scaled coefficient scale /\
    2 * Qnum scaled - Zpos (Qden scaled) <=
      2 * coefficient * Zpos (Qden scaled) <=
    2 * Qnum scaled + Zpos (Qden scaled).
Proof.
intros q scale scaled Hnonnegative coefficient.
subst scaled coefficient.
cbn [numeric_round_to_scale numeric_rounded_coeff
  numeric_finite_rounded_coeff].
split; [reflexivity|].
apply numeric_round_quot_nonnegative_half_ulp; [exact Hnonnegative|lia].
Qed.

(** Successful finite division is exactly one rational division followed by
    rounding at the PostgreSQL-selected display scale. *)
Lemma finite_numeric_division_result_rounding :
  forall left right left_scale right_scale result_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_pg_div_scale
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result_scale ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale =
    Some
      (numeric_round_to_scale
        (NumericFinite (Qcdiv left right)) result_scale).
Proof.
intros left right left_scale right_scale result_scale Hnonzero Hscale.
unfold numeric_div_at_scales.
rewrite Hnonzero, Hscale.
reflexivity.
Qed.

(** A strict comparison survives finite NUMERIC division whenever the exact
    scaled quotient stays below the target by more than the half-unit added
    by PostgreSQL rounding.  The runtime premises are deliberately separate:
    scale-domain validity and result-range fit are observable SQL error
    boundaries, not consequences of rational order. *)
Theorem finite_numeric_division_strict_margin :
  forall left right left_scale right_scale result_scale
      threshold_coeff threshold_scale,
    let quotient := Qcdiv left right in
    let scaled := this (Qcmult quotient
      (numeric_scale_factor result_scale)) in
    let result_coeff :=
      numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)) in
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_pg_div_scale
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result_scale ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    0 <= threshold_scale ->
    0 <= Qnum scaled ->
    (2 * Qnum scaled + Zpos (Qden scaled)) *
        Z.pow 10 threshold_scale <
      2 * threshold_coeff * Zpos (Qden scaled) *
        Z.pow 10 result_scale ->
    numeric_runtime_fits_bool
      (numeric_of_scaled result_coeff result_scale) = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale =
        Some (numeric_of_scaled result_coeff result_scale) /\
    numeric_compare
      (numeric_of_scaled result_coeff result_scale)
      (numeric_of_scaled threshold_coeff threshold_scale) = Lt /\
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      None.
Proof.
intros left right left_scale right_scale result_scale
  threshold_coeff threshold_scale quotient scaled result_coeff
  Hnonzero Hscale Hleft_scale Hright_scale Hthreshold_scale
  Hscaled_nonnegative Hmargin Hfits.
subst quotient scaled.
pose proof
  (numeric_round_to_scale_nonnegative_half_ulp
    (Qcdiv left right) result_scale Hscaled_nonnegative)
  as [Hround [_ Hround_upper]].
pose proof
  (finite_numeric_division_result_rounding
    left right left_scale right_scale result_scale Hnonzero Hscale)
  as Hdivision.
rewrite Hround in Hdivision.
assert (Hthreshold_factor : 0 < Z.pow 10 threshold_scale).
{ apply Z.pow_pos_nonneg; lia. }
assert (Hresult_cross :
  result_coeff * Z.pow 10 threshold_scale <
    threshold_coeff * Z.pow 10 result_scale) by nia.
split; [exact Hdivision|].
split.
- pose proof
    (numeric_pg_div_scale_display_valid
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale result_scale Hscale)
    as Hresult_scale.
  unfold numeric_display_scale_valid_bool in Hresult_scale.
  apply andb_true_iff in Hresult_scale.
  destruct Hresult_scale as [Hresult_nonnegative _].
  apply Z.leb_le in Hresult_nonnegative.
  now apply numeric_of_scaled_compare_lt.
- eapply finite_numeric_division_runtime_error_none; eassumption.
Qed.

(** The complementary finite-division error branches retain PostgreSQL's
    observable category instead of collapsing every failed premise into a
    generic safety condition. *)
Lemma finite_numeric_division_runtime_error_zero_divisor :
  forall left right left_scale right_scale,
    numeric_eqb (NumericFinite right) numeric_zero = true ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException DivisionByZero).
Proof.
intros left right left_scale right_scale Hzero.
cbn [numeric_div_runtime_error numeric_is_nan].
now rewrite Hzero.
Qed.

Lemma finite_numeric_division_runtime_error_invalid_scale :
  forall left right left_scale right_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    (numeric_display_scale_valid_bool left_scale = false \/
     numeric_display_scale_valid_bool right_scale = false) ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
Proof.
intros left right left_scale right_scale Hnonzero Hinvalid.
cbn [numeric_div_runtime_error numeric_is_nan].
rewrite Hnonzero.
destruct Hinvalid as [Hleft | Hright].
- rewrite Hleft; reflexivity.
- rewrite Hright.
  now destruct (numeric_display_scale_valid_bool left_scale).
Qed.

Lemma finite_numeric_division_runtime_error_missing_result :
  forall left right left_scale right_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = None ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
Proof.
intros left right left_scale right_scale
  Hnonzero Hleft_scale Hright_scale Hdivision.
cbn [numeric_div_runtime_error numeric_is_nan].
now rewrite Hnonzero, Hleft_scale, Hright_scale, Hdivision.
Qed.

Lemma finite_numeric_division_runtime_error_result_out_of_range :
  forall left right left_scale right_scale result,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result ->
    numeric_runtime_fits_bool result = false ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
Proof.
intros left right left_scale right_scale result
  Hnonzero Hleft_scale Hright_scale Hdivision Hfits.
cbn [numeric_div_runtime_error numeric_is_nan].
rewrite Hnonzero, Hleft_scale, Hright_scale, Hdivision.
unfold numeric_result_runtime_error, numeric_value_out_of_range.
now rewrite Hfits.
Qed.

(** [numeric_sqrt_at_scale] returns either the integer square-root lower
    coefficient or its successor.  The branch certificate exposes the exact
    half-unit midpoint comparison used by PostgreSQL, while the common lower
    square bound connects the result back to the input rational. *)
Lemma numeric_sqrt_at_scale_half_ulp_shape :
  forall q scale,
    0 <= scale ->
    let raw := this q in
    0 <= Qnum raw ->
    let factor := Z.pow 10 scale in
    let numerator := Qnum raw * factor * factor in
    let denominator := Zpos (Qden raw) in
    let lower := Z.sqrt (Z.div numerator denominator) in
    let midpoint_twice := 2 * lower + 1 in
    let coefficient :=
      if denominator * midpoint_twice * midpoint_twice <=? 4 * numerator
      then lower + 1
      else lower in
    numeric_sqrt_at_scale (NumericFinite q) scale =
      Some (numeric_of_scaled coefficient scale) /\
    0 <= lower /\
    denominator * lower * lower <= numerator /\
    numerator < denominator * (lower + 1) * (lower + 1) /\
    ((coefficient = lower /\
      4 * numerator <
        denominator * midpoint_twice * midpoint_twice) \/
     (coefficient = lower + 1 /\
      denominator * midpoint_twice * midpoint_twice <= 4 * numerator)).
Proof.
intros q scale Hscale raw Hraw factor numerator denominator lower
  midpoint_twice coefficient.
subst raw factor numerator denominator lower midpoint_twice coefficient.
assert (Hfactor : 0 < 10 ^ scale).
{ apply Z.pow_pos_nonneg; lia. }
assert (Hnumerator : 0 <= Qnum q * 10 ^ scale * 10 ^ scale) by nia.
assert (Hdenominator : 0 < Zpos (Qden q)) by lia.
assert (Hquotient :
  0 <= (Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)).
{ apply Z.div_pos; assumption. }
pose proof (Z.sqrt_spec _ Hquotient) as Hsqrt; cbn in Hsqrt.
pose proof
  (Z.mul_div_le
    (Qnum q * 10 ^ scale * 10 ^ scale)
    (Zpos (Qden q)) Hdenominator)
  as Hdivision_lower.
assert (Hlower :
  Zpos (Qden q) *
      Z.sqrt ((Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)) *
      Z.sqrt ((Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)) <=
    Qnum q * 10 ^ scale * 10 ^ scale) by nia.
pose proof
  (Z.div_mod
    (Qnum q * 10 ^ scale * 10 ^ scale)
    (Zpos (Qden q)) ltac:(lia)) as Hdivision_exact.
pose proof
  (Z.mod_pos_bound
    (Qnum q * 10 ^ scale * 10 ^ scale)
    (Zpos (Qden q)) Hdenominator) as Hremainder.
assert (Hupper :
  Qnum q * 10 ^ scale * 10 ^ scale <
    Zpos (Qden q) *
      (Z.sqrt
        ((Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)) + 1) *
      (Z.sqrt
        ((Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)) + 1)) by nia.
unfold numeric_sqrt_at_scale.
rewrite (proj2 (Z.ltb_ge scale 0) Hscale),
  (proj2 (Z.ltb_ge (Qnum q) 0) Hraw).
destruct
  (Zpos (Qden q) *
      (2 * Z.sqrt
        ((Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)) + 1) *
      (2 * Z.sqrt
        ((Qnum q * 10 ^ scale * 10 ^ scale) / Zpos (Qden q)) + 1) <=?
    4 * (Qnum q * 10 ^ scale * 10 ^ scale))
  eqn:Hmidpoint.
- split; [reflexivity|].
  split; [apply Z.sqrt_nonneg|].
  split; [exact Hlower|].
  split; [exact Hupper|].
  right; split; [reflexivity|].
  now apply Z.leb_le in Hmidpoint.
- split; [reflexivity|].
  split; [apply Z.sqrt_nonneg|].
  split; [exact Hlower|].
  split; [exact Hupper|].
  left; split; [reflexivity|].
  now apply Z.leb_gt in Hmidpoint.
Qed.

(** On the positive-variance branch, the scale-preserving sample standard
    deviation finalizer is exactly variance division followed by the rounded
    square root at the selected scale. *)
Theorem numeric_integer_stddev_samp_positive_success_iff :
  forall count sum sum_squares stddev scale,
    2 <= count ->
    0 < count * sum_squares - sum * sum ->
    (numeric_integer_stddev_samp_with_scale count sum sum_squares =
      Some (stddev, scale) <->
     exists variance,
       numeric_pg_div_scale
         (numeric_of_Z (count * sum_squares - sum * sum)) 0
         (numeric_of_Z (count * (count - 1))) 0 = Some scale /\
       numeric_div_at_scales
         (numeric_of_Z (count * sum_squares - sum * sum)) 0
         (numeric_of_Z (count * (count - 1))) 0 = Some variance /\
       numeric_sqrt_at_scale variance scale = Some stddev).
Proof.
intros count sum sum_squares stddev scale Hcount Hnumerator.
assert (Hnonempty : (count =? 0) = false).
{ apply Z.eqb_neq; lia. }
assert (Hsample : (count <=? 1) = false).
{ apply Z.leb_gt; lia. }
assert (Hpositive :
  (count * sum_squares - sum * sum <=? 0) = false).
{ apply Z.leb_gt; lia. }
unfold numeric_integer_stddev_samp_with_scale.
rewrite Hnonempty, Hsample, Hpositive.
split.
- intro Hsuccess.
  destruct
    (numeric_pg_div_scale
      (numeric_of_Z (count * sum_squares - sum * sum)) 0
      (numeric_of_Z (count * (count - 1))) 0)
    as [selected_scale|] eqn:Hscale; [|discriminate].
  destruct
    (numeric_div_at_scales
      (numeric_of_Z (count * sum_squares - sum * sum)) 0
      (numeric_of_Z (count * (count - 1))) 0)
    as [variance|] eqn:Hvariance; [|discriminate].
  destruct (numeric_sqrt_at_scale variance selected_scale)
    as [result|] eqn:Hsqrt; [|discriminate].
  inversion Hsuccess; subst result selected_scale.
  exists variance; repeat split; assumption.
- intros [variance [Hscale [Hvariance Hsqrt]]].
  now rewrite Hscale, Hvariance, Hsqrt.
Qed.

(** The value and display scale of nonempty AVG(int4) expose the same finite
    division components.  This is the raw-state counterpart of
    [interp_avg_int32_value_dscale_coherent]. *)
Theorem int32_avg_numeric_with_scale_success_iff :
  forall values count sum average scale,
    values <> [] ->
    fold_left int32_avg_transition values (0, 0) = (count, sum) ->
    (int32_avg_numeric_with_scale values = Some (average, scale) <->
     numeric_pg_div_scale
       (numeric_of_Z sum) 0 (numeric_of_Z count) 0 = Some scale /\
     numeric_div_at_scales
       (numeric_of_Z sum) 0 (numeric_of_Z count) 0 = Some average).
Proof.
intros values count sum average scale Hnonempty Hfold.
assert (Hcount : 0 < count).
{
  pose proof (int32_avg_fold_count_exact values 0 0) as Hcount_exact.
  rewrite Hfold in Hcount_exact; cbn in Hcount_exact.
  destruct values; [contradiction|cbn in Hcount_exact; lia].
}
destruct values as [|first rest]; [contradiction|].
unfold int32_avg_numeric_with_scale.
rewrite Hfold.
rewrite (proj2 (Z.eqb_neq count 0) ltac:(lia)).
split.
- intro Hsuccess.
  destruct
    (numeric_pg_div_scale
      (numeric_of_Z sum) 0 (numeric_of_Z count) 0)
    as [selected_scale|] eqn:Hscale; [|discriminate].
  destruct
    (numeric_div_at_scales
      (numeric_of_Z sum) 0 (numeric_of_Z count) 0)
    as [result|] eqn:Hdivision; [|discriminate].
  inversion Hsuccess; subst result selected_scale.
  split; reflexivity.
- intros [Hscale Hdivision].
  now rewrite Hscale, Hdivision.
Qed.

(** The non-strict counterpart of [numeric_of_scaled_compare_lt].  It is
    stated as exclusion of [Gt] because SQL's comparison consumers branch on
    the three-way result; equality at the unit boundary must remain visible. *)
Lemma numeric_of_scaled_compare_not_gt :
  forall left_coeff left_scale right_coeff right_scale,
    0 <= left_scale ->
    0 <= right_scale ->
    left_coeff * Z.pow 10 right_scale <=
      right_coeff * Z.pow 10 left_scale ->
    numeric_compare
      (numeric_of_scaled left_coeff left_scale)
      (numeric_of_scaled right_coeff right_scale) <> Gt.
Proof.
intros left_coeff left_scale right_coeff right_scale
  Hleft_scale Hright_scale Hcross.
unfold numeric_of_scaled.
rewrite (proj2 (Z.leb_le 0 left_scale) Hleft_scale),
  (proj2 (Z.leb_le 0 right_scale) Hright_scale).
cbn [numeric_compare].
apply (proj1 (Qcle_alt _ _)).
unfold Qcle, Qcdiv, Qcmult, Qcinv.
simpl; rewrite !Qred_correct.
change
  ((inject_Z left_coeff / inject_Z (10 ^ left_scale)) <=
   (inject_Z right_coeff / inject_Z (10 ^ right_scale)))%Q.
assert (Hleft_factor : (0 < inject_Z (10 ^ left_scale))%Q).
{
  replace 0%Q with (inject_Z 0) by reflexivity.
  rewrite <- Zlt_Qlt.
  apply Z.pow_pos_nonneg; lia.
}
assert (Hright_factor : (0 < inject_Z (10 ^ right_scale))%Q).
{
  replace 0%Q with (inject_Z 0) by reflexivity.
  rewrite <- Zlt_Qlt.
  apply Z.pow_pos_nonneg; lia.
}
apply Qle_shift_div_r; [exact Hleft_factor|].
setoid_replace
  ((inject_Z right_coeff / inject_Z (10 ^ right_scale)) *
    inject_Z (10 ^ left_scale))%Q
  with
  ((inject_Z right_coeff * inject_Z (10 ^ left_scale)) /
    inject_Z (10 ^ right_scale))%Q
  by (unfold Qdiv; ring).
apply Qle_shift_div_l; [exact Hright_factor|].
rewrite <- !inject_Z_mult, <- Zle_Qle.
exact Hcross.
Qed.

Lemma positive_numeric_of_scaled_nonzero :
  forall coefficient scale,
    0 <= scale ->
    0 < coefficient ->
    numeric_eqb (numeric_of_scaled coefficient scale) numeric_zero = false.
Proof.
intros coefficient scale Hscale Hcoefficient.
apply numeric_positive_is_nonzero.
replace numeric_zero with (numeric_of_scaled 0 0) by reflexivity.
apply numeric_of_scaled_compare_lt; [lia|exact Hscale|].
cbn; pose proof (Z.pow_pos_nonneg 10 scale ltac:(lia)); nia.
Qed.

Lemma numeric_runtime_fits_from_decimal_parts :
  forall value coefficient scale,
    numeric_decimal_parts value = Some (coefficient, scale) ->
    numeric_display_scale_valid_bool scale = true ->
    numeric_integer_digit_count coefficient scale <=
      postgres_numeric_max_integer_digits ->
    numeric_runtime_fits_bool value = true.
Proof.
intros value coefficient scale Hparts Hscale Hdigits.
destruct value as [|finite| |]; try discriminate.
cbn [numeric_runtime_fits_bool].
rewrite Hparts, Hscale.
now rewrite (proj2 (Z.leb_le _ _) Hdigits).
Qed.
