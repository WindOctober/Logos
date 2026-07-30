From SQLFS Require Import Bool3 FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  OrderedSet SqlErrorSemantics SqlOutcome SqlQuerySemantics
  SqlQuerySyntax SqlSyntax Values.
From Logos.FormalSQL Require Import NumericDerivedFacts NumericFacts TNullSyntax.
From Stdlib Require Import Bool Lia List Sorting.Permutation String ZArith.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope string_scope.

(** Left-biased runtime-error selection is deterministic and compositional. *)

Lemma first_error_none_iff : forall left right,
  first_error left right = None <-> left = None /\ right = None.
Proof.
  intros [left_error|] right; cbn.
  - split.
    + discriminate.
    + intros [Hleft _]; discriminate.
  - split.
    + intro Hright; now split.
    + intros [_ Hright]; exact Hright.
Qed.

Lemma first_error_some_iff : forall left right error,
  first_error left right = Some error <->
  left = Some error \/ (left = None /\ right = Some error).
Proof.
  intros [left_error|] right error; cbn.
  - split.
    + intro H; now left.
    + intros [H | [Hnone _]]; [exact H|discriminate].
  - split.
    + intro H; right; now split.
    + intros [H | [_ H]]; [discriminate|exact H].
Qed.

Lemma first_runtime_error_app :
  forall (A : Type) (check : A -> option sql_runtime_error) left right,
    first_runtime_error check (left ++ right) =
    first_error
      (first_runtime_error check left)
      (first_runtime_error check right).
Proof.
  intros A check left; induction left as [|value left IH]; intro right; cbn.
  - reflexivity.
  - destruct (check value); cbn; [reflexivity|exact (IH right)].
Qed.

Lemma first_runtime_error_none_iff :
  forall (A : Type) (check : A -> option sql_runtime_error) values,
    first_runtime_error check values = None <->
    Forall (fun value => check value = None) values.
Proof.
  intros A check values; induction values as [|value values IH]; cbn.
  - split; intro; constructor.
  - destruct (check value) as [error|] eqn:Hvalue.
    + split.
      * discriminate.
      * intro Hall; inversion Hall; congruence.
    + split.
      * intro Hrest; constructor; [exact Hvalue|].
        now apply IH.
      * intro Hall; inversion Hall as [|? ? _ Hrest]; subst.
        now apply IH.
Qed.

Lemma first_runtime_error_some_member :
  forall (A : Type) (check : A -> option sql_runtime_error) values error,
    first_runtime_error check values = Some error ->
    exists value, In value values /\ check value = Some error.
Proof.
  intros A check values; induction values as [|value values IH];
    intros error Herror; cbn in Herror.
  - discriminate.
  - destruct (check value) as [head_error|] eqn:Hvalue.
    + inversion Herror; subst.
      exists value; split; [now left|exact Hvalue].
    + destruct (IH error Herror) as [member [Hin Hmember]].
      exists member; split; [now right|exact Hmember].
Qed.

Lemma first_observation_error_as_first_runtime_error : forall observations,
  first_observation_error observations =
  first_runtime_error (fun observation => fst observation) observations.
Proof.
  induction observations as [|[error value] observations IH]; cbn.
  - reflexivity.
  - destruct error; cbn; [reflexivity|exact IH].
Qed.

Lemma first_observation_error_none_iff : forall observations,
  first_observation_error observations = None <->
  Forall (fun observation => fst observation = None) observations.
Proof.
  intro observations.
  rewrite first_observation_error_as_first_runtime_error.
  apply first_runtime_error_none_iff.
Qed.

Lemma first_observation_error_some_member : forall observations error,
  first_observation_error observations = Some error ->
  exists observation,
    In observation observations /\ fst observation = Some error.
Proof.
  intros observations error Herror.
  rewrite first_observation_error_as_first_runtime_error in Herror.
  now apply first_runtime_error_some_member in Herror.
Qed.

Lemma observation_values_length : forall observations,
  List.length (observation_values observations) = List.length observations.
Proof.
  intro observations; unfold observation_values.
  apply length_map.
Qed.

(** Aggregate errors compose child errors with aggregate-local checks. *)

Lemma aggregate_call_child_error_propagates :
  forall function quantifier observations error,
    first_observation_error observations = Some error ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = Some error.
Proof.
  intros function quantifier observations error Herror.
  unfold interp_aggregate_runtime_error; now rewrite Herror.
Qed.

Lemma aggregate_call_safe_children_reduce_to_local :
  forall function quantifier observations,
    first_observation_error observations = None ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations =
    aggregate_local_runtime_error
      (AggregateCall function quantifier) (observation_values observations).
Proof.
  intros function quantifier observations Hsafe.
  unfold interp_aggregate_runtime_error; now rewrite Hsafe.
Qed.

Lemma aggregate_call_runtime_safe :
  forall function quantifier observations,
    first_observation_error observations = None ->
    aggregate_local_runtime_error
      (AggregateCall function quantifier)
      (observation_values observations) = None ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = None.
Proof.
  intros function quantifier observations Hchildren Hlocal.
  rewrite aggregate_call_safe_children_reduce_to_local by exact Hchildren.
  exact Hlocal.
Qed.

Lemma aggregate_call_runtime_error_as_first_error :
  forall function quantifier observations,
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations =
    first_error
      (first_observation_error observations)
      (aggregate_local_runtime_error
        (AggregateCall function quantifier)
        (observation_values observations)).
Proof.
  intros function quantifier observations.
  unfold interp_aggregate_runtime_error, first_error.
  now destruct (first_observation_error observations).
Qed.

Lemma aggregate_call_runtime_error_none_iff :
  forall function quantifier observations,
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = None <->
    first_observation_error observations = None /\
    aggregate_local_runtime_error
      (AggregateCall function quantifier)
      (observation_values observations) = None.
Proof.
  intros function quantifier observations.
  rewrite aggregate_call_runtime_error_as_first_error.
  apply first_error_none_iff.
Qed.

Lemma aggregate_call_runtime_error_some_iff :
  forall function quantifier observations error,
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = Some error <->
    first_observation_error observations = Some error \/
    (first_observation_error observations = None /\
     aggregate_local_runtime_error
       (AggregateCall function quantifier)
       (observation_values observations) = Some error).
Proof.
  intros function quantifier observations error.
  rewrite aggregate_call_runtime_error_as_first_error.
  apply first_error_some_iff.
Qed.

Lemma count_star_runtime_error_observations : forall observations,
  interp_aggregate_runtime_error AggregateCountStar observations =
  count_runtime_error (observation_values observations).
Proof. reflexivity. Qed.

Lemma int64_result_runtime_error_none_of_range : forall integer,
  int64_min <= integer <= int64_max ->
  int64_result_runtime_error integer = None.
Proof.
  intros integer Hrange.
  apply int64_checked_defined_iff in Hrange.
  destruct Hrange as [result Hresult].
  unfold int64_result_runtime_error; now rewrite Hresult.
Qed.

Lemma int64_result_runtime_error_none_iff : forall integer,
  int64_result_runtime_error integer = None <->
  int64_min <= integer <= int64_max.
Proof.
  intro integer; unfold int64_result_runtime_error.
  destruct (int64_checked integer) as [result|] eqn:Hresult.
  - split; intro.
    + apply (proj1 (int64_checked_defined_iff integer)).
      now exists result.
    + reflexivity.
  - split.
    + discriminate.
    + intro Hrange.
      apply (proj2 (int64_checked_defined_iff integer)) in Hrange.
      destruct Hrange as [result Hdefined]; congruence.
Qed.

Lemma count_runtime_error_none_of_row_count_range : forall values,
  int64_min <= row_count values <= int64_max ->
  count_runtime_error values = None.
Proof.
  intros values Hrange; unfold count_runtime_error.
  now apply int64_result_runtime_error_none_of_range.
Qed.

Lemma count_runtime_error_none_iff : forall values,
  count_runtime_error values = None <->
  int64_min <= row_count values <= int64_max.
Proof.
  intro values; unfold count_runtime_error.
  apply int64_result_runtime_error_none_iff.
Qed.

Lemma non_null_count_runtime_error_none_of_range : forall values,
  int64_min <= non_null_count values <= int64_max ->
  non_null_count_runtime_error values = None.
Proof.
  intros values Hrange; unfold non_null_count_runtime_error.
  now apply int64_result_runtime_error_none_of_range.
Qed.

Lemma non_null_count_runtime_error_none_iff : forall values,
  non_null_count_runtime_error values = None <->
  int64_min <= non_null_count values <= int64_max.
Proof.
  intro values; unfold non_null_count_runtime_error.
  apply int64_result_runtime_error_none_iff.
Qed.

(** This classifier contains exactly aggregate functions whose local callback
    is definitionally total for arbitrary value lists.  It says nothing about
    child-expression errors, which remain a separate premise above. *)
Definition aggregate_function_locally_total
    (function : aggregate_function) : bool :=
  match function with
  | AggregateSumZ
  | AggregateBitAndInt32 | AggregateBitOrInt32
  | AggregateBitAndInt64 | AggregateBitOrInt64
  | AggregateMaxZ | AggregateMaxInt32 | AggregateMaxInt64
  | AggregateMaxFloat | AggregateMaxDouble | AggregateMaxNumeric
  | AggregateMaxString
  | AggregateMinZ | AggregateMinInt32 | AggregateMinInt64
  | AggregateMinFloat | AggregateMinDouble | AggregateMinNumeric
  | AggregateAverageZ | AggregateAverageInt32Numeric
  | AggregateNumericDisplayScale _ | AggregateAverageInt64Numeric
  | AggregateVariancePopulationInt32 | AggregateVarianceSampleInt32
  | AggregateStddevPopulationInt32 | AggregateStddevSampleInt32 => true
  | _ => false
  end.

Lemma aggregate_function_locally_total_safe : forall function values,
  aggregate_function_locally_total function = true ->
  aggregate_local_runtime_error_function function values = None.
Proof.
  intros function values Htotal.
  unfold aggregate_function_locally_total in Htotal.
  unfold aggregate_local_runtime_error_function.
  destruct function; cbn in Htotal; try discriminate; reflexivity.
Qed.

Lemma aggregate_call_locally_total_safe :
  forall function quantifier values,
    aggregate_function_locally_total function = true ->
    aggregate_local_runtime_error
      (AggregateCall function quantifier) values = None.
Proof.
  intros function quantifier values Htotal.
  unfold aggregate_local_runtime_error.
  now apply aggregate_function_locally_total_safe.
Qed.

Lemma aggregate_call_runtime_safe_of_locally_total :
  forall function quantifier observations,
    aggregate_function_locally_total function = true ->
    first_observation_error observations = None ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = None.
Proof.
  intros function quantifier observations Htotal Hchildren.
  apply aggregate_call_runtime_safe; [exact Hchildren|].
  now apply aggregate_call_locally_total_safe.
Qed.

(** ALL, DISTINCT, and declarative FILTER-style input selection. *)

Lemma all_null_non_null_count_zero : forall values,
  Forall (fun value => is_null_value value = true) values ->
  non_null_count values = 0.
Proof.
  intros values Hnulls; unfold non_null_count.
  assert (filter (fun value => negb (is_null_value value)) values = [])
    as Hfiltered.
  {
    induction Hnulls as [|value values Hvalue Hvalues IH]; cbn.
    - reflexivity.
    - rewrite Hvalue; cbn; exact IH.
  }
  now rewrite Hfiltered.
Qed.

Lemma aggregate_input_values_membership :
  forall quantifier value values,
    In value (aggregate_input_values quantifier values) <-> In value values.
Proof.
  intros [|] value values; cbn.
  - reflexivity.
  - apply distinct_values_membership.
Qed.

Lemma aggregate_input_values_nonempty_iff : forall quantifier values,
  aggregate_input_values quantifier values <> [] <-> values <> [].
Proof.
  intros quantifier values; split.
  - intros Hselected ->; apply Hselected; destruct quantifier; reflexivity.
  - intros Hvalues Hselected.
    destruct values as [|value values]; [contradiction|].
    assert (Hin : In value
      (aggregate_input_values quantifier (value :: values))).
    {
      apply (proj2
        (aggregate_input_values_membership
          quantifier value (value :: values))).
      now left.
    }
    rewrite Hselected in Hin; contradiction.
Qed.

(** Aggregate quantifiers can discard duplicate occurrences, but they never
    introduce a value outside the original input support.  Stating this once
    for an arbitrary property avoids rebuilding DISTINCT-specific [Forall]
    arguments for every aggregate function. *)
Lemma aggregate_input_values_preserves_Forall :
  forall quantifier (P : value -> Prop) values,
    Forall P values ->
    Forall P (aggregate_input_values quantifier values).
Proof.
  intros quantifier P values Hvalues.
  rewrite Forall_forall in Hvalues |- *.
  intros value Hvalue.
  apply Hvalues.
  exact (proj1
    (aggregate_input_values_membership quantifier value values) Hvalue).
Qed.

(** On an entirely non-NULL input, SQL COUNT observes every occurrence. *)
Lemma non_null_count_eq_length_of_Forall_nonnull :
  forall values,
    Forall (fun value => is_null_value value = false) values ->
    non_null_count values = Z.of_nat (List.length values).
Proof.
  intros values Hvalues.
  unfold non_null_count.
  f_equal.
  induction Hvalues as [|value values Hvalue Hvalues IH]; cbn.
  - reflexivity.
  - rewrite Hvalue; cbn; now rewrite IH.
Qed.

Lemma distinct_values_fixed_of_nodup : forall values,
  NoDup values -> distinct_values values = values.
Proof.
  intros values Hnodup; induction Hnodup as [|value values Hfresh Hnodup IH];
    cbn.
  - reflexivity.
  - destruct (Oset.mem_bool OVal value values) eqn:Hmember.
    + apply Oset.mem_bool_true_iff in Hmember; contradiction.
    + now rewrite IH.
Qed.

Lemma distinct_values_length_le : forall values,
  (List.length (distinct_values values) <= List.length values)%nat.
Proof.
  intro values; induction values as [|value values IH]; cbn; [lia|].
  destruct (Oset.mem_bool OVal value values); cbn; lia.
Qed.

Lemma aggregate_input_values_length_le : forall quantifier values,
  (List.length (aggregate_input_values quantifier values) <=
   List.length values)%nat.
Proof.
  intros [|] values; cbn; [lia|].
  apply distinct_values_length_le.
Qed.

Lemma aggregate_input_values_distinct_nodup : forall values,
  NoDup (aggregate_input_values AggregateDistinct values).
Proof.
  intro values; apply distinct_values_nodup.
Qed.

(** DISTINCT aggregate selection is canonical only up to permutation: any
    duplicate-free list with exactly the original support is an equally valid
    selected input for permutation-invariant aggregate semantics. *)
Theorem aggregate_distinct_input_Permutation_of_NoDup_support :
  forall values selected,
    NoDup selected ->
    (forall value, In value selected <-> In value values) ->
    Permutation
      (aggregate_input_values AggregateDistinct values)
      (aggregate_input_values AggregateAll selected).
Proof.
  intros values selected Hselected Hsupport.
  cbn [aggregate_input_values].
  apply NoDup_Permutation.
  - apply distinct_values_nodup.
  - exact Hselected.
  - intro value.
    rewrite distinct_values_membership.
    symmetry; apply Hsupport.
Qed.

Lemma aggregate_input_values_permutation :
  forall quantifier left right,
    Permutation left right ->
    Permutation
      (aggregate_input_values quantifier left)
      (aggregate_input_values quantifier right).
Proof.
  intros [|] left right Hpermutation; cbn.
  - exact Hpermutation.
  - now apply distinct_values_permutation.
Qed.

Lemma non_null_count_permutation : forall left right,
  Permutation left right -> non_null_count left = non_null_count right.
Proof.
  intros left right Hpermutation.
  assert (Hfiltered :
    Permutation
      (filter (fun value => negb (is_null_value value)) left)
      (filter (fun value => negb (is_null_value value)) right)).
  {
    induction Hpermutation; cbn.
    - constructor.
    - destruct (is_null_value x); cbn; [exact IHHpermutation|].
      now constructor.
    - destruct (is_null_value x), (is_null_value y); cbn;
        try apply Permutation_refl.
      apply perm_swap.
    - now transitivity
        (filter (fun value => negb (is_null_value value)) l').
  }
  unfold non_null_count.
  now rewrite (Permutation_length Hfiltered).
Qed.

Lemma interp_aggregate_count_star_permutation : forall left right,
  Permutation left right ->
  interp_aggregate AggregateCountStar left =
  interp_aggregate AggregateCountStar right.
Proof.
  intros left right Hpermutation.
  change
    (value_int64_checked (row_count left) =
     value_int64_checked (row_count right)).
  unfold row_count.
  now rewrite (Permutation_length Hpermutation).
Qed.

Lemma aggregate_count_star_local_runtime_error_permutation : forall left right,
  Permutation left right ->
  aggregate_local_runtime_error AggregateCountStar left =
  aggregate_local_runtime_error AggregateCountStar right.
Proof.
  intros left right Hpermutation.
  change (count_runtime_error left = count_runtime_error right).
  unfold count_runtime_error, row_count.
  now rewrite (Permutation_length Hpermutation).
Qed.

Lemma interp_aggregate_count_permutation : forall quantifier left right,
  Permutation left right ->
  interp_aggregate (AggregateCall AggregateCount quantifier) left =
  interp_aggregate (AggregateCall AggregateCount quantifier) right.
Proof.
  intros quantifier left right Hpermutation.
  change
    (value_int64_checked
       (non_null_count (aggregate_input_values quantifier left)) =
     value_int64_checked
       (non_null_count (aggregate_input_values quantifier right))).
  rewrite (non_null_count_permutation
    (aggregate_input_values quantifier left)
    (aggregate_input_values quantifier right)).
  - reflexivity.
  - now apply aggregate_input_values_permutation.
Qed.

Lemma aggregate_count_local_runtime_error_permutation :
  forall quantifier left right,
    Permutation left right ->
    aggregate_local_runtime_error
      (AggregateCall AggregateCount quantifier) left =
    aggregate_local_runtime_error
      (AggregateCall AggregateCount quantifier) right.
Proof.
  intros quantifier left right Hpermutation.
  change
    (non_null_count_runtime_error
       (aggregate_input_values quantifier left) =
     non_null_count_runtime_error
       (aggregate_input_values quantifier right)).
  unfold non_null_count_runtime_error.
  rewrite (non_null_count_permutation
    (aggregate_input_values quantifier left)
    (aggregate_input_values quantifier right)).
  - reflexivity.
  - now apply aggregate_input_values_permutation.
Qed.

Lemma aggregate_input_values_idempotent : forall quantifier values,
  aggregate_input_values quantifier
    (aggregate_input_values quantifier values) =
  aggregate_input_values quantifier values.
Proof.
  intros [|] values; cbn.
  - reflexivity.
  - apply distinct_values_fixed_of_nodup, distinct_values_nodup.
Qed.

Lemma interp_aggregate_call_selected_input_congr :
  forall function left_quantifier right_quantifier left right,
    aggregate_input_values left_quantifier left =
    aggregate_input_values right_quantifier right ->
    interp_aggregate (AggregateCall function left_quantifier) left =
    interp_aggregate (AggregateCall function right_quantifier) right.
Proof.
  intros function left_quantifier right_quantifier left right Hselected.
  cbn [interp_aggregate]; now rewrite Hselected.
Qed.

Lemma aggregate_call_local_runtime_error_selected_input_congr :
  forall function left_quantifier right_quantifier left right,
    aggregate_input_values left_quantifier left =
    aggregate_input_values right_quantifier right ->
    aggregate_local_runtime_error
      (AggregateCall function left_quantifier) left =
    aggregate_local_runtime_error
      (AggregateCall function right_quantifier) right.
Proof.
  intros function left_quantifier right_quantifier left right Hselected.
  cbn [aggregate_local_runtime_error]; now rewrite Hselected.
Qed.

Lemma interp_aggregate_call_permutation_congr :
  forall function quantifier left right,
    (forall first second,
      Permutation first second ->
      interp_aggregate_function function first =
      interp_aggregate_function function second) ->
    Permutation left right ->
    interp_aggregate (AggregateCall function quantifier) left =
    interp_aggregate (AggregateCall function quantifier) right.
Proof.
  intros function quantifier left right Hstable Hpermutation.
  cbn [interp_aggregate].
  apply Hstable, aggregate_input_values_permutation, Hpermutation.
Qed.

Lemma aggregate_call_local_runtime_error_permutation_congr :
  forall function quantifier left right,
    (forall first second,
      Permutation first second ->
      aggregate_local_runtime_error_function function first =
      aggregate_local_runtime_error_function function second) ->
    Permutation left right ->
    aggregate_local_runtime_error
      (AggregateCall function quantifier) left =
    aggregate_local_runtime_error
      (AggregateCall function quantifier) right.
Proof.
  intros function quantifier left right Hstable Hpermutation.
  cbn [aggregate_local_runtime_error].
  apply Hstable, aggregate_input_values_permutation, Hpermutation.
Qed.

(** A nonempty fold over an associative, commutative, idempotent operation
    depends only on input support.  In particular, repeating an arbitrary
    input block cannot change the result.  Idempotence is an explicit premise:
    this theorem is not available to SUM, AVG, COUNT, or any other
    multiplicity-sensitive aggregate. *)
Local Lemma fold_left_aci_seed :
  forall (A : Type) (operation : A -> A -> A),
    (forall first second third,
      operation (operation first second) third =
      operation first (operation second third)) ->
    forall values first second,
      fold_left operation values (operation first second) =
      operation first (fold_left operation values second).
Proof.
  intros A operation Hassociative values.
  induction values as [|value values IH]; intros first second; cbn.
  - reflexivity.
  - rewrite Hassociative; apply IH.
Qed.

Local Lemma fold_left_aci_member_absorbed :
  forall (A : Type) (operation : A -> A -> A),
    (forall left right, operation left right = operation right left) ->
    (forall first second third,
      operation (operation first second) third =
      operation first (operation second third)) ->
    (forall value, operation value value = value) ->
    forall values initial member,
      In member (initial :: values) ->
      operation member (fold_left operation values initial) =
      fold_left operation values initial.
Proof.
  intros A operation Hcommutative Hassociative Hidempotent values.
  induction values as [|value values IH];
    intros initial member Hmember; cbn in *.
  - destruct Hmember as [<-|[]]; apply Hidempotent.
  - rewrite
      (fold_left_aci_seed A operation Hassociative values initial value).
    destruct Hmember as [<-|Hmember].
    + rewrite <-
        (Hassociative initial initial
          (fold_left operation values value)).
      now rewrite Hidempotent.
    + rewrite <-
        (Hassociative member initial
          (fold_left operation values value)),
        (Hcommutative member initial),
        (Hassociative initial member
          (fold_left operation values value)),
        (IH value member Hmember).
      reflexivity.
Qed.

Local Lemma fold_left_absorbed_values :
  forall (A : Type) (operation : A -> A -> A) fixed values,
    (forall value, In value values -> operation fixed value = fixed) ->
    fold_left operation values fixed = fixed.
Proof.
  intros A operation fixed values Habsorbed.
  induction values as [|value values IH]; cbn; [reflexivity|].
  rewrite (Habsorbed value (or_introl eq_refl)).
  apply IH; intros current Hcurrent.
  apply Habsorbed; now right.
Qed.

Theorem fold_nonempty_support_equiv :
  forall (A : Type) (operation : A -> A -> A),
    (forall left right, operation left right = operation right left) ->
    (forall first second third,
      operation (operation first second) third =
      operation first (operation second third)) ->
    (forall value, operation value value = value) ->
    forall left right,
      (forall value, In value left <-> In value right) ->
      fold_nonempty operation left = fold_nonempty operation right.
Proof.
  intros A operation Hcommutative Hassociative Hidempotent
    left right Hsupport.
  unfold fold_nonempty.
  destruct left as [|left_head left_tail],
    right as [|right_head right_tail]; cbn.
  - reflexivity.
  - exfalso.
    specialize (proj2 (Hsupport right_head) (or_introl eq_refl)).
    contradiction.
  - exfalso.
    specialize (proj1 (Hsupport left_head) (or_introl eq_refl)).
    contradiction.
  - f_equal.
    set (left_result := fold_left operation left_tail left_head).
    set (right_result := fold_left operation right_tail right_head).
    assert (Hleft_right :
      operation left_result right_result = left_result).
    {
      subst right_result.
      rewrite <-
        (fold_left_aci_seed A operation Hassociative
          right_tail left_result right_head).
      assert (Hhead : operation left_result right_head = left_result).
      {
        rewrite (Hcommutative left_result right_head).
        unfold left_result.
        apply fold_left_aci_member_absorbed; try assumption.
        apply (proj2 (Hsupport right_head)); now left.
      }
      rewrite Hhead.
      apply fold_left_absorbed_values.
      intros current Hcurrent.
      rewrite (Hcommutative left_result current).
      unfold left_result.
      apply fold_left_aci_member_absorbed; try assumption.
      apply (proj2 (Hsupport current)); now right.
    }
    assert (Hright_left :
      operation right_result left_result = right_result).
    {
      subst left_result.
      rewrite <-
        (fold_left_aci_seed A operation Hassociative
          left_tail right_result left_head).
      assert (Hhead : operation right_result left_head = right_result).
      {
        rewrite (Hcommutative right_result left_head).
        unfold right_result.
        apply fold_left_aci_member_absorbed; try assumption.
        apply (proj1 (Hsupport left_head)); now left.
      }
      rewrite Hhead.
      apply fold_left_absorbed_values.
      intros current Hcurrent.
      rewrite (Hcommutative right_result current).
      unfold right_result.
      apply fold_left_aci_member_absorbed; try assumption.
      apply (proj1 (Hsupport current)); now right.
    }
    rewrite Hcommutative in Hright_left.
    congruence.
Qed.

Local Lemma forallb_support_equiv :
  forall (A : Type) (test : A -> bool) left right,
    (forall value, In value left <-> In value right) ->
    forallb test left = forallb test right.
Proof.
  intros A test left right Hsupport.
  destruct (forallb test left) eqn:Hleft,
    (forallb test right) eqn:Hright; try reflexivity.
  - rewrite forallb_forall in Hleft.
    assert (forallb test right = true) as Hcontradiction.
    {
      rewrite forallb_forall; intros value Hvalue.
      apply Hleft, (proj2 (Hsupport value)), Hvalue.
    }
    congruence.
  - rewrite forallb_forall in Hright.
    assert (forallb test left = true) as Hcontradiction.
    {
      rewrite forallb_forall; intros value Hvalue.
      apply Hright, (proj1 (Hsupport value)), Hvalue.
    }
    congruence.
Qed.

Local Lemma flat_map_support_equiv :
  forall (A B : Type) (project : A -> list B) left right,
    (forall value, In value left <-> In value right) ->
    forall projected,
      In projected (flat_map project left) <->
      In projected (flat_map project right).
Proof.
  intros A B project left right Hsupport projected.
  rewrite !in_flat_map.
  split; intros [value [Hvalue Hprojected]];
    exists value; split; try exact Hprojected.
  - now apply (proj1 (Hsupport value)).
  - now apply (proj2 (Hsupport value)).
Qed.

Local Lemma checked_flat_map_fold_nonempty_support_equiv :
  forall (A B : Type) (predicate : value -> bool)
    (project : value -> list A) (operation : A -> A -> A)
    (wrap : option A -> B) left right,
    (forall current, In current left <-> In current right) ->
    (forall first second, operation first second = operation second first) ->
    (forall first second third,
      operation (operation first second) third =
      operation first (operation second third)) ->
    (forall current, operation current current = current) ->
    (if forallb predicate left
     then wrap (fold_nonempty operation (flat_map project left))
     else wrap None) =
    (if forallb predicate right
     then wrap (fold_nonempty operation (flat_map project right))
     else wrap None).
Proof.
  intros A B predicate project operation wrap left right
    Hsupport Hcommutative Hassociative Hidempotent.
  rewrite (forallb_support_equiv value predicate left right Hsupport).
  destruct (forallb predicate right); [|reflexivity].
  f_equal.
  apply fold_nonempty_support_equiv; try assumption.
  now apply flat_map_support_equiv.
Qed.

(** PostgreSQL text MAX under the modeled UTF8/C collation is another exact
    semilattice extremum.  Keep its value extraction local to this boundary so
    the public interface remains phrased over aggregate calls and support. *)
Local Definition text_value_projection_for_extrema
    (input : value) : list string :=
  match input with
  | Value_string (StringText, Some text) => text :: nil
  | _ => nil
  end.

Local Lemma text_values_as_flat_map_for_extrema : forall values,
  text_values values = flat_map text_value_projection_for_extrema values.
Proof.
  induction values as [|value values IH]; cbn; [reflexivity|].
  destruct value; cbn; try exact IH.
  destruct s as [typmod payload].
  destruct typmod; destruct payload; cbn; try exact IH; now rewrite IH.
Qed.

Local Lemma text_c_max_is_ordered_maximum : forall left right,
  text_c_max left right = ordered_maximum Ostring left right.
Proof. reflexivity. Qed.

Local Lemma text_c_max_commutative : forall left right,
  text_c_max left right = text_c_max right left.
Proof.
  intros left right; rewrite !text_c_max_is_ordered_maximum.
  apply ordered_maximum_commutative.
Qed.

Local Lemma text_c_max_associative : forall first second third,
  text_c_max (text_c_max first second) third =
  text_c_max first (text_c_max second third).
Proof.
  intros first second third; rewrite !text_c_max_is_ordered_maximum.
  apply ordered_maximum_associative.
Qed.

Local Lemma text_c_max_idempotent : forall text,
  text_c_max text text = text.
Proof.
  intro text; rewrite text_c_max_is_ordered_maximum.
  unfold ordered_maximum; now rewrite Oset.compare_eq_refl.
Qed.

Local Lemma interp_max_string_support_equiv : forall left right,
  (forall value, In value left <-> In value right) ->
  interp_max_string left = interp_max_string right.
Proof.
  intros left right Hsupport.
  unfold interp_max_string; rewrite !text_values_as_flat_map_for_extrema.
  eapply
    (checked_flat_map_fold_nonempty_support_equiv
      string value is_text_value text_value_projection_for_extrema
      text_c_max
      (fun result => Value_string (StringValue StringText result))
      left right);
    try exact Hsupport.
  - apply text_c_max_commutative.
  - apply text_c_max_associative.
  - apply text_c_max_idempotent.
Qed.

Lemma exact_extrema_aggregate_permutation : forall function quantifier left right,
  (function = AggregateMinZ \/ function = AggregateMaxZ \/
   function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
   function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
   function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
   function = AggregateMaxString) ->
  Permutation left right ->
  interp_aggregate (AggregateCall function quantifier) left =
  interp_aggregate (AggregateCall function quantifier) right.
Proof.
  intros function quantifier left right Hfunction Hperm.
  eapply interp_aggregate_call_permutation_congr; [|exact Hperm].
  intros first second Hselected.
  repeat match type of Hfunction with
  | _ \/ _ => destruct Hfunction as [Hfunction | Hfunction]
  | function = _ => subst function
  end;
    cbn [interp_aggregate_function].
  all: first
    [ now apply interp_min_z_permutation
    | now apply interp_max_z_permutation
    | now apply interp_min_int32_permutation
    | now apply interp_max_int32_permutation
    | now apply interp_min_int64_permutation
    | now apply interp_max_int64_permutation
    | now apply interp_min_numeric_permutation
    | now apply interp_max_numeric_permutation
    | apply interp_max_string_support_equiv; intro value; split; intro Hin;
      [ eapply Permutation_in; [exact Hselected|exact Hin]
      | eapply Permutation_in;
        [apply Permutation_sym; exact Hselected|exact Hin] ] ].
Qed.

Local Lemma exact_extrema_function_support_equiv :
  forall function left right,
    (function = AggregateMinZ \/ function = AggregateMaxZ \/
     function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
     function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
     function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
     function = AggregateMaxString) ->
    (forall value, In value left <-> In value right) ->
    interp_aggregate_function function left =
    interp_aggregate_function function right.
Proof.
  intros function left right Hfunction Hsupport.
  repeat match type of Hfunction with
  | _ \/ _ => destruct Hfunction as [Hfunction | Hfunction]
  | function = _ => subst function
  end; cbn [interp_aggregate_function].
  - unfold interp_min_z; rewrite !z_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply Z.min_comm.
    + intros; symmetry; apply Z.min_assoc.
    + apply Z.min_id.
  - unfold interp_max_z; rewrite !z_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply Z.max_comm.
    + intros; symmetry; apply Z.max_assoc.
    + apply Z.max_id.
  - unfold interp_min_int32; rewrite !int32_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply int32_minimum_commutative.
    + apply int32_minimum_associative.
    + intro value; unfold int32_minimum; now rewrite Z.leb_refl.
  - unfold interp_max_int32; rewrite !int32_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply int32_maximum_commutative.
    + apply int32_maximum_associative.
    + intro value; unfold int32_maximum; now rewrite Z.leb_refl.
  - unfold interp_min_int64; rewrite !int64_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply int64_minimum_commutative.
    + apply int64_minimum_associative.
    + intro value; unfold int64_minimum; now rewrite Z.leb_refl.
  - unfold interp_max_int64; rewrite !int64_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply int64_maximum_commutative.
    + apply int64_maximum_associative.
    + intro value; unfold int64_maximum; now rewrite Z.leb_refl.
  - unfold interp_min_numeric; rewrite !numeric_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply numeric_min_commutative.
    + apply numeric_min_associative.
    + apply numeric_min_idempotent.
  - unfold interp_max_numeric; rewrite !numeric_values_as_flat_map.
    eapply checked_flat_map_fold_nonempty_support_equiv;
      try exact Hsupport.
    + apply numeric_max_commutative.
    + apply numeric_max_associative.
    + apply numeric_max_idempotent.
  - now apply interp_max_string_support_equiv.
Qed.

(** Exact integral, NUMERIC, and C-collated TEXT extrema are support-invariant
    for both ALL and DISTINCT.  The closed function list deliberately excludes
    every SUM and AVG, including FLOAT and DOUBLE SUM/AVG, whose transition
    operations are not idempotent and whose floating variants are not
    generally permutation invariant.  FLOAT/DOUBLE extrema are also
    fail-closed here because exact support invariance has not been established
    for their representation-level tie behavior. *)
Theorem exact_extrema_aggregate_support_equiv :
  forall function quantifier left right,
    (function = AggregateMinZ \/ function = AggregateMaxZ \/
     function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
     function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
     function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
     function = AggregateMaxString) ->
    (forall value, In value left <-> In value right) ->
    interp_aggregate (AggregateCall function quantifier) left =
    interp_aggregate (AggregateCall function quantifier) right.
Proof.
  intros function quantifier left right Hfunction Hsupport.
  cbn [interp_aggregate].
  apply exact_extrema_function_support_equiv; [exact Hfunction|].
  intro value; rewrite !aggregate_input_values_membership.
  apply Hsupport.
Qed.

Theorem exact_extrema_aggregate_duplicate_block :
  forall function quantifier prefix block suffix,
    (function = AggregateMinZ \/ function = AggregateMaxZ \/
     function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
     function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
     function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
     function = AggregateMaxString) ->
    interp_aggregate (AggregateCall function quantifier)
      (prefix ++ block ++ block ++ suffix) =
    interp_aggregate (AggregateCall function quantifier)
      (prefix ++ block ++ suffix).
Proof.
  intros function quantifier prefix block suffix Hfunction.
  apply exact_extrema_aggregate_support_equiv; [exact Hfunction|].
  intro value; repeat rewrite in_app_iff; tauto.
Qed.

Lemma first_runtime_error_duplicate_block :
  forall (A : Type) (check : A -> option sql_runtime_error)
    prefix block suffix,
    first_runtime_error check (prefix ++ block ++ block ++ suffix) =
    first_runtime_error check (prefix ++ block ++ suffix).
Proof.
  intros A check prefix block suffix.
  repeat rewrite first_runtime_error_app.
  destruct (first_runtime_error check block); reflexivity.
Qed.

Lemma first_observation_error_duplicate_block :
  forall prefix block suffix,
    first_observation_error (prefix ++ block ++ block ++ suffix) =
    first_observation_error (prefix ++ block ++ suffix).
Proof.
  intros prefix block suffix.
  rewrite !first_observation_error_as_first_runtime_error.
  apply first_runtime_error_duplicate_block.
Qed.

(** Arbitrary support equivalence is intentionally insufficient for this
    runtime theorem: support does not record which child error is reached
    first.  Repeating the same reached block preserves that left-biased error,
    and exact extrema have no aggregate-local error branch. *)
Theorem exact_extrema_aggregate_runtime_error_duplicate_block :
  forall function quantifier prefix block suffix,
    (function = AggregateMinZ \/ function = AggregateMaxZ \/
     function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
     function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
     function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
     function = AggregateMaxString) ->
    interp_aggregate_runtime_error (AggregateCall function quantifier)
      (prefix ++ block ++ block ++ suffix) =
    interp_aggregate_runtime_error (AggregateCall function quantifier)
      (prefix ++ block ++ suffix).
Proof.
  intros function quantifier prefix block suffix Hfunction.
  unfold interp_aggregate_runtime_error.
  rewrite first_observation_error_duplicate_block.
  destruct
    (first_observation_error (prefix ++ block ++ suffix));
    [reflexivity|].
  repeat match type of Hfunction with
  | _ \/ _ => destruct Hfunction as [Hfunction | Hfunction]
  | function = _ => subst function
  end; reflexivity.
Qed.

Lemma aggregate_input_values_preserves_all_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  Forall (fun value => is_null_value value = true)
    (aggregate_input_values quantifier values).
Proof.
  intros [|] values Hnulls; cbn; [exact Hnulls|].
  rewrite Forall_forall in Hnulls |- *.
  intros value Hin; apply Hnulls.
  exact (proj1 (distinct_values_membership value values) Hin).
Qed.

Definition aggregate_filter_input
    (predicate : value -> bool)
    (quantifier : aggregate_quantifier)
    (values : list value) : list value :=
  aggregate_input_values quantifier (filter predicate values).

Lemma aggregate_filter_input_membership :
  forall predicate quantifier value values,
    In value (aggregate_filter_input predicate quantifier values) <->
    In value values /\ predicate value = true.
Proof.
  intros predicate quantifier value values.
  unfold aggregate_filter_input.
  rewrite aggregate_input_values_membership, filter_In.
  reflexivity.
Qed.

Lemma aggregate_filter_input_distinct_nodup : forall predicate values,
  NoDup (aggregate_filter_input predicate AggregateDistinct values).
Proof.
  intros predicate values; unfold aggregate_filter_input.
  apply distinct_values_nodup.
Qed.

Lemma aggregate_filter_input_length_le :
  forall predicate quantifier values,
    (List.length (aggregate_filter_input predicate quantifier values) <=
     List.length values)%nat.
Proof.
  intros predicate quantifier values; unfold aggregate_filter_input.
  eapply Nat.le_trans.
  - apply aggregate_input_values_length_le.
  - pose proof (filter_length predicate values); lia.
Qed.

Lemma aggregate_filter_input_false_empty : forall quantifier values,
  aggregate_filter_input (fun _ => false) quantifier values = [].
Proof.
  intros quantifier values; unfold aggregate_filter_input.
  assert (filter (fun _ : value => false) values = []) as Hfilter.
  {
    induction values as [|value values IH]; cbn; [reflexivity|exact IH].
  }
  rewrite Hfilter; destruct quantifier; reflexivity.
Qed.

(** COUNT value witnesses retain the exact mathematical cardinality; the
    range premise is also exactly the local runtime-safety obligation above. *)

Lemma count_star_value_of_row_count_range : forall values,
  int64_min <= row_count values <= int64_max ->
  exists result,
    interp_aggregate AggregateCountStar values =
      Value_int64 (Some result) /\
    int64_value result = row_count values.
Proof.
  intros values Hrange.
  apply (proj2 (int64_checked_defined_iff (row_count values))) in Hrange.
  destruct Hrange as [result Hresult].
  exists result; split.
  - change (value_int64_checked (row_count values) =
      Value_int64 (Some result)).
    unfold value_int64_checked; now rewrite Hresult.
  - now apply int64_checked_result_value in Hresult.
Qed.

Lemma count_value_of_non_null_count_range : forall quantifier values,
  int64_min <=
    non_null_count (aggregate_input_values quantifier values) <= int64_max ->
  exists result,
    interp_aggregate
      (AggregateCall AggregateCount quantifier) values =
      Value_int64 (Some result) /\
    int64_value result =
      non_null_count (aggregate_input_values quantifier values).
Proof.
  intros quantifier values Hrange.
  apply (proj2 (int64_checked_defined_iff
    (non_null_count (aggregate_input_values quantifier values)))) in Hrange.
  destruct Hrange as [result Hresult].
  exists result; split.
  - change
      (value_int64_checked
        (non_null_count (aggregate_input_values quantifier values)) =
       Value_int64 (Some result)).
    unfold value_int64_checked; now rewrite Hresult.
  - now apply int64_checked_result_value in Hresult.
Qed.

(** Successful SUM over a nonempty, well-typed, non-NULL input cannot produce
    SQL NULL.  The int32 variant needs the explicit runtime-safety premise
    because PostgreSQL reports bigint overflow instead of returning a value;
    unconstrained NUMERIC retains a non-NULL mathematical value and reports
    any range error through the separate runtime channel. *)
Lemma int32_values_nonempty_of_typed_nonnull : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_int32_value value = true /\ is_null_value value = false)
    values ->
  int32_values values <> [].
Proof.
  intros [|value values] Hnonempty Hvalues; [contradiction|].
  inversion Hvalues as [|? ? [Htyped Hnonnull] ?]; subst.
  destruct value; cbn in Htyped; try discriminate.
  destruct o; cbn in Hnonnull |- *; discriminate.
Qed.

Lemma numeric_values_nonempty_of_typed_nonnull : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_numeric_value value = true /\ is_null_value value = false)
    values ->
  numeric_values values <> [].
Proof.
  intros [|value values] Hnonempty Hvalues; [contradiction|].
  inversion Hvalues as [|? ? [Htyped Hnonnull] ?]; subst.
  destruct value; cbn in Htyped; try discriminate.
  destruct o; cbn in Hnonnull |- *; discriminate.
Qed.

Lemma interp_sum_int32_nonnull_of_nonempty_runtime_safe : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_int32_value value = true /\ is_null_value value = false)
    values ->
  sum_int32_runtime_error values = None ->
  is_null_value (interp_sum_int32_as_int64 values) = false.
Proof.
  intros values Hnonempty Hvalues Hsafe.
  assert (Htyped : forallb is_int32_value values = true).
  {
    apply forallb_forall; intros value Hvalue.
    rewrite Forall_forall in Hvalues.
    exact (proj1 (Hvalues value Hvalue)).
  }
  pose proof
    (int32_values_nonempty_of_typed_nonnull values Hnonempty Hvalues)
    as Hintegers.
  unfold interp_sum_int32_as_int64, sum_int32_runtime_error in *.
  rewrite Htyped in *.
  destruct (int32_values values) as [|integer integers] eqn:Hselected;
    [contradiction|].
  unfold int64_result_runtime_error, value_int64_checked in *.
  destruct
    (int64_checked
      (fold_left
        (fun accumulator next => accumulator + int32_value next)
        (integer :: integers) 0)) eqn:Hresult;
    [reflexivity|discriminate].
Qed.

Lemma interp_sum_numeric_nonnull_of_nonempty : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_numeric_value value = true /\ is_null_value value = false)
    values ->
  is_null_value (interp_sum_numeric values) = false.
Proof.
  intros values Hnonempty Hvalues.
  assert (Htyped : forallb is_numeric_value values = true).
  {
    apply forallb_forall; intros value Hvalue.
    rewrite Forall_forall in Hvalues.
    exact (proj1 (Hvalues value Hvalue)).
  }
  pose proof
    (numeric_values_nonempty_of_typed_nonnull values Hnonempty Hvalues)
    as Hnumbers.
  unfold interp_sum_numeric.
  rewrite Htyped.
  destruct (numeric_values values) as [|number numbers] eqn:Hselected;
    [contradiction|].
  remember
    (fold_left numeric_sum_transition (number :: numbers)
      numeric_sum_initial) as state.
  assert (Hcount :
    numeric_sum_total_count state = Z.of_nat (S (List.length numbers))).
  {
    subst state.
    rewrite numeric_sum_fold_total_count_exact.
    reflexivity.
  }
  unfold numeric_sum_from_state.
  rewrite Hcount.
  destruct (Z.eqb (Z.of_nat (S (List.length numbers))) 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; lia.
  - destruct
      (numeric_agg_special_result
        (numeric_sum_nan_count state)
        (numeric_sum_pos_inf_count state)
        (numeric_sum_neg_inf_count state)); reflexivity.
Qed.

Lemma aggregate_sum_int32_nonnull_of_nonempty_runtime_safe :
  forall quantifier values,
    values <> [] ->
    Forall
      (fun value =>
        is_int32_value value = true /\ is_null_value value = false)
      values ->
    aggregate_local_runtime_error
      (AggregateCall AggregateSumInt32 quantifier) values = None ->
    is_null_value
      (interp_aggregate
        (AggregateCall AggregateSumInt32 quantifier) values) = false.
Proof.
  intros quantifier values Hnonempty Hvalues Hsafe.
  apply interp_sum_int32_nonnull_of_nonempty_runtime_safe.
  - apply (proj2 (aggregate_input_values_nonempty_iff quantifier values)).
    exact Hnonempty.
  - now apply aggregate_input_values_preserves_Forall.
  - exact Hsafe.
Qed.

Lemma aggregate_sum_numeric_nonnull_of_nonempty : forall quantifier values,
  values <> [] ->
  Forall
    (fun value =>
      is_numeric_value value = true /\ is_null_value value = false)
    values ->
  is_null_value
    (interp_aggregate
      (AggregateCall AggregateSumNumeric quantifier) values) = false.
Proof.
  intros quantifier values Hnonempty Hvalues.
  apply interp_sum_numeric_nonnull_of_nonempty.
  - apply (proj2 (aggregate_input_values_nonempty_iff quantifier values)).
    exact Hnonempty.
  - now apply aggregate_input_values_preserves_Forall.
Qed.

(** Empty and all-NULL aggregate results. *)

Lemma count_star_empty_success :
  exists zero,
    interp_aggregate AggregateCountStar [] = Value_int64 (Some zero) /\
    int64_value zero = 0.
Proof.
  assert (int64_min <= 0 <= int64_max) as Hrange.
  { unfold int64_min, int64_max; lia. }
  apply int64_checked_defined_iff in Hrange.
  destruct Hrange as [zero Hzero].
  exists zero; split.
  - change (value_int64_checked 0 = Value_int64 (Some zero)).
    unfold value_int64_checked; now rewrite Hzero.
  - now apply int64_checked_result_value in Hzero.
Qed.

Lemma count_empty_success : forall quantifier,
  exists zero,
    interp_aggregate (AggregateCall AggregateCount quantifier) [] =
      Value_int64 (Some zero) /\
    int64_value zero = 0.
Proof.
  intro quantifier.
  assert (int64_min <= 0 <= int64_max) as Hrange.
  { unfold int64_min, int64_max; lia. }
  apply int64_checked_defined_iff in Hrange.
  destruct Hrange as [zero Hzero].
  exists zero; split.
  - destruct quantifier;
      change (value_int64_checked 0 = Value_int64 (Some zero));
      unfold value_int64_checked; now rewrite Hzero.
  - now apply int64_checked_result_value in Hzero.
Qed.

Lemma count_all_null_success : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  exists zero,
    interp_aggregate (AggregateCall AggregateCount quantifier) values =
      Value_int64 (Some zero) /\
    int64_value zero = 0.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_non_null_count_zero in Hselected.
  assert (int64_min <= 0 <= int64_max) as Hrange.
  { unfold int64_min, int64_max; lia. }
  apply int64_checked_defined_iff in Hrange.
  destruct Hrange as [zero Hzero].
  exists zero; split.
  - change
      (value_int64_checked
        (non_null_count (aggregate_input_values quantifier values)) =
       Value_int64 (Some zero)).
    rewrite Hselected; unfold value_int64_checked; now rewrite Hzero.
  - now apply int64_checked_result_value in Hzero.
Qed.

Lemma all_null_numeric_projections_empty : forall values,
  Forall (fun value => is_null_value value = true) values ->
  int32_values values = [] /\
  int64_values values = [] /\
  numeric_values values = [].
Proof.
  intros values Hnulls; split.
  - induction Hnulls as [|value values Hvalue Hvalues IH]; cbn;
      [reflexivity|].
    destruct value; cbn; try exact IH.
    destruct o; cbn in Hvalue; [discriminate|exact IH].
  - split.
    + induction Hnulls as [|value values Hvalue Hvalues IH]; cbn;
        [reflexivity|].
      destruct value; cbn; try exact IH.
      destruct o; cbn in Hvalue; [discriminate|exact IH].
    + induction Hnulls as [|value values Hvalue Hvalues IH]; cbn;
        [reflexivity|].
      destruct value; cbn; try exact IH.
      destruct o; cbn in Hvalue; [discriminate|exact IH].
Qed.

Lemma all_null_float_string_projections_empty : forall values,
  Forall (fun value => is_null_value value = true) values ->
  float_values values = [] /\
  double_values values = [] /\
  text_values values = [].
Proof.
  intros values Hnulls; split.
  - induction Hnulls as [|value values Hvalue Hvalues IH]; cbn;
      [reflexivity|].
    destruct value; cbn; try exact IH.
    destruct o; cbn in Hvalue; [discriminate|exact IH].
  - split.
    + induction Hnulls as [|value values Hvalue Hvalues IH]; cbn;
        [reflexivity|].
      destruct value; cbn; try exact IH.
      destruct o; cbn in Hvalue; [discriminate|exact IH].
    + induction Hnulls as [|value values Hvalue Hvalues IH]; cbn;
        [reflexivity|].
      destruct value; cbn; try exact IH.
      destruct s as [typmod payload].
      destruct typmod; destruct payload; cbn in Hvalue |- *;
        try exact IH; discriminate.
Qed.

Lemma sum_int32_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumInt32 quantifier) [] =
  Value_int64 None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma sum_int64_numeric_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumInt64Numeric quantifier) [] =
  Value_numeric None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma sum_numeric_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumNumeric quantifier) [] =
  Value_numeric None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma sum_int32_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumInt32 quantifier) values =
  Value_int64 None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_numeric_projections_empty in Hselected.
  destruct Hselected as [Hint32 _].
  change
    (interp_sum_int32_as_int64
      (aggregate_input_values quantifier values) = Value_int64 None).
  unfold interp_sum_int32_as_int64.
  destruct (forallb is_int32_value (aggregate_input_values quantifier values));
    [now rewrite Hint32|reflexivity].
Qed.

Lemma sum_int64_numeric_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate
    (AggregateCall AggregateSumInt64Numeric quantifier) values =
  Value_numeric None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_numeric_projections_empty in Hselected.
  destruct Hselected as [_ [Hint64 _]].
  change
    (interp_sum_int64_as_numeric
      (aggregate_input_values quantifier values) = Value_numeric None).
  unfold interp_sum_int64_as_numeric.
  destruct (forallb is_int64_value (aggregate_input_values quantifier values));
    [now rewrite Hint64|reflexivity].
Qed.

Lemma sum_numeric_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumNumeric quantifier) values =
  Value_numeric None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_numeric_projections_empty in Hselected.
  destruct Hselected as [_ [_ Hnumeric]].
  change
    (interp_sum_numeric (aggregate_input_values quantifier values) =
     Value_numeric None).
  unfold interp_sum_numeric.
  destruct (forallb is_numeric_value (aggregate_input_values quantifier values));
    [now rewrite Hnumeric|reflexivity].
Qed.

Lemma sum_float_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumFloat quantifier) [] =
  Value_float None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma sum_double_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumDouble quantifier) [] =
  Value_double None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma sum_float_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumFloat quantifier) values =
  Value_float None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_float_string_projections_empty in Hselected.
  destruct Hselected as [Hfloat _].
  change
    (interp_sum_float (aggregate_input_values quantifier values) =
     Value_float None).
  unfold interp_sum_float.
  destruct (forallb is_float_value (aggregate_input_values quantifier values));
    [now rewrite Hfloat|reflexivity].
Qed.

Lemma sum_double_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumDouble quantifier) values =
  Value_double None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_float_string_projections_empty in Hselected.
  destruct Hselected as [_ [Hdouble _]].
  change
    (interp_sum_double (aggregate_input_values quantifier values) =
     Value_double None).
  unfold interp_sum_double.
  destruct (forallb is_double_value (aggregate_input_values quantifier values));
    [now rewrite Hdouble|reflexivity].
Qed.

Lemma min_max_int32_empty_is_null : forall function quantifier,
  (function = AggregateMinInt32 \/ function = AggregateMaxInt32) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_int32 None.
Proof.
  intros function quantifier [-> | ->]; destruct quantifier; reflexivity.
Qed.

Lemma min_max_numeric_empty_is_null : forall function quantifier,
  (function = AggregateMinNumeric \/ function = AggregateMaxNumeric) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_numeric None.
Proof.
  intros function quantifier [-> | ->]; destruct quantifier; reflexivity.
Qed.

Lemma min_max_int32_all_null_is_null : forall function quantifier values,
  (function = AggregateMinInt32 \/ function = AggregateMaxInt32) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_int32 None.
Proof.
  intros function quantifier values [-> | ->] Hnulls;
    pose proof (aggregate_input_values_preserves_all_null
      quantifier values Hnulls) as Hselected;
    apply all_null_numeric_projections_empty in Hselected;
    destruct Hselected as [Hint32 _].
  - change
      (interp_min_int32 (aggregate_input_values quantifier values) =
       Value_int32 None).
    unfold interp_min_int32.
    destruct (forallb is_int32_value (aggregate_input_values quantifier values));
      [now rewrite Hint32|reflexivity].
  - change
      (interp_max_int32 (aggregate_input_values quantifier values) =
       Value_int32 None).
    unfold interp_max_int32.
    destruct (forallb is_int32_value (aggregate_input_values quantifier values));
      [now rewrite Hint32|reflexivity].
Qed.

Lemma min_max_numeric_all_null_is_null : forall function quantifier values,
  (function = AggregateMinNumeric \/ function = AggregateMaxNumeric) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_numeric None.
Proof.
  intros function quantifier values [-> | ->] Hnulls;
    pose proof (aggregate_input_values_preserves_all_null
      quantifier values Hnulls) as Hselected;
    apply all_null_numeric_projections_empty in Hselected;
    destruct Hselected as [_ [_ Hnumeric]].
  - change
      (interp_min_numeric (aggregate_input_values quantifier values) =
       Value_numeric None).
    unfold interp_min_numeric.
    destruct (forallb is_numeric_value (aggregate_input_values quantifier values));
      [now rewrite Hnumeric|reflexivity].
  - change
      (interp_max_numeric (aggregate_input_values quantifier values) =
       Value_numeric None).
    unfold interp_max_numeric.
    destruct (forallb is_numeric_value (aggregate_input_values quantifier values));
      [now rewrite Hnumeric|reflexivity].
Qed.

Lemma min_max_int64_empty_is_null : forall function quantifier,
  (function = AggregateMinInt64 \/ function = AggregateMaxInt64) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_int64 None.
Proof.
  intros function quantifier [-> | ->]; destruct quantifier; reflexivity.
Qed.

Lemma min_max_float_empty_is_null : forall function quantifier,
  (function = AggregateMinFloat \/ function = AggregateMaxFloat) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_float None.
Proof.
  intros function quantifier [-> | ->]; destruct quantifier; reflexivity.
Qed.

Lemma min_max_double_empty_is_null : forall function quantifier,
  (function = AggregateMinDouble \/ function = AggregateMaxDouble) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_double None.
Proof.
  intros function quantifier [-> | ->]; destruct quantifier; reflexivity.
Qed.

Lemma max_string_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateMaxString quantifier) [] =
  Value_string (StringValue StringText None).
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma min_max_int64_all_null_is_null : forall function quantifier values,
  (function = AggregateMinInt64 \/ function = AggregateMaxInt64) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_int64 None.
Proof.
  intros function quantifier values [-> | ->] Hnulls;
    pose proof (aggregate_input_values_preserves_all_null
      quantifier values Hnulls) as Hselected;
    apply all_null_numeric_projections_empty in Hselected;
    destruct Hselected as [_ [Hint64 _]].
  - change
      (interp_min_int64 (aggregate_input_values quantifier values) =
       Value_int64 None).
    unfold interp_min_int64.
    destruct (forallb is_int64_value (aggregate_input_values quantifier values));
      [now rewrite Hint64|reflexivity].
  - change
      (interp_max_int64 (aggregate_input_values quantifier values) =
       Value_int64 None).
    unfold interp_max_int64.
    destruct (forallb is_int64_value (aggregate_input_values quantifier values));
      [now rewrite Hint64|reflexivity].
Qed.

Lemma min_max_float_all_null_is_null : forall function quantifier values,
  (function = AggregateMinFloat \/ function = AggregateMaxFloat) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_float None.
Proof.
  intros function quantifier values [-> | ->] Hnulls;
    pose proof (aggregate_input_values_preserves_all_null
      quantifier values Hnulls) as Hselected;
    apply all_null_float_string_projections_empty in Hselected;
    destruct Hselected as [Hfloat _].
  - change
      (interp_min_float (aggregate_input_values quantifier values) =
       Value_float None).
    unfold interp_min_float.
    destruct (forallb is_float_value (aggregate_input_values quantifier values));
      [now rewrite Hfloat|reflexivity].
  - change
      (interp_max_float (aggregate_input_values quantifier values) =
       Value_float None).
    unfold interp_max_float.
    destruct (forallb is_float_value (aggregate_input_values quantifier values));
      [now rewrite Hfloat|reflexivity].
Qed.

Lemma min_max_double_all_null_is_null : forall function quantifier values,
  (function = AggregateMinDouble \/ function = AggregateMaxDouble) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_double None.
Proof.
  intros function quantifier values [-> | ->] Hnulls;
    pose proof (aggregate_input_values_preserves_all_null
      quantifier values Hnulls) as Hselected;
    apply all_null_float_string_projections_empty in Hselected;
    destruct Hselected as [_ [Hdouble _]].
  - change
      (interp_min_double (aggregate_input_values quantifier values) =
       Value_double None).
    unfold interp_min_double.
    destruct (forallb is_double_value (aggregate_input_values quantifier values));
      [now rewrite Hdouble|reflexivity].
  - change
      (interp_max_double (aggregate_input_values quantifier values) =
       Value_double None).
    unfold interp_max_double.
    destruct (forallb is_double_value (aggregate_input_values quantifier values));
      [now rewrite Hdouble|reflexivity].
Qed.

Lemma max_string_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateMaxString quantifier) values =
  Value_string (StringValue StringText None).
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_float_string_projections_empty in Hselected.
  destruct Hselected as [_ [_ Htext]].
  change
    (interp_max_string (aggregate_input_values quantifier values) =
     Value_string (StringValue StringText None)).
  unfold interp_max_string.
  destruct (forallb is_text_value (aggregate_input_values quantifier values));
    [now rewrite Htext|reflexivity].
Qed.

Lemma avg_integral_empty_is_null : forall function quantifier,
  (function = AggregateAverageInt32Numeric \/
   function = AggregateAverageInt64Numeric) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_numeric None.
Proof.
  intros function quantifier [-> | ->]; destruct quantifier; reflexivity.
Qed.

Lemma avg_integral_all_null_is_null : forall function quantifier values,
  (function = AggregateAverageInt32Numeric \/
   function = AggregateAverageInt64Numeric) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_numeric None.
Proof.
  intros function quantifier values [-> | ->] Hnulls;
    pose proof (aggregate_input_values_preserves_all_null
      quantifier values Hnulls) as Hselected;
    apply all_null_numeric_projections_empty in Hselected.
  - destruct Hselected as [Hint32 _].
    change
      (interp_avg_int32_as_numeric
        (aggregate_input_values quantifier values) = Value_numeric None).
    unfold interp_avg_int32_as_numeric.
    destruct (forallb is_int32_value (aggregate_input_values quantifier values));
      [now rewrite Hint32|reflexivity].
  - destruct Hselected as [_ [Hint64 _]].
    change
      (interp_avg_int64_as_numeric
        (aggregate_input_values quantifier values) = Value_numeric None).
    unfold interp_avg_int64_as_numeric.
    destruct (forallb is_int64_value (aggregate_input_values quantifier values));
      [now rewrite Hint64|reflexivity].
Qed.

Lemma avg_float_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateAverageFloat quantifier) [] =
  Value_double None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma avg_double_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateAverageDouble quantifier) [] =
  Value_double None.
Proof. intro quantifier; destruct quantifier; reflexivity. Qed.

Lemma avg_float_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateAverageFloat quantifier) values =
  Value_double None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_float_string_projections_empty in Hselected.
  destruct Hselected as [Hfloat _].
  change
    (interp_avg_float (aggregate_input_values quantifier values) =
     Value_double None).
  unfold interp_avg_float.
  destruct (forallb is_float_value (aggregate_input_values quantifier values));
    [rewrite Hfloat; reflexivity|reflexivity].
Qed.

Lemma avg_double_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateAverageDouble quantifier) values =
  Value_double None.
Proof.
  intros quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_float_string_projections_empty in Hselected.
  destruct Hselected as [_ [Hdouble _]].
  change
    (interp_avg_double (aggregate_input_values quantifier values) =
     Value_double None).
  unfold interp_avg_double.
  destruct (forallb is_double_value (aggregate_input_values quantifier values));
    [now rewrite Hdouble|reflexivity].
Qed.

Lemma avg_numeric_fixed_empty_is_null : forall precision scale quantifier,
  interp_aggregate
    (AggregateCall (AggregateAverageNumericFixed precision scale) quantifier)
    [] = Value_numeric None.
Proof.
  intros precision scale quantifier; destruct quantifier;
    cbn [interp_aggregate interp_aggregate_function aggregate_input_values].
  all: unfold interp_avg_numeric_fixed; cbn.
  all: destruct (numeric_typmod_valid_bool precision scale); reflexivity.
Qed.

Lemma avg_numeric_fixed_all_null_is_null :
  forall precision scale quantifier values,
    Forall (fun value => is_null_value value = true) values ->
    interp_aggregate
      (AggregateCall
        (AggregateAverageNumericFixed precision scale) quantifier) values =
    Value_numeric None.
Proof.
  intros precision scale quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_numeric_projections_empty in Hselected.
  destruct Hselected as [_ [_ Hnumeric]].
  change
    (interp_avg_numeric_fixed precision scale
      (aggregate_input_values quantifier values) = Value_numeric None).
  unfold interp_avg_numeric_fixed.
  destruct
    (numeric_typmod_valid_bool precision scale &&
      forallb is_numeric_value (aggregate_input_values quantifier values));
    [rewrite Hnumeric; reflexivity|reflexivity].
Qed.

Lemma avg_numeric_at_scale_empty_is_null : forall scale quantifier,
  interp_aggregate
    (AggregateCall (AggregateAverageNumericAtScale scale) quantifier) [] =
    Value_numeric None.
Proof.
  intros scale quantifier; destruct quantifier;
    cbn [interp_aggregate interp_aggregate_function aggregate_input_values].
  all: unfold interp_avg_numeric_at_scale; cbn.
  all: destruct (numeric_display_scale_valid_bool scale); reflexivity.
Qed.

Lemma avg_numeric_at_scale_all_null_is_null : forall scale quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate
    (AggregateCall (AggregateAverageNumericAtScale scale) quantifier) values =
  Value_numeric None.
Proof.
  intros scale quantifier values Hnulls.
  pose proof (aggregate_input_values_preserves_all_null
    quantifier values Hnulls) as Hselected.
  apply all_null_numeric_projections_empty in Hselected.
  destruct Hselected as [_ [_ Hnumeric]].
  change
    (interp_avg_numeric_at_scale scale
      (aggregate_input_values quantifier values) = Value_numeric None).
  unfold interp_avg_numeric_at_scale.
  destruct
    (numeric_display_scale_valid_bool scale &&
      forallb is_numeric_value (aggregate_input_values quantifier values));
    [rewrite Hnumeric; reflexivity|reflexivity].
Qed.

(** SINGLE_VALUE is the aggregate boundary used for scalar-subquery
    cardinality.  DISTINCT is applied before this local cardinality check. *)

Lemma single_value_int32_runtime_error_none_iff : forall values,
  single_value_int32_runtime_error values = None <->
  (List.length values <= 1)%nat.
Proof.
  intros [|first [|second rest]]; cbn.
  - split; [intro; lia|intro; reflexivity].
  - split; [intro; lia|intro; reflexivity].
  - split; [discriminate|lia].
Qed.

Lemma single_value_int32_runtime_error_cardinality_iff : forall values,
  single_value_int32_runtime_error values = Some CardinalityViolation <->
  (2 <= List.length values)%nat.
Proof.
  intros [|first [|second rest]]; cbn.
  - split; [discriminate|lia].
  - split; [discriminate|lia].
  - split; [intro; lia|intro; reflexivity].
Qed.

Lemma aggregate_single_value_int32_selected_empty :
  forall quantifier values,
    aggregate_input_values quantifier values = [] ->
    interp_aggregate
      (AggregateCall AggregateSingleValueInt32 quantifier) values =
      Value_int32 None /\
    aggregate_local_runtime_error
      (AggregateCall AggregateSingleValueInt32 quantifier) values = None.
Proof.
  intros quantifier values Hselected; split;
    cbn [interp_aggregate aggregate_local_runtime_error];
    now rewrite Hselected.
Qed.

Lemma aggregate_single_value_int32_selected_singleton :
  forall quantifier values integer,
    aggregate_input_values quantifier values =
      [Value_int32 integer] ->
    interp_aggregate
      (AggregateCall AggregateSingleValueInt32 quantifier) values =
      Value_int32 integer /\
    aggregate_local_runtime_error
      (AggregateCall AggregateSingleValueInt32 quantifier) values = None.
Proof.
  intros quantifier values integer Hselected; split;
    cbn [interp_aggregate aggregate_local_runtime_error];
    now rewrite Hselected.
Qed.

Lemma aggregate_single_value_int32_cardinality_violation_iff :
  forall quantifier values,
    aggregate_local_runtime_error
      (AggregateCall AggregateSingleValueInt32 quantifier) values =
      Some CardinalityViolation <->
    (2 <= List.length
      (aggregate_input_values quantifier values))%nat.
Proof.
  intros quantifier values.
  cbn [aggregate_local_runtime_error].
  apply single_value_int32_runtime_error_cardinality_iff.
Qed.

(** Empty-input grouping distinguishes a global aggregate (one empty group)
    from GROUP BY with at least one key (no groups). *)

Lemma query_make_groups_empty_shape :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms,
    @query_make_groups T env [] group_terms =
    match group_terms with
    | [] => [[]]
    | _ :: _ => []
    end.
Proof.
  intros T env [|group_term group_terms]; reflexivity.
Qed.

(** GROUPING SETS consumes one child bag and combines successful branches
    with UNION ALL.  These structural inversion lemmas expose the exact
    head-before-tail error behavior without unfolding the mutual evaluator. *)

Section GroupingSetsOutcomeFacts.

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

Local Definition grouping_bag :=
  Febag.bag (Fecol.CBag (Tuple.CTuple T)).

Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_grouping_sets_bag :=
  (@eval_grouping_sets_bag_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null).

Lemma eval_grouping_sets_nil_outcome_iff : forall env input_bag outcome,
  eval_grouping_sets_bag env [] input_bag outcome <->
  outcome =
    SqlSuccess (Febag.empty (Fecol.CBag (Tuple.CTuple T))).
Proof.
  intros env input_bag outcome; split.
  - intro Heval; inversion Heval; reflexivity.
  - intro Houtcome; subst outcome; constructor.
Qed.

Lemma eval_grouping_sets_cons_success_iff :
  forall env select_list group_terms grouping_sets input_bag output_bag,
    eval_grouping_sets_bag env
      ((select_list, group_terms) :: grouping_sets) input_bag
      (SqlSuccess output_bag) <->
    exists head_bag tail_bag,
      eval_group_bag env select_list group_terms FExpr_True input_bag
        (SqlSuccess head_bag) /\
      eval_grouping_sets_bag env grouping_sets input_bag
        (SqlSuccess tail_bag) /\
      output_bag = query_set_bag Union head_bag tail_bag.
Proof.
  intros env select_list group_terms grouping_sets input_bag output_bag; split.
  - intro Heval; inversion Heval; subst; eauto 6.
  - intros [head_bag [tail_bag [Hhead [Htail ->]]]].
    now apply EGroupingSets_ConsSuccess.
Qed.

Lemma eval_grouping_sets_cons_error_iff :
  forall env select_list group_terms grouping_sets input_bag error,
    eval_grouping_sets_bag env
      ((select_list, group_terms) :: grouping_sets) input_bag
      (SqlError error) <->
    eval_group_bag env select_list group_terms FExpr_True input_bag
      (SqlError error) \/
    exists head_bag,
      eval_group_bag env select_list group_terms FExpr_True input_bag
        (SqlSuccess head_bag) /\
      eval_grouping_sets_bag env grouping_sets input_bag (SqlError error).
Proof.
  intros env select_list group_terms grouping_sets input_bag error; split.
  - intro Heval; inversion Heval; subst; eauto 6.
  - intros [Hhead | [head_bag [Hhead Htail]]].
    + now apply EGroupingSets_HeadError.
    + eapply EGroupingSets_TailError; eassumption.
Qed.

(** One grouping-set branch observed at an exact successful bag. *)
Definition grouping_set_success_at
    (env : Env.env T) (input_bag : grouping_bag)
    (spec : @query_grouping_set T)
    (output_bag : grouping_bag) : Prop :=
  let '(select_list, group_terms) := spec in
  eval_group_bag env select_list group_terms FExpr_True input_bag
    (SqlSuccess output_bag).

(** One grouping-set branch observed at an exact runtime-error category. *)
Definition grouping_set_error_at
    (env : Env.env T) (input_bag : grouping_bag)
    (spec : @query_grouping_set T)
    (error : sql_runtime_error) : Prop :=
  let '(select_list, group_terms) := spec in
  eval_group_bag env select_list group_terms FExpr_True input_bag
    (SqlError error).

(** Exact branch outcome agreement.  Keeping the output bag literal here is
    what lets the scheduler congruence preserve both UNION ALL multiplicities
    and the original left-to-right error schedule. *)
Definition grouping_set_exact_outcome_at
    (env : Env.env T) (input_bag : grouping_bag)
    (left right : @query_grouping_set T) : Prop :=
  forall outcome,
    let '(left_select, left_terms) := left in
    let '(right_select, right_terms) := right in
    (eval_group_bag env left_select left_terms FExpr_True input_bag outcome <->
     eval_group_bag env right_select right_terms FExpr_True input_bag outcome).

(** Branchwise exact agreement lifts through an arbitrary grouping-set list.
    The [Forall2] order is significant: the proof never permutes branches and
    hence cannot move an error past an earlier successful or failing branch. *)
Theorem eval_grouping_sets_outcome_Forall2_congr :
  forall env input_bag left_sets right_sets,
    Forall2 (grouping_set_exact_outcome_at env input_bag)
      left_sets right_sets ->
    forall outcome,
      eval_grouping_sets_bag env left_sets input_bag outcome <->
      eval_grouping_sets_bag env right_sets input_bag outcome.
Proof.
  intros env input_bag left_sets right_sets Hsets.
  induction Hsets as
    [|[left_select left_terms] [right_select right_terms]
       left_sets right_sets Hhead Htail IH]; intro outcome.
  - reflexivity.
  - destruct outcome as [output_bag|error].
    + rewrite !eval_grouping_sets_cons_success_iff.
      split.
      * intros [head_bag [tail_bag [Hhead_success [Htail_success Houtput]]]].
        exists head_bag, tail_bag; repeat split; try exact Houtput.
        -- exact (proj1 (Hhead (SqlSuccess head_bag)) Hhead_success).
        -- exact (proj1 (IH (SqlSuccess tail_bag)) Htail_success).
      * intros [head_bag [tail_bag [Hhead_success [Htail_success Houtput]]]].
        exists head_bag, tail_bag; repeat split; try exact Houtput.
        -- exact (proj2 (Hhead (SqlSuccess head_bag)) Hhead_success).
        -- exact (proj2 (IH (SqlSuccess tail_bag)) Htail_success).
    + rewrite !eval_grouping_sets_cons_error_iff.
      split.
      * intros [Hhead_error | [head_bag [Hhead_success Htail_error]]].
        -- left; exact (proj1 (Hhead (SqlError error)) Hhead_error).
        -- right; exists head_bag; split.
           ++ exact (proj1 (Hhead (SqlSuccess head_bag)) Hhead_success).
           ++ exact (proj1 (IH (SqlError error)) Htail_error).
      * intros [Hhead_error | [head_bag [Hhead_success Htail_error]]].
        -- left; exact (proj2 (Hhead (SqlError error)) Hhead_error).
        -- right; exists head_bag; split.
           ++ exact (proj2 (Hhead (SqlSuccess head_bag)) Hhead_success).
           ++ exact (proj2 (IH (SqlError error)) Htail_error).
Qed.

Definition grouping_sets_union_fold (bags : list grouping_bag) : grouping_bag :=
  fold_right (query_set_bag Union)
    (Febag.empty (Fecol.CBag (Tuple.CTuple T))) bags.

(** A successful arbitrary grouping-set schedule is precisely an ordered list
    of successful branch bags combined by UNION ALL. *)
Theorem eval_grouping_sets_success_fold_iff :
  forall env input_bag grouping_sets output_bag,
    eval_grouping_sets_bag env grouping_sets input_bag
      (SqlSuccess output_bag) <->
    exists branch_bags,
      Forall2 (grouping_set_success_at env input_bag)
        grouping_sets branch_bags /\
      output_bag = grouping_sets_union_fold branch_bags.
Proof.
  intros env input_bag grouping_sets.
  induction grouping_sets as [|[select_list group_terms] grouping_sets IH];
    intro output_bag.
  - rewrite eval_grouping_sets_nil_outcome_iff.
    split.
    + intro Houtput; injection Houtput as Houtput; subst output_bag.
      exists []; split; [constructor|reflexivity].
    + intros [branch_bags [Hbranches Houtput]].
      inversion Hbranches; subst branch_bags.
      now rewrite Houtput.
  - rewrite eval_grouping_sets_cons_success_iff.
    split.
    + intros [head_bag [tail_bag [Hhead [Htail Houtput]]]].
      apply IH in Htail.
      destruct Htail as [tail_bags [Htail_bags Htail_output]].
      exists (head_bag :: tail_bags); split.
      * constructor; [exact Hhead|exact Htail_bags].
      * subst output_bag; cbn [grouping_sets_union_fold].
        now rewrite Htail_output.
    + intros [branch_bags [Hbranches Houtput]].
      inversion Hbranches as
        [|spec head_bag remaining tail_bags Hhead Htail]; subst.
      exists head_bag, (grouping_sets_union_fold tail_bags).
      split; [exact Hhead|].
      split.
      * apply (proj2 (IH (grouping_sets_union_fold tail_bags))).
        exists tail_bags; now split.
      * reflexivity.
Qed.

(** An error from an arbitrary grouping-set schedule occurs at one exact
    branch after an ordered prefix of successful branches.  Later branches are
    deliberately unconstrained because SQL never evaluates them. *)
Theorem eval_grouping_sets_error_prefix_iff :
  forall env input_bag grouping_sets error,
    eval_grouping_sets_bag env grouping_sets input_bag (SqlError error) <->
    exists (prefix : list (@query_grouping_set T))
        (current : @query_grouping_set T)
        (suffix : list (@query_grouping_set T))
        (prefix_bags : list grouping_bag),
      grouping_sets = List.app prefix (current :: suffix) /\
      Forall2 (grouping_set_success_at env input_bag)
        prefix prefix_bags /\
      grouping_set_error_at env input_bag current error.
Proof.
  intros env input_bag grouping_sets.
  induction grouping_sets as [|[select_list group_terms] grouping_sets IH];
    intro error.
  - split.
    + intro Heval.
      apply eval_grouping_sets_nil_outcome_iff in Heval; discriminate.
    + intros [prefix [current [suffix [prefix_bags [Hsets _]]]]].
      destruct prefix; discriminate.
  - rewrite eval_grouping_sets_cons_error_iff.
    split.
    + intros [Hhead | [head_bag [Hhead Htail]]].
      * exists [], (select_list, group_terms), grouping_sets, [].
        repeat split; [constructor|exact Hhead].
      * apply IH in Htail.
        destruct Htail as
          [prefix [current [suffix [prefix_bags
            [Hsets [Hprefix Hcurrent]]]]]].
        exists ((select_list, group_terms) :: prefix), current, suffix,
          (head_bag :: prefix_bags).
        split.
        -- cbn; now rewrite <- Hsets.
        -- split; [constructor; assumption|exact Hcurrent].
    + intros [prefix [current [suffix [prefix_bags
        [Hsets [Hprefix Hcurrent]]]]]].
      destruct prefix as [|first prefix].
      * cbn in Hsets; injection Hsets as Hcurrent_eq Hsuffix_eq.
        subst current suffix.
        left; exact Hcurrent.
      * destruct prefix_bags as [|first_bag prefix_bags].
        -- inversion Hprefix.
        -- inversion Hprefix as
             [|first_spec observed_bag remaining remaining_bags
                Hfirst Hremaining]; subst.
           cbn in Hsets; injection Hsets as Hfirst_eq Htail_eq.
           subst first.
           right; exists first_bag; split; [exact Hfirst|].
           apply IH.
           exists prefix, current, suffix, prefix_bags.
           repeat split; assumption.
Qed.

End GroupingSetsOutcomeFacts.

(** Constructor and equivalence facts for deterministic SQL outcomes. *)

Lemma successful_outcome_equiv_implies_outcome_equiv :
  forall (A : Type) (value_equiv : A -> A -> Prop) left right,
    successful_outcome_equiv value_equiv left right ->
    outcome_equiv value_equiv left right.
Proof.
  intros A value_equiv [left|left_error] [right|right_error] H;
    cbn in *; try contradiction; exact H.
Qed.

Lemma outcome_equiv_eq_iff : forall (A : Type) (left right : sql_outcome A),
  outcome_equiv eq left right <-> left = right.
Proof.
  intros A [left|left_error] [right|right_error]; cbn.
  - split; intro H.
    + subst; reflexivity.
    + now inversion H.
  - split; [contradiction|discriminate].
  - split; [contradiction|discriminate].
  - split; intro H.
    + subst; reflexivity.
    + now inversion H.
Qed.

Lemma outcome_equiv_symmetric :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall left right, value_equiv left right -> value_equiv right left) ->
    forall left right,
      outcome_equiv value_equiv left right ->
      outcome_equiv value_equiv right left.
Proof.
  intros A value_equiv Hsym [left|left_error] [right|right_error] H;
    cbn in *; try contradiction.
  - now apply Hsym.
  - now symmetry.
Qed.

Lemma outcome_equiv_transitive :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall left middle right,
      value_equiv left middle -> value_equiv middle right ->
      value_equiv left right) ->
    forall left middle right,
      outcome_equiv value_equiv left middle ->
      outcome_equiv value_equiv middle right ->
      outcome_equiv value_equiv left right.
Proof.
  intros A value_equiv Htrans
    [left|left_error] [middle|middle_error] [right|right_error];
    cbn; intros Hleft Hright; try contradiction.
  - exact (Htrans left middle right Hleft Hright).
  - exact (eq_trans Hleft Hright).
Qed.

(** Argument observations for a direct column over one closed group.

    This interface deliberately stops at [Permutation] of the observations
    selected by the aggregate evaluator.  It does not identify aggregate
    results under that permutation: callers using order-sensitive operations
    such as floating-point SUM or AVG must retain the representative order or
    supply a separate stability theorem. *)
Section DirectColumnAggregateArguments.

Context {T : Tuple.Rcd}.

Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.

Definition direct_column_aggregate_term
    (aggregate : Tuple.aggregate T)
    (attribute : Tuple.attribute T) : @ATerms.aggterm T :=
  @ATerms.A_agg T aggregate (@FTerms.F_Dot T attribute).

Definition closed_group_direct_column_argument_envs
    (group_terms : list (@ATerms.aggterm T))
    (group : list (Tuple.tuple T))
    (aggregate : Tuple.aggregate T)
    (attribute : Tuple.attribute T) : list (Env.env T) :=
  let group_env :=
    Env.env_g T nil (@Env.Group_By T group_terms) group in
  let aggregate_term := direct_column_aggregate_term aggregate attribute in
  let function_term := @FTerms.F_Dot T attribute in
  let selected_env :=
    if Fset.is_empty (Tuple.A T) (FTerms.variables_ft T function_term)
    then Some group_env
    else Interp.find_eval_env T group_env aggregate_term in
  match selected_env with
  | None | Some nil => nil
  | Some (slice :: outer_env) =>
      map (fun inner_slice => inner_slice :: outer_env)
        (Interp.unfold_env_slice T slice)
  end.

(** Definitionally, this is the observation list passed to an aggregate
    callback by [eval_aggterm_aggregate_runtime_error] for the corresponding
    direct-column aggregate application. *)
Definition closed_group_direct_column_argument_observations
    (group_terms : list (@ATerms.aggterm T))
    (group : list (Tuple.tuple T))
    (aggregate : Tuple.aggregate T)
    (attribute : Tuple.attribute T) :=
  map
    (fun argument_env =>
      (@eval_funterm_runtime_error T symbol_runtime_error
        argument_env (@FTerms.F_Dot T attribute),
       Interp.interp_funterm T argument_env (@FTerms.F_Dot T attribute)))
    (closed_group_direct_column_argument_envs
      group_terms group aggregate attribute).

Local Lemma direct_column_variables_nonempty : forall attribute,
  Fset.is_empty (Tuple.A T)
    (FTerms.variables_ft T (@FTerms.F_Dot T attribute)) = false.
Proof.
  intro attribute; cbn [FTerms.variables_ft].
  case_eq
    (Fset.is_empty (Tuple.A T)
      (Fset.singleton (Tuple.A T) attribute)); intro Hempty.
  - exfalso.
    rewrite Fset.is_empty_spec, Fset.equal_spec in Hempty.
    specialize (Hempty attribute).
    rewrite Fset.singleton_spec, Oset.eq_bool_refl,
      Fset.empty_spec in Hempty.
    discriminate.
  - reflexivity.
Qed.

Local Lemma direct_column_aggregate_selects_closed_group :
  forall group_terms group aggregate attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS Tuple.labels T row)
      group ->
    Interp.find_eval_env T
      (Env.env_g T nil (@Env.Group_By T group_terms) group)
      (direct_column_aggregate_term aggregate attribute) =
    Some (Env.env_g T nil (@Env.Group_By T group_terms) group).
Proof.
  intros group_terms group aggregate attribute Hnonempty Hpresent.
  case_eq (ListSort.quicksort (Tuple.OTuple T) group).
  - intro Hsorted.
    pose proof
      (ListSort.length_quicksort (Tuple.OTuple T) group) as Hlength.
    rewrite Hsorted in Hlength; symmetry in Hlength.
    apply length_zero_iff_nil in Hlength; contradiction.
  - intros first rest Hsorted.
    assert (Hfirst : attribute inS Tuple.labels T first).
    {
      rewrite Forall_forall in Hpresent.
      apply Hpresent.
      apply (proj2
        (ListSort.In_quicksort (Tuple.OTuple T) group first)).
      rewrite Hsorted; now left.
    }
    unfold Env.env_g; rewrite Hsorted.
    assert (Hsuitable :
      Interp.is_a_suitable_env T (Tuple.labels T first) nil
        (direct_column_aggregate_term aggregate attribute) = true).
    {
      unfold Interp.is_a_suitable_env, direct_column_aggregate_term.
      cbn [ATerms.is_built_upon_ag FTerms.is_built_upon_ft].
      rewrite Bool.Bool.orb_true_iff; right.
      cbn [FTerms.is_built_upon_ft flat_map].
      rewrite FTerms.funterm_mem_true_iff.
      rewrite ATerms.in_extract_funterms, app_nil_r.
      apply
        (in_map
          (fun current : Tuple.attribute T =>
            @ATerms.A_Expr T (@FTerms.F_Dot T current))
          (Fset.elements (Tuple.A T) (Tuple.labels T first)) attribute).
      now apply Fset.mem_in_elements.
    }
    unfold Interp.find_eval_env at 1; fold Interp.find_eval_env.
    rewrite Hsuitable; reflexivity.
Qed.

Local Lemma direct_column_singleton_observation :
  forall stored_labels row attribute,
    attribute inS Tuple.labels T row ->
    (@eval_funterm_runtime_error T symbol_runtime_error
       ((stored_labels, @Env.Group_Fine T, row :: nil) :: nil)
       (@FTerms.F_Dot T attribute),
     Interp.interp_funterm T
       ((stored_labels, @Env.Group_Fine T, row :: nil) :: nil)
       (@FTerms.F_Dot T attribute)) =
    (None, Tuple.dot T row attribute).
Proof.
  intros stored_labels row attribute Hpresent.
  unfold Interp.interp_funterm, Interp.interp_dot.
  cbn [eval_funterm_runtime_error].
  rewrite ListSort.quicksort_1; now rewrite Hpresent.
Qed.

(** A nonempty closed group whose rows expose the referenced column produces
    exactly one error-free direct-column observation per row, modulo the
    evaluator's representative ordering.  Neither the tuple schema nor the
    aggregate operator is fixed by this statement. *)
Theorem closed_group_direct_column_argument_observations_permutation_rows :
  forall group_terms group aggregate attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS Tuple.labels T row)
      group ->
    Permutation
      (closed_group_direct_column_argument_observations
        group_terms group aggregate attribute)
      (map
        (fun row => (None, Tuple.dot T row attribute))
        group).
Proof.
  intros group_terms group aggregate attribute Hnonempty Hpresent.
  pose proof
    (direct_column_aggregate_selects_closed_group
      group_terms group aggregate attribute Hnonempty Hpresent) as Hselected.
  unfold closed_group_direct_column_argument_observations,
    closed_group_direct_column_argument_envs.
  rewrite direct_column_variables_nonempty, Hselected.
  unfold Env.env_g.
  case_eq (ListSort.quicksort (Tuple.OTuple T) group).
  - intro Hsorted.
    pose proof
      (ListSort.length_quicksort (Tuple.OTuple T) group) as Hlength.
    rewrite Hsorted in Hlength; symmetry in Hlength.
    apply length_zero_iff_nil in Hlength; contradiction.
  - intros first rest Hsorted; cbn.
    unfold Interp.unfold_env_slice; rewrite !map_map.
    apply Permutation_refl'.
    apply map_ext_in; intros row Hrow.
    apply
      (direct_column_singleton_observation
        (Tuple.labels T first) row attribute).
    rewrite Forall_forall in Hpresent; now apply Hpresent.
Qed.

End DirectColumnAggregateArguments.
