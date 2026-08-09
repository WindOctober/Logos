(******************************************************************************)
(** Small value/error bridges from aggregate semantics to group outcomes.    **)
(******************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Env Formula Bool3 Projection SqlOutcome SqlQuerySyntax
  SqlQuerySemantics SqlErrorSemantics.
From Logos.FormalSQL Require Import
  AggregateRuntimeFacts TNullSyntax.
From Stdlib Require Import List Sorting.Permutation ZArith.

Import ListNotations.
Import Tuple.
Import NullValues.

Open Scope Z_scope.

(** COUNT-star observes the number of rows in a group both in its value and in
    its BIGINT overflow check.  The statement includes the aggregate-only and
    full expression check because grouping finalizes the former before HAVING
    and evaluates the latter only for a reached projection. *)
Lemma tnull_group_count_star_value_runtime_exact :
  forall env group_terms group,
    Interp.interp_aggterm TNull
      (Env.env_g TNull env (@Env.Group_By TNull group_terms) group)
      ACountStar =
      value_int64_checked (Z.of_nat (List.length group)) /\
    @eval_aggterm_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull env (@Env.Group_By TNull group_terms) group)
      ACountStar =
      int64_result_runtime_error (Z.of_nat (List.length group)) /\
    @eval_aggterm_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull env (@Env.Group_By TNull group_terms) group)
      ACountStar =
      int64_result_runtime_error (Z.of_nat (List.length group)).
Proof.
  intros env group_terms group.
  unfold ACountStar.
  cbn [Interp.interp_aggterm
    eval_aggterm_aggregate_runtime_error eval_aggterm_runtime_error
    FTerms.variables_ft].
  assert (Hempty :
    Fset.is_empty (A TNull) (Fset.empty (A TNull)) = true).
  { reflexivity. }
  rewrite !Hempty.
  unfold Env.env_g.
  cbn [Interp.unfold_env_slice
    NullValues.interp_aggregate NullValues.interp_aggregate_runtime_error
    NullValues.count_runtime_error NullValues.row_count
    NullValues.observation_values].
  split.
  - lazymatch goal with
    | |- Tuple.interp_aggregate TNull AggregateCountStar ?values = _ =>
        change
          (value_int64_checked (row_count values) =
           value_int64_checked (Z.of_nat (List.length group)))
    end.
    unfold row_count; repeat rewrite length_map; reflexivity.
  - split.
    + lazymatch goal with
      | |- count_runtime_error (observation_values ?observations) = _ =>
          change
            (count_runtime_error (observation_values observations) =
             int64_result_runtime_error (Z.of_nat (List.length group)))
      end.
      unfold count_runtime_error, row_count, observation_values.
      repeat rewrite length_map; reflexivity.
    + lazymatch goal with
      | |- count_runtime_error (observation_values ?observations) = _ =>
          change
            (count_runtime_error (observation_values observations) =
             int64_result_runtime_error (Z.of_nat (List.length group)))
      end.
      unfold count_runtime_error, row_count, observation_values.
      repeat rewrite length_map; reflexivity.
Qed.

(** Equal row cardinality is the complete COUNT-star value/local-error
    observation.  No in-range premise is needed: an out-of-range cardinality
    produces the same NULL placeholder and the same numeric error on both
    sides. *)
Theorem count_star_value_local_error_exact_of_equal_length :
  forall left right,
    List.length left = List.length right ->
    interp_aggregate AggregateCountStar left =
      interp_aggregate AggregateCountStar right /\
    aggregate_local_runtime_error AggregateCountStar left =
      aggregate_local_runtime_error AggregateCountStar right.
Proof.
  intros left right Hlength.
  split.
  - change
      (value_int64_checked (row_count left) =
       value_int64_checked (row_count right)).
    unfold row_count; now rewrite Hlength.
  - change (count_runtime_error left = count_runtime_error right).
    unfold count_runtime_error, row_count; now rewrite Hlength.
Qed.

(** Full COUNT-star observations also depend only on cardinality.  FormalSQL's
    private COUNT-star child is not an SQL expression, so its observation
    errors are intentionally ignored by the aggregate callback. *)
Theorem count_star_value_runtime_error_exact_of_equal_observation_length :
  forall left right,
    List.length left = List.length right ->
    interp_aggregate AggregateCountStar (observation_values left) =
      interp_aggregate AggregateCountStar (observation_values right) /\
    interp_aggregate_runtime_error AggregateCountStar left =
      interp_aggregate_runtime_error AggregateCountStar right.
Proof.
  intros left right Hlength.
  assert (Hvalues :
    List.length (observation_values left) =
    List.length (observation_values right)).
  { now rewrite !observation_values_length. }
  split.
  - exact (proj1
      (count_star_value_local_error_exact_of_equal_length
        (observation_values left) (observation_values right) Hvalues)).
  - rewrite !count_star_runtime_error_observations.
    exact (proj2
      (count_star_value_local_error_exact_of_equal_length
        (observation_values left) (observation_values right) Hvalues)).
Qed.

(** COUNT(expr) agrees exactly with COUNT-star only when every reached
    expression value is non-NULL.  This statement keeps DISTINCT out of the
    contract because duplicate elimination would change COUNT multiplicity. *)
Theorem count_star_count_all_nonnull_value_local_error_exact :
  forall star_values expression_values,
    List.length star_values = List.length expression_values ->
    Forall
      (fun value => NullValues.is_null_value value = false)
      expression_values ->
    interp_aggregate AggregateCountStar star_values =
      interp_aggregate
        (AggregateCall AggregateCount AggregateAll) expression_values /\
    aggregate_local_runtime_error AggregateCountStar star_values =
      aggregate_local_runtime_error
        (AggregateCall AggregateCount AggregateAll) expression_values.
Proof.
  intros star_values expression_values Hlength Hnonnull.
  pose proof
    (non_null_count_eq_length_of_Forall_nonnull expression_values Hnonnull)
    as Hcount.
  split.
  - change
      (value_int64_checked (row_count star_values) =
       value_int64_checked (non_null_count expression_values)).
    unfold row_count; now rewrite Hcount, Hlength.
  - change
      (count_runtime_error star_values =
       non_null_count_runtime_error expression_values).
    unfold count_runtime_error, non_null_count_runtime_error, row_count.
    now rewrite Hcount, Hlength.
Qed.

(** The expression form additionally evaluates every reached child.  Child
    safety is therefore explicit; once it holds, equal cardinality preserves
    both the successful BIGINT value and the overflow category. *)
Theorem count_star_count_all_nonnull_value_runtime_error_exact :
  forall star_observations expression_observations,
    List.length star_observations = List.length expression_observations ->
    Forall
      (fun observation =>
        fst observation = None /\
        NullValues.is_null_value (snd observation) = false)
      expression_observations ->
    interp_aggregate AggregateCountStar
      (observation_values star_observations) =
      interp_aggregate (AggregateCall AggregateCount AggregateAll)
        (observation_values expression_observations) /\
    interp_aggregate_runtime_error AggregateCountStar star_observations =
      interp_aggregate_runtime_error
        (AggregateCall AggregateCount AggregateAll)
        expression_observations.
Proof.
  intros star_observations expression_observations Hlength Hsafe_nonnull.
  assert (Hvalue_length :
    List.length (observation_values star_observations) =
    List.length (observation_values expression_observations)).
  { now rewrite !observation_values_length. }
  assert (Hnonnull :
    Forall
      (fun value => NullValues.is_null_value value = false)
      (observation_values expression_observations)).
  {
    clear Hlength Hvalue_length star_observations.
    unfold observation_values.
    induction Hsafe_nonnull as
      [|[error value] observations [Herror Hvalue] Hrest IH].
    - constructor.
    - cbn; constructor; [exact Hvalue|exact IH].
  }
  pose proof
    (count_star_count_all_nonnull_value_local_error_exact
      (observation_values star_observations)
      (observation_values expression_observations)
      Hvalue_length Hnonnull) as [Hvalue Hlocal].
  split; [exact Hvalue|].
  rewrite count_star_runtime_error_observations.
  rewrite aggregate_call_safe_children_reduce_to_local.
  - exact Hlocal.
  - apply first_observation_error_none_iff.
    rewrite Forall_forall.
    intros [error value] Hin; cbn.
    rewrite Forall_forall in Hsafe_nonnull.
    exact (proj1 (Hsafe_nonnull (error, value) Hin)).
Qed.
