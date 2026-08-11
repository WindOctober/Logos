(******************************************************************************)
(** Small value/error bridges from aggregate semantics to group outcomes.    **)
(******************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Env Formula Bool3 Projection SqlOutcome SqlQuerySyntax
  SqlQuerySemantics SqlErrorSemantics.
From Logos.FormalSQL Require Import
  AggregateRuntimeFacts BitwiseFacts NumericFacts TNullSyntax.
From Stdlib Require Import List Sorting.Permutation ZArith.

Import ListNotations.
Import Tuple.
Import NullValues.

Open Scope Z_scope.

(** The deterministic scalar observation exported by an aggregate call.  This
    is deliberately a small wrapper around the authoritative value and error
    callbacks: it does not introduce another aggregate semantics. *)
Definition aggregate_observation_outcome
    (call : ValueCore.aggregate)
    (observations : list (option sql_runtime_error * value))
    : sql_outcome value :=
  match interp_aggregate_runtime_error call observations with
  | Some error => SqlError error
  | None =>
      SqlSuccess
        (interp_aggregate call (observation_values observations))
  end.

(** Generic evaluator-level bridge.  A client may relate different aggregate
    calls and different represented values: equal observable runtime errors
    plus the requested successful-value relation are exactly the obligations
    needed for complete outcome equivalence. *)
Theorem aggregate_observation_outcome_transport :
  forall (value_rel : value -> value -> Prop)
    left_call right_call left_observations right_observations,
    interp_aggregate_runtime_error left_call left_observations =
      interp_aggregate_runtime_error right_call right_observations ->
    (interp_aggregate_runtime_error left_call left_observations = None ->
      value_rel
        (interp_aggregate left_call
          (observation_values left_observations))
        (interp_aggregate right_call
          (observation_values right_observations))) ->
    outcome_equiv value_rel
      (aggregate_observation_outcome left_call left_observations)
      (aggregate_observation_outcome right_call right_observations).
Proof.
  intros value_rel left_call right_call left_observations right_observations
    Herror Hvalue.
  unfold aggregate_observation_outcome.
  rewrite Herror.
  destruct (interp_aggregate_runtime_error
    right_call right_observations) eqn:Hright; cbn.
  - reflexivity.
  - apply Hvalue.
    exact Herror.
Qed.

(** AggregateCall exposes a useful decomposition of the generic bridge.  The
    first reached child error must agree; only when there is no such error does
    the local aggregate error matter.  This preserves PostgreSQL's eager child
    evaluation and the identity of the first observable error. *)
Theorem aggregate_call_observation_outcome_transport :
  forall (value_rel : value -> value -> Prop)
    left_function left_quantifier right_function right_quantifier
    left_observations right_observations,
    first_observation_error left_observations =
      first_observation_error right_observations ->
    aggregate_local_runtime_error
      (AggregateCall left_function left_quantifier)
      (observation_values left_observations) =
    aggregate_local_runtime_error
      (AggregateCall right_function right_quantifier)
      (observation_values right_observations) ->
    value_rel
      (interp_aggregate (AggregateCall left_function left_quantifier)
        (observation_values left_observations))
      (interp_aggregate (AggregateCall right_function right_quantifier)
        (observation_values right_observations)) ->
    outcome_equiv value_rel
      (aggregate_observation_outcome
        (AggregateCall left_function left_quantifier) left_observations)
      (aggregate_observation_outcome
        (AggregateCall right_function right_quantifier) right_observations).
Proof.
  intros value_rel left_function left_quantifier
    right_function right_quantifier left_observations right_observations
    Hchildren Hlocal Hvalue.
  apply aggregate_observation_outcome_transport; [|intros _; exact Hvalue].
  cbn [interp_aggregate_runtime_error].
  rewrite Hchildren.
  destruct (first_observation_error right_observations);
    [reflexivity|exact Hlocal].
Qed.

(** Error freedom is invariant under permutation, but the identity of the
    first error is not.  Consequently all permutation-based outcome bridges
    below require error-free child observations. *)
Lemma first_observation_error_none_permutation :
  forall left right,
    Permutation left right ->
    first_observation_error left = None ->
    first_observation_error right = None.
Proof.
  intros left right Hperm Hnone.
  apply first_observation_error_none_iff.
  apply first_observation_error_none_iff in Hnone.
  rewrite Forall_forall in Hnone |- *.
  intros observation Hin.
  apply Hnone.
  eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin].
Qed.

Lemma observation_values_permutation :
  forall left right,
    Permutation left right ->
    Permutation (observation_values left) (observation_values right).
Proof.
  intros left right Hperm.
  unfold observation_values; now apply Permutation_map.
Qed.

Lemma first_observation_error_map_none :
  forall (A : Type) (project : A -> value) rows,
    first_observation_error
      (map (fun row => (None, project row)) rows) = None.
Proof.
  intros A project rows; induction rows as [|row rest IH];
    cbn [first_observation_error]; auto.
Qed.

(** A reusable contract for aggregates whose successful value and local error
    are insensitive to input permutation.  It intentionally excludes child
    expression errors, which are handled by the preceding theorem. *)
Definition aggregate_value_local_permutation_stable
    (call : ValueCore.aggregate) : Prop :=
  forall left right,
    Permutation left right ->
    interp_aggregate call left = interp_aggregate call right /\
    aggregate_local_runtime_error call left =
      aggregate_local_runtime_error call right.

Theorem aggregate_observation_outcome_permutation_exact :
  forall call left_observations right_observations,
    aggregate_value_local_permutation_stable call ->
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome call left_observations =
      aggregate_observation_outcome call right_observations.
Proof.
  intros call left_observations right_observations
    Hstable Hperm Hleft_safe.
  pose proof
    (first_observation_error_none_permutation
      left_observations right_observations Hperm Hleft_safe)
    as Hright_safe.
  pose proof
    (observation_values_permutation
      left_observations right_observations Hperm) as Hvalues.
  specialize (Hstable _ _ Hvalues) as [Hvalue Hlocal].
  apply (proj1 (outcome_equiv_eq_iff value _ _)).
  apply aggregate_observation_outcome_transport; [|intros _; exact Hvalue].
  destruct call as [function quantifier|].
  - cbn [interp_aggregate_runtime_error].
    now rewrite Hleft_safe, Hright_safe.
  - cbn [interp_aggregate_runtime_error].
    exact Hlocal.
Qed.

(** COUNT(expr), including COUNT(DISTINCT expr), is permutation-stable once
    child observations are error-free. *)
Theorem count_observation_outcome_permutation_exact :
  forall quantifier left_observations right_observations,
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome
      (AggregateCall AggregateCount quantifier) left_observations =
    aggregate_observation_outcome
      (AggregateCall AggregateCount quantifier) right_observations.
Proof.
  intros quantifier left_observations right_observations Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply interp_aggregate_count_permutation.
  - now apply aggregate_count_local_runtime_error_permutation.
Qed.

(** COUNT-star has no child SQL expression, so even observation-error payloads
    are irrelevant; only cardinality is observed. *)
Theorem count_star_observation_outcome_permutation_exact :
  forall left_observations right_observations,
    Permutation left_observations right_observations ->
    aggregate_observation_outcome AggregateCountStar left_observations =
    aggregate_observation_outcome AggregateCountStar right_observations.
Proof.
  intros left_observations right_observations Hperm.
  apply (proj1 (outcome_equiv_eq_iff value _ _)).
  apply aggregate_observation_outcome_transport.
  - rewrite !count_star_runtime_error_observations.
    apply aggregate_count_star_local_runtime_error_permutation.
    now apply observation_values_permutation.
  - intros _; apply interp_aggregate_count_star_permutation.
    now apply observation_values_permutation.
Qed.

(** Exact PostgreSQL integer/NUMERIC SUM families.  REAL and DOUBLE PRECISION
    SUM are intentionally absent: their left-fold result may depend on input
    order, so a permutation is not a sound premise for those functions. *)
Theorem exact_sum_observation_outcome_permutation :
  forall call left_observations right_observations,
    In call
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome call left_observations =
      aggregate_observation_outcome call right_observations.
Proof.
  intros call left_observations right_observations
    Hcall Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply exact_sum_aggregate_permutation.
  - now apply exact_sum_runtime_error_permutation.
Qed.

(** Fixed-typmod NUMERIC AVG (and the same transition-state bridge used by
    fixed NUMERIC sample standard deviation). *)
Theorem fixed_numeric_observation_outcome_permutation :
  forall precision scale call left_observations right_observations,
    In call
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate
         (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome call left_observations =
      aggregate_observation_outcome call right_observations.
Proof.
  intros precision scale call left_observations right_observations
    Hcall Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply (fixed_numeric_aggregate_permutation
      precision scale call left right).
  - now apply (fixed_numeric_aggregate_runtime_error_permutation
      precision scale call left right).
Qed.

Theorem numeric_average_at_scale_observation_outcome_permutation :
  forall scale call left_observations right_observations,
    In call
      [Aggregate (AggregateAverageNumericAtScale scale);
       DistinctAggregate (AggregateAverageNumericAtScale scale)] ->
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome call left_observations =
      aggregate_observation_outcome call right_observations.
Proof.
  intros scale call left_observations right_observations
    Hcall Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply (numeric_average_at_scale_aggregate_permutation
      scale call left right).
  - now apply (numeric_average_at_scale_runtime_error_permutation
      scale call left right).
Qed.

(** Integral-input AVG and integer statistical aggregates share exact
    mathematical transition states.  Their local error callbacks are total;
    only child-expression errors remain observable. *)
Theorem integral_numeric_observation_outcome_permutation :
  forall call left_observations right_observations,
    In call
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
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome call left_observations =
      aggregate_observation_outcome call right_observations.
Proof.
  intros call left_observations right_observations Hcall Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply integral_numeric_aggregate_permutation.
  - repeat (destruct Hcall as [Hcall | Hcall];
      [subst call; reflexivity|]); contradiction.
Qed.

(** Exact MIN/MAX families.  Float/double extrema are deliberately excluded:
    equal numeric keys can retain different represented payloads depending on
    representative order. *)
Theorem exact_extrema_observation_outcome_permutation :
  forall function quantifier left_observations right_observations,
    (function = AggregateMinZ \/ function = AggregateMaxZ \/
     function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
     function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
     function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
     function = AggregateMaxString) ->
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome
      (AggregateCall function quantifier) left_observations =
    aggregate_observation_outcome
      (AggregateCall function quantifier) right_observations.
Proof.
  intros function quantifier left_observations right_observations
    Hfunction Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply exact_extrema_aggregate_permutation.
  - repeat match type of Hfunction with
    | _ \/ _ => destruct Hfunction as [Hfunction | Hfunction]
    | function = _ => subst function
    end; reflexivity.
Qed.

Lemma exact_bitwise_aggregate_permutation :
  forall function quantifier left right,
    In function
      [AggregateBitAndInt32; AggregateBitOrInt32;
       AggregateBitAndInt64; AggregateBitOrInt64] ->
    Permutation left right ->
    interp_aggregate (AggregateCall function quantifier) left =
      interp_aggregate (AggregateCall function quantifier) right.
Proof.
  intros function quantifier left right Hfunction Hperm.
  eapply interp_aggregate_call_permutation_congr; [|exact Hperm].
  intros first second Hselected.
  repeat (destruct Hfunction as [Hfunction | Hfunction];
    [subst function|]); try contradiction;
    cbn [interp_aggregate_function].
  - unfold interp_bit_and_int32.
    rewrite (forallb_permutation value is_int32_value first second Hselected).
    destruct (forallb is_int32_value second); [|reflexivity].
    f_equal; apply int32_bit_and_fold_permutation.
    now apply int32_values_permutation.
  - unfold interp_bit_or_int32.
    rewrite (forallb_permutation value is_int32_value first second Hselected).
    destruct (forallb is_int32_value second); [|reflexivity].
    f_equal; apply int32_bit_or_fold_permutation.
    now apply int32_values_permutation.
  - unfold interp_bit_and_int64.
    rewrite (forallb_permutation value is_int64_value first second Hselected).
    destruct (forallb is_int64_value second); [|reflexivity].
    f_equal; apply int64_bit_and_fold_permutation.
    now apply int64_values_permutation.
  - unfold interp_bit_or_int64.
    rewrite (forallb_permutation value is_int64_value first second Hselected).
    destruct (forallb is_int64_value second); [|reflexivity].
    f_equal; apply int64_bit_or_fold_permutation.
    now apply int64_values_permutation.
Qed.

Theorem exact_bitwise_observation_outcome_permutation :
  forall function quantifier left_observations right_observations,
    In function
      [AggregateBitAndInt32; AggregateBitOrInt32;
       AggregateBitAndInt64; AggregateBitOrInt64] ->
    Permutation left_observations right_observations ->
    first_observation_error left_observations = None ->
    aggregate_observation_outcome
      (AggregateCall function quantifier) left_observations =
    aggregate_observation_outcome
      (AggregateCall function quantifier) right_observations.
Proof.
  intros function quantifier left_observations right_observations
    Hfunction Hperm Hsafe.
  eapply aggregate_observation_outcome_permutation_exact;
    [|exact Hperm|exact Hsafe].
  intros left right Hvalues; split.
  - now apply exact_bitwise_aggregate_permutation.
  - repeat (destruct Hfunction as [Hfunction | Hfunction];
      [subst function; reflexivity|]); contradiction.
Qed.

(** DISTINCT and ALL are indistinguishable for any aggregate function once
    both select the same input.  The first theorem exposes the exact semantic
    contract; the NoDup corollary is the common duplicate-free-support case. *)
Theorem aggregate_distinct_all_observation_outcome_exact_of_selected_input :
  forall function observations,
    aggregate_input_values AggregateDistinct
      (observation_values observations) =
      aggregate_input_values AggregateAll
        (observation_values observations) ->
    aggregate_observation_outcome
      (AggregateCall function AggregateDistinct) observations =
    aggregate_observation_outcome
      (AggregateCall function AggregateAll) observations.
Proof.
  intros function observations Hselected.
  apply (proj1 (outcome_equiv_eq_iff value _ _)).
  apply aggregate_call_observation_outcome_transport.
  - reflexivity.
  - now apply aggregate_call_local_runtime_error_selected_input_congr.
  - now apply interp_aggregate_call_selected_input_congr.
Qed.

Corollary aggregate_distinct_all_observation_outcome_exact_of_nodup :
  forall function observations,
    NoDup (observation_values observations) ->
    aggregate_observation_outcome
      (AggregateCall function AggregateDistinct) observations =
    aggregate_observation_outcome
      (AggregateCall function AggregateAll) observations.
Proof.
  intros function observations Hnodup.
  apply aggregate_distinct_all_observation_outcome_exact_of_selected_input.
  cbn [aggregate_input_values].
  now apply distinct_values_fixed_of_nodup.
Qed.

(** End-to-end bridge for the direct-column shape generated by GROUP lowering.
    It converts the evaluator-selected observations to the logical group-row
    observations before applying any family-specific stability certificate. *)
Theorem closed_group_direct_column_aggregate_outcome_permutation_rows :
  forall group_terms group call attribute,
    aggregate_value_local_permutation_stable call ->
    group <> nil ->
    Forall (fun row => attribute inS Tuple.labels TNull row) group ->
    aggregate_observation_outcome call
      (@closed_group_direct_column_argument_observations
        TNull NullValues.interp_scalar_operator_runtime_error
        group_terms group call attribute) =
    aggregate_observation_outcome call
      (map (fun row => (None, Tuple.dot TNull row attribute)) group).
Proof.
  intros group_terms group call attribute Hstable Hnonempty Hpresent.
  pose proof
    (@closed_group_direct_column_argument_observations_permutation_rows
      TNull NullValues.interp_scalar_operator_runtime_error
      group_terms group call attribute Hnonempty Hpresent) as Hperm.
  apply aggregate_observation_outcome_permutation_exact;
    [exact Hstable|exact Hperm|].
  apply first_observation_error_none_permutation with
    (left := map
      (fun row => (None, Tuple.dot TNull row attribute)) group).
  - now apply Permutation_sym.
  - apply first_observation_error_map_none.
Qed.

(** Common GROUP/SUM specialization.  This is still operator-generic: the
    schema, column, grouping terms, quantifier, and exact SUM family remain
    parameters.  It closes the recurring gap between evaluator-selected
    arguments and the logical rows of a group without encoding a rewrite. *)
Corollary closed_group_direct_column_exact_sum_outcome_permutation_rows :
  forall group_terms group call attribute,
    In call
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    group <> nil ->
    Forall (fun row => attribute inS Tuple.labels TNull row) group ->
    aggregate_observation_outcome call
      (@closed_group_direct_column_argument_observations
        TNull NullValues.interp_scalar_operator_runtime_error
        group_terms group call attribute) =
    aggregate_observation_outcome call
      (map (fun row => (None, Tuple.dot TNull row attribute)) group).
Proof.
  intros group_terms group call attribute Hcall Hnonempty Hpresent.
  apply closed_group_direct_column_aggregate_outcome_permutation_rows;
    [|exact Hnonempty|exact Hpresent].
  intros left right Hperm; split.
  - now apply exact_sum_aggregate_permutation.
  - now apply exact_sum_runtime_error_permutation.
Qed.

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
