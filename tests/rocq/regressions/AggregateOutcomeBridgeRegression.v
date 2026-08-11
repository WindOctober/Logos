From SQLFS Require Import
  ATerms Bool3 FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  OrderedSet SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax
  Values.
From Logos.FormalSQL Require Import AggregateOutcomeBridgeFacts.
From Stdlib Require Import List Sorting.Permutation ZArith.

Import ListNotations.
Import NullValues.

Open Scope Z_scope.

(** Equal cardinality, rather than row type or row equality, is the complete
    COUNT-star value and overflow observation. *)
Theorem count_star_equal_cardinality_interface : forall left right,
  List.length left = List.length right ->
  interp_aggregate AggregateCountStar left =
    interp_aggregate AggregateCountStar right /\
  aggregate_local_runtime_error AggregateCountStar left =
    aggregate_local_runtime_error AggregateCountStar right.
Proof.
  apply count_star_value_local_error_exact_of_equal_length.
Qed.

(** COUNT(ALL expr) retains duplicate multiplicity.  Explicit child safety
    and non-NULL values make it agree with COUNT-star, including overflow. *)
Example count_star_count_all_nonnull_runtime_interface :
  interp_aggregate AggregateCountStar
    (observation_values
      [(None, Value_bool (Some true)); (None, Value_Z None)]) =
  interp_aggregate (AggregateCall AggregateCount AggregateAll)
    (observation_values
      [(None, Value_Z (Some 7)); (None, Value_Z (Some 7))]) /\
  interp_aggregate_runtime_error AggregateCountStar
    [(None, Value_bool (Some true)); (None, Value_Z None)] =
  interp_aggregate_runtime_error
    (AggregateCall AggregateCount AggregateAll)
    [(None, Value_Z (Some 7)); (None, Value_Z (Some 7))].
Proof.
  apply count_star_count_all_nonnull_value_runtime_error_exact.
  - reflexivity.
  - repeat constructor; reflexivity.
Qed.

(** The generic bridge is relation-parametric rather than tied to represented
    value equality. *)
Theorem aggregate_outcome_relation_interface :
  forall (value_rel : value -> value -> Prop)
    left_call right_call left_observations right_observations,
    interp_aggregate_runtime_error left_call left_observations =
      interp_aggregate_runtime_error right_call right_observations ->
    (interp_aggregate_runtime_error left_call left_observations = None ->
      value_rel
        (interp_aggregate left_call (observation_values left_observations))
        (interp_aggregate right_call
          (observation_values right_observations))) ->
    outcome_equiv value_rel
      (aggregate_observation_outcome left_call left_observations)
      (aggregate_observation_outcome right_call right_observations).
Proof. apply aggregate_observation_outcome_transport. Qed.

Theorem exact_sum_outcome_interface :
  forall call left right,
    In call
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    Permutation left right ->
    first_observation_error left = None ->
    aggregate_observation_outcome call left =
      aggregate_observation_outcome call right.
Proof. apply exact_sum_observation_outcome_permutation. Qed.

Theorem count_distinct_outcome_interface :
  forall left right,
    Permutation left right ->
    first_observation_error left = None ->
    aggregate_observation_outcome
      (AggregateCall AggregateCount AggregateDistinct) left =
    aggregate_observation_outcome
      (AggregateCall AggregateCount AggregateDistinct) right.
Proof. apply count_observation_outcome_permutation_exact. Qed.

Theorem fixed_numeric_outcome_interface :
  forall precision scale call left right,
    In call
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate
         (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    first_observation_error left = None ->
    aggregate_observation_outcome call left =
      aggregate_observation_outcome call right.
Proof. apply fixed_numeric_observation_outcome_permutation. Qed.

Theorem exact_extrema_outcome_interface :
  forall function quantifier left right,
    (function = AggregateMinZ \/ function = AggregateMaxZ \/
     function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
     function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
     function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
     function = AggregateMaxString) ->
    Permutation left right ->
    first_observation_error left = None ->
    aggregate_observation_outcome
      (AggregateCall function quantifier) left =
    aggregate_observation_outcome
      (AggregateCall function quantifier) right.
Proof. apply exact_extrema_observation_outcome_permutation. Qed.

Theorem exact_bitwise_outcome_interface :
  forall function quantifier left right,
    In function
      [AggregateBitAndInt32; AggregateBitOrInt32;
       AggregateBitAndInt64; AggregateBitOrInt64] ->
    Permutation left right ->
    first_observation_error left = None ->
    aggregate_observation_outcome
      (AggregateCall function quantifier) left =
    aggregate_observation_outcome
      (AggregateCall function quantifier) right.
Proof. apply exact_bitwise_observation_outcome_permutation. Qed.

Theorem distinct_all_duplicate_free_interface :
  forall function observations,
    NoDup (observation_values observations) ->
    aggregate_observation_outcome
      (AggregateCall function AggregateDistinct) observations =
    aggregate_observation_outcome
      (AggregateCall function AggregateAll) observations.
Proof.
  apply aggregate_distinct_all_observation_outcome_exact_of_nodup.
Qed.

Print Assumptions tnull_group_count_star_value_runtime_exact.
Print Assumptions count_star_value_local_error_exact_of_equal_length.
Print Assumptions count_star_value_runtime_error_exact_of_equal_observation_length.
Print Assumptions count_star_count_all_nonnull_value_local_error_exact.
Print Assumptions count_star_count_all_nonnull_value_runtime_error_exact.
Print Assumptions aggregate_observation_outcome_transport.
Print Assumptions aggregate_call_observation_outcome_transport.
Print Assumptions aggregate_observation_outcome_permutation_exact.
Print Assumptions exact_sum_observation_outcome_permutation.
Print Assumptions fixed_numeric_observation_outcome_permutation.
Print Assumptions numeric_average_at_scale_observation_outcome_permutation.
Print Assumptions integral_numeric_observation_outcome_permutation.
Print Assumptions exact_extrema_observation_outcome_permutation.
Print Assumptions exact_bitwise_observation_outcome_permutation.
Print Assumptions aggregate_distinct_all_observation_outcome_exact_of_nodup.
Print Assumptions closed_group_direct_column_aggregate_outcome_permutation_rows.
Print Assumptions
  closed_group_direct_column_exact_sum_outcome_permutation_rows.
