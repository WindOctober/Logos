From SQLFS Require Import
  ATerms Bool3 FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  OrderedSet SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax
  Values.
From Logos.FormalSQL Require Import AggregateOutcomeBridgeFacts.
From Stdlib Require Import List ZArith.

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

Print Assumptions tnull_group_count_star_value_runtime_exact.
Print Assumptions count_star_value_local_error_exact_of_equal_length.
Print Assumptions count_star_value_runtime_error_exact_of_equal_observation_length.
Print Assumptions count_star_count_all_nonnull_value_local_error_exact.
Print Assumptions count_star_count_all_nonnull_value_runtime_error_exact.
