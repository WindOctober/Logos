# Aggregates, modifiers, grouping, and aggregate errors

Route here for: COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality.

This focused catalog contains 136 declarations routed at declaration granularity from `AggregateRuntimeFacts.v`, `GroupedFilterOutcomeFacts.v`, `GroupingRewriteFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `first_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:14`](../AggregateRuntimeFacts.v#L14)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_error_none_iff : forall left right,
  first_error left right = None <-> left = None /\ right = None.
```

## `first_error_some_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:26`](../AggregateRuntimeFacts.v#L26)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_error_some_iff : forall left right error,
  first_error left right = Some error <->
  left = Some error \/ (left = None /\ right = Some error).
```

## `first_runtime_error_app`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:39`](../AggregateRuntimeFacts.v#L39)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_app :
  forall (A : Type) (check : A -> option sql_runtime_error) left right,
    first_runtime_error check (left ++ right) =
    first_error
      (first_runtime_error check left)
      (first_runtime_error check right).
```

## `first_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:51`](../AggregateRuntimeFacts.v#L51)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_none_iff :
  forall (A : Type) (check : A -> option sql_runtime_error) values,
    first_runtime_error check values = None <->
    Forall (fun value => check value = None) values.
```

## `first_runtime_error_some_member`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:69`](../AggregateRuntimeFacts.v#L69)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_some_member :
  forall (A : Type) (check : A -> option sql_runtime_error) values error,
    first_runtime_error check values = Some error ->
    exists value, In value values /\ check value = Some error.
```

## `first_observation_error_as_first_runtime_error`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:84`](../AggregateRuntimeFacts.v#L84)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_observation_error_as_first_runtime_error : forall observations,
  first_observation_error observations =
  first_runtime_error (fun observation => fst observation) observations.
```

## `first_observation_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:93`](../AggregateRuntimeFacts.v#L93)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_observation_error_none_iff : forall observations,
  first_observation_error observations = None <->
  Forall (fun observation => fst observation = None) observations.
```

## `first_observation_error_some_member`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:102`](../AggregateRuntimeFacts.v#L102)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_observation_error_some_member : forall observations error,
  first_observation_error observations = Some error ->
  exists observation,
    In observation observations /\ fst observation = Some error.
```

## `observation_values_length`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:112`](../AggregateRuntimeFacts.v#L112)

Purpose/direction: Relates aggregate evaluation to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `cardinality` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `cardinality`

```rocq
Lemma observation_values_length : forall observations,
  List.length (observation_values observations) = List.length observations.
```

## `aggregate_call_child_error_propagates`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:121`](../AggregateRuntimeFacts.v#L121)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_child_error_propagates :
  forall function quantifier observations error,
    first_observation_error observations = Some error ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = Some error.
```

## `aggregate_call_safe_children_reduce_to_local`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:131`](../AggregateRuntimeFacts.v#L131)

Purpose/direction: Reduces the composite aggregate evaluation condition to the displayed local condition.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_safe_children_reduce_to_local :
  forall function quantifier observations,
    first_observation_error observations = None ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations =
    aggregate_local_runtime_error
      (AggregateCall function quantifier) (observation_values observations).
```

## `aggregate_call_runtime_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:143`](../AggregateRuntimeFacts.v#L143)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 46)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_runtime_safe :
  forall function quantifier observations,
    first_observation_error observations = None ->
    aggregate_local_runtime_error
      (AggregateCall function quantifier)
      (observation_values observations) = None ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = None.
```

## `aggregate_call_runtime_error_as_first_error`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:157`](../AggregateRuntimeFacts.v#L157)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_runtime_error_as_first_error :
  forall function quantifier observations,
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations =
    first_error
      (first_observation_error observations)
      (aggregate_local_runtime_error
        (AggregateCall function quantifier)
        (observation_values observations)).
```

## `aggregate_call_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:172`](../AggregateRuntimeFacts.v#L172)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_runtime_error_none_iff :
  forall function quantifier observations,
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = None <->
    first_observation_error observations = None /\
    aggregate_local_runtime_error
      (AggregateCall function quantifier)
      (observation_values observations) = None.
```

## `aggregate_call_runtime_error_some_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:186`](../AggregateRuntimeFacts.v#L186)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_runtime_error_some_iff :
  forall function quantifier observations error,
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = Some error <->
    first_observation_error observations = Some error \/
    (first_observation_error observations = None /\
     aggregate_local_runtime_error
       (AggregateCall function quantifier)
       (observation_values observations) = Some error).
```

## `count_star_runtime_error_observations`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:201`](../AggregateRuntimeFacts.v#L201)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma count_star_runtime_error_observations : forall observations,
  interp_aggregate_runtime_error AggregateCountStar observations =
  count_runtime_error (observation_values observations).
```

## `int64_result_runtime_error_none_of_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:206`](../AggregateRuntimeFacts.v#L206)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_result_runtime_error_none_of_range : forall integer,
  int64_min <= integer <= int64_max ->
  int64_result_runtime_error integer = None.
```

## `int64_result_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:216`](../AggregateRuntimeFacts.v#L216)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_result_runtime_error_none_iff : forall integer,
  int64_result_runtime_error integer = None <->
  int64_min <= integer <= int64_max.
```

## `count_runtime_error_none_of_row_count_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:233`](../AggregateRuntimeFacts.v#L233)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `cardinality` (rank 52), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma count_runtime_error_none_of_row_count_range : forall values,
  int64_min <= row_count values <= int64_max ->
  count_runtime_error values = None.
```

## `count_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:241`](../AggregateRuntimeFacts.v#L241)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma count_runtime_error_none_iff : forall values,
  count_runtime_error values = None <->
  int64_min <= row_count values <= int64_max.
```

## `non_null_count_runtime_error_none_of_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:249`](../AggregateRuntimeFacts.v#L249)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma non_null_count_runtime_error_none_of_range : forall values,
  int64_min <= non_null_count values <= int64_max ->
  non_null_count_runtime_error values = None.
```

## `non_null_count_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:257`](../AggregateRuntimeFacts.v#L257)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma non_null_count_runtime_error_none_iff : forall values,
  non_null_count_runtime_error values = None <->
  int64_min <= non_null_count values <= int64_max.
```

## `aggregate_function_locally_total_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:286`](../AggregateRuntimeFacts.v#L286)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_function_locally_total_safe : forall function values,
  aggregate_function_locally_total function = true ->
  aggregate_local_runtime_error_function function values = None.
```

## `aggregate_call_locally_total_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:296`](../AggregateRuntimeFacts.v#L296)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_locally_total_safe :
  forall function quantifier values,
    aggregate_function_locally_total function = true ->
    aggregate_local_runtime_error
      (AggregateCall function quantifier) values = None.
```

## `aggregate_call_runtime_safe_of_locally_total`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:307`](../AggregateRuntimeFacts.v#L307)

Purpose/direction: Establishes totality of the indicated aggregate evaluation operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 46)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_call_runtime_safe_of_locally_total :
  forall function quantifier observations,
    aggregate_function_locally_total function = true ->
    first_observation_error observations = None ->
    interp_aggregate_runtime_error
      (AggregateCall function quantifier) observations = None.
```

## `all_null_non_null_count_zero`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:321`](../AggregateRuntimeFacts.v#L321)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `all_null_non_null_count_zero` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma all_null_non_null_count_zero : forall values,
  Forall (fun value => is_null_value value = true) values ->
  non_null_count values = 0.
```

## `aggregate_input_values_membership`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:336`](../AggregateRuntimeFacts.v#L336)

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_membership` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 30)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_membership :
  forall quantifier value values,
    In value (aggregate_input_values quantifier values) <-> In value values.
```

## `distinct_values_fixed_of_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:345`](../AggregateRuntimeFacts.v#L345)

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma distinct_values_fixed_of_nodup : forall values,
  NoDup values -> distinct_values values = values.
```

## `distinct_values_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:356`](../AggregateRuntimeFacts.v#L356)

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `cardinality` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `cardinality`

```rocq
Lemma distinct_values_length_le : forall values,
  (List.length (distinct_values values) <= List.length values)%nat.
```

## `aggregate_input_values_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:363`](../AggregateRuntimeFacts.v#L363)

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 30), `cardinality` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `cardinality`

```rocq
Lemma aggregate_input_values_length_le : forall quantifier values,
  (List.length (aggregate_input_values quantifier values) <=
   List.length values)%nat.
```

## `aggregate_input_values_distinct_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:371`](../AggregateRuntimeFacts.v#L371)

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 30), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma aggregate_input_values_distinct_nodup : forall values,
  NoDup (aggregate_input_values AggregateDistinct values).
```

## `aggregate_input_values_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:377`](../AggregateRuntimeFacts.v#L377)

Purpose/direction: Shows that the declared aggregate evaluation result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 30), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma aggregate_input_values_permutation :
  forall quantifier left right,
    Permutation left right ->
    Permutation
      (aggregate_input_values quantifier left)
      (aggregate_input_values quantifier right).
```

## `aggregate_input_values_idempotent`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:389`](../AggregateRuntimeFacts.v#L389)

Purpose/direction: Establishes idempotence for the declared aggregate evaluation operator.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_idempotent` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 30)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_idempotent : forall quantifier values,
  aggregate_input_values quantifier
    (aggregate_input_values quantifier values) =
  aggregate_input_values quantifier values.
```

## `interp_aggregate_call_selected_input_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:399`](../AggregateRuntimeFacts.v#L399)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 30)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `equivalence`, `congruence`

```rocq
Lemma interp_aggregate_call_selected_input_congr :
  forall function left_quantifier right_quantifier left right,
    aggregate_input_values left_quantifier left =
    aggregate_input_values right_quantifier right ->
    interp_aggregate (AggregateCall function left_quantifier) left =
    interp_aggregate (AggregateCall function right_quantifier) right.
```

## `aggregate_call_local_runtime_error_selected_input_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:410`](../AggregateRuntimeFacts.v#L410)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma aggregate_call_local_runtime_error_selected_input_congr :
  forall function left_quantifier right_quantifier left right,
    aggregate_input_values left_quantifier left =
    aggregate_input_values right_quantifier right ->
    aggregate_local_runtime_error
      (AggregateCall function left_quantifier) left =
    aggregate_local_runtime_error
      (AggregateCall function right_quantifier) right.
```

## `interp_aggregate_call_permutation_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:423`](../AggregateRuntimeFacts.v#L423)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 30), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma interp_aggregate_call_permutation_congr :
  forall function quantifier left right,
    (forall first second,
      Permutation first second ->
      interp_aggregate_function function first =
      interp_aggregate_function function second) ->
    Permutation left right ->
    interp_aggregate (AggregateCall function quantifier) left =
    interp_aggregate (AggregateCall function quantifier) right.
```

## `aggregate_call_local_runtime_error_permutation_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:438`](../AggregateRuntimeFacts.v#L438)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 30), `runtime` (rank 52), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
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
```

## `aggregate_input_values_preserves_all_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:455`](../AggregateRuntimeFacts.v#L455)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_preserves_all_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 30), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma aggregate_input_values_preserves_all_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  Forall (fun value => is_null_value value = true)
    (aggregate_input_values quantifier values).
```

## `aggregate_filter_input_membership`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:472`](../AggregateRuntimeFacts.v#L472)

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_filter_input_membership` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 30), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma aggregate_filter_input_membership :
  forall predicate quantifier value values,
    In value (aggregate_filter_input predicate quantifier values) <->
    In value values /\ predicate value = true.
```

## `aggregate_filter_input_distinct_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:483`](../AggregateRuntimeFacts.v#L483)

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 30), `filter` (rank 44), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `filter`, `WHERE`, `multiplicity`

```rocq
Lemma aggregate_filter_input_distinct_nodup : forall predicate values,
  NoDup (aggregate_filter_input predicate AggregateDistinct values).
```

## `aggregate_filter_input_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:490`](../AggregateRuntimeFacts.v#L490)

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 30), `filter` (rank 44), `cardinality` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma aggregate_filter_input_length_le :
  forall predicate quantifier values,
    (List.length (aggregate_filter_input predicate quantifier values) <=
     List.length values)%nat.
```

## `aggregate_filter_input_false_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:501`](../AggregateRuntimeFacts.v#L501)

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_filter_input_false_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 30), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma aggregate_filter_input_false_empty : forall quantifier values,
  aggregate_filter_input (fun _ => false) quantifier values = [].
```

## `count_star_value_of_row_count_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:515`](../AggregateRuntimeFacts.v#L515)

Purpose/direction: Connects the displayed range/representability premise to aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36), `cardinality` (rank 52), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `cardinality`

```rocq
Lemma count_star_value_of_row_count_range : forall values,
  int64_min <= row_count values <= int64_max ->
  exists result,
    interp_aggregate AggregateCountStar values =
      Value_int64 (Some result) /\
    int64_value result = row_count values.
```

## `count_value_of_non_null_count_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:532`](../AggregateRuntimeFacts.v#L532)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_value_of_non_null_count_range` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`

```rocq
Lemma count_value_of_non_null_count_range : forall quantifier values,
  int64_min <=
    non_null_count (aggregate_input_values quantifier values) <= int64_max ->
  exists result,
    interp_aggregate
      (AggregateCall AggregateCount quantifier) values =
      Value_int64 (Some result) /\
    int64_value result =
      non_null_count (aggregate_input_values quantifier values).
```

## `count_star_empty_success`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:557`](../AggregateRuntimeFacts.v#L557)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_star_empty_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma count_star_empty_success :
  exists zero,
    interp_aggregate AggregateCountStar [] = Value_int64 (Some zero) /\
    int64_value zero = 0.
```

## `count_empty_success`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:572`](../AggregateRuntimeFacts.v#L572)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_empty_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma count_empty_success : forall quantifier,
  exists zero,
    interp_aggregate (AggregateCall AggregateCount quantifier) [] =
      Value_int64 (Some zero) /\
    int64_value zero = 0.
```

## `count_all_null_success`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:590`](../AggregateRuntimeFacts.v#L590)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_all_null_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`

```rocq
Lemma count_all_null_success : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  exists zero,
    interp_aggregate (AggregateCall AggregateCount quantifier) values =
      Value_int64 (Some zero) /\
    int64_value zero = 0.
```

## `all_null_numeric_projections_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:614`](../AggregateRuntimeFacts.v#L614)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `all_null_numeric_projections_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma all_null_numeric_projections_empty : forall values,
  Forall (fun value => is_null_value value = true) values ->
  int32_values values = [] /\
  int64_values values = [] /\
  numeric_values values = [].
```

## `all_null_float_string_projections_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:636`](../AggregateRuntimeFacts.v#L636)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `all_null_float_string_projections_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`, `string`, `VARCHAR`

```rocq
Lemma all_null_float_string_projections_empty : forall values,
  Forall (fun value => is_null_value value = true) values ->
  float_values values = [] /\
  double_values values = [] /\
  text_values values = [].
```

## `sum_int32_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:660`](../AggregateRuntimeFacts.v#L660)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int32_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma sum_int32_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumInt32 quantifier) [] =
  Value_int64 None.
```

## `sum_int64_numeric_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:665`](../AggregateRuntimeFacts.v#L665)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int64_numeric_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`

```rocq
Lemma sum_int64_numeric_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumInt64Numeric quantifier) [] =
  Value_numeric None.
```

## `sum_numeric_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:670`](../AggregateRuntimeFacts.v#L670)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_numeric_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma sum_numeric_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumNumeric quantifier) [] =
  Value_numeric None.
```

## `sum_int32_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:675`](../AggregateRuntimeFacts.v#L675)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int32_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma sum_int32_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumInt32 quantifier) values =
  Value_int64 None.
```

## `sum_int64_numeric_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:693`](../AggregateRuntimeFacts.v#L693)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int64_numeric_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`

```rocq
Lemma sum_int64_numeric_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate
    (AggregateCall AggregateSumInt64Numeric quantifier) values =
  Value_numeric None.
```

## `sum_numeric_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:712`](../AggregateRuntimeFacts.v#L712)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_numeric_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma sum_numeric_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumNumeric quantifier) values =
  Value_numeric None.
```

## `sum_float_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:730`](../AggregateRuntimeFacts.v#L730)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_float_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_float_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumFloat quantifier) [] =
  Value_float None.
```

## `sum_double_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:735`](../AggregateRuntimeFacts.v#L735)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_double_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_double_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumDouble quantifier) [] =
  Value_double None.
```

## `sum_float_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:740`](../AggregateRuntimeFacts.v#L740)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_float_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_float_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumFloat quantifier) values =
  Value_float None.
```

## `sum_double_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:758`](../AggregateRuntimeFacts.v#L758)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_double_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_double_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumDouble quantifier) values =
  Value_double None.
```

## `min_max_int32_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:776`](../AggregateRuntimeFacts.v#L776)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int32_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`

```rocq
Lemma min_max_int32_empty_is_null : forall function quantifier,
  (function = AggregateMinInt32 \/ function = AggregateMaxInt32) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_int32 None.
```

## `min_max_numeric_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:783`](../AggregateRuntimeFacts.v#L783)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_numeric_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma min_max_numeric_empty_is_null : forall function quantifier,
  (function = AggregateMinNumeric \/ function = AggregateMaxNumeric) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_numeric None.
```

## `min_max_int32_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:790`](../AggregateRuntimeFacts.v#L790)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int32_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`

```rocq
Lemma min_max_int32_all_null_is_null : forall function quantifier values,
  (function = AggregateMinInt32 \/ function = AggregateMaxInt32) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_int32 None.
```

## `min_max_numeric_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:814`](../AggregateRuntimeFacts.v#L814)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_numeric_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma min_max_numeric_all_null_is_null : forall function quantifier values,
  (function = AggregateMinNumeric \/ function = AggregateMaxNumeric) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_numeric None.
```

## `min_max_int64_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:838`](../AggregateRuntimeFacts.v#L838)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int64_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`

```rocq
Lemma min_max_int64_empty_is_null : forall function quantifier,
  (function = AggregateMinInt64 \/ function = AggregateMaxInt64) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_int64 None.
```

## `min_max_float_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:845`](../AggregateRuntimeFacts.v#L845)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_float_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_float_empty_is_null : forall function quantifier,
  (function = AggregateMinFloat \/ function = AggregateMaxFloat) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_float None.
```

## `min_max_double_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:852`](../AggregateRuntimeFacts.v#L852)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_double_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_double_empty_is_null : forall function quantifier,
  (function = AggregateMinDouble \/ function = AggregateMaxDouble) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_double None.
```

## `max_string_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:859`](../AggregateRuntimeFacts.v#L859)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `max_string_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma max_string_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateMaxString quantifier) [] =
  Value_string (StringValue StringText None).
```

## `min_max_int64_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:864`](../AggregateRuntimeFacts.v#L864)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int64_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`

```rocq
Lemma min_max_int64_all_null_is_null : forall function quantifier values,
  (function = AggregateMinInt64 \/ function = AggregateMaxInt64) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_int64 None.
```

## `min_max_float_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:888`](../AggregateRuntimeFacts.v#L888)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_float_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_float_all_null_is_null : forall function quantifier values,
  (function = AggregateMinFloat \/ function = AggregateMaxFloat) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_float None.
```

## `min_max_double_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:912`](../AggregateRuntimeFacts.v#L912)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_double_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_double_all_null_is_null : forall function quantifier values,
  (function = AggregateMinDouble \/ function = AggregateMaxDouble) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_double None.
```

## `max_string_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:936`](../AggregateRuntimeFacts.v#L936)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `max_string_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma max_string_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateMaxString quantifier) values =
  Value_string (StringValue StringText None).
```

## `avg_integral_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:954`](../AggregateRuntimeFacts.v#L954)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_integral_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_integral_empty_is_null : forall function quantifier,
  (function = AggregateAverageInt32Numeric \/
   function = AggregateAverageInt64Numeric) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_numeric None.
```

## `avg_integral_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:962`](../AggregateRuntimeFacts.v#L962)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_integral_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_integral_all_null_is_null : forall function quantifier values,
  (function = AggregateAverageInt32Numeric \/
   function = AggregateAverageInt64Numeric) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_numeric None.
```

## `avg_float_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:988`](../AggregateRuntimeFacts.v#L988)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_float_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_float_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateAverageFloat quantifier) [] =
  Value_float None.
```

## `avg_double_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:993`](../AggregateRuntimeFacts.v#L993)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_double_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_double_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateAverageDouble quantifier) [] =
  Value_double None.
```

## `avg_float_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:998`](../AggregateRuntimeFacts.v#L998)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_float_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_float_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateAverageFloat quantifier) values =
  Value_float None.
```

## `avg_double_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1016`](../AggregateRuntimeFacts.v#L1016)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_double_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_double_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateAverageDouble quantifier) values =
  Value_double None.
```

## `avg_numeric_fixed_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1034`](../AggregateRuntimeFacts.v#L1034)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_fixed_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_numeric_fixed_empty_is_null : forall precision scale quantifier,
  interp_aggregate
    (AggregateCall (AggregateAverageNumericFixed precision scale) quantifier)
    [] = Value_numeric None.
```

## `avg_numeric_fixed_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1045`](../AggregateRuntimeFacts.v#L1045)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_fixed_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_numeric_fixed_all_null_is_null :
  forall precision scale quantifier values,
    Forall (fun value => is_null_value value = true) values ->
    interp_aggregate
      (AggregateCall
        (AggregateAverageNumericFixed precision scale) quantifier) values =
    Value_numeric None.
```

## `avg_numeric_at_scale_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1068`](../AggregateRuntimeFacts.v#L1068)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_at_scale_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; retain every typmod/precision/scale and representability condition.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma avg_numeric_at_scale_empty_is_null : forall scale quantifier,
  interp_aggregate
    (AggregateCall (AggregateAverageNumericAtScale scale) quantifier) [] =
    Value_numeric None.
```

## `avg_numeric_at_scale_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1079`](../AggregateRuntimeFacts.v#L1079)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_at_scale_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; retain every typmod/precision/scale and representability condition.

Cross-index: `grouping` (rank 36), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma avg_numeric_at_scale_all_null_is_null : forall scale quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate
    (AggregateCall (AggregateAverageNumericAtScale scale) quantifier) values =
  Value_numeric None.
```

## `single_value_int32_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1103`](../AggregateRuntimeFacts.v#L1103)

Purpose/direction: Characterizes SINGLE_VALUE safety exactly as at most one selected INT32 value.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `cardinality` (rank 38), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma single_value_int32_runtime_error_none_iff : forall values,
  single_value_int32_runtime_error values = None <->
  (List.length values <= 1)%nat.
```

## `single_value_int32_runtime_error_cardinality_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1113`](../AggregateRuntimeFacts.v#L1113)

Purpose/direction: Characterizes CardinalityViolation exactly as at least two selected INT32 values.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma single_value_int32_runtime_error_cardinality_iff : forall values,
  single_value_int32_runtime_error values = Some CardinalityViolation <->
  (2 <= List.length values)%nat.
```

## `aggregate_single_value_int32_selected_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1123`](../AggregateRuntimeFacts.v#L1123)

Purpose/direction: Shows that empty selected input yields SQL NULL with no SINGLE_VALUE runtime error.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: every explicit antecedent (`->`) in the declaration is required; the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma aggregate_single_value_int32_selected_empty :
  forall quantifier values,
    aggregate_input_values quantifier values = [] ->
    interp_aggregate
      (AggregateCall AggregateSingleValueInt32 quantifier) values =
      Value_int32 None /\
    aggregate_local_runtime_error
      (AggregateCall AggregateSingleValueInt32 quantifier) values = None.
```

## `aggregate_single_value_int32_selected_singleton`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1137`](../AggregateRuntimeFacts.v#L1137)

Purpose/direction: Shows that singleton selected input returns its INT32 value with no SINGLE_VALUE runtime error.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: every explicit antecedent (`->`) in the declaration is required; the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma aggregate_single_value_int32_selected_singleton :
  forall quantifier values integer,
    aggregate_input_values quantifier values =
      [Value_int32 integer] ->
    interp_aggregate
      (AggregateCall AggregateSingleValueInt32 quantifier) values =
      Value_int32 integer /\
    aggregate_local_runtime_error
      (AggregateCall AggregateSingleValueInt32 quantifier) values = None.
```

## `aggregate_single_value_int32_cardinality_violation_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1152`](../AggregateRuntimeFacts.v#L1152)

Purpose/direction: Characterizes CardinalityViolation exactly as at least two selected INT32 values.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 30), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma aggregate_single_value_int32_cardinality_violation_iff :
  forall quantifier values,
    aggregate_local_runtime_error
      (AggregateCall AggregateSingleValueInt32 quantifier) values =
      Some CardinalityViolation <->
    (2 <= List.length
      (aggregate_input_values quantifier values))%nat.
```

## `query_make_groups_empty_shape`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1168`](../AggregateRuntimeFacts.v#L1168)

Purpose/direction: States the exact empty-input or empty-result law for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_empty_shape` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Lemma query_make_groups_empty_shape :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms,
    @query_make_groups T env [] group_terms =
    match group_terms with
    | [] => [[]]
    | _ :: _ => []
    end.
```

## `eval_grouping_sets_nil_outcome_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1212`](../AggregateRuntimeFacts.v#L1212)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome` (rank 52), `grouping` (rank 24), `runtime` (rank 52), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_grouping_sets_nil_outcome_iff : forall env input_bag outcome,
  eval_grouping_sets_bag env [] input_bag outcome <->
  outcome =
    SqlSuccess (Febag.empty (Fecol.CBag (Tuple.CTuple T))).
```

## `eval_grouping_sets_cons_success_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1222`](../AggregateRuntimeFacts.v#L1222)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`

```rocq
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
```

## `eval_grouping_sets_cons_error_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1240`](../AggregateRuntimeFacts.v#L1240)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 24), `runtime` (rank 48)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
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
```

## `successful_outcome_equiv_implies_outcome_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1263`](../AggregateRuntimeFacts.v#L1263)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 46), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma successful_outcome_equiv_implies_outcome_equiv :
  forall (A : Type) (value_equiv : A -> A -> Prop) left right,
    successful_outcome_equiv value_equiv left right ->
    outcome_equiv value_equiv left right.
```

## `outcome_equiv_eq_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1272`](../AggregateRuntimeFacts.v#L1272)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 46), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_eq_iff : forall (A : Type) (left right : sql_outcome A),
  outcome_equiv eq left right <-> left = right.
```

## `outcome_equiv_symmetric`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1286`](../AggregateRuntimeFacts.v#L1286)

Purpose/direction: Reverses a proved aggregate evaluation relation.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 46), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_symmetric :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall left right, value_equiv left right -> value_equiv right left) ->
    forall left right,
      outcome_equiv value_equiv left right ->
      outcome_equiv value_equiv right left.
```

## `outcome_equiv_transitive`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1299`](../AggregateRuntimeFacts.v#L1299)

Purpose/direction: Composes two aggregate evaluation relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 46), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_transitive :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall left middle right,
      value_equiv left middle -> value_equiv middle right ->
      value_equiv left right) ->
    forall left middle right,
      outcome_equiv value_equiv left middle ->
      outcome_equiv value_equiv middle right ->
      outcome_equiv value_equiv left right.
```

## `eval_query_outcome_in_state_success_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1318`](../AggregateRuntimeFacts.v#L1318)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 52), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_outcome_in_state_success_iff : forall db query rows,
  eval_query_outcome_in_state db query = SqlSuccess rows <->
  query_succeeds db query /\ rows = eval_query_in_state db query.
```

## `eval_query_outcome_in_state_error_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1339`](../AggregateRuntimeFacts.v#L1339)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 52), `grouping` (rank 36), `runtime` (rank 48)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_outcome_in_state_error_iff : forall db query error,
  eval_query_outcome_in_state db query = SqlError error <->
  query_runtime_error_in_state db query = Some error.
```

## `query_succeeds_iff_self_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1356`](../AggregateRuntimeFacts.v#L1356)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 35)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `equivalence`, `congruence`

```rocq
Corollary query_succeeds_iff_self_equiv : forall db query,
  query_succeeds db query <-> query_equiv db query query.
```

## `formula_acceptance_exact_total_success`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:56`](../GroupedFilterOutcomeFacts.v#L56)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `formula_acceptance_exact_total_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma formula_acceptance_exact_total_success :
  forall env formula accepted,
    formula_acceptance_exact_at env formula accepted ->
    formula_total_success_at env formula.
```

## `formula_and_success_intro`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:69`](../GroupedFilterOutcomeFacts.v#L69)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `formula_and_success_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma formula_and_success_intro :
  forall env left right left_truth right_truth,
    eval_formula env left (SqlSuccess left_truth) ->
    eval_formula env right (SqlSuccess right_truth) ->
    eval_formula env (FExpr_Conj And_F left right)
      (SqlSuccess (Bool.andb (B T) left_truth right_truth)).
```

## `formula_and_right_error_intro`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:79`](../GroupedFilterOutcomeFacts.v#L79)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma formula_and_right_error_intro :
  forall env left right left_truth error,
    eval_formula env left (SqlSuccess left_truth) ->
    eval_formula env right (SqlError error) ->
    eval_formula env (FExpr_Conj And_F left right) (SqlError error).
```

## `formula_and_true_left_outcome_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:90`](../GroupedFilterOutcomeFacts.v#L90)

Purpose/direction: States the formula and true left outcome exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 52), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma formula_and_true_left_outcome_exact :
  forall env left right,
    formula_acceptance_exact_at env left true ->
    forall outcome,
      eval_formula env (FExpr_Conj And_F left right) outcome <->
      eval_formula env right outcome.
```

## `formula_and_total_success_at_intro`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:121`](../GroupedFilterOutcomeFacts.v#L121)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `formula_and_total_success_at_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma formula_and_total_success_at_intro :
  forall env left right,
    formula_total_success_at env left ->
    formula_total_success_at env right ->
    formula_total_success_at env (FExpr_Conj And_F left right).
```

## `formula_and_left_nontrue_success_rejected`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:138`](../GroupedFilterOutcomeFacts.v#L138)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `formula_and_left_nontrue_success_rejected` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma formula_and_left_nontrue_success_rejected :
  forall env left right truth,
    formula_acceptance_exact_at env left false ->
    eval_formula env (FExpr_Conj And_F left right) (SqlSuccess truth) ->
    Bool.is_true (B T) truth = false.
```

## `grouped_key_formula_contract_tail`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:235`](../GroupedFilterOutcomeFacts.v#L235)

Purpose/direction: States the grouped key formula contract tail law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `grouped_key_formula_contract_tail` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma grouped_key_formula_contract_tail :
  forall env group_terms key_formula group groups keep,
    grouped_key_formula_contract env group_terms key_formula
      (group :: groups) keep ->
    grouped_key_formula_contract env group_terms key_formula groups keep.
```

## `skipped_group_runtime_safe_tail`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:245`](../GroupedFilterOutcomeFacts.v#L245)

Purpose/direction: States the skipped group runtime safe tail law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 46)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma skipped_group_runtime_safe_tail :
  forall env select_list group_terms rest_having group groups keep,
    skipped_group_runtime_safe env select_list group_terms rest_having
      (group :: groups) keep ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      groups keep.
```

## `eval_groups_having_key_conj_filter_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:257`](../GroupedFilterOutcomeFacts.v#L257)

Purpose/direction: States the eval groups having key conj filter exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_having_key_conj_filter_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 20), `filter` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`

```rocq
Theorem eval_groups_having_key_conj_filter_exact :
  forall env select_list group_terms key_formula rest_having groups keep,
    grouped_key_formula_contract env group_terms key_formula groups keep ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      groups keep ->
    forall outcome,
      eval_groups env select_list group_terms
        (FExpr_Conj And_F key_formula rest_having) groups outcome <->
      eval_groups env select_list group_terms rest_having
        (filter keep groups) outcome.
```

## `first_runtime_error_filter_none`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:413`](../GroupedFilterOutcomeFacts.v#L413)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_filter_none :
  forall (A : Type) (check : A -> option sql_runtime_error) keep rows,
    first_runtime_error check rows = None ->
    first_runtime_error check (filter keep rows) = None.
```

## `group_keys_runtime_error_filter_none`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:428`](../GroupedFilterOutcomeFacts.v#L428)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate grouping.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 36), `runtime` (rank 52), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma group_keys_runtime_error_filter_none :
  forall env group_terms rows keep,
    @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
      env group_terms rows = None ->
    @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
      env group_terms (filter keep rows) = None.
```

## `bag_sigma_eval_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:440`](../GroupedFilterOutcomeFacts.v#L440)

Purpose/direction: States the bag sigma eval exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `filter` (rank 46), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_sigma_eval_exact :
  forall env bag_formula input,
    @eval_query T relname basesort instance unknown contains_nulls env
      (Q_Sigma bag_formula input) =
    Febag.filter (Fecol.CBag (CTuple T))
      (bag_formula_row_keep env bag_formula)
      (@eval_query T relname basesort instance unknown contains_nulls env
        input).
```

## `bag_sigma_runtime_error_none_iff`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:454`](../GroupedFilterOutcomeFacts.v#L454)

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `runtime` (rank 40), `filter` (rank 46), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_sigma_runtime_error_none_iff :
  forall env bag_formula input,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env
      (Q_Sigma bag_formula input) = None <->
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env input = None /\
    first_runtime_error
      (fun row =>
        @eval_formula_runtime_error T relname symbol_runtime_error
          aggregate_runtime_error
          (@eval_query_runtime_error T relname basesort instance unknown
            contains_nulls symbol_runtime_error aggregate_runtime_error)
          (env_t T env row) bag_formula)
      (Febag.elements (Fecol.CBag (CTuple T))
        (@eval_query T relname basesort instance unknown contains_nulls env
          input)) = None.
```

## `bag_formula_key_factorization_is_constant`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:517`](../GroupedFilterOutcomeFacts.v#L517)

Purpose/direction: States the bag formula key factorization is constant law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_formula_key_factorization_is_constant :
  forall env group_terms bag_formula rows keep_key left right,
    (forall row,
      In row rows ->
      bag_formula_row_keep env bag_formula row =
        keep_key (query_grouping_key env group_terms row)) ->
    In left rows ->
    In right rows ->
    query_grouping_key env group_terms left =
      query_grouping_key env group_terms right ->
    bag_formula_row_keep env bag_formula left =
      bag_formula_row_keep env bag_formula right.
```

## `filter_extensional_on_members`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:536`](../GroupedFilterOutcomeFacts.v#L536)

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `filter_extensional_on_members` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma filter_extensional_on_members :
  forall (A : Type) (left right : A -> bool) rows,
    (forall value, In value rows -> left value = right value) ->
    filter left rows = filter right rows.
```

## `eval_groups_having_key_conj_after_bag_formula_filter_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:553`](../GroupedFilterOutcomeFacts.v#L553)

Purpose/direction: States the eval groups having key conj after bag formula filter exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 20), `filter` (rank 36), `bag` (rank 50)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_groups_having_key_conj_after_bag_formula_filter_exact :
  forall env select_list group_terms key_formula rest_having rows
      bag_formula keep_key,
    group_terms <> nil ->
    bag_formula_group_key_link env group_terms bag_formula key_formula
      rows keep_key ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      (query_make_groups env rows group_terms)
      (grouped_key_keep env group_terms keep_key) ->
    forall outcome,
      eval_groups env select_list group_terms
        (FExpr_Conj And_F key_formula rest_having)
        (query_make_groups env rows group_terms) outcome <->
      eval_groups env select_list group_terms rest_having
        (query_make_groups env
          (filter (bag_formula_row_keep env bag_formula) rows)
          group_terms) outcome.
```

## `filter_insert_in_partition_by_key`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:23`](../GroupingRewriteFacts.v#L23)

Purpose/direction: States the filter insert in partition by key law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `filter_insert_in_partition_by_key` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma filter_insert_in_partition_by_key :
  forall (keep : Key -> bool) key row groups,
    filter (fun group => keep (fst group))
      (@Partition.insert_in_partition A Key key_order key row groups) =
    if keep key
    then @Partition.insert_in_partition A Key key_order key row
           (filter (fun group => keep (fst group)) groups)
    else filter (fun group => keep (fst group)) groups.
```

## `filter_partition_rec_by_key`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:44`](../GroupingRewriteFacts.v#L44)

Purpose/direction: States the filter partition rec by key law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `filter_partition_rec_by_key` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma filter_partition_rec_by_key :
  forall (keep : Key -> bool) (key_of : A -> Key) rows groups,
    filter (fun group => keep (fst group))
      (@Partition.partition_rec A Key key_order key_of groups rows) =
    @Partition.partition_rec A Key key_order key_of
      (filter (fun group => keep (fst group)) groups)
      (filter (fun row => keep (key_of row)) rows).
```

## `partition_filter_by_key_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:59`](../GroupingRewriteFacts.v#L59)

Purpose/direction: States the partition filter by key exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `partition_filter_by_key_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34), `filter` (rank 42)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Theorem partition_filter_by_key_exact :
  forall (keep : Key -> bool) (key_of : A -> Key) rows,
    @Partition.partition A Key key_order key_of
      (filter (fun row => keep (key_of row)) rows) =
    filter (fun group => keep (fst group))
      (@Partition.partition A Key key_order key_of rows).
```

## `map_snd_filter_keyed_groups`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:74`](../GroupingRewriteFacts.v#L74)

Purpose/direction: States the map snd filter keyed groups law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `map_snd_filter_keyed_groups` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 36), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma map_snd_filter_keyed_groups :
  forall (keep : Key -> bool) (key_of : A -> Key) groups,
    (forall key members,
      In (key, members) groups ->
      exists row rest, members = row :: rest /\ key_of row = key) ->
    map snd (filter (fun group => keep (fst group)) groups) =
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (key_of row)
        end)
      (map snd groups).
```

## `partition_members_filter_by_key_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:112`](../GroupingRewriteFacts.v#L112)

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `partition_members_filter_by_key_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34), `filter` (rank 42)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Theorem partition_members_filter_by_key_exact :
  forall (keep : Key -> bool) (key_of : A -> Key) rows,
    map snd
      (@Partition.partition A Key key_order key_of
        (filter (fun row => keep (key_of row)) rows)) =
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (key_of row)
        end)
      (map snd (@Partition.partition A Key key_order key_of rows)).
```

## `query_make_groups_filter_by_key_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:152`](../GroupingRewriteFacts.v#L152)

Purpose/direction: States the query make groups filter by key exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_filter_by_key_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 34), `filter` (rank 42)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`

```rocq
Theorem query_make_groups_filter_by_key_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms rows
      (keep : list (value T) -> bool),
    group_terms <> nil ->
    @query_make_groups T env
      (filter
        (fun row => keep (query_grouping_key env group_terms row)) rows)
      group_terms =
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (query_grouping_key env group_terms row)
        end)
      (@query_make_groups T env rows group_terms).
```

## `formula_expr_admissible_conj_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:182`](../GroupingRewriteFacts.v#L182)

Purpose/direction: States the formula expr admissible conj intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_expr_admissible_conj_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma formula_expr_admissible_conj_intro :
  forall operation left right,
    @formula_expr_admissible T relname basesort left ->
    @formula_expr_admissible T relname basesort right ->
    @formula_expr_admissible T relname basesort
      (FExpr_Conj operation left right).
```

## `query_expr_admissible_bag_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:190`](../GroupingRewriteFacts.v#L190)

Purpose/direction: States the query expr admissible bag intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_admissible_bag_intro :
  forall outputs query,
    @query_output_attributes_unique T outputs ->
    @bag_query_admissible T relname basesort query ->
    @query_outputs_sort T outputs =S=
      @SqlAlgebra.sort T relname basesort query ->
    @query_expr_admissible T relname basesort
      (QExpr_Bag outputs query).
```

## `query_expr_admissible_set_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:200`](../GroupingRewriteFacts.v#L200)

Purpose/direction: States the query expr admissible set intro law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_set_intro` direction for SQL bag/set operations; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `aggregate`

```rocq
Lemma query_expr_admissible_set_intro :
  forall operation left right,
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    query_expr_outputs left = query_expr_outputs right ->
    @query_expr_admissible T relname basesort
      (QExpr_Set operation left right).
```

## `query_expr_admissible_natural_join_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:209`](../GroupingRewriteFacts.v#L209)

Purpose/direction: States the query expr admissible natural join intro law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_natural_join_intro` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `join`, `aggregate`

```rocq
Lemma query_expr_admissible_natural_join_intro :
  forall left right,
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    @query_expr_admissible T relname basesort
      (QExpr_NaturalJoin left right).
```

## `query_expr_admissible_cross_join_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:217`](../GroupingRewriteFacts.v#L217)

Purpose/direction: States the query expr admissible cross join intro law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_cross_join_intro` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `aggregate`

```rocq
Lemma query_expr_admissible_cross_join_intro :
  forall left right,
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    @query_output_sorts_disjoint T
      (query_expr_sort left) (query_expr_sort right) ->
    @query_expr_admissible T relname basesort
      (QExpr_CrossJoin left right).
```

## `query_expr_admissible_join_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:227`](../GroupingRewriteFacts.v#L227)

Purpose/direction: States the query expr admissible join intro law for outer/semi/anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `aggregate`

```rocq
Lemma query_expr_admissible_join_intro :
  forall kind predicate matched_select left_select right_select left right,
    @formula_expr_admissible T relname basesort predicate ->
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    @query_expr_admissible T relname basesort
      (QExpr_Join kind predicate matched_select left_select right_select
        left right).
```

## `query_expr_admissible_project_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:241`](../GroupingRewriteFacts.v#L241)

Purpose/direction: States the query expr admissible project intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_project_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `projection`, `SELECT list`

```rocq
Lemma query_expr_admissible_project_intro :
  forall select_list input,
    @query_expr_admissible T relname basesort input ->
    query_select_list_outputs_unique select_list ->
    @query_expr_admissible T relname basesort
      (QExpr_Project select_list input).
```

## `query_expr_admissible_filter_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:249`](../GroupingRewriteFacts.v#L249)

Purpose/direction: States the query expr admissible filter intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_filter_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma query_expr_admissible_filter_intro :
  forall formula input,
    @query_expr_admissible T relname basesort input ->
    @formula_expr_admissible T relname basesort formula ->
    @query_expr_admissible T relname basesort
      (QExpr_Filter formula input).
```

## `query_expr_admissible_group_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:257`](../GroupingRewriteFacts.v#L257)

Purpose/direction: States the query expr admissible group intro law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_group_intro` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Lemma query_expr_admissible_group_intro :
  forall select_list group_terms having input,
    @query_expr_admissible T relname basesort input ->
    @formula_expr_admissible T relname basesort having ->
    query_select_list_outputs_unique select_list ->
    @query_expr_admissible T relname basesort
      (QExpr_Group select_list group_terms having input).
```

## `query_expr_admissible_grouping_sets_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:266`](../GroupingRewriteFacts.v#L266)

Purpose/direction: States the query expr admissible grouping sets intro law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_grouping_sets_intro` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`

```rocq
Lemma query_expr_admissible_grouping_sets_intro :
  forall grouping_sets input,
    @query_expr_admissible T relname basesort input ->
    query_grouping_sets_well_formed grouping_sets ->
    @query_expr_admissible T relname basesort
      (QExpr_GroupingSets grouping_sets input).
```

## `query_expr_admissible_distinct_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:274`](../GroupingRewriteFacts.v#L274)

Purpose/direction: States the query expr admissible distinct intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_distinct_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`

```rocq
Lemma query_expr_admissible_distinct_intro :
  forall input,
    @query_expr_admissible T relname basesort input ->
    @query_expr_admissible T relname basesort (QExpr_Distinct input).
```

## `query_expr_admissible_offset_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:280`](../GroupingRewriteFacts.v#L280)

Purpose/direction: States the query expr admissible offset intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_offset_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `OFFSET`

```rocq
Lemma query_expr_admissible_offset_intro :
  forall count input,
    @query_expr_admissible T relname basesort input ->
    @query_expr_admissible T relname basesort (QExpr_Offset count input).
```

## `query_expr_admissible_fetch_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:286`](../GroupingRewriteFacts.v#L286)

Purpose/direction: States the query expr admissible fetch intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_fetch_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `FETCH`, `LIMIT`

```rocq
Lemma query_expr_admissible_fetch_intro :
  forall count input,
    @query_expr_admissible T relname basesort input ->
    @query_expr_admissible T relname basesort (QExpr_Fetch count input).
```

## `query_expr_admissible_order_by_intro`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:292`](../GroupingRewriteFacts.v#L292)

Purpose/direction: States the query expr admissible order by intro law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_order_by_intro` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `ORDER BY`, `ordered observation`

```rocq
Lemma query_expr_admissible_order_by_intro :
  forall keys input,
    @query_expr_admissible T relname basesort input ->
    query_sort_keys_in_scope (query_expr_sort input) keys ->
    @query_expr_admissible T relname basesort (QExpr_OrderBy keys input).
```

## `query_expr_group_outcome_equiv_of_global_having`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:195`](../OrderedQueryFacts.v#L195)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 40), `grouping` (rank 26), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_outcome_equiv_of_global_having :
  forall env select_list group_terms left_having right_having input,
    @formula_expr_global_group_outcome_equiv T relname basesort instance
      unknown contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null left_having right_having ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms left_having input) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms left_having input)
      (QExpr_Group select_list group_terms right_having input).
```

## `tnull_eval_groups_having_key_conj_filter_exact`

Source: [`theories/FormalSQL/ProofAgentFacade.v:140`](../ProofAgentFacade.v#L140)

Purpose/direction: States the tnull eval groups having key conj filter exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_eval_groups_having_key_conj_filter_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 6), `grouping` (rank 2), `filter` (rank 2)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma tnull_eval_groups_having_key_conj_filter_exact :
  forall db env select group_terms key_formula rest_having groups keep,
    TNullGroupedKeyFormulaContract
      db env group_terms key_formula groups keep ->
    TNullSkippedGroupRuntimeSafe
      db env select group_terms rest_having groups keep ->
    forall outcome,
      TNullEvalGroupsOutcome db env select group_terms
        (FExpr_Conj And_F key_formula rest_having) groups outcome <->
      TNullEvalGroupsOutcome db env select group_terms rest_having
        (filter keep groups) outcome.
```

## `tnull_eval_groups_having_key_conj_after_bag_filter_exact`

Source: [`theories/FormalSQL/ProofAgentFacade.v:165`](../ProofAgentFacade.v#L165)

Purpose/direction: States the tnull eval groups having key conj after bag filter exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 6), `grouping` (rank 2), `filter` (rank 2), `bag` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_eval_groups_having_key_conj_after_bag_filter_exact :
  forall db env select group_terms key_formula rest_having rows
      bag_formula keep_key,
    group_terms <> nil ->
    TNullBagFormulaGroupKeyLink
      db env group_terms bag_formula key_formula rows keep_key ->
    TNullSkippedGroupRuntimeSafe db env select group_terms rest_having
      (@query_make_groups TNull env rows group_terms)
      (TNullGroupedKeyKeep env group_terms keep_key) ->
    forall outcome,
      TNullEvalGroupsOutcome db env select group_terms
        (FExpr_Conj And_F key_formula rest_having)
        (@query_make_groups TNull env rows group_terms) outcome <->
      TNullEvalGroupsOutcome db env select group_terms rest_having
        (@query_make_groups TNull env
          (filter (TNullBagFormulaRowKeep db env bag_formula) rows)
          group_terms) outcome.
```
