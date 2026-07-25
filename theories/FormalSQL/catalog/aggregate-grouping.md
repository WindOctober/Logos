# Aggregates, modifiers, grouping, and aggregate errors

Route here for: COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality.

This focused catalog contains 166 declarations routed at declaration granularity from `AggregateRuntimeFacts.v`, `GroupedFilterOutcomeFacts.v`, `GroupingRewriteFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

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

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 46)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 40)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Cross-index: `grouping` (rank 34), `runtime` (rank 46)

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

Cross-index: `grouping` (rank 34)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_membership :
  forall quantifier value values,
    In value (aggregate_input_values quantifier values) <-> In value values.
```

## `aggregate_input_values_preserves_Forall`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:349`](../AggregateRuntimeFacts.v#L349)

Purpose/direction: Transports an arbitrary pointwise input property through ALL or DISTINCT aggregate input selection.

Applicability: Use for properties insensitive to occurrence removal; DISTINCT may discard duplicates but cannot introduce a new value.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_preserves_Forall :
  forall quantifier (P : value -> Prop) values,
    Forall P values ->
    Forall P (aggregate_input_values quantifier values).
```

## `non_null_count_eq_length_of_Forall_nonnull`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:363`](../AggregateRuntimeFacts.v#L363)

Purpose/direction: Computes aggregate non-NULL count as the exact list length when every input value is proved non-NULL.

Applicability: Use only with an explicit `Forall` non-NULL proof; SQL NULL inputs would otherwise be omitted by the count.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 12), `cardinality` (rank 8), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `cardinality`

```rocq
Lemma non_null_count_eq_length_of_Forall_nonnull :
  forall values,
    Forall (fun value => is_null_value value = false) values ->
    non_null_count values = Z.of_nat (List.length values).
```

## `distinct_values_fixed_of_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:376`](../AggregateRuntimeFacts.v#L376)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:387`](../AggregateRuntimeFacts.v#L387)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:394`](../AggregateRuntimeFacts.v#L394)

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34), `cardinality` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `cardinality`

```rocq
Lemma aggregate_input_values_length_le : forall quantifier values,
  (List.length (aggregate_input_values quantifier values) <=
   List.length values)%nat.
```

## `aggregate_input_values_distinct_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:402`](../AggregateRuntimeFacts.v#L402)

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 34), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma aggregate_input_values_distinct_nodup : forall values,
  NoDup (aggregate_input_values AggregateDistinct values).
```

## `aggregate_distinct_input_Permutation_of_NoDup_support`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:411`](../AggregateRuntimeFacts.v#L411)

Purpose/direction: Identifies DISTINCT aggregate selection, up to permutation, with any duplicate-free list having exactly the original value support.

Applicability: Use only after supplying both duplicate-freedom and exact support equivalence; neither premise follows from cardinality alone.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 6), `bag` (rank 8)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem aggregate_distinct_input_Permutation_of_NoDup_support :
  forall values selected,
    NoDup selected ->
    (forall value, In value selected <-> In value values) ->
    Permutation
      (aggregate_input_values AggregateDistinct values)
      (aggregate_input_values AggregateAll selected).
```

## `aggregate_input_values_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:429`](../AggregateRuntimeFacts.v#L429)

Purpose/direction: Shows that the declared aggregate evaluation result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 34), `bag` (rank 44)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:441`](../AggregateRuntimeFacts.v#L441)

Purpose/direction: Establishes idempotence for the declared aggregate evaluation operator.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_idempotent` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_idempotent : forall quantifier values,
  aggregate_input_values quantifier
    (aggregate_input_values quantifier values) =
  aggregate_input_values quantifier values.
```

## `interp_aggregate_call_selected_input_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:451`](../AggregateRuntimeFacts.v#L451)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 34)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:462`](../AggregateRuntimeFacts.v#L462)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 34), `runtime` (rank 52)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:475`](../AggregateRuntimeFacts.v#L475)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 34), `bag` (rank 44)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:490`](../AggregateRuntimeFacts.v#L490)

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 34), `runtime` (rank 52), `bag` (rank 44)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:507`](../AggregateRuntimeFacts.v#L507)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_preserves_all_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping` (rank 34), `scalar` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma aggregate_input_values_preserves_all_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  Forall (fun value => is_null_value value = true)
    (aggregate_input_values quantifier values).
```

## `aggregate_filter_input_membership`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:524`](../AggregateRuntimeFacts.v#L524)

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_filter_input_membership` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34), `filter` (rank 46)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma aggregate_filter_input_membership :
  forall predicate quantifier value values,
    In value (aggregate_filter_input predicate quantifier values) <->
    In value values /\ predicate value = true.
```

## `aggregate_filter_input_distinct_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:535`](../AggregateRuntimeFacts.v#L535)

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 34), `filter` (rank 46), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `filter`, `WHERE`, `multiplicity`

```rocq
Lemma aggregate_filter_input_distinct_nodup : forall predicate values,
  NoDup (aggregate_filter_input predicate AggregateDistinct values).
```

## `aggregate_filter_input_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:542`](../AggregateRuntimeFacts.v#L542)

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34), `filter` (rank 46), `cardinality` (rank 40)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma aggregate_filter_input_length_le :
  forall predicate quantifier values,
    (List.length (aggregate_filter_input predicate quantifier values) <=
     List.length values)%nat.
```

## `aggregate_filter_input_false_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:553`](../AggregateRuntimeFacts.v#L553)

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_filter_input_false_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 34), `filter` (rank 46)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma aggregate_filter_input_false_empty : forall quantifier values,
  aggregate_filter_input (fun _ => false) quantifier values = [].
```

## `count_star_value_of_row_count_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:567`](../AggregateRuntimeFacts.v#L567)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:584`](../AggregateRuntimeFacts.v#L584)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:609`](../AggregateRuntimeFacts.v#L609)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:624`](../AggregateRuntimeFacts.v#L624)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:642`](../AggregateRuntimeFacts.v#L642)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:666`](../AggregateRuntimeFacts.v#L666)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:688`](../AggregateRuntimeFacts.v#L688)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:712`](../AggregateRuntimeFacts.v#L712)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:717`](../AggregateRuntimeFacts.v#L717)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:722`](../AggregateRuntimeFacts.v#L722)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:727`](../AggregateRuntimeFacts.v#L727)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:745`](../AggregateRuntimeFacts.v#L745)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:764`](../AggregateRuntimeFacts.v#L764)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:782`](../AggregateRuntimeFacts.v#L782)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:787`](../AggregateRuntimeFacts.v#L787)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:792`](../AggregateRuntimeFacts.v#L792)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:810`](../AggregateRuntimeFacts.v#L810)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:828`](../AggregateRuntimeFacts.v#L828)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:835`](../AggregateRuntimeFacts.v#L835)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:842`](../AggregateRuntimeFacts.v#L842)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:866`](../AggregateRuntimeFacts.v#L866)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:890`](../AggregateRuntimeFacts.v#L890)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:897`](../AggregateRuntimeFacts.v#L897)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:904`](../AggregateRuntimeFacts.v#L904)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:911`](../AggregateRuntimeFacts.v#L911)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:916`](../AggregateRuntimeFacts.v#L916)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:940`](../AggregateRuntimeFacts.v#L940)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:964`](../AggregateRuntimeFacts.v#L964)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:988`](../AggregateRuntimeFacts.v#L988)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1006`](../AggregateRuntimeFacts.v#L1006)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1014`](../AggregateRuntimeFacts.v#L1014)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1040`](../AggregateRuntimeFacts.v#L1040)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1045`](../AggregateRuntimeFacts.v#L1045)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1050`](../AggregateRuntimeFacts.v#L1050)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1068`](../AggregateRuntimeFacts.v#L1068)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1086`](../AggregateRuntimeFacts.v#L1086)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1097`](../AggregateRuntimeFacts.v#L1097)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1120`](../AggregateRuntimeFacts.v#L1120)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1131`](../AggregateRuntimeFacts.v#L1131)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1155`](../AggregateRuntimeFacts.v#L1155)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1165`](../AggregateRuntimeFacts.v#L1165)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1175`](../AggregateRuntimeFacts.v#L1175)

Purpose/direction: Shows that empty selected input yields SQL NULL with no SINGLE_VALUE runtime error.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: every explicit antecedent (`->`) in the declaration is required; the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 34), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1189`](../AggregateRuntimeFacts.v#L1189)

Purpose/direction: Shows that singleton selected input returns its INT32 value with no SINGLE_VALUE runtime error.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: every explicit antecedent (`->`) in the declaration is required; the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 34), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1204`](../AggregateRuntimeFacts.v#L1204)

Purpose/direction: Characterizes CardinalityViolation exactly as at least two selected INT32 values.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 34), `runtime` (rank 52), `cardinality` (rank 38), `scalar` (rank 44)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1220`](../AggregateRuntimeFacts.v#L1220)

Purpose/direction: States the exact empty-input or empty-result law for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_empty_shape` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 26)

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1262`](../AggregateRuntimeFacts.v#L1262)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome` (rank 52), `grouping` (rank 28), `runtime` (rank 52), `bag` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_grouping_sets_nil_outcome_iff : forall env input_bag outcome,
  eval_grouping_sets_bag env [] input_bag outcome <->
  outcome =
    SqlSuccess (Febag.empty (Fecol.CBag (Tuple.CTuple T))).
```

## `eval_grouping_sets_cons_success_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1272`](../AggregateRuntimeFacts.v#L1272)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 52), `grouping` (rank 28), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1290`](../AggregateRuntimeFacts.v#L1290)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 52), `grouping` (rank 28), `runtime` (rank 48)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

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

## `eval_grouping_sets_outcome_Forall2_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1342`](../AggregateRuntimeFacts.v#L1342)

Purpose/direction: Lifts branchwise exact outcome agreement through an arbitrary ordered GROUPING SETS schedule without moving its first error.

Applicability: Use for arbitrary grouping-set lists in their original order.  Branch order is semantic for runtime errors and must not be replaced by a permutation premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 0), `grouping` (rank 0), `runtime` (rank 0)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem eval_grouping_sets_outcome_Forall2_congr :
  forall env input_bag left_sets right_sets,
    Forall2 (grouping_set_exact_outcome_at env input_bag)
      left_sets right_sets ->
    forall outcome,
      eval_grouping_sets_bag env left_sets input_bag outcome <->
      eval_grouping_sets_bag env right_sets input_bag outcome.
```

## `eval_grouping_sets_success_fold_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1386`](../AggregateRuntimeFacts.v#L1386)

Purpose/direction: Characterizes every successful GROUPING SETS schedule as the ordered UNION ALL fold of one successful bag per branch.

Applicability: Use for arbitrary grouping-set lists in their original order.  Branch order is semantic for runtime errors and must not be replaced by a permutation premise.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 2)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`

```rocq
Theorem eval_grouping_sets_success_fold_iff :
  forall env input_bag grouping_sets output_bag,
    eval_grouping_sets_bag env grouping_sets input_bag
      (SqlSuccess output_bag) <->
    exists branch_bags,
      Forall2 (grouping_set_success_at env input_bag)
        grouping_sets branch_bags /\
      output_bag = grouping_sets_union_fold branch_bags.
```

## `eval_grouping_sets_error_prefix_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1428`](../AggregateRuntimeFacts.v#L1428)

Purpose/direction: Characterizes a GROUPING SETS error by an ordered prefix of successful branches followed by the exact failing branch.

Applicability: Use for arbitrary grouping-set lists in their original order.  Branch order is semantic for runtime errors and must not be replaced by a permutation premise.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping` (rank 4), `runtime` (rank 4)

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
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
```

## `query_make_groups_support_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:23`](../GroupedFilterOutcomeFacts.v#L23)

Purpose/direction: States the query make groups support exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_support_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 26)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Lemma query_make_groups_support_exact :
  forall env rows group_terms row,
    group_terms <> nil ->
    In row rows <->
    exists group,
      In group (@query_make_groups T env rows group_terms) /\
      In row group.
```

## `query_make_groups_support_rel`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:57`](../GroupedFilterOutcomeFacts.v#L57)

Purpose/direction: States the query make groups support rel law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_support_rel` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 24), `bag` (rank 50)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_make_groups_support_rel :
  forall (R : tuple T -> tuple T -> Prop) env rows group_terms
      (emit : list (tuple T) -> tuple T),
    group_terms <> nil ->
    (forall group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      R row (emit group)) ->
    list_support_rel R rows
      (map emit (@query_make_groups T env rows group_terms)).
```

## `query_make_groups_emit_NoDupA_of_key_reflection`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:101`](../GroupedFilterOutcomeFacts.v#L101)

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_emit_NoDupA_of_key_reflection` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_emit_NoDupA_of_key_reflection :
  forall env rows group_terms
      (emit : list (tuple T) -> tuple T),
    group_terms <> nil ->
    (forall left_group left_row right_group right_row,
      In left_group (@query_make_groups T env rows group_terms) ->
      In left_row left_group ->
      In right_group (@query_make_groups T env rows group_terms) ->
      In right_row right_group ->
      Oeset.compare (OTuple T) (emit left_group) (emit right_group) = Eq ->
      query_grouping_key env group_terms left_row =
      query_grouping_key env group_terms right_row) ->
    SetoidList.NoDupA
      (fun left right => Oeset.compare (OTuple T) left right = Eq)
      (map emit (@query_make_groups T env rows group_terms)).
```

## `query_make_groups_projected_bag_eq_of_support_rel`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:207`](../GroupedFilterOutcomeFacts.v#L207)

Purpose/direction: States the query make groups projected bag equality of support rel law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 4), `bag` (rank 6)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_make_groups_projected_bag_eq_of_support_rel :
  forall env group_terms
      (project : tuple T -> tuple T)
      (emit : list (tuple T) -> tuple T)
      left_rows right_rows,
    group_terms <> nil ->
    (forall rows group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (emit group) = Eq) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env group_terms left =
      query_grouping_key env group_terms right) ->
    list_support_rel
      (fun left right =>
        Oeset.compare (OTuple T) (project left) (project right) = Eq)
      left_rows right_rows ->
    bag_eq T
      (rows_bag T
        (map emit (@query_make_groups T env left_rows group_terms)))
      (rows_bag T
        (map emit (@query_make_groups T env right_rows group_terms))).
```

## `oeset_permut_support_rel`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:292`](../GroupedFilterOutcomeFacts.v#L292)

Purpose/direction: States the oeset permut support rel law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `oeset_permut_support_rel` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `bag semantics`, `list/bag bridge`

```rocq
Lemma oeset_permut_support_rel :
  forall (A : Type) (ordered : Oeset.Rcd A) left right,
    Oeset.permut ordered left right ->
    list_support_rel
      (fun first second => Oeset.compare ordered first second = Eq)
      left right.
```

## `rows_bag_eq_implies_permut`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:329`](../GroupedFilterOutcomeFacts.v#L329)

Purpose/direction: States the rows bag equality implies permut law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `bag` (rank 42)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_eq_implies_permut :
  forall (T : Tuple.Rcd) left right,
    bag_eq T (rows_bag T left) (rows_bag T right) ->
    Oeset.permut (OTuple T) left right.
```

## `query_same_rows_as_bag_permut_between`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:342`](../GroupedFilterOutcomeFacts.v#L342)

Purpose/direction: Bridges the two displayed representations of aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_permut_between :
  forall (T : Tuple.Rcd) first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    Oeset.permut (OTuple T) first second.
```

## `formula_acceptance_exact_total_success`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:396`](../GroupedFilterOutcomeFacts.v#L396)

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

## `formula_true_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:406`](../GroupedFilterOutcomeFacts.v#L406)

Purpose/direction: States the formula true acceptance exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_true_acceptance_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma formula_true_acceptance_exact :
  forall env,
    formula_acceptance_exact_at env FExpr_True true.
```

## `acceptance_interp_conj_is_true`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:472`](../GroupedFilterOutcomeFacts.v#L472)

Purpose/direction: States the acceptance interp conj is true law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `acceptance_interp_conj_is_true` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma acceptance_interp_conj_is_true :
  forall operation left right,
    Bool.is_true (B T) (interp_conj (B T) operation left right) =
    acceptance_interp_conj operation
      (Bool.is_true (B T) left) (Bool.is_true (B T) right).
```

## `formula_conj_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:486`](../GroupedFilterOutcomeFacts.v#L486)

Purpose/direction: Composes exact TRUE-acceptance contracts through eager SQL AND or OR without identifying the underlying FALSE and UNKNOWN values.

Applicability: Use after proving exact acceptance for both eager children; the conclusion combines only their `Bool.is_true` decisions, not their underlying SQL FALSE/UNKNOWN values.

Important premises: Both displayed child exact-acceptance contracts are mandatory because FormalSQL evaluates the right child eagerly for both AND and OR.

Cross-index: `grouping` (rank 34), `filter` (rank 38), `scalar` (rank 20)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `predicate`, `Bool3`

```rocq
Theorem formula_conj_acceptance_exact :
  forall env operation left right left_accepted right_accepted,
    formula_acceptance_exact_at env left left_accepted ->
    formula_acceptance_exact_at env right right_accepted ->
    formula_acceptance_exact_at env
      (FExpr_Conj operation left right)
      (acceptance_interp_conj operation left_accepted right_accepted).
```

## `formula_and_success_intro`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:528`](../GroupedFilterOutcomeFacts.v#L528)

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:538`](../GroupedFilterOutcomeFacts.v#L538)

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:549`](../GroupedFilterOutcomeFacts.v#L549)

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:580`](../GroupedFilterOutcomeFacts.v#L580)

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:597`](../GroupedFilterOutcomeFacts.v#L597)

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

## `eval_groups_success_Forall_projection`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1190`](../GroupedFilterOutcomeFacts.v#L1190)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_success_Forall_projection` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 6), `projection` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `projection`, `SELECT list`

```rocq
Theorem eval_groups_success_Forall_projection :
  forall env select_list group_terms having groups output
      (P : tuple T -> Prop),
    (forall group,
      In group groups ->
      P (group_projection env select_list group_terms group)) ->
    eval_groups env select_list group_terms having groups
      (SqlSuccess output) ->
    Forall P output.
```

## `eval_groups_global_success_length_le_one`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1218`](../GroupedFilterOutcomeFacts.v#L1218)

Purpose/direction: Provides the stated reusable upper bound for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_global_success_length_le_one` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 34)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem eval_groups_global_success_length_le_one :
  forall env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    (length output <= 1)%nat.
```

## `eval_groups_global_success_NoDupA`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1235`](../GroupedFilterOutcomeFacts.v#L1235)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_global_success_NoDupA` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 34)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem eval_groups_global_success_NoDupA :
  forall (R : tuple T -> tuple T -> Prop)
      env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    SetoidList.NoDupA R output.
```

## `eval_group_bag_success_occurrence_property`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1257`](../GroupedFilterOutcomeFacts.v#L1257)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate grouping.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome` (rank 50), `grouping` (rank 8), `runtime` (rank 50), `bag` (rank 12)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_group_bag_success_occurrence_property :
  forall env select_list group_terms having input_bag output_bag
      (P : tuple T -> Prop),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      P left -> P right) ->
    (forall representative,
      query_same_rows_as_bag representative input_bag ->
      forall group,
        In group
          (@query_make_groups T env
            (query_canonical_rows representative) group_terms) ->
        P (group_projection env select_list group_terms group)) ->
    eval_group_bag env select_list group_terms having input_bag
      (SqlSuccess output_bag) ->
    forall row,
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row output_bag <> 0%N ->
      P row.
```

## `group_execution_observation_equiv_sym`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1345`](../GroupedFilterOutcomeFacts.v#L1345)

Purpose/direction: Reverses a proved aggregate grouping relation.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 36)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `equivalence`, `congruence`

```rocq
Lemma group_execution_observation_equiv_sym :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_group right_group,
    group_execution_observation_equiv
      left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_group right_group ->
    group_execution_observation_equiv
      right_env right_select right_group_terms right_having
      left_env left_select left_group_terms left_having
      right_group left_group.
```

## `eval_groups_outcome_Forall2_congr_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1374`](../GroupedFilterOutcomeFacts.v#L1374)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 52), `grouping` (rank 36), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_groups_outcome_Forall2_congr_forward :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_groups right_groups,
    Forall2
      (group_execution_observation_equiv
        left_env left_select left_group_terms left_having
        right_env right_select right_group_terms right_having)
      left_groups right_groups ->
    forall left_outcome,
      eval_groups left_env left_select left_group_terms left_having
        left_groups left_outcome ->
      exists right_outcome,
        eval_groups right_env right_select right_group_terms right_having
          right_groups right_outcome /\
        outcome_equiv (Oeset.permut (OTuple T))
          left_outcome right_outcome.
```

## `eval_groups_outcome_Forall2_congr`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1497`](../GroupedFilterOutcomeFacts.v#L1497)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 50), `grouping` (rank 34), `runtime` (rank 50)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem eval_groups_outcome_Forall2_congr :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_groups right_groups,
    Forall2
      (group_execution_observation_equiv
        left_env left_select left_group_terms left_having
        right_env right_select right_group_terms right_having)
      left_groups right_groups ->
    (exists outcome,
      eval_groups left_env left_select left_group_terms left_having
        left_groups outcome) ->
    outcome_relation_equiv (Oeset.permut (OTuple T))
      (eval_groups left_env left_select left_group_terms left_having
        left_groups)
      (eval_groups right_env right_select right_group_terms right_having
        right_groups).
```

## `eval_groups_true_outcome_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1581`](../GroupedFilterOutcomeFacts.v#L1581)

Purpose/direction: Characterizes all-TRUE evaluation in each `group_env` exactly as the ordered projection map after all four per-group runtime checks, including as the group-processing component of a regrouping proof.

Applicability: Use when every reached HAVING decision is exactly TRUE and each of the four displayed per-group checks is safe; the conclusion is an ordered map and keeps duplicate group occurrences.

Important premises: For every reached group retain SELECT aggregate safety, HAVING aggregate safety, exact TRUE acceptance, and scalar SELECT safety; do not replace the resulting list map by a bag or set.

Cross-index: `outcome` (rank 50), `grouping` (rank 22), `runtime` (rank 50)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem eval_groups_true_outcome_exact :
  forall env select_list group_terms having groups,
    (forall group,
      In group groups ->
      eval_select_aggregates
        (group_env env group_terms group) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms group) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms group) having true /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (group_env env group_terms group) select_list = None) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess
        (map (group_projection env select_list group_terms) groups).
```

## `eval_groups_acceptance_outcome_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1673`](../GroupedFilterOutcomeFacts.v#L1673)

Purpose/direction: Characterizes arbitrary exact HAVING acceptance in each `group_env` as the ordered projection map over `List.filter`, retaining duplicate groups and requiring scalar SELECT safety only for accepted groups.

Applicability: Use after choosing a Boolean `keep` for every reached group and proving exact HAVING acceptance plus eager aggregate safety; the result is literally `map projection (filter keep groups)`.

Important premises: For every reached group retain SELECT and HAVING aggregate safety and exact acceptance/no-error evidence; scalar SELECT safety is mandatory exactly when `keep group = true`.

Cross-index: `outcome` (rank 20), `grouping` (rank 18), `runtime` (rank 22)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem eval_groups_acceptance_outcome_exact :
  forall env select_list group_terms having groups keep,
    (forall group,
      In group groups ->
      eval_select_aggregates
        (group_env env group_terms group) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms group) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms group) having (keep group) /\
      (keep group = true ->
        @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (group_env env group_terms group) select_list = None)) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess
        (map (group_projection env select_list group_terms)
          (filter keep groups)).
```

## `grouped_key_formula_contract_tail`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1831`](../GroupedFilterOutcomeFacts.v#L1831)

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1841`](../GroupedFilterOutcomeFacts.v#L1841)

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1853`](../GroupedFilterOutcomeFacts.v#L1853)

Purpose/direction: States the eval groups having key conj filter exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_having_key_conj_filter_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 6), `filter` (rank 8)

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

## `eval_group_bag_exact_rows_permut_equiv`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:2051`](../GroupedFilterOutcomeFacts.v#L2051)

Purpose/direction: Lifts exact per-representative group evaluation through the quotient-saturated group-bag reset when emitted rows are semantic permutations, preserving key and processing errors.

Applicability: Use at a `QExpr_Group` bag reset after characterizing `eval_groups` for every legal representative and proving the two emitted row functions permutation-equivalent.

Important premises: Both exact contracts quantify over every bag representative and include group-key safety; the cross-representative output permutation premise may not be weakened to support equality.

Cross-index: `outcome` (rank 50), `grouping` (rank 8), `runtime` (rank 50), `bag` (rank 18)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem eval_group_bag_exact_rows_permut_equiv :
  forall env select_list group_terms left_having right_having
      (left_bag right_bag :
        Febag.bag (Fecol.CBag (Tuple.CTuple T)))
      (left_rows right_rows :
        list (list (tuple T)) -> list (tuple T)),
    (forall representative,
      query_same_rows_as_bag representative left_bag ->
      let canonical := query_canonical_rows representative in
      let groups := query_make_groups env canonical group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms canonical = None /\
      forall outcome,
        eval_groups env select_list group_terms left_having groups outcome <->
        outcome = SqlSuccess (left_rows groups)) ->
    (forall representative,
      query_same_rows_as_bag representative right_bag ->
      let canonical := query_canonical_rows representative in
      let groups := query_make_groups env canonical group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms canonical = None /\
      forall outcome,
        eval_groups env select_list group_terms right_having groups outcome <->
        outcome = SqlSuccess (right_rows groups)) ->
    (forall left_representative right_representative,
      query_same_rows_as_bag left_representative left_bag ->
      query_same_rows_as_bag right_representative right_bag ->
      Oeset.permut (OTuple T)
        (left_rows
          (query_make_groups env
            (query_canonical_rows left_representative) group_terms))
        (right_rows
          (query_make_groups env
            (query_canonical_rows right_representative) group_terms))) ->
    forall outcome,
      eval_group_bag env select_list group_terms left_having left_bag outcome <->
      eval_group_bag env select_list group_terms right_having right_bag outcome.
```

## `eval_group_bag_true_projected_support_equiv`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:2198`](../GroupedFilterOutcomeFacts.v#L2198)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 8), `grouping` (rank 4), `runtime` (rank 50), `bag` (rank 50)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem eval_group_bag_true_projected_support_equiv :
  forall env select_list group_terms
      (project : tuple T -> tuple T) left_rows right_rows,
    group_terms <> nil ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (project first) (project second) = Eq) ->
    (forall rows group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row)
        (group_projection env select_list group_terms group) = Eq) ->
    (forall first second,
      Oeset.compare (OTuple T) (project first) (project second) = Eq ->
      query_grouping_key env group_terms first =
      query_grouping_key env group_terms second) ->
    (forall rows,
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms rows = None) ->
    (forall rows group,
      In group (@query_make_groups T env rows group_terms) ->
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (env_g T env (@Group_By T group_terms) group) select_list = None /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (env_g T env (@Group_By T group_terms) group) select_list = None) ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) (project first) (project second) = Eq)
      left_rows right_rows ->
    forall outcome,
      eval_group_bag env select_list group_terms FExpr_True
        (rows_bag T left_rows) outcome <->
      eval_group_bag env select_list group_terms FExpr_True
        (rows_bag T right_rows) outcome.
```

## `query_expr_group_outcome_equiv_of_supported_child_outcomes`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:2355`](../GroupedFilterOutcomeFacts.v#L2355)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 4), `grouping` (rank 4), `runtime` (rank 50), `bag` (rank 50)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_outcome_equiv_of_supported_child_outcomes :
  forall env select_list group_terms having left right
      (supported : list (tuple T) -> list (tuple T) -> Prop),
    query_expr_outputs
      (QExpr_Group select_list group_terms having left) =
    query_expr_outputs
      (QExpr_Group select_list group_terms having right) ->
    (exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group select_list group_terms having left) outcome) ->
    (forall left_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null env right
          (SqlSuccess right_rows) /\
        supported left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null env left
          (SqlSuccess left_rows) /\
        supported left_rows right_rows) ->
    (forall error,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlError error) <->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlError error)) ->
    (forall left_rows right_rows,
      supported left_rows right_rows ->
      forall outcome,
        eval_group_bag env select_list group_terms having
          (rows_bag T left_rows) outcome <->
        eval_group_bag env select_list group_terms having
          (rows_bag T right_rows) outcome) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
```

## `filter_insert_in_partition_by_key`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:23`](../GroupingRewriteFacts.v#L23)

Purpose/direction: States the filter insert in partition by key law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `filter_insert_in_partition_by_key` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 36), `filter` (rank 46)

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

Cross-index: `grouping` (rank 36), `filter` (rank 46)

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

Cross-index: `grouping` (rank 34), `filter` (rank 44)

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

Cross-index: `grouping` (rank 36), `filter` (rank 46)

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

Cross-index: `grouping` (rank 34), `filter` (rank 44)

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

## `partition_map_heterogeneous`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:157`](../GroupingRewriteFacts.v#L157)

Purpose/direction: States the partition map heterogeneous law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `partition_map_heterogeneous` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 34)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Theorem partition_map_heterogeneous :
  forall (A B Key : Type) (key_order : Oset.Rcd Key)
      (keyA : A -> Key) (keyB : B -> Key) (emit : A -> B) rows,
    (forall row, In row rows -> keyB (emit row) = keyA row) ->
    @Partition.partition B Key key_order keyB (map emit rows) =
    map (fun group => (fst group, map emit (snd group)))
      (@Partition.partition A Key key_order keyA rows).
```

## `list_permut_eq_implies_Permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:189`](../GroupingRewriteFacts.v#L189)

Purpose/direction: States the list permut equality implies permutation law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 36), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_permut_eq_implies_Permutation :
  forall (A : Type) (left right : list A),
    ListPermut._permut (@eq A) left right ->
    Sorting.Permutation.Permutation left right.
```

## `partition_keys_Permutation_of_NoDup_support`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:228`](../GroupingRewriteFacts.v#L228)

Purpose/direction: Identifies the keys materialized by generic partitioning with any duplicate-free same-support key representative, up to permutation.

Applicability: Use only after supplying both duplicate-freedom and exact support equivalence; neither premise follows from cardinality alone.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 8), `bag` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem partition_keys_Permutation_of_NoDup_support :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows selected,
    NoDup selected ->
    (forall key, In key selected <-> In key (map key_of rows)) ->
    Sorting.Permutation.Permutation
      (map fst (@Partition.partition A Key key_order key_of rows))
      selected.
```

## `partition_member_exact_key_filter`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:506`](../GroupingRewriteFacts.v#L506)

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `partition_member_exact_key_filter` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 34), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Theorem partition_member_exact_key_filter :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows key members,
    In (key, members)
      (@Partition.partition A Key key_order key_of rows) ->
    members =
      rev
        (filter
          (fun row => Oset.eq_bool key_order (key_of row) key)
          rows).
```

## `partition_factored_key_refinement_Forall2`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:654`](../GroupingRewriteFacts.v#L654)

Purpose/direction: States the partition factored key refinement forall2 law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `partition_factored_key_refinement_Forall2` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 34)

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Theorem partition_factored_key_refinement_Forall2 :
  forall (A Fine Coarse : Type)
      (fine_order : Oset.Rcd Fine) (coarse_order : Oset.Rcd Coarse)
      (fine_key : A -> Fine) (coarse_key : A -> Coarse)
      (factor : Fine -> Coarse) rows,
    (forall row, In row rows -> coarse_key row = factor (fine_key row)) ->
    Forall2
      (fun coarse_group refined_group =>
        fst coarse_group = fst refined_group /\
        Sorting.Permutation.Permutation
          (snd coarse_group)
          (concat (map snd (snd refined_group))))
      (@Partition.partition A Coarse coarse_order coarse_key rows)
      (@Partition.partition (Fine * list A) Coarse coarse_order
        (fun fine_group => factor (fst fine_group))
        (@Partition.partition A Fine fine_order fine_key rows)).
```

## `query_make_groups_map_heterogeneous`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:712`](../GroupingRewriteFacts.v#L712)

Purpose/direction: States the query make groups map heterogeneous law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_map_heterogeneous` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_map_heterogeneous :
  forall (T : Tuple.Rcd) (A : Type) env group_terms
      (keyA : A -> list (value T)) (emit : A -> tuple T) rows,
    group_terms <> nil ->
    (forall item, In item rows ->
      query_grouping_key env group_terms (emit item) = keyA item) ->
    @query_make_groups T env (map emit rows) group_terms =
    map (fun keyed => map emit (snd keyed))
      (@Partition.partition A (list (value T))
        (OrderedSet.mk_olists (OVal T)) keyA rows).
```

## `query_make_groups_factored_refinement_Forall2`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:754`](../GroupingRewriteFacts.v#L754)

Purpose/direction: States the query make groups factored refinement forall2 law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_factored_refinement_Forall2` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_factored_refinement_Forall2 :
  forall (T : Tuple.Rcd) (env : Env.env T) rows
      fine_terms coarse_terms
      (factor : list (value T) -> list (value T)),
    fine_terms <> nil ->
    coarse_terms <> nil ->
    (forall row, In row rows ->
      query_grouping_key env coarse_terms row =
      factor (query_grouping_key env fine_terms row)) ->
    Forall2 (@Sorting.Permutation.Permutation (tuple T))
      (@query_make_groups T env rows coarse_terms)
      (map
        (fun coarse_group => concat (snd coarse_group))
        (@Partition.partition
          (list (tuple T)) (list (value T))
          (OrderedSet.mk_olists (OVal T))
          (fun fine_group =>
            factor (query_grouping_head_key env fine_terms fine_group))
          (@query_make_groups T env rows fine_terms))).
```

## `query_make_groups_filter_by_key_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:857`](../GroupingRewriteFacts.v#L857)

Purpose/direction: States the query make groups filter by key exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_filter_by_key_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 8), `filter` (rank 10)

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

## `query_make_groups_selected_members_permut`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:881`](../GroupingRewriteFacts.v#L881)

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_selected_members_permut` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_selected_members_permut :
  forall (T : Tuple.Rcd) env rows group_terms keep,
    group_terms <> nil ->
    Oeset.permut (OTuple T)
      (filter
        (fun row => keep (query_grouping_key env group_terms row)) rows)
      (concat
        (filter
          (fun members =>
            match members with
            | nil => false
            | row :: _ => keep (query_grouping_key env group_terms row)
            end)
          (@query_make_groups T env rows group_terms))).
```

## `query_make_groups_selected_members_Permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:917`](../GroupingRewriteFacts.v#L917)

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 24), `bag` (rank 42)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_make_groups_selected_members_Permutation :
  forall (T : Tuple.Rcd) env rows group_terms keep,
    group_terms <> nil ->
    Sorting.Permutation.Permutation
      (filter
        (fun row => keep (query_grouping_key env group_terms row)) rows)
      (concat
        (filter
          (fun members =>
            match members with
            | nil => false
            | row :: _ => keep (query_grouping_key env group_terms row)
            end)
          (@query_make_groups T env rows group_terms))).
```

## `query_make_groups_constant_nonempty_key`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:954`](../GroupingRewriteFacts.v#L954)

Purpose/direction: Computes groups for one constant nonempty grouping key as no group on empty input or one reverse-ordered member list otherwise.

Applicability: Use only with a nonempty grouping-term list and one proved key for every row; retain the literal `rev rows` and prove key runtime safety separately.

Important premises: The grouping terms must be nonempty and every input row must have the displayed key; the nonempty result is exactly `[rev rows]`.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_constant_nonempty_key :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms
      (key : list (value T)),
    group_terms <> nil ->
    (forall row,
      In row rows ->
      query_grouping_key env group_terms row = key) ->
    @query_make_groups T env rows group_terms =
      match rows with
      | nil => nil
      | _ :: _ => rev rows :: nil
      end.
```

## `query_make_groups_matching_one_key_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:977`](../GroupingRewriteFacts.v#L977)

Purpose/direction: States the query make groups matching one key exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_matching_one_key_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_matching_one_key_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms rows
      (keep : list (value T) -> bool) key,
    group_terms <> nil ->
    (forall row,
      In row
        (filter
          (fun item =>
            keep (query_grouping_key env group_terms item)) rows) ->
      query_grouping_key env group_terms row = key) ->
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (query_grouping_key env group_terms row)
        end)
      (@query_make_groups T env rows group_terms) =
    match
      filter
        (fun item =>
          keep (query_grouping_key env group_terms item)) rows
    with
    | nil => nil
    | _ :: _ =>
        [rev
          (filter
            (fun item =>
              keep (query_grouping_key env group_terms item)) rows)]
    end.
```

## `query_make_groups_members_same_key_nonempty`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1021`](../GroupingRewriteFacts.v#L1021)

Purpose/direction: States the exact empty-input or empty-result law for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_members_same_key_nonempty` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 26)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Lemma query_make_groups_members_same_key_nonempty :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms group left right,
    group_terms <> nil ->
    In group (@query_make_groups T env rows group_terms) ->
    In left group ->
    In right group ->
    query_grouping_key env group_terms left =
    query_grouping_key env group_terms right.
```

## `query_make_groups_member_exact_key_filter`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1049`](../GroupingRewriteFacts.v#L1049)

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_member_exact_key_filter` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping` (rank 24), `filter` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`

```rocq
Theorem query_make_groups_member_exact_key_filter :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms group row,
    group_terms <> nil ->
    In group (@query_make_groups T env rows group_terms) ->
    In row group ->
    group =
      rev
        (filter
          (fun item =>
            Oset.eq_bool (OrderedSet.mk_olists (OVal T))
              (query_grouping_key env group_terms item)
              (query_grouping_key env group_terms row))
          rows).
```

## `query_make_groups_member_key_filter_Permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1126`](../GroupingRewriteFacts.v#L1126)

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping` (rank 25), `filter` (rank 45), `bag` (rank 43)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_make_groups_member_key_filter_Permutation :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms group row,
    group_terms <> nil ->
    In group (@query_make_groups T env rows group_terms) ->
    In row group ->
    Sorting.Permutation.Permutation group
      (filter
        (fun item =>
          Oset.eq_bool (OrderedSet.mk_olists (OVal T))
            (query_grouping_key env group_terms item)
            (query_grouping_key env group_terms row))
        rows).
```

## `query_make_groups_global_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1149`](../GroupingRewriteFacts.v#L1149)

Purpose/direction: States the query make groups global exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_global_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 24)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_global_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) rows,
    @query_make_groups T env rows [] = [rev rows].
```

## `query_make_groups_global_length_one`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1161`](../GroupingRewriteFacts.v#L1161)

Purpose/direction: Relates aggregate grouping to the exact list length or bag cardinality shown below.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_global_length_one` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping` (rank 25)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Corollary query_make_groups_global_length_one :
  forall (T : Tuple.Rcd) (env : Env.env T) rows,
    length (@query_make_groups T env rows []) = 1%nat.
```

## `query_make_groups_permut_nonempty`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1174`](../GroupingRewriteFacts.v#L1174)

Purpose/direction: Transports semantic row permutation to semantic group permutation for a nonempty grouping-term list.

Applicability: Use when two input row lists represent the same bag and grouping terms are nonempty; the result compares whole groups semantically.

Important premises: The nonempty grouping-term premise is mandatory because the global empty grouping set has distinct empty-input semantics.

Cross-index: `grouping` (rank 12)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Lemma query_make_groups_permut_nonempty :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms left right,
    group_terms <> nil ->
    Oeset.permut (OTuple T) left right ->
    Oeset.permut (OLTuple T)
      (@query_make_groups T env left group_terms)
      (@query_make_groups T env right group_terms).
```

## `group_filter_map_permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1195`](../GroupingRewriteFacts.v#L1195)

Purpose/direction: Transports a semantic group permutation through an equality-respecting group filter and projection map while retaining occurrences.

Applicability: Use after proving both the retained-group decision and emitted row respect semantic group equality; it composes directly with exact HAVING acceptance.

Important premises: Supply semantic-equality compatibility for both `keep` and `emit`; the conclusion is occurrence-preserving permutation, not set equality.

Cross-index: `grouping` (rank 14), `filter` (rank 46), `bag` (rank 44)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma group_filter_map_permutation :
  forall (T : Tuple.Rcd) left right
      (keep : list (tuple T) -> bool)
      (emit : list (tuple T) -> tuple T),
    (forall first second,
      Oeset.compare (OLTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall first second,
      Oeset.compare (OLTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    Oeset.permut (OLTuple T) left right ->
    Oeset.permut (OTuple T)
      (map emit (filter keep left))
      (map emit (filter keep right)).
```

## `query_expr_group_outcome_equiv_of_global_having`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:616`](../OrderedQueryFacts.v#L616)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 40), `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_outcome_equiv_of_global_having :
  forall env select_list group_terms left_having right_having input,
    @formula_expr_global_group_outcome_equiv T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null left_having right_having ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms left_having input) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms left_having input)
      (QExpr_Group select_list group_terms right_having input).
```

## `eval_query_expr_group_outcome_iff_of_child_outcome_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:641`](../OrderedQueryFacts.v#L641)

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 46), `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_query_expr_group_outcome_iff_of_child_outcome_equiv :
  forall env select_list group_terms having left right,
    query_outcome_equiv env left right ->
    forall outcome,
      eval_query env
        (QExpr_Group select_list group_terms having left) outcome <->
      eval_query env
        (QExpr_Group select_list group_terms having right) outcome.
```

## `query_expr_group_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:699`](../OrderedQueryFacts.v#L699)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `grouping` (rank 30), `runtime` (rank 52)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_outcome_equiv_congr :
  forall env select_list group_terms having left right,
    query_outcome_equiv env left right ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms having left) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
```

## `tnull_eval_groups_having_key_conj_filter_exact`

Source: [`theories/FormalSQL/ProofAgentFacade.v:179`](../ProofAgentFacade.v#L179)

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

## `tnull_direct_columns_group_projection_member_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1250`](../ProofAgentFacade.v#L1250)

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_columns_group_projection_member_eq` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `grouping` (rank 16), `projection` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_columns_group_projection_member_eq :
  forall env rows columns group row,
    In group
      (@query_make_groups TNull env rows (map DotColumn columns)) ->
    In row group ->
    TNullRowEq
      (TNullProjectRow env (SelectColumns columns) row)
      (group_projection env (SelectColumns columns)
        (map DotColumn columns) group).
```

## `tnull_direct_columns_projection_reflects_grouping_key`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1295`](../ProofAgentFacade.v#L1295)

Purpose/direction: States the tnull direct columns projection reflects grouping key law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_columns_projection_reflects_grouping_key` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `grouping` (rank 12), `projection` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_columns_projection_reflects_grouping_key :
  forall env columns left right,
    select_list_has_unique_outputs (SelectColumns columns) ->
    TNullRowEq
      (TNullProjectRow env (SelectColumns columns) left)
      (TNullProjectRow env (SelectColumns columns) right) ->
    query_grouping_key env (map DotColumn columns) left =
    query_grouping_key env (map DotColumn columns) right.
```

## `tnull_direct_columns_group_projection_support_rel`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1323`](../ProofAgentFacade.v#L1323)

Purpose/direction: States the tnull direct columns group projection support rel law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_columns_group_projection_support_rel` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `grouping` (rank 6), `projection` (rank 8), `bag` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_direct_columns_group_projection_support_rel :
  forall env rows columns,
    columns <> nil ->
    list_support_rel
      (fun row output =>
        TNullRowEq (TNullProjectRow env (SelectColumns columns) row) output)
      rows
      (map
        (group_projection env (SelectColumns columns)
          (map DotColumn columns))
        (@query_make_groups TNull env rows (map DotColumn columns))).
```

## `tnull_direct_columns_group_rows_bag_eq_of_projection_support`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1348`](../ProofAgentFacade.v#L1348)

Purpose/direction: States the tnull direct columns group rows bag equality of projection support law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `grouping` (rank 2), `projection` (rank 16), `bag` (rank 2)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_direct_columns_group_rows_bag_eq_of_projection_support :
  forall env columns left_rows right_rows,
    columns <> nil ->
    select_list_has_unique_outputs (SelectColumns columns) ->
    list_support_rel
      (fun left right =>
        TNullRowEq
          (TNullProjectRow env (SelectColumns columns) left)
          (TNullProjectRow env (SelectColumns columns) right))
      left_rows right_rows ->
    TNullBagEq
      (TNullRowsBag
        (map
          (group_projection env (SelectColumns columns)
            (map DotColumn columns))
          (@query_make_groups TNull env left_rows
            (map DotColumn columns))))
      (TNullRowsBag
        (map
          (group_projection env (SelectColumns columns)
            (map DotColumn columns))
          (@query_make_groups TNull env right_rows
            (map DotColumn columns)))).
```

## `tnull_direct_columns_group_keys_runtime_safe`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1394`](../ProofAgentFacade.v#L1394)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate grouping.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade` (rank 16), `grouping` (rank 16), `runtime` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_direct_columns_group_keys_runtime_safe :
  forall env rows columns,
    @group_keys_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (map DotColumn columns) rows = None.
```

## `tnull_direct_columns_group_select_runtime_safe`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1427`](../ProofAgentFacade.v#L1427)

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate grouping.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade` (rank 16), `grouping` (rank 16), `runtime` (rank 10)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_direct_columns_group_select_runtime_safe :
  forall env columns,
    @eval_select_list_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) = None /\
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) = None.
```

## `tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1507`](../ProofAgentFacade.v#L1507)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 16), `outcome` (rank 4), `grouping` (rank 2), `runtime` (rank 16), `projection` (rank 16), `bag` (rank 16), `scalar` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `projection`, `SELECT list`, `NULL`, `UNKNOWN`, `three-valued logic`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support :
  forall db env columns left_rows right_rows,
    columns <> nil ->
    select_list_has_unique_outputs (SelectColumns columns) ->
    list_support_rel
      (fun left right =>
        TNullRowEq
          (TNullProjectRow env (SelectColumns columns) left)
          (TNullProjectRow env (SelectColumns columns) right))
      left_rows right_rows ->
    forall outcome,
      @eval_group_bag_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (TNullRowsBag left_rows) outcome <->
      @eval_group_bag_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (TNullRowsBag right_rows) outcome.
```

## `tnull_direct_columns_group_bag_has_success`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1554`](../ProofAgentFacade.v#L1554)

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate grouping.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `outcome` (rank 16), `grouping` (rank 16), `runtime` (rank 16), `bag` (rank 16), `scalar` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_direct_columns_group_bag_has_success :
  forall db env columns rows,
    exists output_bag,
      @eval_group_bag_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (TNullRowsBag rows) (SqlSuccess output_bag).
```

## `tnull_eval_group_bag_direct_columns_true_no_error`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1626`](../ProofAgentFacade.v#L1626)

Purpose/direction: Rules out every local group-bag error for direct-column GROUP BY with TRUE HAVING, for any supplied successful child bag.

Applicability: Use after a child bag has been supplied to discharge only the local direct-column grouping error branch; it does not prove child safety or equivalence of successful group bags.

Important premises: Keep all three displayed restrictions: direct-column SELECT, matching direct grouping keys, and TRUE HAVING.  The theorem starts after a child input bag is supplied and does not erase child-query errors.

Cross-index: `facade` (rank 2), `outcome` (rank 4), `grouping` (rank 2), `runtime` (rank 2), `bag` (rank 8), `scalar` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_eval_group_bag_direct_columns_true_no_error :
  forall db env columns input_bag error,
    ~ @eval_group_bag_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (SelectColumns columns) (map DotColumn columns) FExpr_True
      input_bag (SqlError error).
```

## `tnull_direct_columns_group_outcome_equiv_of_projected_support`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1710`](../ProofAgentFacade.v#L1710)

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 0), `outcome` (rank 0), `grouping` (rank 0), `runtime` (rank 4), `bag` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma tnull_direct_columns_group_outcome_equiv_of_projected_support :
  forall db env columns left right,
    columns <> nil ->
    select_list_has_unique_outputs (SelectColumns columns) ->
    (exists outcome, TNullQueryExprOutcome db env left outcome) ->
    (forall left_rows,
      TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
      exists right_rows,
        TNullQueryExprOutcome db env right (SqlSuccess right_rows) /\
        list_support_rel
          (fun left_row right_row =>
            TNullRowEq
              (TNullProjectRow env (SelectColumns columns) left_row)
              (TNullProjectRow env (SelectColumns columns) right_row))
          left_rows right_rows) ->
    (forall right_rows,
      TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
      exists left_rows,
        TNullQueryExprOutcome db env left (SqlSuccess left_rows) /\
        list_support_rel
          (fun left_row right_row =>
            TNullRowEq
              (TNullProjectRow env (SelectColumns columns) left_row)
              (TNullProjectRow env (SelectColumns columns) right_row))
          left_rows right_rows) ->
    (forall error,
      TNullQueryExprOutcome db env left (SqlError error) <->
      TNullQueryExprOutcome db env right (SqlError error)) ->
    TNullQueryExprOutcomeEq db env
      (QExpr_Group (SelectColumns columns) (map DotColumn columns)
        FExpr_True left)
      (QExpr_Group (SelectColumns columns) (map DotColumn columns)
        FExpr_True right).
```

## `tnull_query_groups_matching_one_key`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2067`](../ProofAgentFacade.v#L2067)

Purpose/direction: States the tnull query groups matching one key law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_groups_matching_one_key` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `grouping` (rank 16)

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Lemma tnull_query_groups_matching_one_key :
  forall env group_terms rows
      (keep : list TNullValue -> bool) key,
    group_terms <> nil ->
    (forall row,
      In row
        (filter
          (fun item =>
            keep (query_grouping_key env group_terms item)) rows) ->
      query_grouping_key env group_terms row = key) ->
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (query_grouping_key env group_terms row)
        end)
      (@query_make_groups TNull env rows group_terms) =
    match
      filter
        (fun item =>
          keep (query_grouping_key env group_terms item)) rows
    with
    | nil => nil
    | _ :: _ =>
        [rev
          (filter
            (fun item =>
              keep (query_grouping_key env group_terms item)) rows)]
    end.
```
