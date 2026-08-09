# Aggregates, modifiers, grouping, and aggregate errors

Route here for: COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality.

This focused catalog contains 192 declarations routed at declaration granularity from `AggregateOutcomeBridgeFacts.v`, `AggregateRuntimeFacts.v`, `GroupedFilterOutcomeFacts.v`, `GroupingRewriteFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`, `SqlQueryContexts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `tnull_group_count_star_value_runtime_exact`

Source: [`theories/FormalSQL/AggregateOutcomeBridgeFacts.v:23`](../AggregateOutcomeBridgeFacts.v#L23)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Computes one TNull group COUNT-star value and both aggregate/full runtime checks exactly from the group's mathematical cardinality.

Applicability: Use for COUNT-star cardinality transport without assuming the count is inside BIGINT range.  Equal lengths preserve both the value placeholder and the exact overflow category; child query errors remain separate.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`, `COUNT star`, `group cardinality`, `BIGINT overflow`, `runtime error`

```rocq
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
```

## `count_star_value_local_error_exact_of_equal_length`

Source: [`theories/FormalSQL/AggregateOutcomeBridgeFacts.v:87`](../AggregateOutcomeBridgeFacts.v#L87)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows equal occurrence cardinality gives the same COUNT-star value and exact BIGINT overflow/error observation, without an in-range premise.

Applicability: Use for COUNT-star cardinality transport without assuming the count is inside BIGINT range.  Equal lengths preserve both the value placeholder and the exact overflow category; child query errors remain separate.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `COUNT star`, `equal cardinality`, `BIGINT overflow`, `local error`

```rocq
Theorem count_star_value_local_error_exact_of_equal_length :
  forall left right,
    List.length left = List.length right ->
    interp_aggregate AggregateCountStar left =
      interp_aggregate AggregateCountStar right /\
    aggregate_local_runtime_error AggregateCountStar left =
      aggregate_local_runtime_error AggregateCountStar right.
```

## `count_star_value_runtime_error_exact_of_equal_observation_length`

Source: [`theories/FormalSQL/AggregateOutcomeBridgeFacts.v:108`](../AggregateOutcomeBridgeFacts.v#L108)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows equal occurrence cardinality gives the same COUNT-star value and exact BIGINT overflow/error observation, without an in-range premise.

Applicability: Use for COUNT-star cardinality transport without assuming the count is inside BIGINT range.  Equal lengths preserve both the value placeholder and the exact overflow category; child query errors remain separate.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `COUNT star`, `equal cardinality`, `runtime error`, `observations`

```rocq
Theorem count_star_value_runtime_error_exact_of_equal_observation_length :
  forall left right,
    List.length left = List.length right ->
    interp_aggregate AggregateCountStar (observation_values left) =
      interp_aggregate AggregateCountStar (observation_values right) /\
    interp_aggregate_runtime_error AggregateCountStar left =
      interp_aggregate_runtime_error AggregateCountStar right.
```

## `count_star_count_all_nonnull_value_local_error_exact`

Source: [`theories/FormalSQL/AggregateOutcomeBridgeFacts.v:134`](../AggregateOutcomeBridgeFacts.v#L134)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates COUNT-star to COUNT ALL over an equally long reached expression list under explicit non-NULL and, for full outcomes, child-safety premises.

Applicability: Use only for AggregateAll after proving equal reached cardinality and every expression value non-NULL.  The full runtime form also requires each reached child observation to be error-free; DISTINCT is excluded.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `COUNT star`, `COUNT expression`, `NOT NULL`, `local error`

```rocq
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
```

## `count_star_count_all_nonnull_value_runtime_error_exact`

Source: [`theories/FormalSQL/AggregateOutcomeBridgeFacts.v:166`](../AggregateOutcomeBridgeFacts.v#L166)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates COUNT-star to COUNT ALL over an equally long reached expression list under explicit non-NULL and, for full outcomes, child-safety premises.

Applicability: Use only for AggregateAll after proving equal reached cardinality and every expression value non-NULL.  The full runtime form also requires each reached child observation to be error-free; DISTINCT is excluded.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `COUNT star`, `COUNT expression`, `NOT NULL`, `runtime error`

```rocq
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
```

## `first_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:14`](../AggregateRuntimeFacts.v#L14)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_error_none_iff : forall left right,
  first_error left right = None <-> left = None /\ right = None.
```

## `first_error_some_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:26`](../AggregateRuntimeFacts.v#L26)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_error_some_iff : forall left right error,
  first_error left right = Some error <->
  left = Some error \/ (left = None /\ right = Some error).
```

## `first_runtime_error_app`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:39`](../AggregateRuntimeFacts.v#L39)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_none_iff :
  forall (A : Type) (check : A -> option sql_runtime_error) values,
    first_runtime_error check values = None <->
    Forall (fun value => check value = None) values.
```

## `first_runtime_error_some_member`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:69`](../AggregateRuntimeFacts.v#L69)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_some_member :
  forall (A : Type) (check : A -> option sql_runtime_error) values error,
    first_runtime_error check values = Some error ->
    exists value, In value values /\ check value = Some error.
```

## `first_observation_error_as_first_runtime_error`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:84`](../AggregateRuntimeFacts.v#L84)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_observation_error_as_first_runtime_error : forall observations,
  first_observation_error observations =
  first_runtime_error (fun observation => fst observation) observations.
```

## `first_observation_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:93`](../AggregateRuntimeFacts.v#L93)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_observation_error_none_iff : forall observations,
  first_observation_error observations = None <->
  Forall (fun observation => fst observation = None) observations.
```

## `first_observation_error_some_member`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:102`](../AggregateRuntimeFacts.v#L102)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_observation_error_some_member : forall observations error,
  first_observation_error observations = Some error ->
  exists observation,
    In observation observations /\ fst observation = Some error.
```

## `observation_values_length`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:112`](../AggregateRuntimeFacts.v#L112)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates aggregate evaluation to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `cardinality`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `cardinality`

```rocq
Lemma observation_values_length : forall observations,
  List.length (observation_values observations) = List.length observations.
```

## `aggregate_call_child_error_propagates`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:121`](../AggregateRuntimeFacts.v#L121)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Reduces the composite aggregate evaluation condition to the displayed local condition.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma count_star_runtime_error_observations : forall observations,
  interp_aggregate_runtime_error AggregateCountStar observations =
  count_runtime_error (observation_values observations).
```

## `int64_result_runtime_error_none_of_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:206`](../AggregateRuntimeFacts.v#L206)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_result_runtime_error_none_of_range : forall integer,
  int64_min <= integer <= int64_max ->
  int64_result_runtime_error integer = None.
```

## `int64_result_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:216`](../AggregateRuntimeFacts.v#L216)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_result_runtime_error_none_iff : forall integer,
  int64_result_runtime_error integer = None <->
  int64_min <= integer <= int64_max.
```

## `count_runtime_error_none_of_row_count_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:233`](../AggregateRuntimeFacts.v#L233)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `cardinality`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma count_runtime_error_none_of_row_count_range : forall values,
  int64_min <= row_count values <= int64_max ->
  count_runtime_error values = None.
```

## `count_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:241`](../AggregateRuntimeFacts.v#L241)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma count_runtime_error_none_iff : forall values,
  count_runtime_error values = None <->
  int64_min <= row_count values <= int64_max.
```

## `non_null_count_runtime_error_none_of_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:249`](../AggregateRuntimeFacts.v#L249)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma non_null_count_runtime_error_none_of_range : forall values,
  int64_min <= non_null_count values <= int64_max ->
  non_null_count_runtime_error values = None.
```

## `non_null_count_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:257`](../AggregateRuntimeFacts.v#L257)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma non_null_count_runtime_error_none_iff : forall values,
  non_null_count_runtime_error values = None <->
  int64_min <= non_null_count values <= int64_max.
```

## `aggregate_function_locally_total_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:286`](../AggregateRuntimeFacts.v#L286)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma aggregate_function_locally_total_safe : forall function values,
  aggregate_function_locally_total function = true ->
  aggregate_local_runtime_error_function function values = None.
```

## `aggregate_call_locally_total_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:296`](../AggregateRuntimeFacts.v#L296)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes totality of the indicated aggregate evaluation operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `all_null_non_null_count_zero` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma all_null_non_null_count_zero : forall values,
  Forall (fun value => is_null_value value = true) values ->
  non_null_count values = 0.
```

## `aggregate_input_values_membership`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:336`](../AggregateRuntimeFacts.v#L336)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_membership` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_membership :
  forall quantifier value values,
    In value (aggregate_input_values quantifier values) <-> In value values.
```

## `aggregate_input_values_nonempty_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:345`](../AggregateRuntimeFacts.v#L345)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate evaluation.

Applicability: Use in either direction to invert or construct a goal about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_nonempty_iff : forall quantifier values,
  aggregate_input_values quantifier values <> [] <-> values <> [].
```

## `aggregate_input_values_preserves_Forall`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:367`](../AggregateRuntimeFacts.v#L367)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports an arbitrary pointwise input property through ALL or DISTINCT aggregate input selection.

Applicability: Use for properties insensitive to occurrence removal; DISTINCT may discard duplicates but cannot introduce a new value.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_preserves_Forall :
  forall quantifier (P : value -> Prop) values,
    Forall P values ->
    Forall P (aggregate_input_values quantifier values).
```

## `non_null_count_eq_length_of_Forall_nonnull`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:381`](../AggregateRuntimeFacts.v#L381)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Computes aggregate non-NULL count as the exact list length when every input value is proved non-NULL.

Applicability: Use only with an explicit `Forall` non-NULL proof; SQL NULL inputs would otherwise be omitted by the count.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `cardinality`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `cardinality`

```rocq
Lemma non_null_count_eq_length_of_Forall_nonnull :
  forall values,
    Forall (fun value => is_null_value value = false) values ->
    non_null_count values = Z.of_nat (List.length values).
```

## `distinct_values_fixed_of_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:394`](../AggregateRuntimeFacts.v#L394)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma distinct_values_fixed_of_nodup : forall values,
  NoDup values -> distinct_values values = values.
```

## `distinct_values_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:405`](../AggregateRuntimeFacts.v#L405)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `cardinality`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `cardinality`

```rocq
Lemma distinct_values_length_le : forall values,
  (List.length (distinct_values values) <= List.length values)%nat.
```

## `aggregate_input_values_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:412`](../AggregateRuntimeFacts.v#L412)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `cardinality`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `cardinality`

```rocq
Lemma aggregate_input_values_length_le : forall quantifier values,
  (List.length (aggregate_input_values quantifier values) <=
   List.length values)%nat.
```

## `aggregate_input_values_distinct_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:420`](../AggregateRuntimeFacts.v#L420)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma aggregate_input_values_distinct_nodup : forall values,
  NoDup (aggregate_input_values AggregateDistinct values).
```

## `aggregate_distinct_input_Permutation_of_NoDup_support`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:429`](../AggregateRuntimeFacts.v#L429)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies DISTINCT aggregate selection, up to permutation, with any duplicate-free list having exactly the original value support.

Applicability: Use only after supplying both duplicate-freedom and exact support equivalence; neither premise follows from cardinality alone.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:447`](../AggregateRuntimeFacts.v#L447)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared aggregate evaluation result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma aggregate_input_values_permutation :
  forall quantifier left right,
    Permutation left right ->
    Permutation
      (aggregate_input_values quantifier left)
      (aggregate_input_values quantifier right).
```

## `non_null_count_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:459`](../AggregateRuntimeFacts.v#L459)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma non_null_count_permutation : forall left right,
  Permutation left right -> non_null_count left = non_null_count right.
```

## `interp_aggregate_count_star_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:482`](../AggregateRuntimeFacts.v#L482)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared aggregate evaluation result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_aggregate_count_star_permutation : forall left right,
  Permutation left right ->
  interp_aggregate AggregateCountStar left =
  interp_aggregate AggregateCountStar right.
```

## `aggregate_count_star_local_runtime_error_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:495`](../AggregateRuntimeFacts.v#L495)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `runtime`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma aggregate_count_star_local_runtime_error_permutation : forall left right,
  Permutation left right ->
  aggregate_local_runtime_error AggregateCountStar left =
  aggregate_local_runtime_error AggregateCountStar right.
```

## `interp_aggregate_count_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:506`](../AggregateRuntimeFacts.v#L506)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared aggregate evaluation result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_aggregate_count_permutation : forall quantifier left right,
  Permutation left right ->
  interp_aggregate (AggregateCall AggregateCount quantifier) left =
  interp_aggregate (AggregateCall AggregateCount quantifier) right.
```

## `aggregate_count_local_runtime_error_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:524`](../AggregateRuntimeFacts.v#L524)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `runtime`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma aggregate_count_local_runtime_error_permutation :
  forall quantifier left right,
    Permutation left right ->
    aggregate_local_runtime_error
      (AggregateCall AggregateCount quantifier) left =
    aggregate_local_runtime_error
      (AggregateCall AggregateCount quantifier) right.
```

## `aggregate_input_values_idempotent`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:546`](../AggregateRuntimeFacts.v#L546)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared aggregate evaluation operator.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_idempotent` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma aggregate_input_values_idempotent : forall quantifier values,
  aggregate_input_values quantifier
    (aggregate_input_values quantifier values) =
  aggregate_input_values quantifier values.
```

## `interp_aggregate_call_selected_input_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:556`](../AggregateRuntimeFacts.v#L556)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:567`](../AggregateRuntimeFacts.v#L567)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `grouping`, `runtime`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:580`](../AggregateRuntimeFacts.v#L580)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping`, `bag`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:595`](../AggregateRuntimeFacts.v#L595)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping`, `runtime`, `bag`

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

## `fold_nonempty_support_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:677`](../AggregateRuntimeFacts.v#L677)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the displayed associative/commutative/idempotent fold or exact integral, NUMERIC, and C-collation textual extrema invariant under permutation, support equivalence, or repeated input blocks.

Applicability: Use only for the explicitly enumerated exact MIN/MAX functions.  The law is deliberately unavailable for SUM/AVG, especially FLOAT/DOUBLE; preserve child-error order through the separate runtime theorem.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `equivalence`, `congruence`, `associative commutative idempotent fold`, `support`, `duplicates`

```rocq
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
```

## `exact_extrema_aggregate_permutation`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:879`](../AggregateRuntimeFacts.v#L879)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the displayed associative/commutative/idempotent fold or exact integral, NUMERIC, and C-collation textual extrema invariant under permutation, support equivalence, or repeated input blocks.

Applicability: Use only for the explicitly enumerated exact MIN/MAX functions.  The law is deliberately unavailable for SUM/AVG, especially FLOAT/DOUBLE; preserve child-error order through the separate runtime theorem.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`, `MIN`, `MAX`, `permutation`, `C collation`

```rocq
Lemma exact_extrema_aggregate_permutation : forall function quantifier left right,
  (function = AggregateMinZ \/ function = AggregateMaxZ \/
   function = AggregateMinInt32 \/ function = AggregateMaxInt32 \/
   function = AggregateMinInt64 \/ function = AggregateMaxInt64 \/
   function = AggregateMinNumeric \/ function = AggregateMaxNumeric \/
   function = AggregateMaxString) ->
  Permutation left right ->
  interp_aggregate (AggregateCall function quantifier) left =
  interp_aggregate (AggregateCall function quantifier) right.
```

## `exact_extrema_aggregate_support_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:986`](../AggregateRuntimeFacts.v#L986)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the displayed associative/commutative/idempotent fold or exact integral, NUMERIC, and C-collation textual extrema invariant under permutation, support equivalence, or repeated input blocks.

Applicability: Use only for the explicitly enumerated exact MIN/MAX functions.  The law is deliberately unavailable for SUM/AVG, especially FLOAT/DOUBLE; preserve child-error order through the separate runtime theorem.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `equivalence`, `congruence`, `MIN`, `MAX`, `duplicate-insensitive support`, `runtime boundary`

```rocq
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
```

## `exact_extrema_aggregate_duplicate_block`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1004`](../AggregateRuntimeFacts.v#L1004)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the displayed associative/commutative/idempotent fold or exact integral, NUMERIC, and C-collation textual extrema invariant under permutation, support equivalence, or repeated input blocks.

Applicability: Use only for the explicitly enumerated exact MIN/MAX functions.  The law is deliberately unavailable for SUM/AVG, especially FLOAT/DOUBLE; preserve child-error order through the separate runtime theorem.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `MIN`, `MAX`, `idempotence`, `duplicate block`

```rocq
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
```

## `first_runtime_error_duplicate_block`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1021`](../AggregateRuntimeFacts.v#L1021)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that repeating one reached input block preserves its left-biased first runtime error, and packages that boundary for exact extrema aggregates.

Applicability: Use only for literal repetition of the same reached block in the same prefix/suffix schedule.  Arbitrary support equivalence does not preserve which SQL error is observed first.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `runtime error`, `evaluation order`, `duplicate block`

```rocq
Lemma first_runtime_error_duplicate_block :
  forall (A : Type) (check : A -> option sql_runtime_error)
    prefix block suffix,
    first_runtime_error check (prefix ++ block ++ block ++ suffix) =
    first_runtime_error check (prefix ++ block ++ suffix).
```

## `first_observation_error_duplicate_block`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1032`](../AggregateRuntimeFacts.v#L1032)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that repeating one reached input block preserves its left-biased first runtime error, and packages that boundary for exact extrema aggregates.

Applicability: Use only for literal repetition of the same reached block in the same prefix/suffix schedule.  Arbitrary support equivalence does not preserve which SQL error is observed first.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `runtime error`, `evaluation order`, `duplicate block`

```rocq
Lemma first_observation_error_duplicate_block :
  forall prefix block suffix,
    first_observation_error (prefix ++ block ++ block ++ suffix) =
    first_observation_error (prefix ++ block ++ suffix).
```

## `exact_extrema_aggregate_runtime_error_duplicate_block`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1046`](../AggregateRuntimeFacts.v#L1046)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that repeating one reached input block preserves its left-biased first runtime error, and packages that boundary for exact extrema aggregates.

Applicability: Use only for the explicitly enumerated exact MIN/MAX functions.  The law is deliberately unavailable for SUM/AVG, especially FLOAT/DOUBLE; preserve child-error order through the separate runtime theorem.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `MIN`, `MAX`, `runtime error`, `duplicate block`

```rocq
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
```

## `aggregate_input_values_preserves_all_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1070`](../AggregateRuntimeFacts.v#L1070)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_input_values_preserves_all_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma aggregate_input_values_preserves_all_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  Forall (fun value => is_null_value value = true)
    (aggregate_input_values quantifier values).
```

## `aggregate_filter_input_membership`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1087`](../AggregateRuntimeFacts.v#L1087)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_filter_input_membership` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma aggregate_filter_input_membership :
  forall predicate quantifier value values,
    In value (aggregate_filter_input predicate quantifier values) <->
    In value values /\ predicate value = true.
```

## `aggregate_filter_input_distinct_nodup`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1098`](../AggregateRuntimeFacts.v#L1098)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `filter`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `DISTINCT`, `duplicate elimination`, `filter`, `WHERE`, `multiplicity`

```rocq
Lemma aggregate_filter_input_distinct_nodup : forall predicate values,
  NoDup (aggregate_filter_input predicate AggregateDistinct values).
```

## `aggregate_filter_input_length_le`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1105`](../AggregateRuntimeFacts.v#L1105)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`, `cardinality`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `cardinality`

```rocq
Lemma aggregate_filter_input_length_le :
  forall predicate quantifier values,
    (List.length (aggregate_filter_input predicate quantifier values) <=
     List.length values)%nat.
```

## `aggregate_filter_input_false_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1116`](../AggregateRuntimeFacts.v#L1116)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_filter_input_false_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`

```rocq
Lemma aggregate_filter_input_false_empty : forall quantifier values,
  aggregate_filter_input (fun _ => false) quantifier values = [].
```

## `count_star_value_of_row_count_range`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1130`](../AggregateRuntimeFacts.v#L1130)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Connects the displayed range/representability premise to aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `cardinality`, `scalar`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1147`](../AggregateRuntimeFacts.v#L1147)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_value_of_non_null_count_range` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

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

## `int32_values_nonempty_of_typed_nonnull`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1175`](../AggregateRuntimeFacts.v#L1175)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `int32_values_nonempty_of_typed_nonnull` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `grouping`, `schema`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `INTEGER`, `int32`, `schema conformance`, `typing`

```rocq
Lemma int32_values_nonempty_of_typed_nonnull : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_int32_value value = true /\ is_null_value value = false)
    values ->
  int32_values values <> [].
```

## `numeric_values_nonempty_of_typed_nonnull`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1189`](../AggregateRuntimeFacts.v#L1189)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `numeric_values_nonempty_of_typed_nonnull` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `grouping`, `schema`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `schema conformance`, `typing`

```rocq
Lemma numeric_values_nonempty_of_typed_nonnull : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_numeric_value value = true /\ is_null_value value = false)
    values ->
  numeric_values values <> [].
```

## `interp_sum_int32_nonnull_of_nonempty_runtime_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1203`](../AggregateRuntimeFacts.v#L1203)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma interp_sum_int32_nonnull_of_nonempty_runtime_safe : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_int32_value value = true /\ is_null_value value = false)
    values ->
  sum_int32_runtime_error values = None ->
  is_null_value (interp_sum_int32_as_int64 values) = false.
```

## `interp_sum_numeric_nonnull_of_nonempty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1235`](../AggregateRuntimeFacts.v#L1235)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `interp_sum_numeric_nonnull_of_nonempty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma interp_sum_numeric_nonnull_of_nonempty : forall values,
  values <> [] ->
  Forall
    (fun value =>
      is_numeric_value value = true /\ is_null_value value = false)
    values ->
  is_null_value (interp_sum_numeric values) = false.
```

## `aggregate_sum_int32_nonnull_of_nonempty_runtime_safe`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1278`](../AggregateRuntimeFacts.v#L1278)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for aggregate evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
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
```

## `aggregate_sum_numeric_nonnull_of_nonempty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1299`](../AggregateRuntimeFacts.v#L1299)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `aggregate_sum_numeric_nonnull_of_nonempty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma aggregate_sum_numeric_nonnull_of_nonempty : forall quantifier values,
  values <> [] ->
  Forall
    (fun value =>
      is_numeric_value value = true /\ is_null_value value = false)
    values ->
  is_null_value
    (interp_aggregate
      (AggregateCall AggregateSumNumeric quantifier) values) = false.
```

## `count_star_empty_success`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1318`](../AggregateRuntimeFacts.v#L1318)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_star_empty_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma count_star_empty_success :
  exists zero,
    interp_aggregate AggregateCountStar [] = Value_int64 (Some zero) /\
    int64_value zero = 0.
```

## `count_empty_success`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1333`](../AggregateRuntimeFacts.v#L1333)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_empty_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma count_empty_success : forall quantifier,
  exists zero,
    interp_aggregate (AggregateCall AggregateCount quantifier) [] =
      Value_int64 (Some zero) /\
    int64_value zero = 0.
```

## `count_all_null_success`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1351`](../AggregateRuntimeFacts.v#L1351)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `count_all_null_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1375`](../AggregateRuntimeFacts.v#L1375)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `all_null_numeric_projections_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma all_null_numeric_projections_empty : forall values,
  Forall (fun value => is_null_value value = true) values ->
  int32_values values = [] /\
  int64_values values = [] /\
  numeric_values values = [].
```

## `all_null_float_string_projections_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1397`](../AggregateRuntimeFacts.v#L1397)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `all_null_float_string_projections_empty` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`, `string`, `VARCHAR`

```rocq
Lemma all_null_float_string_projections_empty : forall values,
  Forall (fun value => is_null_value value = true) values ->
  float_values values = [] /\
  double_values values = [] /\
  text_values values = [].
```

## `sum_int32_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1421`](../AggregateRuntimeFacts.v#L1421)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int32_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma sum_int32_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumInt32 quantifier) [] =
  Value_int64 None.
```

## `sum_int64_numeric_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1426`](../AggregateRuntimeFacts.v#L1426)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int64_numeric_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`

```rocq
Lemma sum_int64_numeric_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumInt64Numeric quantifier) [] =
  Value_numeric None.
```

## `sum_numeric_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1431`](../AggregateRuntimeFacts.v#L1431)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_numeric_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma sum_numeric_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumNumeric quantifier) [] =
  Value_numeric None.
```

## `sum_int32_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1436`](../AggregateRuntimeFacts.v#L1436)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int32_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma sum_int32_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumInt32 quantifier) values =
  Value_int64 None.
```

## `sum_int64_numeric_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1454`](../AggregateRuntimeFacts.v#L1454)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_int64_numeric_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`

```rocq
Lemma sum_int64_numeric_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate
    (AggregateCall AggregateSumInt64Numeric quantifier) values =
  Value_numeric None.
```

## `sum_numeric_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1473`](../AggregateRuntimeFacts.v#L1473)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_numeric_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma sum_numeric_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumNumeric quantifier) values =
  Value_numeric None.
```

## `sum_float_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1491`](../AggregateRuntimeFacts.v#L1491)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_float_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_float_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumFloat quantifier) [] =
  Value_float None.
```

## `sum_double_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1496`](../AggregateRuntimeFacts.v#L1496)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_double_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_double_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateSumDouble quantifier) [] =
  Value_double None.
```

## `sum_float_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1501`](../AggregateRuntimeFacts.v#L1501)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_float_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_float_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumFloat quantifier) values =
  Value_float None.
```

## `sum_double_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1519`](../AggregateRuntimeFacts.v#L1519)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `sum_double_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma sum_double_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateSumDouble quantifier) values =
  Value_double None.
```

## `min_max_int32_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1537`](../AggregateRuntimeFacts.v#L1537)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int32_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`

```rocq
Lemma min_max_int32_empty_is_null : forall function quantifier,
  (function = AggregateMinInt32 \/ function = AggregateMaxInt32) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_int32 None.
```

## `min_max_numeric_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1544`](../AggregateRuntimeFacts.v#L1544)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_numeric_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma min_max_numeric_empty_is_null : forall function quantifier,
  (function = AggregateMinNumeric \/ function = AggregateMaxNumeric) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_numeric None.
```

## `min_max_int32_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1551`](../AggregateRuntimeFacts.v#L1551)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int32_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`

```rocq
Lemma min_max_int32_all_null_is_null : forall function quantifier values,
  (function = AggregateMinInt32 \/ function = AggregateMaxInt32) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_int32 None.
```

## `min_max_numeric_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1575`](../AggregateRuntimeFacts.v#L1575)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_numeric_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma min_max_numeric_all_null_is_null : forall function quantifier values,
  (function = AggregateMinNumeric \/ function = AggregateMaxNumeric) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_numeric None.
```

## `min_max_int64_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1599`](../AggregateRuntimeFacts.v#L1599)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int64_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`

```rocq
Lemma min_max_int64_empty_is_null : forall function quantifier,
  (function = AggregateMinInt64 \/ function = AggregateMaxInt64) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_int64 None.
```

## `min_max_float_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1606`](../AggregateRuntimeFacts.v#L1606)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_float_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_float_empty_is_null : forall function quantifier,
  (function = AggregateMinFloat \/ function = AggregateMaxFloat) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_float None.
```

## `min_max_double_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1613`](../AggregateRuntimeFacts.v#L1613)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_double_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_double_empty_is_null : forall function quantifier,
  (function = AggregateMinDouble \/ function = AggregateMaxDouble) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_double None.
```

## `max_string_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1620`](../AggregateRuntimeFacts.v#L1620)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `max_string_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma max_string_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateMaxString quantifier) [] =
  Value_string (StringValue StringText None).
```

## `min_max_int64_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1625`](../AggregateRuntimeFacts.v#L1625)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_int64_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `BIGINT`, `int64`

```rocq
Lemma min_max_int64_all_null_is_null : forall function quantifier values,
  (function = AggregateMinInt64 \/ function = AggregateMaxInt64) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_int64 None.
```

## `min_max_float_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1649`](../AggregateRuntimeFacts.v#L1649)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_float_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_float_all_null_is_null : forall function quantifier values,
  (function = AggregateMinFloat \/ function = AggregateMaxFloat) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_float None.
```

## `min_max_double_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1673`](../AggregateRuntimeFacts.v#L1673)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `min_max_double_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma min_max_double_all_null_is_null : forall function quantifier values,
  (function = AggregateMinDouble \/ function = AggregateMaxDouble) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_double None.
```

## `max_string_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1697`](../AggregateRuntimeFacts.v#L1697)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `max_string_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma max_string_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateMaxString quantifier) values =
  Value_string (StringValue StringText None).
```

## `avg_integral_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1715`](../AggregateRuntimeFacts.v#L1715)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_integral_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_integral_empty_is_null : forall function quantifier,
  (function = AggregateAverageInt32Numeric \/
   function = AggregateAverageInt64Numeric) ->
  interp_aggregate (AggregateCall function quantifier) [] = Value_numeric None.
```

## `avg_integral_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1723`](../AggregateRuntimeFacts.v#L1723)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_integral_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_integral_all_null_is_null : forall function quantifier values,
  (function = AggregateAverageInt32Numeric \/
   function = AggregateAverageInt64Numeric) ->
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall function quantifier) values = Value_numeric None.
```

## `avg_float_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1749`](../AggregateRuntimeFacts.v#L1749)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_float_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_float_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateAverageFloat quantifier) [] =
  Value_double None.
```

## `avg_double_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1754`](../AggregateRuntimeFacts.v#L1754)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_double_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_double_empty_is_null : forall quantifier,
  interp_aggregate (AggregateCall AggregateAverageDouble quantifier) [] =
  Value_double None.
```

## `avg_float_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1759`](../AggregateRuntimeFacts.v#L1759)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_float_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_float_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateAverageFloat quantifier) values =
  Value_double None.
```

## `avg_double_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1777`](../AggregateRuntimeFacts.v#L1777)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_double_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `floating point`, `special value`

```rocq
Lemma avg_double_all_null_is_null : forall quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate (AggregateCall AggregateAverageDouble quantifier) values =
  Value_double None.
```

## `avg_numeric_fixed_empty_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1795`](../AggregateRuntimeFacts.v#L1795)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_fixed_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma avg_numeric_fixed_empty_is_null : forall precision scale quantifier,
  interp_aggregate
    (AggregateCall (AggregateAverageNumericFixed precision scale) quantifier)
    [] = Value_numeric None.
```

## `avg_numeric_fixed_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1806`](../AggregateRuntimeFacts.v#L1806)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_fixed_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `grouping`, `scalar`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1829`](../AggregateRuntimeFacts.v#L1829)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_at_scale_empty_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; retain every typmod/precision/scale and representability condition.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma avg_numeric_at_scale_empty_is_null : forall scale quantifier,
  interp_aggregate
    (AggregateCall (AggregateAverageNumericAtScale scale) quantifier) [] =
    Value_numeric None.
```

## `avg_numeric_at_scale_all_null_is_null`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1840`](../AggregateRuntimeFacts.v#L1840)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `avg_numeric_at_scale_all_null_is_null` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; retain every typmod/precision/scale and representability condition.

Cross-index: `grouping`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma avg_numeric_at_scale_all_null_is_null : forall scale quantifier values,
  Forall (fun value => is_null_value value = true) values ->
  interp_aggregate
    (AggregateCall (AggregateAverageNumericAtScale scale) quantifier) values =
  Value_numeric None.
```

## `single_value_int32_runtime_error_none_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1864`](../AggregateRuntimeFacts.v#L1864)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes SINGLE_VALUE safety exactly as at most one selected INT32 value.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `cardinality`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma single_value_int32_runtime_error_none_iff : forall values,
  single_value_int32_runtime_error values = None <->
  (List.length values <= 1)%nat.
```

## `single_value_int32_runtime_error_cardinality_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1874`](../AggregateRuntimeFacts.v#L1874)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes CardinalityViolation exactly as at least two selected INT32 values.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `cardinality`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `scalar subquery`, `SINGLE_VALUE`, `scalar cardinality`, `CardinalityViolation`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`

```rocq
Lemma single_value_int32_runtime_error_cardinality_iff : forall values,
  single_value_int32_runtime_error values = Some CardinalityViolation <->
  (2 <= List.length values)%nat.
```

## `aggregate_single_value_int32_selected_empty`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1884`](../AggregateRuntimeFacts.v#L1884)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that empty selected input yields SQL NULL with no SINGLE_VALUE runtime error.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: every explicit antecedent (`->`) in the declaration is required; the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `cardinality`, `scalar`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1898`](../AggregateRuntimeFacts.v#L1898)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that singleton selected input returns its INT32 value with no SINGLE_VALUE runtime error.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: every explicit antecedent (`->`) in the declaration is required; the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `cardinality`, `scalar`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1913`](../AggregateRuntimeFacts.v#L1913)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes CardinalityViolation exactly as at least two selected INT32 values.

Applicability: Use after lowering a supported one-column INT32 scalar comparison through SINGLE_VALUE, to prove empty/singleton safety or the many-row CardinalityViolation branch.

Important premises: the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `cardinality`, `scalar`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1929`](../AggregateRuntimeFacts.v#L1929)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_empty_shape` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1975`](../AggregateRuntimeFacts.v#L1975)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_grouping_sets_nil_outcome_iff : forall env input_bag outcome,
  eval_grouping_sets_bag env [] input_bag outcome <->
  outcome =
    SqlSuccess (Febag.empty (Fecol.CBag (Tuple.CTuple T))).
```

## `eval_grouping_sets_cons_success_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1985`](../AggregateRuntimeFacts.v#L1985)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_grouping_sets_cons_success_iff :
  forall env select_list group_terms grouping_sets input_bag output_bag,
    eval_grouping_sets_bag env
      ((select_list, group_terms) :: grouping_sets) input_bag
      (SqlSuccess output_bag) <->
    exists head_bag tail_bag,
      eval_group_bag env select_list group_terms SExpr_True input_bag
        (SqlSuccess head_bag) /\
      eval_grouping_sets_bag env grouping_sets input_bag
        (SqlSuccess tail_bag) /\
      output_bag = query_set_bag Union head_bag tail_bag.
```

## `eval_grouping_sets_cons_error_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2003`](../AggregateRuntimeFacts.v#L2003)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_grouping_sets_cons_error_iff :
  forall env select_list group_terms grouping_sets input_bag error,
    eval_grouping_sets_bag env
      ((select_list, group_terms) :: grouping_sets) input_bag
      (SqlError error) <->
    eval_group_bag env select_list group_terms SExpr_True input_bag
      (SqlError error) \/
    exists head_bag,
      eval_group_bag env select_list group_terms SExpr_True input_bag
        (SqlSuccess head_bag) /\
      eval_grouping_sets_bag env grouping_sets input_bag (SqlError error).
```

## `eval_grouping_sets_outcome_Forall2_congr`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2055`](../AggregateRuntimeFacts.v#L2055)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts branchwise exact outcome agreement through an arbitrary ordered GROUPING SETS schedule without moving its first error.

Applicability: Use for arbitrary grouping-set lists in their original order.  Branch order is semantic for runtime errors and must not be replaced by a permutation premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2099`](../AggregateRuntimeFacts.v#L2099)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes every successful GROUPING SETS schedule as the ordered UNION ALL fold of one successful bag per branch.

Applicability: Use for arbitrary grouping-set lists in their original order.  Branch order is semantic for runtime errors and must not be replaced by a permutation premise.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2141`](../AggregateRuntimeFacts.v#L2141)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes a GROUPING SETS error by an ordered prefix of successful branches followed by the exact failing branch.

Applicability: Use for arbitrary grouping-set lists in their original order.  Branch order is semantic for runtime errors and must not be replaced by a permutation premise.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`

Search aliases: `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem eval_grouping_sets_error_prefix_iff :
  forall env input_bag grouping_sets error,
    eval_grouping_sets_bag env grouping_sets input_bag (SqlError error) <->
    exists (prefix : list (@query_grouping_set T relname))
        (current : @query_grouping_set T relname)
        (suffix : list (@query_grouping_set T relname))
        (prefix_bags : list grouping_bag),
      grouping_sets = List.app prefix (current :: suffix) /\
      Forall2 (grouping_set_success_at env input_bag)
        prefix prefix_bags /\
      grouping_set_error_at env input_bag current error.
```

## `closed_group_direct_column_argument_observations_permutation_rows`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2395`](../AggregateRuntimeFacts.v#L2395)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared aggregate grouping result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
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
```

## `query_make_groups_support_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:23`](../GroupedFilterOutcomeFacts.v#L23)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups support exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_support_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups support rel law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_support_rel` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_emit_NoDupA_of_key_reflection` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups projected bag equality of support rel law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

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

## `query_make_groups_heterogeneous_projected_bag_eq`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:294`](../GroupedFilterOutcomeFacts.v#L294)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups heterogeneous projected bag equality law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_make_groups_heterogeneous_projected_bag_eq :
  forall env left_terms right_terms
      (project : tuple T -> tuple T)
      (left_emit right_emit : list (tuple T) -> tuple T) rows,
    left_terms <> nil ->
    right_terms <> nil ->
    (forall group row,
      In group (@query_make_groups T env rows left_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (left_emit group) = Eq) ->
    (forall group row,
      In group (@query_make_groups T env rows right_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (right_emit group) = Eq) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env left_terms left =
      query_grouping_key env left_terms right) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env right_terms left =
      query_grouping_key env right_terms right) ->
    bag_eq T
      (rows_bag T
        (map left_emit (@query_make_groups T env rows left_terms)))
      (rows_bag T
        (map right_emit (@query_make_groups T env rows right_terms))).
```

## `oeset_permut_support_rel`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:390`](../GroupedFilterOutcomeFacts.v#L390)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the oeset permut support rel law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `oeset_permut_support_rel` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:427`](../GroupedFilterOutcomeFacts.v#L427)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the rows bag equality implies permut law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_eq_implies_permut :
  forall (T : Tuple.Rcd) left right,
    bag_eq T (rows_bag T left) (rows_bag T right) ->
    Oeset.permut (OTuple T) left right.
```

## `rows_permut_implies_bag_eq`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:445`](../GroupedFilterOutcomeFacts.v#L445)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Converts semantic row permutation into equality of finite row bags, the converse of the reset-boundary occurrence bridge.

Applicability: Use after a semantic list-permutation proof when the enclosing constructor or equivalence goal expects finite-bag equality.

Important premises: The two row lists must be semantically permuted under `OTuple`.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_permut_implies_bag_eq :
  forall (T : Tuple.Rcd) left right,
    Oeset.permut (OTuple T) left right ->
    bag_eq T (rows_bag T left) (rows_bag T right).
```

## `rows_reverse_permut_congr`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:460`](../GroupedFilterOutcomeFacts.v#L460)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes aggregate evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `equivalence`, `congruence`

```rocq
Lemma rows_reverse_permut_congr :
  forall (T : Tuple.Rcd) left right,
    Oeset.permut (OTuple T) left right ->
    Oeset.permut (OTuple T) (rev left) (rev right).
```

## `query_same_rows_as_bag_permut_between`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:480`](../GroupedFilterOutcomeFacts.v#L480)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of aggregate evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_permut_between :
  forall (T : Tuple.Rcd) first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    Oeset.permut (OTuple T) first second.
```

## `scalar_expr_acceptance_exact_total_success`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:561`](../GroupedFilterOutcomeFacts.v#L561)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `scalar_expr_acceptance_exact_total_success` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma scalar_expr_acceptance_exact_total_success :
  forall env expression accepted,
    scalar_expr_acceptance_exact_at env expression accepted ->
    scalar_expr_total_success_at env expression.
```

## `scalar_expr_true_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:571`](../GroupedFilterOutcomeFacts.v#L571)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the scalar expr true acceptance exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `scalar_expr_true_acceptance_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma scalar_expr_true_acceptance_exact :
  forall env,
    scalar_expr_acceptance_exact_at env SExpr_True true.
```

## `scalar_acceptance_interp_conj`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:640`](../GroupedFilterOutcomeFacts.v#L640)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the scalar acceptance interp conj law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `scalar_acceptance_interp_conj` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma scalar_acceptance_interp_conj :
  forall operation left right,
    Bool.is_true (B T) (interp_conj (B T) operation left right) =
    scalar_acceptance_combine operation
      (Bool.is_true (B T) left) (Bool.is_true (B T) right).
```

## `eval_scalar_boolean_operands_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:695`](../GroupedFilterOutcomeFacts.v#L695)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the eval scalar boolean operands acceptance exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_scalar_boolean_operands_acceptance_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma eval_scalar_boolean_operands_acceptance_exact :
  forall env operation expressions accepted,
    Forall2
      (fun expression decision =>
        scalar_expr_acceptance_exact_at env expression decision)
      expressions accepted ->
    scalar_boolean_operands_acceptance_exact_at env operation expressions
      (scalar_acceptance_fold operation accepted).
```

## `scalar_expr_conj_list_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:863`](../GroupedFilterOutcomeFacts.v#L863)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Composes exact TRUE-acceptance contracts through the scheduled flattened SQL AND/OR traversal without identifying FALSE and UNKNOWN values.

Applicability: Use after proving the displayed exact acceptance contract for every scheduled operand; the conclusion combines only `Bool.is_true` decisions, not the underlying SQL FALSE/UNKNOWN values.

Important premises: Retain the complete insertion-site schedule and every displayed operand contract; no one fixed eager order represents all legal AND/OR outcomes.

Cross-index: `grouping`, `filter`, `scalar`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `filter`, `WHERE`, `predicate`, `Bool3`

```rocq
Theorem scalar_expr_conj_list_acceptance_exact :
  forall site_rows env operation expressions decide,
    (forall expression,
      In expression expressions ->
      scalar_expr_acceptance_exact_at env expression (decide expression)) ->
    scalar_expr_acceptance_exact_at env
      (SExpr_ConjList site_rows operation expressions)
      (scalar_acceptance_fold operation (map decide expressions)).
```

## `scalar_expr_conj_list_redundant_operand_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:921`](../GroupedFilterOutcomeFacts.v#L921)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Eliminates an acceptance-redundant flattened operand only after every legal schedule preserves exact error-free acceptance and the operand is proved redundant whenever earlier operands do not decide the result.

Applicability: Use for guarded correlated predicates only after the candidate operand is exact and cannot error on every reached row. A legal schedule may evaluate it before a decisive operand, so accepting guard rows alone are insufficient.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `SQL AND`, `flattened operands`, `redundant conjunct`, `Boolean schedule`, `runtime error`

```rocq
Theorem scalar_expr_conj_list_redundant_operand_acceptance_exact :
  forall site_rows env expressions redundant decide,
    (forall expression,
      In expression expressions ->
      scalar_expr_acceptance_exact_at env expression (decide expression)) ->
    scalar_expr_acceptance_exact_at env redundant (decide redundant) ->
    (scalar_acceptance_fold And_F (map decide expressions) = true ->
      decide redundant = true) ->
    scalar_expr_acceptance_exact_at env
      (SExpr_ConjList site_rows And_F (expressions ++ [redundant]))
      (scalar_acceptance_fold And_F (map decide expressions)).
```

## `eval_groups_global_success_length_le_one`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1519`](../GroupedFilterOutcomeFacts.v#L1519)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_global_success_length_le_one` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem eval_groups_global_success_length_le_one :
  forall env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    (length output <= 1)%nat.
```

## `eval_groups_global_success_NoDupA`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1538`](../GroupedFilterOutcomeFacts.v#L1538)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `eval_groups_global_success_NoDupA` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem eval_groups_global_success_NoDupA :
  forall (R : tuple T -> tuple T -> Prop)
      env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    SetoidList.NoDupA R output.
```

## `eval_group_bag_exact_rows_permut_equiv`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1594`](../GroupedFilterOutcomeFacts.v#L1594)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Lifts exact per-representative group evaluation through the quotient-saturated group-bag reset when emitted rows are semantic permutations, preserving key and processing errors.

Applicability: Use at a `QExpr_Group` bag reset after characterizing `eval_groups` for every legal representative and proving the two emitted row functions permutation-equivalent.

Important premises: Both exact contracts quantify over every bag representative and include group-key safety; the cross-representative output permutation premise may not be weakened to support equality.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem eval_group_bag_exact_rows_permut_equiv :
  forall left_schedule right_schedule env select_list group_keys group_terms
      left_having right_having
      (left_bag right_bag :
        Febag.bag (Fecol.CBag (Tuple.CTuple T)))
      (left_rows right_rows :
        list (list (tuple T)) -> list (tuple T)),
    scalar_group_key_terms group_keys = Some group_terms ->
    (forall representative,
      query_same_rows_as_bag representative left_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        @eval_groups_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env select_list group_terms left_having groups outcome <->
        outcome = SqlSuccess (left_rows groups)) ->
    (forall representative,
      query_same_rows_as_bag representative right_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        @eval_groups_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env select_list group_terms right_having groups outcome <->
        outcome = SqlSuccess (right_rows groups)) ->
    (forall left_representative right_representative,
      query_same_rows_as_bag left_representative left_bag ->
      query_same_rows_as_bag right_representative right_bag ->
      Oeset.permut (OTuple T)
        (left_rows
          (query_make_groups env left_representative group_terms))
        (right_rows
          (query_make_groups env right_representative group_terms))) ->
    forall outcome,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env select_list group_keys left_having left_bag outcome <->
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env select_list group_keys right_having right_bag outcome.
```

## `query_expr_group_outcome_equiv_of_supported_child_outcomes`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1786`](../GroupedFilterOutcomeFacts.v#L1786)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_group_possible_outcome_equiv_of_supported_child_outcomes` for the public result.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_outcome_equiv_of_supported_child_outcomes :
  forall env select_list group_keys having left right
      (supported : list (tuple T) -> list (tuple T) -> Prop),
    query_expr_outputs
      (QExpr_Group select_list group_keys having left) =
    query_expr_outputs
      (QExpr_Group select_list group_keys having right) ->
    (exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env
        (QExpr_Group select_list group_keys having left) outcome) ->
    (forall left_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule env right (SqlSuccess right_rows) /\
        supported left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule env left (SqlSuccess left_rows) /\
        supported left_rows right_rows) ->
    (forall error,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left (SqlError error) <->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right (SqlError error)) ->
    (forall left_rows right_rows,
      supported left_rows right_rows ->
      forall outcome,
        eval_group_bag env select_list group_keys having
          (rows_bag T left_rows) outcome <->
        eval_group_bag env select_list group_keys having
          (rows_bag T right_rows) outcome) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env
      (QExpr_Group select_list group_keys having left)
      (QExpr_Group select_list group_keys having right).
```

## `query_canonical_rows_permut`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:16`](../GroupingRewriteFacts.v#L16)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query canonical rows permut law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_canonical_rows_permut` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Lemma query_canonical_rows_permut :
  forall (T : Tuple.Rcd) rows,
    Oeset.permut (OTuple T) (@query_canonical_rows T rows) rows.
```

## `query_canonical_rows_map_factor_permut`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:31`](../GroupingRewriteFacts.v#L31)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports a projection or rename through canonical bag-row selection up to semantic permutation, without exposing the bag implementation's concrete sorting algorithm.

Applicability: Use when a schema-changing projection or alias rename is moved across grouping, quantified predicates, or another canonical bag representative boundary.

Important premises: The representation map must respect semantic tuple equality, and the displayed pointwise factor equation must hold for every source item.

Cross-index: `renaming`, `grouping`, `projection`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Theorem query_canonical_rows_map_factor_permut :
  forall (T : Tuple.Rcd) (A : Type)
      (first second : A -> tuple T) (rename : tuple T -> tuple T),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      Oeset.compare (OTuple T) (rename left) (rename right) = Eq) ->
    (forall item, rename (first item) = second item) ->
    forall rows,
      Oeset.permut (OTuple T)
        (@query_canonical_rows T (map second rows))
        (map rename (@query_canonical_rows T (map first rows))).
```

## `filter_insert_in_partition_by_key`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:71`](../GroupingRewriteFacts.v#L71)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the filter insert in partition by key law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `filter_insert_in_partition_by_key` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:92`](../GroupingRewriteFacts.v#L92)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the filter partition rec by key law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `filter_partition_rec_by_key` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:107`](../GroupingRewriteFacts.v#L107)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the partition filter by key exact law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `partition_filter_by_key_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:122`](../GroupingRewriteFacts.v#L122)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the map snd filter keyed groups law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `map_snd_filter_keyed_groups` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:160`](../GroupingRewriteFacts.v#L160)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `partition_members_filter_by_key_exact` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:205`](../GroupingRewriteFacts.v#L205)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the partition map heterogeneous law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `partition_map_heterogeneous` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

## `partition_members_equal_of_key_decisions`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:333`](../GroupingRewriteFacts.v#L333)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `partition_members_equal_of_key_decisions` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`

```rocq
Theorem partition_members_equal_of_key_decisions :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (left_key right_key : A -> Key) rows,
    (forall first second,
      In first rows ->
      In second rows ->
      Oset.eq_bool key_order (left_key first) (left_key second) =
      Oset.eq_bool key_order (right_key first) (right_key second)) ->
    map snd (@Partition.partition A Key key_order left_key rows) =
    map snd (@Partition.partition A Key key_order right_key rows).
```

## `list_permut_eq_implies_Permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:356`](../GroupingRewriteFacts.v#L356)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the list permut equality implies permutation law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_permut_eq_implies_Permutation :
  forall (A : Type) (left right : list A),
    ListPermut._permut (@eq A) left right ->
    Sorting.Permutation.Permutation left right.
```

## `partition_keys_Permutation_of_NoDup_support`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:395`](../GroupingRewriteFacts.v#L395)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies the keys materialized by generic partitioning with any duplicate-free same-support key representative, up to permutation.

Applicability: Use only after supplying both duplicate-freedom and exact support equivalence; neither premise follows from cardinality alone.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:673`](../GroupingRewriteFacts.v#L673)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate evaluation.

Applicability: Use when the goal or a hypothesis matches the `partition_member_exact_key_filter` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:821`](../GroupingRewriteFacts.v#L821)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the partition factored key refinement forall2 law for aggregate evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `partition_factored_key_refinement_Forall2` direction for aggregate evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

## `query_grouping_key_decision_Permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:883`](../GroupingRewriteFacts.v#L883)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query grouping key decision permutation law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_grouping_key_decision_Permutation :
  forall (T : Tuple.Rcd) (env : Env.env T) left_terms right_terms left right,
    Sorting.Permutation.Permutation left_terms right_terms ->
    Oset.eq_bool (OrderedSet.mk_olists (OVal T))
      (query_grouping_key env left_terms left)
      (query_grouping_key env left_terms right) =
    Oset.eq_bool (OrderedSet.mk_olists (OVal T))
      (query_grouping_key env right_terms left)
      (query_grouping_key env right_terms right).
```

## `query_make_groups_group_terms_Permutation`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:929`](../GroupingRewriteFacts.v#L929)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups group terms permutation law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_make_groups_group_terms_Permutation :
  forall (T : Tuple.Rcd) (env : Env.env T) rows left_terms right_terms,
    Sorting.Permutation.Permutation left_terms right_terms ->
    @query_make_groups T env rows left_terms =
    @query_make_groups T env rows right_terms.
```

## `query_make_groups_map_heterogeneous`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:984`](../GroupingRewriteFacts.v#L984)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups map heterogeneous law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_map_heterogeneous` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1026`](../GroupingRewriteFacts.v#L1026)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups factored refinement forall2 law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_factored_refinement_Forall2` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1129`](../GroupingRewriteFacts.v#L1129)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups filter by key exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_filter_by_key_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1153`](../GroupingRewriteFacts.v#L1153)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_selected_members_permut` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1189`](../GroupingRewriteFacts.v#L1189)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1226`](../GroupingRewriteFacts.v#L1226)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Computes groups for one constant nonempty grouping key as no group on empty input or one reverse-ordered member list otherwise.

Applicability: Use only with a nonempty grouping-term list and one proved key for every row; retain the literal `rev rows` and prove key runtime safety separately.

Important premises: The grouping terms must be nonempty and every input row must have the displayed key; the nonempty result is exactly `[rev rows]`.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1249`](../GroupingRewriteFacts.v#L1249)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups matching one key exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_matching_one_key_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

## `query_make_groups_lookup_key_exact`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1297`](../GroupingRewriteFacts.v#L1297)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups lookup key exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_lookup_key_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_lookup_key_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms rows key,
    group_terms <> nil ->
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ =>
            Oset.eq_bool (OrderedSet.mk_olists (OVal T))
              (query_grouping_key env group_terms row) key
        end)
      (@query_make_groups T env rows group_terms) =
    match
      filter
        (fun row =>
          Oset.eq_bool (OrderedSet.mk_olists (OVal T))
            (query_grouping_key env group_terms row) key)
        rows
    with
    | nil => nil
    | _ :: _ =>
        [rev
          (filter
            (fun row =>
              Oset.eq_bool (OrderedSet.mk_olists (OVal T))
                (query_grouping_key env group_terms row) key)
            rows)]
    end.
```

## `query_make_groups_members_same_key_nonempty`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1339`](../GroupingRewriteFacts.v#L1339)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_members_same_key_nonempty` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1367`](../GroupingRewriteFacts.v#L1367)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_member_exact_key_filter` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `grouping`, `filter`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1444`](../GroupingRewriteFacts.v#L1444)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to aggregate grouping.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `filter`, `bag`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1467`](../GroupingRewriteFacts.v#L1467)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query make groups global exact law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_global_exact` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Theorem query_make_groups_global_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) rows,
    @query_make_groups T env rows [] = [rev rows].
```

## `query_make_groups_global_length_one`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1479`](../GroupingRewriteFacts.v#L1479)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates aggregate grouping to the exact list length or bag cardinality shown below.

Applicability: Use when the goal or a hypothesis matches the `query_make_groups_global_length_one` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`

Search aliases: `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`

```rocq
Corollary query_make_groups_global_length_one :
  forall (T : Tuple.Rcd) (env : Env.env T) rows,
    length (@query_make_groups T env rows []) = 1%nat.
```

## `query_make_groups_permut_nonempty`

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1492`](../GroupingRewriteFacts.v#L1492)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports semantic row permutation to semantic group permutation for a nonempty grouping-term list.

Applicability: Use when two input row lists represent the same bag and grouping terms are nonempty; the result compares whole groups semantically.

Important premises: The nonempty grouping-term premise is mandatory because the global empty grouping set has distinct empty-input semantics.

Cross-index: `grouping`

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

Source: [`theories/FormalSQL/GroupingRewriteFacts.v:1513`](../GroupingRewriteFacts.v#L1513)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports a semantic group permutation through an equality-respecting group filter and projection map while retaining occurrences.

Applicability: Use after proving both the retained-group decision and emitted row respect semantic group equality; it composes directly with exact HAVING acceptance.

Important premises: Supply semantic-equality compatibility for both `keep` and `emit`; the conclusion is occurrence-preserving permutation, not set equality.

Cross-index: `grouping`, `filter`, `bag`

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

## `query_group_success_bags_congr_extensional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:470`](../OrderedQueryFacts.v#L470)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `grouping`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_group_success_bags_congr_extensional :
  forall env left_select left_terms left_having
      right_select right_terms right_having left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    unary_bag_relation_equiv
      (@query_group_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_select left_terms left_having)
      (@query_group_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_select right_terms right_having) ->
    rel_equiv
      (success_bags env
        (QExpr_Group left_select left_terms left_having left))
      (success_bags env
        (QExpr_Group right_select right_terms right_having right)).
```

## `query_grouping_sets_success_bags_congr_extensional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:496`](../OrderedQueryFacts.v#L496)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `grouping`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_grouping_sets_success_bags_congr_extensional :
  forall env left_sets right_sets left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    unary_bag_relation_equiv
      (@query_grouping_sets_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_sets)
      (@query_grouping_sets_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_sets) ->
    rel_equiv
      (success_bags env (QExpr_GroupingSets left_sets left))
      (success_bags env (QExpr_GroupingSets right_sets right)).
```

## `query_expr_group_outcome_equiv_of_global_having`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1024`](../OrderedQueryFacts.v#L1024)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_group_possible_outcome_equiv_of_uniform_having` for the public result.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_outcome_equiv_of_global_having :
  forall env select_list group_terms
      (left_having right_having : scalar_expr T relname ScalarResultBoolean)
      input,
    @scalar_expr_global_group_outcome_equiv T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule ScalarResultBoolean
      left_having right_having ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms left_having input) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms left_having input)
      (QExpr_Group select_list group_terms right_having input).
```

## `eval_query_expr_group_outcome_iff_of_child_outcome_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1053`](../OrderedQueryFacts.v#L1053)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for aggregate grouping.

Applicability: Use in either direction to invert or construct a goal about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1111`](../OrderedQueryFacts.v#L1111)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_group_possible_outcome_equiv_congr_uniform` for the public result.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

## `tnull_query_groups_matching_one_key`

Source: [`theories/FormalSQL/ProofAgentFacade.v:708`](../ProofAgentFacade.v#L708)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull query groups matching one key law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_groups_matching_one_key` direction for aggregate grouping; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `grouping`

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

## `query_expr_group_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1296`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1296)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_global_typed_congr :
  forall select_list group_keys having input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list group_keys having input)
      (QExpr_Group select_list group_keys having input').
```

## `query_expr_grouping_sets_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1326`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1326)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_grouping_sets_global_typed_congr :
  forall grouping_sets input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets grouping_sets input)
      (QExpr_GroupingSets grouping_sets input').
```

## `eval_groups_scalar_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1989`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1989)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_groups_scalar_global_congr :
  forall left_select right_select group_terms left_having right_having,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    scalar_expr_global_outcome_equiv left_having right_having ->
    (forall current_env,
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    (forall current_env,
      eval_scalar_expr_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env left_having =
      eval_scalar_expr_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env right_having) ->
    forall env groups outcome,
      eval_groups env left_select group_terms left_having groups outcome <->
      eval_groups env right_select group_terms right_having groups outcome.
```

## `eval_group_bag_scalar_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2117`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2117)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes aggregate grouping across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_group_bag_scalar_global_congr :
  forall left_select right_select group_keys left_having right_having,
    (forall current_env group_terms groups outcome,
      eval_groups current_env left_select group_terms left_having
        groups outcome <->
      eval_groups current_env right_select group_terms right_having
        groups outcome) ->
    forall env input_bag outcome,
      eval_group_bag env left_select group_keys left_having input_bag outcome <->
      eval_group_bag env right_select group_keys right_having input_bag outcome.
```

## `eval_group_bag_group_keys_none`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2211`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2211)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the eval group bag group keys none law for aggregate grouping, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_group_bag_group_keys_none :
  forall env select_list group_keys having input_bag outcome,
    scalar_group_key_terms group_keys = None ->
    ~ eval_group_bag env select_list group_keys having input_bag outcome.
```

## `query_group_rows_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5346`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5346)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines the constructor-local successful-bag and runtime-error relation on one actual ordered child row list.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_group_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (select_list : @query_select_list T relname)
    (group_keys : list (scalar_expr T relname ScalarResultValue))
    (having : scalar_expr T relname ScalarResultBoolean)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        @query_group_bag_relation T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env select_list group_keys having (rows_bag T rows) output_bag
    | SqlError error =>
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env select_list group_keys having (rows_bag T rows)
          (SqlError error)
    end.
```

## `query_grouping_sets_rows_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5365`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5365)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines the constructor-local successful-bag and runtime-error relation on one actual ordered child row list.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_grouping_sets_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T)
    (grouping_sets : list (@query_grouping_set T relname))
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        @query_grouping_sets_bag_relation T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env grouping_sets (rows_bag T rows) output_bag
    | SqlError error =>
        @eval_grouping_sets_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env grouping_sets (rows_bag T rows) (SqlError error)
    end.
```

## `query_group_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5597`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5597)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled unary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: No semantic premise is hidden: this is the exact fixed-schedule characterization of the displayed constructor-local relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_group_scheduled_bag_outcomes_characterization :
  forall schedule env select_list group_keys having input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Group select_list group_keys having input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_reset_query schedule env input)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env select_list group_keys having)).
```

## `query_grouping_sets_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5641`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5641)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled unary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: No semantic premise is hidden: this is the exact fixed-schedule characterization of the displayed constructor-local relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_grouping_sets_scheduled_bag_outcomes_characterization :
  forall schedule env grouping_sets input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_GroupingSets grouping_sets input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_reset_query schedule env input)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null schedule env grouping_sets)).
```

## `query_group_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5868`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5868)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports one child bag/error relation under a matched schedule pair using the exact reachable-list local contract.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: Supply complete child bag/error equivalence under the matched schedule pair and the exact reachable-list `scheduled_local_rows_to_bag_contract`.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_group_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_select left_keys left_having right_select right_keys right_having
      left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_group_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_select left_keys left_having)
      (@query_group_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_select right_keys right_having) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Group left_select left_keys left_having left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Group right_select right_keys right_having right)).
```

## `query_grouping_sets_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5907`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5907)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports one child bag/error relation under a matched schedule pair using the exact reachable-list local contract.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: Supply complete child bag/error equivalence under the matched schedule pair and the exact reachable-list `scheduled_local_rows_to_bag_contract`.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_grouping_sets_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env left_sets right_sets left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_grouping_sets_rows_bag_outcomes T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null left_schedule env left_sets)
      (@query_grouping_sets_rows_bag_outcomes T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null right_schedule env right_sets) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_GroupingSets left_sets left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_GroupingSets right_sets right)).
```

## `query_expr_group_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6221`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6221)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_group_possible_bag_schedule_transport :
  forall env
      left_select left_keys left_having right_select right_keys right_having
      left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_select left_keys left_having)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_select right_keys right_having)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select left_keys left_having left)
      (QExpr_Group right_select right_keys right_having right).
```

## `query_expr_group_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6264`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6264)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `aggregate/grouping runtime semantics`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_group_possible_bag_outcome_equiv :
  forall env
      left_select left_keys left_having right_select right_keys right_having
      left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_select left_keys left_having)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_select right_keys right_having)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select left_keys left_having left)
      (QExpr_Group right_select right_keys right_having right).
```

## `query_expr_grouping_sets_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6302`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6302)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about aggregate grouping.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_grouping_sets_possible_bag_schedule_transport :
  forall env left_sets right_sets left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_grouping_sets_outputs T relname left_sets =
      @query_grouping_sets_outputs T relname right_sets ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_sets)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_sets)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_GroupingSets left_sets left)
      (QExpr_GroupingSets right_sets right).
```

## `query_expr_grouping_sets_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6344`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6344)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about aggregate grouping.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `aggregate/grouping runtime semantics`, `grouping sets`, `GROUP BY`, `aggregate`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_grouping_sets_possible_bag_outcome_equiv :
  forall env left_sets right_sets left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_grouping_sets_outputs T relname left_sets =
      @query_grouping_sets_outputs T relname right_sets ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_sets)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_sets)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_GroupingSets left_sets left)
      (QExpr_GroupingSets right_sets right).
```
