# Derived numeric, integer, float, and cast facts

Route here for: INTEGER/BIGINT bounds, derived NUMERIC laws, floats, casts, overflow.

This focused catalog contains 127 declarations routed at declaration granularity from `NumericDerivedFacts.v`, `NumericRegroupFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `int32_checked_result_value`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:12`](../NumericDerivedFacts.v#L12)

Purpose/direction: States the int32 checked result value law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_checked_result_value` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_checked_result_value : forall integer result,
  int32_checked integer = Some result ->
  int32_value result = integer.
```

## `int64_checked_result_value`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:23`](../NumericDerivedFacts.v#L23)

Purpose/direction: States the int64 checked result value law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int64_checked_result_value` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_checked_result_value : forall integer result,
  int64_checked integer = Some result ->
  int64_value result = integer.
```

## `interp_int32_neq_disjunction_true_of_unequal_constants`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:37`](../NumericDerivedFacts.v#L37)

Purpose/direction: States the interp int32 disequality disjunction true of unequal constants law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_int32_neq_disjunction_true_of_unequal_constants` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `predicate`, `Bool3`, `INTEGER`, `int32`

```rocq
Lemma interp_int32_neq_disjunction_true_of_unequal_constants :
  forall value first second,
    int32_value first <> int32_value second ->
    Bool3.orb3
      (NullValues.interp_predicate PredicateNeq
        [Value_int32 (Some value); Value_int32 (Some first)])
      (NullValues.interp_predicate PredicateNeq
        [Value_int32 (Some value); Value_int32 (Some second)]) =
    Bool3.true3.
```

## `int32_checked_defined_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:59`](../NumericDerivedFacts.v#L59)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_checked_defined_iff : forall integer,
  (exists result, int32_checked integer = Some result) <->
  int32_min <= integer <= int32_max.
```

## `int64_checked_defined_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:74`](../NumericDerivedFacts.v#L74)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_checked_defined_iff : forall integer,
  (exists result, int64_checked integer = Some result) <->
  int64_min <= integer <= int64_max.
```

## `int32_checked_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:89`](../NumericDerivedFacts.v#L89)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_checked_none_iff : forall integer,
  int32_checked integer = None <->
  integer < int32_min \/ int32_max < integer.
```

## `int64_checked_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:106`](../NumericDerivedFacts.v#L106)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_checked_none_iff : forall integer,
  int64_checked integer = None <->
  integer < int64_min \/ int64_max < integer.
```

## `int32_checked_value`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:123`](../NumericDerivedFacts.v#L123)

Purpose/direction: States the int32 checked value law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_checked_value` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_checked_value : forall value,
  int32_checked (int32_value value) = Some value.
```

## `int32_to_int64_injective`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:135`](../NumericDerivedFacts.v#L135)

Purpose/direction: Recovers source equality from the declared typed numeric semantics representation.

Applicability: Use when the goal or a hypothesis matches the `int32_to_int64_injective` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma int32_to_int64_injective : forall left right,
  int32_to_int64 left = int32_to_int64 right -> left = right.
```

## `int32_to_int64_value`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:143`](../NumericDerivedFacts.v#L143)

Purpose/direction: States the int32 to int64 value law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_to_int64_value` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma int32_to_int64_value : forall value,
  int64_value (int32_to_int64 value) = int32_value value.
```

## `int32_add_total_of_range`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:149`](../NumericDerivedFacts.v#L149)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `int32_add_total_of_range` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_add_total_of_range : forall left right,
  int32_min <= int32_value left + int32_value right <= int32_max ->
  exists result,
    int32_add left right = Some result /\
    int32_value result = int32_value left + int32_value right.
```

## `int32_sub_total_of_range`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:162`](../NumericDerivedFacts.v#L162)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `int32_sub_total_of_range` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_sub_total_of_range : forall left right,
  int32_min <= int32_value left - int32_value right <= int32_max ->
  exists result,
    int32_sub left right = Some result /\
    int32_value result = int32_value left - int32_value right.
```

## `int32_mul_total_of_range`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:175`](../NumericDerivedFacts.v#L175)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `int32_mul_total_of_range` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_mul_total_of_range : forall left right,
  int32_min <= int32_value left * int32_value right <= int32_max ->
  exists result,
    int32_mul left right = Some result /\
    int32_value result = int32_value left * int32_value right.
```

## `int32_div_total_of_nonzero_range`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:188`](../NumericDerivedFacts.v#L188)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `int32_div_total_of_nonzero_range` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_div_total_of_nonzero_range : forall left right,
  int32_value right <> 0 ->
  int32_min <= Z.quot (int32_value left) (int32_value right) <= int32_max ->
  exists result,
    int32_div left right = Some result /\
    int32_value result = Z.quot (int32_value left) (int32_value right).
```

## `int32_add_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:210`](../NumericDerivedFacts.v#L210)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_add_some_iff : forall left right result,
  int32_add left right = Some result <->
  int32_value result = int32_value left + int32_value right.
```

## `int32_sub_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:221`](../NumericDerivedFacts.v#L221)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_sub_some_iff : forall left right result,
  int32_sub left right = Some result <->
  int32_value result = int32_value left - int32_value right.
```

## `int32_mul_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:232`](../NumericDerivedFacts.v#L232)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_mul_some_iff : forall left right result,
  int32_mul left right = Some result <->
  int32_value result = int32_value left * int32_value right.
```

## `int32_div_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:243`](../NumericDerivedFacts.v#L243)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_div_some_iff : forall left right result,
  int32_div left right = Some result <->
  int32_value right <> 0 /\
  int32_value result = Z.quot (int32_value left) (int32_value right).
```

## `int32_opp_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:262`](../NumericDerivedFacts.v#L262)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_opp_some_iff : forall input result,
  int32_opp input = Some result <->
  int32_value result = - int32_value input.
```

## `int32_add_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:273`](../NumericDerivedFacts.v#L273)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_add_none_iff : forall left right,
  int32_add left right = None <->
  int32_value left + int32_value right < int32_min \/
  int32_max < int32_value left + int32_value right.
```

## `int32_sub_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:282`](../NumericDerivedFacts.v#L282)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_sub_none_iff : forall left right,
  int32_sub left right = None <->
  int32_value left - int32_value right < int32_min \/
  int32_max < int32_value left - int32_value right.
```

## `int32_mul_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:291`](../NumericDerivedFacts.v#L291)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_mul_none_iff : forall left right,
  int32_mul left right = None <->
  int32_value left * int32_value right < int32_min \/
  int32_max < int32_value left * int32_value right.
```

## `int32_div_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:300`](../NumericDerivedFacts.v#L300)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_div_none_iff : forall left right,
  int32_div left right = None <->
  int32_value right = 0 \/
  Z.quot (int32_value left) (int32_value right) < int32_min \/
  int32_max < Z.quot (int32_value left) (int32_value right).
```

## `int32_opp_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:316`](../NumericDerivedFacts.v#L316)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_opp_none_iff : forall input,
  int32_opp input = None <->
  - int32_value input < int32_min \/
  int32_max < - int32_value input.
```

## `int32_binary_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:328`](../NumericDerivedFacts.v#L328)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int32_binary_runtime_error_none_iff : forall operation left right,
  int32_binary_runtime_error operation
    [Value_int32 (Some left); Value_int32 (Some right)] = None <->
  exists result, operation left right = Some result.
```

## `int32_binary_runtime_error_out_of_range_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:340`](../NumericDerivedFacts.v#L340)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int32_binary_runtime_error_out_of_range_iff :
  forall operation left right,
    int32_binary_runtime_error operation
      [Value_int32 (Some left); Value_int32 (Some right)] =
      Some (DataException NumericValueOutOfRange) <->
    operation left right = None.
```

## `int32_div_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:353`](../NumericDerivedFacts.v#L353)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int32_div_runtime_error_none_iff : forall left right,
  int32_div_runtime_error
    [Value_int32 (Some left); Value_int32 (Some right)] = None <->
  int32_value right <> 0 /\
  exists result, int32_div left right = Some result.
```

## `int32_div_runtime_error_division_by_zero_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:370`](../NumericDerivedFacts.v#L370)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int32_div_runtime_error_division_by_zero_iff : forall left right,
  int32_div_runtime_error
    [Value_int32 (Some left); Value_int32 (Some right)] =
    Some (DataException DivisionByZero) <->
  int32_value right = 0.
```

## `int32_div_runtime_error_out_of_range_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:386`](../NumericDerivedFacts.v#L386)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int32_div_runtime_error_out_of_range_iff : forall left right,
  int32_div_runtime_error
    [Value_int32 (Some left); Value_int32 (Some right)] =
    Some (DataException NumericValueOutOfRange) <->
  int32_value right <> 0 /\ int32_div left right = None.
```

## `int32_opp_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:406`](../NumericDerivedFacts.v#L406)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int32_opp_runtime_error_none_iff : forall input,
  int32_opp_runtime_error [Value_int32 (Some input)] = None <->
  exists result, int32_opp input = Some result.
```

## `int64_binary_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:416`](../NumericDerivedFacts.v#L416)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_binary_runtime_error_none_iff :
  forall operation left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_binary_runtime_error operation [left; right] = None <->
    exists result,
      int64_checked (operation left_integer right_integer) = Some result.
```

## `int64_binary_runtime_error_out_of_range_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:433`](../NumericDerivedFacts.v#L433)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_binary_runtime_error_out_of_range_iff :
  forall operation left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_binary_runtime_error operation [left; right] =
      Some (DataException NumericValueOutOfRange) <->
    int64_checked (operation left_integer right_integer) = None.
```

## `int64_div_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:448`](../NumericDerivedFacts.v#L448)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_div_runtime_error_none_iff :
  forall left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_div_runtime_error [left; right] = None <->
    right_integer <> 0 /\
    exists result,
      int64_checked (Z.quot left_integer right_integer) = Some result.
```

## `int64_div_runtime_error_division_by_zero_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:470`](../NumericDerivedFacts.v#L470)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_div_runtime_error_division_by_zero_iff :
  forall left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_div_runtime_error [left; right] =
      Some (DataException DivisionByZero) <->
    right_integer = 0.
```

## `int64_div_runtime_error_out_of_range_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:489`](../NumericDerivedFacts.v#L489)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma int64_div_runtime_error_out_of_range_iff :
  forall left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_div_runtime_error [left; right] =
      Some (DataException NumericValueOutOfRange) <->
    right_integer <> 0 /\
    int64_checked (Z.quot left_integer right_integer) = None.
```

## `interp_cast_int32_to_double_nonnull`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:517`](../NumericDerivedFacts.v#L517)

Purpose/direction: States the interp cast int32 to double nonnull law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_cast_int32_to_double_nonnull` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `floating point`, `special value`

```rocq
Lemma interp_cast_int32_to_double_nonnull : forall value,
  interp_cast_int32_to_double [Value_int32 (Some value)] =
  Value_double (Some (float64_of_Z (int32_value value))).
```

## `interp_cast_int32_to_int64_nonnull`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:522`](../NumericDerivedFacts.v#L522)

Purpose/direction: States the interp cast int32 to int64 nonnull law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_cast_int32_to_int64_nonnull` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma interp_cast_int32_to_int64_nonnull : forall value,
  interp_cast_int32_to_int64 [Value_int32 (Some value)] =
  Value_int64 (Some (int32_to_int64 value)).
```

## `interp_cast_int64_to_int32_nonnull`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:527`](../NumericDerivedFacts.v#L527)

Purpose/direction: States the interp cast int64 to int32 nonnull law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_cast_int64_to_int32_nonnull` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma interp_cast_int64_to_int32_nonnull : forall value,
  interp_cast_int64_to_int32 [Value_int64 (Some value)] =
  Value_int32 (int32_checked (int64_value value)).
```

## `interp_int32_int64_cast_roundtrip`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:532`](../NumericDerivedFacts.v#L532)

Purpose/direction: Proves the stated cast or representation round trip for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_int32_int64_cast_roundtrip` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`

```rocq
Lemma interp_int32_int64_cast_roundtrip : forall value,
  interp_cast_int64_to_int32
    [Value_int64 (Some (int32_to_int64 value))] =
  Value_int32 (Some value).
```

## `numeric_integer_casts_preserve_null`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:543`](../NumericDerivedFacts.v#L543)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_integer_casts_preserve_null` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `BIGINT`, `int64`, `floating point`, `special value`

```rocq
Lemma numeric_integer_casts_preserve_null :
  interp_cast_int32_to_double [Value_int32 None] = Value_double None /\
  interp_cast_int32_to_int64 [Value_int32 None] = Value_int64 None /\
  interp_cast_int64_to_int32 [Value_int64 None] = Value_int32 None /\
  interp_cast_numeric_to_int32 [Value_numeric None] = Value_int32 None.
```

## `scalar_widening_casts_runtime_safe`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:550`](../NumericDerivedFacts.v#L550)

Purpose/direction: Establishes the explicit runtime-safety direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_widening_casts_runtime_safe : forall values,
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt32ToDouble) values = None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt32ToInt64) values = None.
```

## `scalar_cast_int64_to_int32_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:557`](../NumericDerivedFacts.v#L557)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_int64_to_int32_runtime_error_none_iff : forall value,
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt64ToInt32)
    [Value_int64 (Some value)] = None <->
  exists result, int32_checked (int64_value value) = Some result.
```

## `scalar_cast_int64_to_int32_out_of_range_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:569`](../NumericDerivedFacts.v#L569)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_int64_to_int32_out_of_range_iff : forall value,
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt64ToInt32)
    [Value_int64 (Some value)] =
      Some (DataException NumericValueOutOfRange) <->
  int32_checked (int64_value value) = None.
```

## `numeric_to_int32_checked_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:582`](../NumericDerivedFacts.v#L582)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma numeric_to_int32_checked_some_iff : forall value result,
  numeric_to_int32_checked value = Some result <->
  exists finite,
    value = NumericFinite finite /\
    int32_checked (numeric_finite_rounded_coeff finite 0) = Some result.
```

## `numeric_to_int32_checked_result_value`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:599`](../NumericDerivedFacts.v#L599)

Purpose/direction: States the numeric to int32 checked result value law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_to_int32_checked_result_value` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma numeric_to_int32_checked_result_value : forall value result,
  numeric_to_int32_checked value = Some result ->
  exists finite,
    value = NumericFinite finite /\
    int32_value result = numeric_finite_rounded_coeff finite 0.
```

## `scalar_cast_numeric_to_int32_finite_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:612`](../NumericDerivedFacts.v#L612)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_numeric_to_int32_finite_runtime_error_none_iff :
  forall finite,
    scalar_operator_local_runtime_error
      (ScalarCast ScalarCastNumericToInt32)
      [Value_numeric (Some (NumericFinite finite))] = None <->
    exists result,
      numeric_to_int32_checked (NumericFinite finite) = Some result.
```

## `scalar_cast_numeric_to_int32_special_unsupported`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:627`](../NumericDerivedFacts.v#L627)

Purpose/direction: States the scalar cast numeric to int32 special unsupported law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `scalar_cast_numeric_to_int32_special_unsupported` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma scalar_cast_numeric_to_int32_special_unsupported : forall value,
  (value = NumericNegInfinity \/
   value = NumericPosInfinity \/
   value = NumericNaN) ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastNumericToInt32)
    [Value_numeric (Some value)] = Some FeatureNotSupported.
```

## `float32_add_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:642`](../NumericDerivedFacts.v#L642)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float32_add_runtime_error_none_iff : forall operation left right,
  float32_add_runtime_error operation
    [Value_float (Some left); Value_float (Some right)] = None <->
  andb (float32_is_infinite (operation left right))
    (andb (negb (float32_is_infinite left))
      (negb (float32_is_infinite right))) = false.
```

## `float64_add_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:658`](../NumericDerivedFacts.v#L658)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float64_add_runtime_error_none_iff : forall operation left right,
  float64_add_runtime_error operation
    [Value_double (Some left); Value_double (Some right)] = None <->
  andb (float64_is_infinite (operation left right))
    (andb (negb (float64_is_infinite left))
      (negb (float64_is_infinite right))) = false.
```

## `float32_mul_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:674`](../NumericDerivedFacts.v#L674)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float32_mul_runtime_error_none_iff : forall left right,
  float32_mul_runtime_error
    [Value_float (Some left); Value_float (Some right)] = None <->
  andb (float32_is_infinite (float32_mul left right))
    (andb (negb (float32_is_infinite left))
      (negb (float32_is_infinite right))) = false /\
  andb (float32_is_zero (float32_mul left right))
    (andb (negb (float32_is_zero left))
      (negb (float32_is_zero right))) = false.
```

## `float64_mul_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:705`](../NumericDerivedFacts.v#L705)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float64_mul_runtime_error_none_iff : forall left right,
  float64_mul_runtime_error
    [Value_double (Some left); Value_double (Some right)] = None <->
  andb (float64_is_infinite (float64_mul left right))
    (andb (negb (float64_is_infinite left))
      (negb (float64_is_infinite right))) = false /\
  andb (float64_is_zero (float64_mul left right))
    (andb (negb (float64_is_zero left))
      (negb (float64_is_zero right))) = false.
```

## `float32_div_runtime_error_division_by_zero_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:736`](../NumericDerivedFacts.v#L736)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float32_div_runtime_error_division_by_zero_iff : forall left right,
  float32_div_runtime_error
    [Value_float (Some left); Value_float (Some right)] =
      Some (DataException DivisionByZero) <->
  andb (float32_is_zero right) (negb (float32_is_nan left)) = true.
```

## `float64_div_runtime_error_division_by_zero_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:764`](../NumericDerivedFacts.v#L764)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float64_div_runtime_error_division_by_zero_iff : forall left right,
  float64_div_runtime_error
    [Value_double (Some left); Value_double (Some right)] =
      Some (DataException DivisionByZero) <->
  andb (float64_is_zero right) (negb (float64_is_nan left)) = true.
```

## `float32_div_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:792`](../NumericDerivedFacts.v#L792)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float32_div_runtime_error_none_iff : forall left right,
  float32_div_runtime_error
    [Value_float (Some left); Value_float (Some right)] = None <->
  andb (float32_is_zero right) (negb (float32_is_nan left)) = false /\
  andb (float32_is_infinite (float32_div left right))
    (negb (float32_is_infinite left)) = false /\
  andb (float32_is_zero (float32_div left right))
    (andb (negb (float32_is_zero left))
      (negb (float32_is_infinite right))) = false.
```

## `float64_div_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:827`](../NumericDerivedFacts.v#L827)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma float64_div_runtime_error_none_iff : forall left right,
  float64_div_runtime_error
    [Value_double (Some left); Value_double (Some right)] = None <->
  andb (float64_is_zero right) (negb (float64_is_nan left)) = false /\
  andb (float64_is_infinite (float64_div left right))
    (negb (float64_is_infinite left)) = false /\
  andb (float64_is_zero (float64_div left right))
    (andb (negb (float64_is_zero left))
      (negb (float64_is_infinite right))) = false.
```

## `numeric_add_commutative`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:864`](../NumericDerivedFacts.v#L864)

Purpose/direction: Establishes commutativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_add_commutative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_add_commutative : forall left right,
  numeric_add left right = numeric_add right left.
```

## `numeric_mul_commutative`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:873`](../NumericDerivedFacts.v#L873)

Purpose/direction: Establishes commutativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_mul_commutative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_mul_commutative : forall left right,
  numeric_mul left right = numeric_mul right left.
```

## `numeric_opp_involutive`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:882`](../NumericDerivedFacts.v#L882)

Purpose/direction: States the numeric opp involutive law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_opp_involutive` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_opp_involutive : forall value,
  numeric_opp (numeric_opp value) = value.
```

## `numeric_add_zero_left`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:889`](../NumericDerivedFacts.v#L889)

Purpose/direction: States the numeric add zero left law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_add_zero_left` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_add_zero_left : forall value,
  numeric_add numeric_zero value = value.
```

## `numeric_sub_self_finite`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:897`](../NumericDerivedFacts.v#L897)

Purpose/direction: States the numeric sub self finite law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_sub_self_finite` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sub_self_finite : forall value,
  numeric_sub (NumericFinite value) (NumericFinite value) = numeric_zero.
```

## `numeric_min_idempotent`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:905`](../NumericDerivedFacts.v#L905)

Purpose/direction: Establishes idempotence for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_min_idempotent` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_min_idempotent : forall value,
  numeric_min value value = value.
```

## `numeric_max_idempotent`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:912`](../NumericDerivedFacts.v#L912)

Purpose/direction: Establishes idempotence for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_max_idempotent` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_max_idempotent : forall value,
  numeric_max value value = value.
```

## `numeric_is_nan_true_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:922`](../NumericDerivedFacts.v#L922)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_is_nan_true_iff : forall value,
  numeric_is_nan value = true <-> value = NumericNaN.
```

## `numeric_rounded_coeff_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:929`](../NumericDerivedFacts.v#L929)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_rounded_coeff_some_iff : forall value scale coefficient,
  numeric_rounded_coeff value scale = Some coefficient <->
  exists finite,
    value = NumericFinite finite /\
    coefficient = numeric_finite_rounded_coeff finite scale.
```

## `numeric_decimal_parts_some_is_finite`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:946`](../NumericDerivedFacts.v#L946)

Purpose/direction: States the numeric decimal parts some is finite law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_decimal_parts_some_is_finite` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_decimal_parts_some_is_finite : forall value parts,
  numeric_decimal_parts value = Some parts ->
  exists finite, value = NumericFinite finite.
```

## `numeric_round_special_identity`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:955`](../NumericDerivedFacts.v#L955)

Purpose/direction: States the numeric round special identity law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_round_special_identity` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_round_special_identity : forall value scale,
  (value = NumericNegInfinity \/
   value = NumericPosInfinity \/
   value = NumericNaN) ->
  numeric_round_to_scale value scale = value.
```

## `numeric_runtime_fits_special`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:964`](../NumericDerivedFacts.v#L964)

Purpose/direction: States the numeric runtime fits special law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_runtime_fits_special : forall value,
  (value = NumericNegInfinity \/
   value = NumericPosInfinity \/
   value = NumericNaN) ->
  numeric_runtime_fits_bool value = true.
```

## `numeric_typmod_valid_true_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:975`](../NumericDerivedFacts.v#L975)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_typmod_valid_true_iff : forall precision scale,
  numeric_typmod_valid_bool precision scale = true <->
  1 <= precision /\ precision <= numeric_max_precision /\
  numeric_min_scale <= scale /\ scale <= numeric_max_scale.
```

## `numeric_fits_typmod_true_implies_valid`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:986`](../NumericDerivedFacts.v#L986)

Purpose/direction: States the numeric fits typmod true implies valid law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_fits_typmod_true_implies_valid` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_fits_typmod_true_implies_valid : forall value precision scale,
  numeric_fits_typmod_bool value precision scale = true ->
  numeric_typmod_valid_bool precision scale = true.
```

## `numeric_cast_typmod_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:995`](../NumericDerivedFacts.v#L995)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_cast_typmod_some_iff : forall value precision scale result,
  numeric_cast_typmod value precision scale = Some result <->
  numeric_fits_typmod_bool value precision scale = true /\
  result = numeric_round_to_scale value scale.
```

## `numeric_cast_typmod_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1011`](../NumericDerivedFacts.v#L1011)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_cast_typmod_none_iff : forall value precision scale,
  numeric_cast_typmod value precision scale = None <->
  numeric_fits_typmod_bool value precision scale = false.
```

## `numeric_cast_typmod_nan_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1022`](../NumericDerivedFacts.v#L1022)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `floating point`, `special value`

```rocq
Lemma numeric_cast_typmod_nan_iff : forall precision scale,
  numeric_cast_typmod NumericNaN precision scale = Some NumericNaN <->
  numeric_typmod_valid_bool precision scale = true.
```

## `numeric_cast_typmod_infinity_rejected`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1033`](../NumericDerivedFacts.v#L1033)

Purpose/direction: States the numeric cast typmod infinity rejected law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_cast_typmod_infinity_rejected` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `floating point`, `special value`

```rocq
Lemma numeric_cast_typmod_infinity_rejected : forall value precision scale,
  (value = NumericNegInfinity \/ value = NumericPosInfinity) ->
  numeric_cast_typmod value precision scale = None.
```

## `numeric_of_scaled_with_typmod_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1042`](../NumericDerivedFacts.v#L1042)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_of_scaled_with_typmod_some_iff :
  forall precision scale coefficient result,
    numeric_of_scaled_with_typmod precision scale coefficient = Some result <->
    numeric_fits_typmod_bool
      (numeric_of_scaled coefficient scale) precision scale = true /\
    result = numeric_round_to_scale
      (numeric_of_scaled coefficient scale) scale.
```

## `numeric_div_with_typmod_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1055`](../NumericDerivedFacts.v#L1055)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_div_with_typmod_some_iff :
  forall left left_scale right right_scale precision scale result,
    numeric_div_with_typmod
      left left_scale right right_scale precision scale = Some result <->
    exists quotient,
      numeric_div_at_scales left left_scale right right_scale = Some quotient /\
      numeric_cast_typmod quotient precision scale = Some result.
```

## `numeric_result_runtime_error_none_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1079`](../NumericDerivedFacts.v#L1079)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_result_runtime_error_none_iff : forall result,
  numeric_result_runtime_error result = None <->
  numeric_runtime_fits_bool result = true.
```

## `numeric_binary_runtime_error_total`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1089`](../NumericDerivedFacts.v#L1089)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_binary_runtime_error_total : forall operation left right,
  numeric_runtime_fits_bool (operation left right) = true ->
  numeric_binary_runtime_error operation
    [Value_numeric (Some left); Value_numeric (Some right)] = None.
```

## `numeric_unary_runtime_error_total`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1099`](../NumericDerivedFacts.v#L1099)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_unary_runtime_error_total : forall operation input,
  numeric_runtime_fits_bool (operation input) = true ->
  numeric_unary_runtime_error operation [Value_numeric (Some input)] = None.
```

## `numeric_typmod_runtime_error_success_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1108`](../NumericDerivedFacts.v#L1108)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_typmod_runtime_error_success_iff :
  forall value precision scale,
    numeric_typmod_runtime_error
      [Value_numeric (Some value); Value_Z (Some precision);
       Value_Z (Some scale)] = None <->
    exists result,
      numeric_cast_typmod value precision scale = Some result.
```

## `numeric_typmod_runtime_error_failure_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1125`](../NumericDerivedFacts.v#L1125)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_typmod_runtime_error_failure_iff :
  forall value precision scale,
    numeric_typmod_runtime_error
      [Value_numeric (Some value); Value_Z (Some precision);
       Value_Z (Some scale)] =
      Some (DataException NumericValueOutOfRange) <->
    numeric_cast_typmod value precision scale = None.
```

## `numeric_div_nan_left`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1142`](../NumericDerivedFacts.v#L1142)

Purpose/direction: States the numeric div nan left law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_div_nan_left` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_div_nan_left : forall right left_scale right_scale,
  numeric_div_at_scales NumericNaN left_scale right right_scale =
  Some NumericNaN.
```

## `numeric_div_nan_right`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1147`](../NumericDerivedFacts.v#L1147)

Purpose/direction: States the numeric div nan right law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_div_nan_right` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_div_nan_right : forall left left_scale right_scale,
  numeric_div_at_scales left left_scale NumericNaN right_scale =
  Some NumericNaN.
```

## `numeric_div_finite_by_infinity`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1152`](../NumericDerivedFacts.v#L1152)

Purpose/direction: States the numeric div finite by infinity law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_div_finite_by_infinity` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_div_finite_by_infinity : forall finite divisor left_scale right_scale,
  (divisor = NumericNegInfinity \/ divisor = NumericPosInfinity) ->
  numeric_div_at_scales
    (NumericFinite finite) left_scale divisor right_scale = Some numeric_zero.
```

## `numeric_div_runtime_error_zero_divisor`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1160`](../NumericDerivedFacts.v#L1160)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_runtime_error_zero_divisor : forall left left_scale right_scale,
  numeric_div_runtime_error
    [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
     Value_numeric (Some numeric_zero); Value_Z (Some right_scale)] =
  Some (DataException DivisionByZero).
```

## `numeric_div_runtime_error_nan`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1171`](../NumericDerivedFacts.v#L1171)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_runtime_error_nan :
  forall left left_scale right right_scale,
    (numeric_is_nan left = true \/ numeric_is_nan right = true) ->
    numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] = None.
```

## `numeric_div_runtime_error_division_by_zero`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1184`](../NumericDerivedFacts.v#L1184)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_runtime_error_division_by_zero :
  forall left left_scale right right_scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = true ->
    numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] =
      Some (DataException DivisionByZero).
```

## `numeric_div_runtime_error_success_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1199`](../NumericDerivedFacts.v#L1199)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_runtime_error_success_iff :
  forall left left_scale right right_scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    (numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] = None <->
     exists result,
       numeric_div_at_scales left left_scale right right_scale = Some result /\
       numeric_runtime_fits_bool result = true).
```

## `numeric_div_runtime_error_invalid_scale`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1232`](../NumericDerivedFacts.v#L1232)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_runtime_error_invalid_scale :
  forall left left_scale right right_scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    (numeric_display_scale_valid_bool left_scale = false \/
     numeric_display_scale_valid_bool right_scale = false) ->
    numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
```

## `numeric_div_typmod_runtime_error_success_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1252`](../NumericDerivedFacts.v#L1252)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_typmod_runtime_error_success_iff :
  forall left left_scale right right_scale precision scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    (numeric_div_typmod_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale);
       Value_Z (Some precision); Value_Z (Some scale)] = None <->
     exists result,
       numeric_div_with_typmod
         left left_scale right right_scale precision scale = Some result).
```

## `numeric_div_typmod_runtime_error_total`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1278`](../NumericDerivedFacts.v#L1278)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_div_typmod_runtime_error_total :
  forall left left_scale right right_scale precision scale result,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_with_typmod
      left left_scale right right_scale precision scale = Some result ->
    numeric_div_typmod_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale);
       Value_Z (Some precision); Value_Z (Some scale)] = None.
```

## `numeric_sum_from_state_empty`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1303`](../NumericDerivedFacts.v#L1303)

Purpose/direction: States the exact empty-input or empty-result law for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_from_state_empty` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_from_state_empty : forall state,
  numeric_sum_total_count state = 0 ->
  numeric_sum_from_state state = None.
```

## `numeric_sum_from_state_special`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1311`](../NumericDerivedFacts.v#L1311)

Purpose/direction: States the numeric sum from state special law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_from_state_special` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_from_state_special : forall state special,
  numeric_sum_total_count state <> 0 ->
  numeric_agg_special_result
    (numeric_sum_nan_count state)
    (numeric_sum_pos_inf_count state)
    (numeric_sum_neg_inf_count state) = Some special ->
  numeric_sum_from_state state = Some special.
```

## `numeric_sum_from_state_finite`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1327`](../NumericDerivedFacts.v#L1327)

Purpose/direction: States the numeric sum from state finite law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_from_state_finite` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_from_state_finite : forall state,
  numeric_sum_total_count state <> 0 ->
  numeric_agg_special_result
    (numeric_sum_nan_count state)
    (numeric_sum_pos_inf_count state)
    (numeric_sum_neg_inf_count state) = None ->
  numeric_sum_from_state state =
    Some (NumericFinite (numeric_sum_finite_accumulator state)).
```

## `numeric_avg_from_scale_state_empty`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1344`](../NumericDerivedFacts.v#L1344)

Purpose/direction: States the exact empty-input or empty-result law for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_from_scale_state_empty` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_from_scale_state_empty : forall input_scale state,
  numeric_avg_scale_total_count state = 0 ->
  numeric_avg_from_scale_state input_scale state = None.
```

## `numeric_avg_from_scale_state_finite`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1352`](../NumericDerivedFacts.v#L1352)

Purpose/direction: States the numeric avg from scale state finite law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_from_scale_state_finite` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_from_scale_state_finite :
  forall input_scale state result,
    numeric_avg_scale_total_count state <> 0 ->
    numeric_agg_special_result
      (numeric_avg_nan_count state)
      (numeric_avg_pos_inf_count state)
      (numeric_avg_neg_inf_count state) = None ->
    numeric_div_at_scales
      (numeric_of_scaled (numeric_avg_sum_coeff state) input_scale)
      input_scale
      (numeric_of_Z (numeric_avg_finite_count state)) 0 = Some result ->
    numeric_avg_from_scale_state input_scale state = Some result.
```

## `numeric_agg_special_result_nan`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1373`](../NumericDerivedFacts.v#L1373)

Purpose/direction: States the numeric agg special result nan law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_agg_special_result_nan` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_agg_special_result_nan : forall nan_count pos_count neg_count,
  0 < nan_count ->
  numeric_agg_special_result nan_count pos_count neg_count = Some NumericNaN.
```

## `numeric_agg_special_result_mixed_infinities`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1384`](../NumericDerivedFacts.v#L1384)

Purpose/direction: States the numeric agg special result mixed infinities law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_agg_special_result_mixed_infinities` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_agg_special_result_mixed_infinities :
  forall nan_count pos_count neg_count,
    nan_count <= 0 -> 0 < pos_count -> 0 < neg_count ->
    numeric_agg_special_result nan_count pos_count neg_count = Some NumericNaN.
```

## `numeric_agg_special_result_positive_infinity`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1400`](../NumericDerivedFacts.v#L1400)

Purpose/direction: States the numeric agg special result positive infinity law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_agg_special_result_positive_infinity` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_agg_special_result_positive_infinity :
  forall nan_count pos_count neg_count,
    nan_count <= 0 -> 0 < pos_count -> neg_count <= 0 ->
    numeric_agg_special_result nan_count pos_count neg_count =
      Some NumericPosInfinity.
```

## `numeric_agg_special_result_negative_infinity`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1417`](../NumericDerivedFacts.v#L1417)

Purpose/direction: States the numeric agg special result negative infinity law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_agg_special_result_negative_infinity` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`

```rocq
Lemma numeric_agg_special_result_negative_infinity :
  forall nan_count pos_count neg_count,
    nan_count <= 0 -> pos_count <= 0 -> 0 < neg_count ->
    numeric_agg_special_result nan_count pos_count neg_count =
      Some NumericNegInfinity.
```

## `numeric_agg_special_result_none`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1434`](../NumericDerivedFacts.v#L1434)

Purpose/direction: States the numeric agg special result none law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_agg_special_result_none` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_agg_special_result_none : forall nan_count pos_count neg_count,
  nan_count <= 0 -> pos_count <= 0 -> neg_count <= 0 ->
  numeric_agg_special_result nan_count pos_count neg_count = None.
```

## `eval_int32_neq_disjunction_true_of_unequal_constants`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1456`](../NumericDerivedFacts.v#L1456)

Purpose/direction: States the eval int32 disequality disjunction true of unequal constants law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_int32_neq_disjunction_true_of_unequal_constants` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `INTEGER`, `int32`

```rocq
Lemma eval_int32_neq_disjunction_true_of_unequal_constants :
  forall basesort instance value_is_null env subject first_term second_term
      value first second,
    @Interp.interp_aggterm TNull env subject = Value_int32 (Some value) ->
    @Interp.interp_aggterm TNull env first_term = Value_int32 (Some first) ->
    @Interp.interp_aggterm TNull env second_term = Value_int32 (Some second) ->
    @eval_aggterm_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env subject = None ->
    @eval_aggterm_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env first_term = None ->
    @eval_aggterm_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env second_term = None ->
    int32_value first <> int32_value second ->
    forall outcome,
      @eval_formula_expr_outcome TNull relname basesort instance
        unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error value_is_null env
        (FExpr_Conj Formula.Or_F
          (FExpr_Pred (PredicateNeq : FTuples.Tuple.predicate TNull)
            [subject; first_term])
          (FExpr_Pred (PredicateNeq : FTuples.Tuple.predicate TNull)
            [subject; second_term])) outcome <->
      outcome = SqlSuccess Bool3.true3.
```

## `numeric_add_associative`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:23`](../NumericRegroupFacts.v#L23)

Purpose/direction: Establishes associativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_add_associative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_add_associative : forall first second third,
  numeric_add (numeric_add first second) third =
  numeric_add first (numeric_add second third).
```

## `numeric_sum_initial_reachable_invariant`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:41`](../NumericRegroupFacts.v#L41)

Purpose/direction: Preserves the declared typed numeric semantics result across the indicated transformation.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_initial_reachable_invariant` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_initial_reachable_invariant :
  numeric_sum_state_reachable_invariant numeric_sum_initial.
```

## `numeric_sum_transition_preserves_reachable_invariant`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:49`](../NumericRegroupFacts.v#L49)

Purpose/direction: Preserves the declared typed numeric semantics result across the indicated transformation.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_transition_preserves_reachable_invariant` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_transition_preserves_reachable_invariant :
  forall state next,
    numeric_sum_state_reachable_invariant state ->
    numeric_sum_state_reachable_invariant
      (numeric_sum_transition state next).
```

## `numeric_sum_option_regroup`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:80`](../NumericRegroupFacts.v#L80)

Purpose/direction: States the numeric sum option regroup law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_option_regroup` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Theorem numeric_sum_option_regroup : forall groups,
  fold_left numeric_sum_option_add
    (flat_map
      (fun group =>
        match fold_left numeric_sum_option_add group None with
        | Some total => [total]
        | None => []
        end)
      groups)
    None =
  fold_left numeric_sum_option_add (concat groups) None.
```

## `numeric_sum_from_state_transition`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:146`](../NumericRegroupFacts.v#L146)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_from_state_transition` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_from_state_transition : forall state next,
  numeric_sum_state_reachable_invariant state ->
  numeric_sum_from_state (numeric_sum_transition state next) =
  numeric_sum_option_add (numeric_sum_from_state state) next.
```

## `numeric_sum_fold_option_add`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:185`](../NumericRegroupFacts.v#L185)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_fold_option_add` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_fold_option_add : forall numbers state,
  numeric_sum_state_reachable_invariant state ->
  numeric_sum_from_state
    (fold_left numeric_sum_transition numbers state) =
  fold_left numeric_sum_option_add numbers
    (numeric_sum_from_state state).
```

## `numeric_sum_fold_from_initial`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:199`](../NumericRegroupFacts.v#L199)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_fold_from_initial` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Corollary numeric_sum_fold_from_initial : forall numbers,
  numeric_sum_from_state
    (fold_left numeric_sum_transition numbers numeric_sum_initial) =
  fold_left numeric_sum_option_add numbers None.
```

## `interp_sum_numeric_option_fold`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:210`](../NumericRegroupFacts.v#L210)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `interp_sum_numeric_option_fold` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma interp_sum_numeric_option_fold : forall observations,
  forallb is_numeric_value observations = true ->
  interp_sum_numeric observations =
  Value_numeric
    (fold_left numeric_sum_option_add (numeric_values observations) None).
```

## `interp_sum_numeric_singleton`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:223`](../NumericRegroupFacts.v#L223)

Purpose/direction: States the interp sum numeric singleton law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_sum_numeric_singleton` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma interp_sum_numeric_singleton : forall number,
  interp_sum_numeric [Value_numeric number] = Value_numeric number.
```

## `sum_numeric_runtime_error_singleton`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:240`](../NumericRegroupFacts.v#L240)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma sum_numeric_runtime_error_singleton : forall number,
  sum_numeric_runtime_error [Value_numeric number] =
  match number with
  | None => None
  | Some result => numeric_result_runtime_error result
  end.
```

## `interp_sum_numeric_regroup_value_runtime_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:294`](../NumericRegroupFacts.v#L294)

Purpose/direction: States the interp sum numeric regroup value runtime exact law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem interp_sum_numeric_regroup_value_runtime_exact :
  forall groups subtotals,
    Forall
      (fun observations => forallb is_numeric_value observations = true)
      groups ->
    forallb is_numeric_value subtotals = true ->
    numeric_values subtotals =
      flat_map
        (fun numbers =>
          match fold_left numeric_sum_option_add numbers None with
          | Some total => [total]
          | None => []
          end)
        (map numeric_values groups) ->
    interp_sum_numeric subtotals = interp_sum_numeric (concat groups) /\
    sum_numeric_runtime_error subtotals =
      sum_numeric_runtime_error (concat groups).
```

## `tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:531`](../NumericRegroupFacts.v#L531)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `grouping`, `bag`, `scalar`

Search aliases: `numeric and cast semantics`, `GROUP BY`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Permutation
      (tnull_closed_group_sum_numeric_dot_argument_observations
        group_terms group attribute)
      (map
        (fun row =>
          (None, dot TNull row attribute))
        group).
```

## `tnull_closed_group_sum_numeric_dot_value_runtime_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:576`](../NumericRegroupFacts.v#L576)

Purpose/direction: Establishes the displayed closure property for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `GROUP BY`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem tnull_closed_group_sum_numeric_dot_value_runtime_exact :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Interp.interp_aggterm TNull
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
      NullValues.interp_sum_numeric
        (map (fun row => dot TNull row attribute) group) /\
    @eval_aggterm_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
      NullValues.sum_numeric_runtime_error
        (map (fun row => dot TNull row attribute) group).
```

## `query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:728`](../NumericRegroupFacts.v#L728)

Purpose/direction: Regroups closed-group SUM(NUMERIC column) values while preserving only the outer SUM value and its local runtime callback.

Applicability: Use only for the displayed closed-group SUM(NUMERIC Dot) family. The conclusion covers the outer SUM value/local callback; it does not prove inner aggregate safety or a complete grouped-query outcome.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `grouping`, `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `GROUP BY`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact :
  forall grouping_env rows group_terms attribute,
    group_terms <> nil ->
    Forall
      (fun row =>
        attribute inS labels TNull row /\
        NullValues.is_numeric_value (dot TNull row attribute) = true)
      rows ->
    let groups := @query_make_groups TNull grouping_env rows group_terms in
    let grouped_sums :=
      map
        (fun group =>
          Interp.interp_aggterm TNull
            (Env.env_g TNull nil
              (@Env.Group_By TNull group_terms) group)
            (tnull_sum_numeric_dot_term attribute))
        groups in
    NullValues.interp_sum_numeric grouped_sums =
      NullValues.interp_sum_numeric
        (map (fun row => dot TNull row attribute) rows) /\
    NullValues.sum_numeric_runtime_error grouped_sums =
      NullValues.sum_numeric_runtime_error
        (map (fun row => dot TNull row attribute) rows).
```

## `numeric_values_finite_observations`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:880`](../NumericRegroupFacts.v#L880)

Purpose/direction: States the numeric values finite observations law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_values_finite_observations` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_values_finite_observations : forall numbers,
  numeric_values (map finite_numeric_observation numbers) =
  map NumericFinite numbers.
```

## `finite_observations_all_numeric`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:887`](../NumericRegroupFacts.v#L887)

Purpose/direction: States the finite observations all numeric law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `finite_observations_all_numeric` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma finite_observations_all_numeric : forall numbers,
  forallb is_numeric_value (map finite_numeric_observation numbers) = true.
```

## `numeric_sum_finite_fold_state`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:893`](../NumericRegroupFacts.v#L893)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_finite_fold_state` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_finite_fold_state :
  forall numbers finite_count nan_count pos_inf_count neg_inf_count accumulator,
    fold_left numeric_sum_transition (map NumericFinite numbers)
      (NumericSumState finite_count nan_count pos_inf_count neg_inf_count
        accumulator) =
    NumericSumState
      (finite_count + Z.of_nat (length numbers))
      nan_count pos_inf_count neg_inf_count
      (fold_left Qcplus numbers accumulator).
```

## `interp_sum_finite_observations`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:909`](../NumericRegroupFacts.v#L909)

Purpose/direction: States the interp sum finite observations law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_sum_finite_observations` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma interp_sum_finite_observations : forall numbers,
  interp_sum_numeric (map finite_numeric_observation numbers) =
  match numbers with
  | [] => Value_numeric None
  | _ => Value_numeric (Some (NumericFinite (finite_numeric_total numbers)))
  end.
```

## `interp_sum_numeric_values_extensional`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:932`](../NumericRegroupFacts.v#L932)

Purpose/direction: States the interp sum numeric values extensional law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_sum_numeric_values_extensional` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma interp_sum_numeric_values_extensional : forall left right,
  forallb is_numeric_value left = true ->
  forallb is_numeric_value right = true ->
  numeric_values left = numeric_values right ->
  interp_sum_numeric left = interp_sum_numeric right.
```

## `finite_numeric_total_from_accumulator`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:942`](../NumericRegroupFacts.v#L942)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `finite_numeric_total_from_accumulator` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma finite_numeric_total_from_accumulator : forall numbers accumulator,
  fold_left Qcplus numbers accumulator =
  Qcplus accumulator (finite_numeric_total numbers).
```

## `nonempty_group_totals_flatten`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:954`](../NumericRegroupFacts.v#L954)

Purpose/direction: States the exact empty-input or empty-result law for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `nonempty_group_totals_flatten` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `scalar`

Search aliases: `numeric and cast semantics`, `GROUP BY`

```rocq
Lemma nonempty_group_totals_flatten : forall groups,
  finite_numeric_total (nonempty_finite_group_totals groups) =
  finite_numeric_total (concat groups).
```

## `grouped_finite_sums_all_numeric`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:976`](../NumericRegroupFacts.v#L976)

Purpose/direction: States the grouped finite sums all numeric law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `grouped_finite_sums_all_numeric` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma grouped_finite_sums_all_numeric : forall groups,
  forallb is_numeric_value
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) = true.
```

## `numeric_values_grouped_finite_sums`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:988`](../NumericRegroupFacts.v#L988)

Purpose/direction: States the numeric values grouped finite sums law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_values_grouped_finite_sums` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_values_grouped_finite_sums : forall groups,
  numeric_values
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) =
  map NumericFinite (nonempty_finite_group_totals groups).
```

## `nonempty_group_totals_nil_iff`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1001`](../NumericRegroupFacts.v#L1001)

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `grouping`, `scalar`

Search aliases: `numeric and cast semantics`, `GROUP BY`

```rocq
Lemma nonempty_group_totals_nil_iff : forall groups,
  nonempty_finite_group_totals groups = [] <-> concat groups = [].
```

## `interp_sum_numeric_finite_regroup`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1019`](../NumericRegroupFacts.v#L1019)

Purpose/direction: States the interp sum numeric finite regroup law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_sum_numeric_finite_regroup` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Theorem interp_sum_numeric_finite_regroup : forall groups,
  interp_sum_numeric
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) =
  interp_sum_numeric
    (map finite_numeric_observation (concat groups)).
```

## `eval_group_bag_global_success_duplicate_free`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1140`](../NumericRegroupFacts.v#L1140)

Purpose/direction: Inverts or constructs the successful evaluation branch for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome`, `grouping`, `runtime`, `bag`, `scalar`

Search aliases: `numeric and cast semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_group_bag_global_success_duplicate_free :
  forall env select_list having input_bag output_bag,
    @eval_group_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env select_list [] having input_bag (SqlSuccess output_bag) ->
    query_bag_duplicate_free output_bag.
```
