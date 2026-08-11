# Derived numeric, integer, float, and cast facts

Route here for: INTEGER/BIGINT bounds, derived NUMERIC laws, floats, casts, overflow.

This focused catalog contains 141 declarations routed at declaration granularity from `NumericDerivedFacts.v`, `NumericRegroupFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `int32_checked_result_value`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:12`](../NumericDerivedFacts.v#L12)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `int32_checked_defined_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:34`](../NumericDerivedFacts.v#L34)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:49`](../NumericDerivedFacts.v#L49)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:64`](../NumericDerivedFacts.v#L64)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:81`](../NumericDerivedFacts.v#L81)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:98`](../NumericDerivedFacts.v#L98)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int32 checked value law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_checked_value` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_checked_value : forall value,
  int32_checked (int32_value value) = Some value.
```

## `int32_checked_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:110`](../NumericDerivedFacts.v#L110)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_checked_some_iff : forall integer result,
  int32_checked integer = Some result <->
  int32_value result = integer.
```

## `int64_checked_some_iff`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:119`](../NumericDerivedFacts.v#L119)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for typed numeric semantics.

Applicability: Use in either direction to invert or construct a goal about typed numeric semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_checked_some_iff : forall integer result,
  int64_checked integer = Some result <->
  int64_value result = integer.
```

## `int32_to_int64_injective`

Source: [`theories/FormalSQL/NumericDerivedFacts.v:128`](../NumericDerivedFacts.v#L128)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:136`](../NumericDerivedFacts.v#L136)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:142`](../NumericDerivedFacts.v#L142)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:155`](../NumericDerivedFacts.v#L155)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:168`](../NumericDerivedFacts.v#L168)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:181`](../NumericDerivedFacts.v#L181)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:203`](../NumericDerivedFacts.v#L203)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:214`](../NumericDerivedFacts.v#L214)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:225`](../NumericDerivedFacts.v#L225)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:236`](../NumericDerivedFacts.v#L236)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:255`](../NumericDerivedFacts.v#L255)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:266`](../NumericDerivedFacts.v#L266)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:275`](../NumericDerivedFacts.v#L275)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:284`](../NumericDerivedFacts.v#L284)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:293`](../NumericDerivedFacts.v#L293)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:309`](../NumericDerivedFacts.v#L309)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:321`](../NumericDerivedFacts.v#L321)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:333`](../NumericDerivedFacts.v#L333)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:346`](../NumericDerivedFacts.v#L346)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:363`](../NumericDerivedFacts.v#L363)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:379`](../NumericDerivedFacts.v#L379)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:399`](../NumericDerivedFacts.v#L399)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:409`](../NumericDerivedFacts.v#L409)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:426`](../NumericDerivedFacts.v#L426)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:441`](../NumericDerivedFacts.v#L441)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:463`](../NumericDerivedFacts.v#L463)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:482`](../NumericDerivedFacts.v#L482)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:510`](../NumericDerivedFacts.v#L510)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:515`](../NumericDerivedFacts.v#L515)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:520`](../NumericDerivedFacts.v#L520)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:525`](../NumericDerivedFacts.v#L525)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:536`](../NumericDerivedFacts.v#L536)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:543`](../NumericDerivedFacts.v#L543)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:550`](../NumericDerivedFacts.v#L550)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:562`](../NumericDerivedFacts.v#L562)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:575`](../NumericDerivedFacts.v#L575)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:592`](../NumericDerivedFacts.v#L592)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:605`](../NumericDerivedFacts.v#L605)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:620`](../NumericDerivedFacts.v#L620)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:635`](../NumericDerivedFacts.v#L635)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:651`](../NumericDerivedFacts.v#L651)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:667`](../NumericDerivedFacts.v#L667)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:698`](../NumericDerivedFacts.v#L698)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:729`](../NumericDerivedFacts.v#L729)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:757`](../NumericDerivedFacts.v#L757)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:785`](../NumericDerivedFacts.v#L785)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:820`](../NumericDerivedFacts.v#L820)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:857`](../NumericDerivedFacts.v#L857)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:866`](../NumericDerivedFacts.v#L866)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:875`](../NumericDerivedFacts.v#L875)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:882`](../NumericDerivedFacts.v#L882)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:890`](../NumericDerivedFacts.v#L890)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:898`](../NumericDerivedFacts.v#L898)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:905`](../NumericDerivedFacts.v#L905)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:915`](../NumericDerivedFacts.v#L915)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:922`](../NumericDerivedFacts.v#L922)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:939`](../NumericDerivedFacts.v#L939)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:948`](../NumericDerivedFacts.v#L948)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:957`](../NumericDerivedFacts.v#L957)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:968`](../NumericDerivedFacts.v#L968)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:979`](../NumericDerivedFacts.v#L979)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:988`](../NumericDerivedFacts.v#L988)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1004`](../NumericDerivedFacts.v#L1004)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1015`](../NumericDerivedFacts.v#L1015)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1026`](../NumericDerivedFacts.v#L1026)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1035`](../NumericDerivedFacts.v#L1035)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1048`](../NumericDerivedFacts.v#L1048)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1072`](../NumericDerivedFacts.v#L1072)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1082`](../NumericDerivedFacts.v#L1082)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1092`](../NumericDerivedFacts.v#L1092)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1101`](../NumericDerivedFacts.v#L1101)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1118`](../NumericDerivedFacts.v#L1118)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1135`](../NumericDerivedFacts.v#L1135)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1140`](../NumericDerivedFacts.v#L1140)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1145`](../NumericDerivedFacts.v#L1145)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1153`](../NumericDerivedFacts.v#L1153)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1164`](../NumericDerivedFacts.v#L1164)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1177`](../NumericDerivedFacts.v#L1177)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1192`](../NumericDerivedFacts.v#L1192)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1225`](../NumericDerivedFacts.v#L1225)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1245`](../NumericDerivedFacts.v#L1245)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1271`](../NumericDerivedFacts.v#L1271)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1296`](../NumericDerivedFacts.v#L1296)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1304`](../NumericDerivedFacts.v#L1304)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1320`](../NumericDerivedFacts.v#L1320)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1337`](../NumericDerivedFacts.v#L1337)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1345`](../NumericDerivedFacts.v#L1345)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1366`](../NumericDerivedFacts.v#L1366)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1377`](../NumericDerivedFacts.v#L1377)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1393`](../NumericDerivedFacts.v#L1393)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1410`](../NumericDerivedFacts.v#L1410)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericDerivedFacts.v:1427`](../NumericDerivedFacts.v#L1427)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `numeric_add_associative`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:23`](../NumericRegroupFacts.v#L23)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `numeric_sum_option_regroup_from`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:80`](../NumericRegroupFacts.v#L80)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric sum option regroup from law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_option_regroup_from` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Theorem numeric_sum_option_regroup_from : forall groups current,
  fold_left numeric_sum_option_add
    (flat_map
      (fun group =>
        match fold_left numeric_sum_option_add group None with
        | Some total => [total]
        | None => []
        end)
      groups)
    current =
  fold_left numeric_sum_option_add (concat groups) current.
```

## `numeric_sum_option_regroup`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:146`](../NumericRegroupFacts.v#L146)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric sum option regroup law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_option_regroup` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Corollary numeric_sum_option_regroup : forall groups,
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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:161`](../NumericRegroupFacts.v#L161)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:200`](../NumericRegroupFacts.v#L200)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:214`](../NumericRegroupFacts.v#L214)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:225`](../NumericRegroupFacts.v#L225)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:238`](../NumericRegroupFacts.v#L238)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:255`](../NumericRegroupFacts.v#L255)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:309`](../NumericRegroupFacts.v#L309)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:546`](../NumericRegroupFacts.v#L546)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:591`](../NumericRegroupFacts.v#L591)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `fixed_decimal_conforms_shape`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:689`](../NumericRegroupFacts.v#L689)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fixed decimal conforms shape law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_conforms_shape` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_conforms_shape :
  forall name precision scale observation,
    value_conforms_attribute
      (AttrDecimal name precision scale) observation ->
    fixed_decimal_value_shape precision scale observation.
```

## `fixed_decimal_shapes_are_numeric`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:718`](../NumericRegroupFacts.v#L718)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fixed decimal shapes are numeric law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_shapes_are_numeric` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_shapes_are_numeric :
  forall precision scale observations,
    Forall (fixed_decimal_value_shape precision scale) observations ->
    forallb is_numeric_value observations = true.
```

## `fixed_decimal_conforms_numeric_values`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:730`](../NumericRegroupFacts.v#L730)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fixed decimal conforms numeric values law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_conforms_numeric_values` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_conforms_numeric_values :
  forall name precision scale observations,
    Forall
      (value_conforms_attribute (AttrDecimal name precision scale))
      observations ->
    Forall (fixed_decimal_numeric_shape precision scale)
      (numeric_values observations).
```

## `fixed_decimal_conforms_typmod_forallb`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:749`](../NumericRegroupFacts.v#L749)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fixed decimal conforms typmod forallb law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_conforms_typmod_forallb` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma fixed_decimal_conforms_typmod_forallb :
  forall name precision scale observations,
    Forall
      (value_conforms_attribute (AttrDecimal name precision scale))
      observations ->
    forallb (numeric_conforms_typmod_bool precision scale)
      (numeric_values observations) = true.
```

## `numeric_values_length_le`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:767`](../NumericRegroupFacts.v#L767)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_values_length_le` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_values_length_le :
  forall observations,
    (List.length (numeric_values observations) <=
      List.length observations)%nat.
```

## `numeric_add_same_nonnegative_scale`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:778`](../NumericRegroupFacts.v#L778)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric add same nonnegative scale law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_add_same_nonnegative_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_add_same_nonnegative_scale :
  forall left right scale,
    0 <= scale ->
    numeric_add (numeric_of_scaled left scale)
      (numeric_of_scaled right scale) =
    numeric_of_scaled (left + right) scale.
```

## `numeric_add_same_negative_scale`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:811`](../NumericRegroupFacts.v#L811)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric add same negative scale law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_add_same_negative_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_add_same_negative_scale :
  forall left right scale,
    scale < 0 ->
    numeric_add (numeric_of_scaled left scale)
      (numeric_of_scaled right scale) =
    numeric_of_scaled (left + right) scale.
```

## `numeric_add_same_scale`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:845`](../NumericRegroupFacts.v#L845)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric add same scale law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_add_same_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_add_same_scale :
  forall left right scale,
    numeric_add (numeric_of_scaled left scale)
      (numeric_of_scaled right scale) =
    numeric_of_scaled (left + right) scale.
```

## `fixed_decimal_sum_option_shape_mono`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:864`](../NumericRegroupFacts.v#L864)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fixed decimal sum option shape mono law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_sum_option_shape_mono` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_sum_option_shape_mono :
  forall scale lower upper state,
    lower <= upper ->
    fixed_decimal_sum_option_shape scale lower state ->
    fixed_decimal_sum_option_shape scale upper state.
```

## `fixed_decimal_sum_fold_shape`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:877`](../NumericRegroupFacts.v#L877)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_sum_fold_shape` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_sum_fold_shape :
  forall precision scale numbers current bound,
    0 <= precision ->
    Forall (fixed_decimal_numeric_shape precision scale) numbers ->
    0 <= bound ->
    fixed_decimal_sum_option_shape scale bound current ->
    fixed_decimal_sum_option_shape scale
      (bound + Z.of_nat (List.length numbers) * Z.pow 10 precision)
      (fold_left numeric_sum_option_add numbers current).
```

## `fixed_decimal_sum_runtime_safe_of_cardinality`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:920`](../NumericRegroupFacts.v#L920)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates typed numeric semantics to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem fixed_decimal_sum_runtime_safe_of_cardinality :
  forall name precision scale observations max_count accumulator_bound,
    0 <= precision ->
    0 <= max_count ->
    Z.of_nat (List.length observations) <= max_count ->
    max_count * Z.pow 10 precision <= accumulator_bound ->
    (forall coefficient,
      Z.abs coefficient <= accumulator_bound ->
      numeric_runtime_fits_bool
        (numeric_of_scaled coefficient scale) = true) ->
    Forall
      (value_conforms_attribute (AttrDecimal name precision scale))
      observations ->
    sum_numeric_runtime_error observations = None.
```

## `fixed_decimal_avg_transition_shape`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:984`](../NumericRegroupFacts.v#L984)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_avg_transition_shape` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_avg_transition_shape :
  forall precision scale state number,
    0 <= precision ->
    fixed_decimal_avg_state_shape precision state ->
    fixed_decimal_numeric_shape precision scale number ->
    fixed_decimal_avg_state_shape precision
      (numeric_avg_scale_transition scale state number).
```

## `fixed_decimal_avg_fold_shape`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1007`](../NumericRegroupFacts.v#L1007)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `fixed_decimal_avg_fold_shape` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma fixed_decimal_avg_fold_shape :
  forall precision scale numbers,
    0 <= precision ->
    Forall (fixed_decimal_numeric_shape precision scale) numbers ->
    fixed_decimal_avg_state_shape precision
      (fold_left (numeric_avg_scale_transition scale) numbers
        numeric_avg_scale_initial).
```

## `fixed_decimal_avg_runtime_safe_of_cardinality`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1039`](../NumericRegroupFacts.v#L1039)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates typed numeric semantics to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric and cast semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem fixed_decimal_avg_runtime_safe_of_cardinality :
  forall name precision scale observations max_count,
    numeric_typmod_valid_bool precision scale = true ->
    0 <= precision ->
    Z.of_nat (List.length observations) <= max_count ->
    (forall finite_count coefficient,
      1 <= finite_count <= max_count ->
      Z.abs coefficient <=
        finite_count * Z.pow 10 precision ->
      numeric_div_runtime_error
        [Value_numeric (Some (numeric_of_scaled coefficient scale));
         Value_Z (Some scale);
         Value_numeric (Some (numeric_of_Z finite_count));
         Value_Z (Some 0)] = None) ->
    Forall
      (value_conforms_attribute (AttrDecimal name precision scale))
      observations ->
    avg_numeric_fixed_runtime_error precision scale observations = None.
```

## `numeric_values_finite_observations`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1137`](../NumericRegroupFacts.v#L1137)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1144`](../NumericRegroupFacts.v#L1144)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1150`](../NumericRegroupFacts.v#L1150)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1166`](../NumericRegroupFacts.v#L1166)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1189`](../NumericRegroupFacts.v#L1189)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1199`](../NumericRegroupFacts.v#L1199)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1211`](../NumericRegroupFacts.v#L1211)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1233`](../NumericRegroupFacts.v#L1233)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1245`](../NumericRegroupFacts.v#L1245)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1258`](../NumericRegroupFacts.v#L1258)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1276`](../NumericRegroupFacts.v#L1276)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1399`](../NumericRegroupFacts.v#L1399)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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
      boolean_schedule env select_list [] having input_bag
      (SqlSuccess output_bag) ->
    query_bag_duplicate_free output_bag.
```
