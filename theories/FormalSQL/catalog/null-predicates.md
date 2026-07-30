# NULL, Bool3, predicates, and CASE

Route here for: UNKNOWN/TRUE/FALSE, strict predicates, NULL tests, comparisons, CASE.

This focused catalog contains 99 declarations routed at declaration granularity from `ScalarPredicateFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `andb3_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:33`](../ScalarPredicateFacts.v#L33)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma andb3_unknown_iff : forall left right,
  andb3 left right = unknown3 <->
  (left = unknown3 \/ right = unknown3) /\
  left <> false3 /\ right <> false3.
```

## `orb3_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:69`](../ScalarPredicateFacts.v#L69)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma orb3_unknown_iff : forall left right,
  orb3 left right = unknown3 <->
  (left = unknown3 \/ right = unknown3) /\
  left <> true3 /\ right <> true3.
```

## `negb3_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:105`](../ScalarPredicateFacts.v#L105)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma negb3_true_iff : forall value,
  negb3 value = true3 <-> value = false3.
```

## `negb3_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:112`](../ScalarPredicateFacts.v#L112)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma negb3_false_iff : forall value,
  negb3 value = false3 <-> value = true3.
```

## `negb3_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:119`](../ScalarPredicateFacts.v#L119)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma negb3_unknown_iff : forall value,
  negb3 value = unknown3 <-> value = unknown3.
```

## `value_bool_to_bool3_roundtrip`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:126`](../ScalarPredicateFacts.v#L126)

Purpose/direction: Proves the stated cast or representation round trip for scalar-predicate semantics.

Applicability: Use when the goal or a hypothesis matches the `value_bool_to_bool3_roundtrip` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma value_bool_to_bool3_roundtrip : forall value,
  value_bool_to_bool3 (bool3_to_value_bool value) = value.
```

## `bool3_to_value_bool_injective`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:132`](../ScalarPredicateFacts.v#L132)

Purpose/direction: Recovers source equality from the declared scalar-predicate semantics representation.

Applicability: Use when the goal or a hypothesis matches the `bool3_to_value_bool_injective` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma bool3_to_value_bool_injective : forall left right,
  bool3_to_value_bool left = bool3_to_value_bool right -> left = right.
```

## `bool3_to_value_bool_is_null_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:139`](../ScalarPredicateFacts.v#L139)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma bool3_to_value_bool_is_null_iff : forall value,
  is_null_value (bool3_to_value_bool value) = true <-> value = unknown3.
```

## `value_bool_to_bool3_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:146`](../ScalarPredicateFacts.v#L146)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma value_bool_to_bool3_true_iff : forall value,
  value_bool_to_bool3 value = true3 <->
  value = Value_bool (Some true).
```

## `value_bool_to_bool3_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:157`](../ScalarPredicateFacts.v#L157)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma value_bool_to_bool3_false_iff : forall value,
  value_bool_to_bool3 value = false3 <->
  value = Value_bool (Some false).
```

## `value_bool_to_bool3_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:168`](../ScalarPredicateFacts.v#L168)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma value_bool_to_bool3_unknown_iff : forall value,
  value_bool_to_bool3 value = unknown3 <->
  value <> Value_bool (Some true) /\
  value <> Value_bool (Some false).
```

## `default_value_is_typed_null`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:183`](../ScalarPredicateFacts.v#L183)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `default_value_is_typed_null` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit.

Cross-index: `schema`, `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `schema conformance`, `typing`

```rocq
Lemma default_value_is_typed_null : forall value_type,
  is_null_value (default_value value_type) = true.
```

## `default_value_preserves_type`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:189`](../ScalarPredicateFacts.v#L189)

Purpose/direction: Shows that the indicated operator preserves the displayed scalar-predicate semantics property.

Applicability: Use when the goal or a hypothesis matches the `default_value_preserves_type` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma default_value_preserves_type : forall value_type,
  type_of_value (default_value value_type) = value_type.
```

## `interp_bool_and_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:195`](../ScalarPredicateFacts.v#L195)

Purpose/direction: States the interp bool and bool3 law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_bool_and_bool3` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_and_bool3 : forall left right,
  value_bool_to_bool3 (interp_bool_and [left; right]) =
  andb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right).
```

## `interp_bool_or_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:203`](../ScalarPredicateFacts.v#L203)

Purpose/direction: States the interp bool or bool3 law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_bool_or_bool3` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_or_bool3 : forall left right,
  value_bool_to_bool3 (interp_bool_or [left; right]) =
  orb3 (value_bool_to_bool3 left) (value_bool_to_bool3 right).
```

## `interp_bool_not_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:211`](../ScalarPredicateFacts.v#L211)

Purpose/direction: States the interp bool not bool3 law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_bool_not_bool3` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_not_bool3 : forall value,
  value_bool_to_bool3 (interp_bool_not [value]) =
  negb3 (value_bool_to_bool3 value).
```

## `interp_bool_and_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:219`](../ScalarPredicateFacts.v#L219)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_and_true_iff : forall left right,
  interp_bool_and [left; right] = Value_bool (Some true) <->
  value_bool_to_bool3 left = true3 /\
  value_bool_to_bool3 right = true3.
```

## `interp_bool_and_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:235`](../ScalarPredicateFacts.v#L235)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_and_false_iff : forall left right,
  interp_bool_and [left; right] = Value_bool (Some false) <->
  value_bool_to_bool3 left = false3 \/
  value_bool_to_bool3 right = false3.
```

## `interp_bool_and_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:251`](../ScalarPredicateFacts.v#L251)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_and_unknown_iff : forall left right,
  interp_bool_and [left; right] = Value_bool None <->
  (value_bool_to_bool3 left = unknown3 \/
   value_bool_to_bool3 right = unknown3) /\
  value_bool_to_bool3 left <> false3 /\
  value_bool_to_bool3 right <> false3.
```

## `interp_bool_or_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:276`](../ScalarPredicateFacts.v#L276)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_or_true_iff : forall left right,
  interp_bool_or [left; right] = Value_bool (Some true) <->
  value_bool_to_bool3 left = true3 \/
  value_bool_to_bool3 right = true3.
```

## `interp_bool_or_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:292`](../ScalarPredicateFacts.v#L292)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_or_false_iff : forall left right,
  interp_bool_or [left; right] = Value_bool (Some false) <->
  value_bool_to_bool3 left = false3 /\
  value_bool_to_bool3 right = false3.
```

## `interp_bool_or_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:308`](../ScalarPredicateFacts.v#L308)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_or_unknown_iff : forall left right,
  interp_bool_or [left; right] = Value_bool None <->
  (value_bool_to_bool3 left = unknown3 \/
   value_bool_to_bool3 right = unknown3) /\
  value_bool_to_bool3 left <> true3 /\
  value_bool_to_bool3 right <> true3.
```

## `interp_bool_not_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:333`](../ScalarPredicateFacts.v#L333)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_not_true_iff : forall value,
  interp_bool_not [value] = Value_bool (Some true) <->
  value_bool_to_bool3 value = false3.
```

## `interp_bool_not_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:348`](../ScalarPredicateFacts.v#L348)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_not_false_iff : forall value,
  interp_bool_not [value] = Value_bool (Some false) <->
  value_bool_to_bool3 value = true3.
```

## `interp_bool_not_unknown_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:363`](../ScalarPredicateFacts.v#L363)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_not_unknown_iff : forall value,
  interp_bool_not [value] = Value_bool None <->
  value_bool_to_bool3 value = unknown3.
```

## `interp_bool_and_wrong_arity`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:378`](../ScalarPredicateFacts.v#L378)

Purpose/direction: States the interp bool and wrong arity law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_bool_and_wrong_arity` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_and_wrong_arity : forall values,
  List.length values <> 2%nat -> interp_bool_and values = Value_bool None.
```

## `interp_bool_or_wrong_arity`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:389`](../ScalarPredicateFacts.v#L389)

Purpose/direction: States the interp bool or wrong arity law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_bool_or_wrong_arity` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_or_wrong_arity : forall values,
  List.length values <> 2%nat -> interp_bool_or values = Value_bool None.
```

## `interp_bool_not_wrong_arity`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:400`](../ScalarPredicateFacts.v#L400)

Purpose/direction: States the interp bool not wrong arity law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_bool_not_wrong_arity` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_bool_not_wrong_arity : forall values,
  List.length values <> 1%nat -> interp_bool_not values = Value_bool None.
```

## `interp_bool_and_bool3_congr`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:410`](../ScalarPredicateFacts.v#L410)

Purpose/direction: Transports or composes scalar-predicate semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`, `equivalence`, `congruence`

```rocq
Lemma interp_bool_and_bool3_congr : forall left1 right1 left2 right2,
  value_bool_to_bool3 left1 = value_bool_to_bool3 left2 ->
  value_bool_to_bool3 right1 = value_bool_to_bool3 right2 ->
  interp_bool_and [left1; right1] = interp_bool_and [left2; right2].
```

## `interp_bool_or_bool3_congr`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:419`](../ScalarPredicateFacts.v#L419)

Purpose/direction: Transports or composes scalar-predicate semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`, `equivalence`, `congruence`

```rocq
Lemma interp_bool_or_bool3_congr : forall left1 right1 left2 right2,
  value_bool_to_bool3 left1 = value_bool_to_bool3 left2 ->
  value_bool_to_bool3 right1 = value_bool_to_bool3 right2 ->
  interp_bool_or [left1; right1] = interp_bool_or [left2; right2].
```

## `interp_bool_not_bool3_congr`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:428`](../ScalarPredicateFacts.v#L428)

Purpose/direction: Transports or composes scalar-predicate semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`, `equivalence`, `congruence`

```rocq
Lemma interp_bool_not_bool3_congr : forall left right,
  value_bool_to_bool3 left = value_bool_to_bool3 right ->
  interp_bool_not [left] = interp_bool_not [right].
```

## `is_null_value_true_elim`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:436`](../ScalarPredicateFacts.v#L436)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `is_null_value_true_elim` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `BIGINT`, `int64`, `floating point`, `special value`, `string`, `VARCHAR`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma is_null_value_true_elim : forall value,
  is_null_value value = true ->
  (exists typmod,
      value = Value_string (StringValue typmod None)) \/
  value = Value_Z None \/
  value = Value_int32 None \/
  value = Value_int64 None \/
  value = Value_bool None \/
  value = Value_float None \/
  value = Value_double None \/
  value = Value_numeric None \/
  value = Value_date None \/
  value = Value_time None \/
  value = Value_timestamp None \/
  value = Value_timestamptz None.
```

## `strict_binary_predicate_null_left`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:474`](../ScalarPredicateFacts.v#L474)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `strict_binary_predicate_null_left` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma strict_binary_predicate_null_left : forall predicate left right,
  strict_binary_predicate predicate = true ->
  is_null_value left = true ->
  NullValues.interp_predicate predicate [left; right] = unknown3.
```

## `strict_binary_predicate_null_right`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:487`](../ScalarPredicateFacts.v#L487)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `strict_binary_predicate_null_right` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma strict_binary_predicate_null_right : forall predicate left right,
  strict_binary_predicate predicate = true ->
  is_null_value right = true ->
  NullValues.interp_predicate predicate [left; right] = unknown3.
```

## `strict_binary_predicate_has_arity_two`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:504`](../ScalarPredicateFacts.v#L504)

Purpose/direction: States the strict binary predicate has arity two law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `strict_binary_predicate_has_arity_two` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma strict_binary_predicate_has_arity_two : forall predicate,
  strict_binary_predicate predicate = true ->
  predicate_arity predicate = 2%nat.
```

## `strict_binary_predicate_nonunknown_operands_nonnull`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:513`](../ScalarPredicateFacts.v#L513)

Purpose/direction: States the strict binary predicate nonunknown operands nonnull law for SQL NULL and three-valued behavior, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `strict_binary_predicate_nonunknown_operands_nonnull` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma strict_binary_predicate_nonunknown_operands_nonnull :
  forall predicate left right,
    strict_binary_predicate predicate = true ->
    NullValues.interp_predicate predicate [left; right] <> unknown3 ->
    is_null_value left = false /\ is_null_value right = false.
```

## `interp_predicate_wrong_arity_unknown`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:529`](../ScalarPredicateFacts.v#L529)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_wrong_arity_unknown` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_wrong_arity_unknown : forall predicate values,
  List.length values <> predicate_arity predicate ->
  NullValues.interp_predicate predicate values = unknown3.
```

## `interp_predicate_is_null_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:555`](../ScalarPredicateFacts.v#L555)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_null_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNull [value] = true3 <->
  is_null_value value = true.
```

## `interp_predicate_is_not_null_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:565`](../ScalarPredicateFacts.v#L565)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_null_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] = true3 <->
  is_null_value value = false.
```

## `interp_predicate_is_null_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:575`](../ScalarPredicateFacts.v#L575)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_null_false_iff : forall value,
  NullValues.interp_predicate PredicateIsNull [value] = false3 <->
  is_null_value value = false.
```

## `interp_predicate_is_not_null_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:585`](../ScalarPredicateFacts.v#L585)

Purpose/direction: Gives necessary and sufficient conditions for SQL NULL and three-valued behavior.

Applicability: Use in either direction to invert or construct a goal about SQL NULL and three-valued behavior.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_null_false_iff : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] = false3 <->
  is_null_value value = true.
```

## `interp_predicate_is_not_null_dual`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:595`](../ScalarPredicateFacts.v#L595)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_not_null_dual` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_null_dual : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] =
  negb3 (NullValues.interp_predicate PredicateIsNull [value]).
```

## `interp_predicate_is_null_never_unknown`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:604`](../ScalarPredicateFacts.v#L604)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_null_never_unknown` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_null_never_unknown : forall value,
  NullValues.interp_predicate PredicateIsNull [value] <> unknown3.
```

## `interp_predicate_is_not_null_never_unknown`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:612`](../ScalarPredicateFacts.v#L612)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_not_null_never_unknown` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_null_never_unknown : forall value,
  NullValues.interp_predicate PredicateIsNotNull [value] <> unknown3.
```

## `interp_predicate_eq_true_is_true_acceptance`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:624`](../ScalarPredicateFacts.v#L624)

Purpose/direction: States the interp predicate equality true is true acceptance law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_eq_true_is_true_acceptance` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `filter`, `scalar`

Search aliases: `scalar predicate semantics`, `filter`, `WHERE`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_eq_true_is_true_acceptance : forall value,
  Bool.is_true Bool3
    (NullValues.interp_predicate PredicateEq
      [value; Value_bool (Some true)]) =
  Bool.is_true Bool3
    (NullValues.interp_predicate PredicateIsTrue [value]).
```

## `interp_predicate_is_true_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:643`](../ScalarPredicateFacts.v#L643)

Purpose/direction: States the interp predicate is true bool3 law for SQL NULL and three-valued behavior, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_true_bool3` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_true_bool3 : forall value,
  NullValues.interp_predicate PredicateIsTrue [bool3_to_value_bool value] =
  match value with true3 => true3 | false3 | unknown3 => false3 end.
```

## `interp_predicate_is_not_true_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:650`](../ScalarPredicateFacts.v#L650)

Purpose/direction: States the interp predicate is not true bool3 law for SQL NULL and three-valued behavior, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_not_true_bool3` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_true_bool3 : forall value,
  NullValues.interp_predicate PredicateIsNotTrue [bool3_to_value_bool value] =
  match value with true3 => false3 | false3 | unknown3 => true3 end.
```

## `interp_predicate_is_false_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:657`](../ScalarPredicateFacts.v#L657)

Purpose/direction: States the interp predicate is false bool3 law for SQL NULL and three-valued behavior, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_false_bool3` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_false_bool3 : forall value,
  NullValues.interp_predicate PredicateIsFalse [bool3_to_value_bool value] =
  match value with false3 => true3 | true3 | unknown3 => false3 end.
```

## `interp_predicate_is_not_false_bool3`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:664`](../ScalarPredicateFacts.v#L664)

Purpose/direction: States the interp predicate is not false bool3 law for SQL NULL and three-valued behavior, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_not_false_bool3` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_false_bool3 : forall value,
  NullValues.interp_predicate PredicateIsNotFalse [bool3_to_value_bool value] =
  match value with false3 => false3 | true3 | unknown3 => true3 end.
```

## `interp_predicate_is_true_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:671`](../ScalarPredicateFacts.v#L671)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_true_true_iff : forall value,
  NullValues.interp_predicate PredicateIsTrue [bool3_to_value_bool value] =
    true3 <-> value = true3.
```

## `interp_predicate_is_not_true_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:679`](../ScalarPredicateFacts.v#L679)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_true_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNotTrue [bool3_to_value_bool value] =
    true3 <-> value <> true3.
```

## `interp_predicate_is_false_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:687`](../ScalarPredicateFacts.v#L687)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_false_true_iff : forall value,
  NullValues.interp_predicate PredicateIsFalse [bool3_to_value_bool value] =
    true3 <-> value = false3.
```

## `interp_predicate_is_not_false_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:695`](../ScalarPredicateFacts.v#L695)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_false_true_iff : forall value,
  NullValues.interp_predicate PredicateIsNotFalse [bool3_to_value_bool value] =
    true3 <-> value <> false3.
```

## `interp_predicate_is_not_true_dual`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:703`](../ScalarPredicateFacts.v#L703)

Purpose/direction: States the interp predicate is not true dual law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_not_true_dual` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_true_dual : forall value,
  NullValues.interp_predicate PredicateIsNotTrue [bool3_to_value_bool value] =
  negb3
    (NullValues.interp_predicate PredicateIsTrue [bool3_to_value_bool value]).
```

## `interp_predicate_is_not_false_dual`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:713`](../ScalarPredicateFacts.v#L713)

Purpose/direction: States the interp predicate is not false dual law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_is_not_false_dual` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_is_not_false_dual : forall value,
  NullValues.interp_predicate PredicateIsNotFalse [bool3_to_value_bool value] =
  negb3
    (NullValues.interp_predicate PredicateIsFalse [bool3_to_value_bool value]).
```

## `interp_is_not_distinct_from_both_null`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:723`](../ScalarPredicateFacts.v#L723)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_is_not_distinct_from_both_null` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `DISTINCT`, `duplicate elimination`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_is_not_distinct_from_both_null : forall left right,
  is_null_value left = true ->
  is_null_value right = true ->
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = true3.
```

## `interp_is_not_distinct_from_exactly_one_null`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:733`](../ScalarPredicateFacts.v#L733)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_is_not_distinct_from_exactly_one_null` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `DISTINCT`, `duplicate elimination`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_is_not_distinct_from_exactly_one_null : forall left right,
  (is_null_value left = true /\ is_null_value right = false) \/
  (is_null_value left = false /\ is_null_value right = true) ->
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = false3.
```

## `interp_is_not_distinct_from_never_unknown`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:743`](../ScalarPredicateFacts.v#L743)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_is_not_distinct_from_never_unknown` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `DISTINCT`, `duplicate elimination`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_is_not_distinct_from_never_unknown : forall left right,
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] <>
  unknown3.
```

## `interp_is_not_distinct_from_true_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:754`](../ScalarPredicateFacts.v#L754)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `DISTINCT`, `duplicate elimination`, `predicate`, `Bool3`

```rocq
Lemma interp_is_not_distinct_from_true_iff : forall left right,
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = true3
  <->
  (is_null_value left = true /\ is_null_value right = true) \/
  (is_null_value left = false /\ is_null_value right = false /\
   same_non_null_value left right = true).
```

## `interp_is_not_distinct_from_false_iff`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:769`](../ScalarPredicateFacts.v#L769)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `DISTINCT`, `duplicate elimination`, `predicate`, `Bool3`

```rocq
Lemma interp_is_not_distinct_from_false_iff : forall left right,
  NullValues.interp_predicate PredicateIsNotDistinctFrom [left; right] = false3
  <->
  (is_null_value left = true /\ is_null_value right = false) \/
  (is_null_value left = false /\ is_null_value right = true) \/
  (is_null_value left = false /\ is_null_value right = false /\
   same_non_null_value left right = false).
```

## `interp_case_values_empty`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:808`](../ScalarPredicateFacts.v#L808)

Purpose/direction: States the exact empty-input or empty-result law for scalar-predicate semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_empty` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_empty :
  interp_case_values [] = Value_Z None.
```

## `interp_case_values_else`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:814`](../ScalarPredicateFacts.v#L814)

Purpose/direction: States the interp case values else law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_else` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_else : forall else_value,
  interp_case_values [else_value] = else_value.
```

## `interp_case_values_true_branch`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:820`](../ScalarPredicateFacts.v#L820)

Purpose/direction: States the interp case values true branch law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_true_branch` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_true_branch : forall then_value rest,
  interp_case_values
    (bool3_to_value_bool true3 :: then_value :: rest) = then_value.
```

## `interp_case_values_true_branch_if`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:827`](../ScalarPredicateFacts.v#L827)

Purpose/direction: States the interp case values true branch if law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_true_branch_if` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_true_branch_if : forall condition then_value rest,
  value_bool_to_bool3 condition = true3 ->
  interp_case_values (condition :: then_value :: rest) = then_value.
```

## `interp_case_is_not_null_identity`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:837`](../ScalarPredicateFacts.v#L837)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for SQL NULL and three-valued behavior.

Applicability: Use when the goal or a hypothesis matches the `interp_case_is_not_null_identity` direction for SQL NULL and three-valued behavior; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`

```rocq
Lemma interp_case_is_not_null_identity : forall value fallback,
  is_null_value value = false ->
  interp_case_values
    [interp_scalar_operator
       (ScalarPredicateValue PredicateIsNotNull) [value];
     value;
     fallback] = value.
```

## `interp_case_values_skip_nontrue`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:855`](../ScalarPredicateFacts.v#L855)

Purpose/direction: States the interp case values skip nontrue law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_skip_nontrue` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_skip_nontrue : forall condition then_value rest,
  value_bool_to_bool3 condition <> true3 ->
  interp_case_values (condition :: then_value :: rest) =
  interp_case_values rest.
```

## `interp_case_values_skip_prefix`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:868`](../ScalarPredicateFacts.v#L868)

Purpose/direction: States the interp case values skip prefix law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_skip_prefix` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_skip_prefix : forall prefix suffix,
  case_prefix_nontrue prefix ->
  interp_case_values (prefix ++ suffix) = interp_case_values suffix.
```

## `interp_case_values_first_true`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:879`](../ScalarPredicateFacts.v#L879)

Purpose/direction: States the interp case values first true law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_case_values_first_true` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_case_values_first_true :
  forall prefix condition then_value rest,
    case_prefix_nontrue prefix ->
    value_bool_to_bool3 condition = true3 ->
    interp_case_values
      (prefix ++ condition :: then_value :: rest) = then_value.
```

## `case_runtime_error_empty`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:891`](../ScalarPredicateFacts.v#L891)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_empty :
  case_runtime_error [] = None.
```

## `case_runtime_error_else`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:897`](../ScalarPredicateFacts.v#L897)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_else : forall else_error else_value,
  case_runtime_error [(else_error, else_value)] = else_error.
```

## `case_runtime_error_condition_error`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:903`](../ScalarPredicateFacts.v#L903)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_condition_error : forall error condition then_error
    then_value rest,
  case_runtime_error
    ((Some error, condition) :: (then_error, then_value) :: rest) = Some error.
```

## `case_runtime_error_true_branch`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:911`](../ScalarPredicateFacts.v#L911)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_true_branch : forall condition then_error then_value rest,
  value_bool_to_bool3 condition = true3 ->
  case_runtime_error
    ((None, condition) :: (then_error, then_value) :: rest) = then_error.
```

## `case_runtime_error_is_not_null_identity`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:920`](../ScalarPredicateFacts.v#L920)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL NULL and three-valued behavior.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL NULL and three-valued behavior.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_is_not_null_identity :
  forall value fallback value_error fallback_error,
    is_null_value value = false ->
    case_runtime_error
      [(None,
          interp_scalar_operator
            (ScalarPredicateValue PredicateIsNotNull) [value]);
       (value_error, value);
       (fallback_error, fallback)] = value_error.
```

## `case_runtime_error_skip_nontrue`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:940`](../ScalarPredicateFacts.v#L940)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_skip_nontrue : forall condition then_error then_value rest,
  value_bool_to_bool3 condition <> true3 ->
  case_runtime_error
    ((None, condition) :: (then_error, then_value) :: rest) =
  case_runtime_error rest.
```

## `case_runtime_error_skipped_arm_irrelevant`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:954`](../ScalarPredicateFacts.v#L954)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_skipped_arm_irrelevant :
  forall condition first_error first_value second_error second_value rest,
    value_bool_to_bool3 condition <> true3 ->
    case_runtime_error
      ((None, condition) :: (first_error, first_value) :: rest) =
    case_runtime_error
      ((None, condition) :: (second_error, second_value) :: rest).
```

## `case_runtime_error_skip_prefix`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:968`](../ScalarPredicateFacts.v#L968)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_skip_prefix : forall prefix suffix,
  case_runtime_prefix_skippable prefix ->
  case_runtime_error (prefix ++ suffix) = case_runtime_error suffix.
```

## `case_runtime_error_first_true`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:979`](../ScalarPredicateFacts.v#L979)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_first_true :
  forall prefix condition then_error then_value rest,
    case_runtime_prefix_skippable prefix ->
    value_bool_to_bool3 condition = true3 ->
    case_runtime_error
      (prefix ++ (None, condition) :: (then_error, then_value) :: rest) =
    then_error.
```

## `case_runtime_error_some_member`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:992`](../ScalarPredicateFacts.v#L992)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_some_member : forall observations error,
  case_runtime_error observations = Some error ->
  exists observation,
    In observation observations /\ fst observation = Some error.
```

## `case_runtime_error_none_of_all_none`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1018`](../ScalarPredicateFacts.v#L1018)

Purpose/direction: Establishes the explicit runtime-safety direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma case_runtime_error_none_of_all_none : forall observations,
  Forall (fun observation => fst observation = None) observations ->
  case_runtime_error observations = None.
```

## `interp_scalar_case_values`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1032`](../ScalarPredicateFacts.v#L1032)

Purpose/direction: States the interp scalar case values law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_scalar_case_values` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`

```rocq
Lemma interp_scalar_case_values : forall values,
  interp_scalar_operator ScalarCase values = interp_case_values values.
```

## `interp_scalar_case_runtime_error`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1038`](../ScalarPredicateFacts.v#L1038)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `CASE`, `conditional expression`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma interp_scalar_case_runtime_error : forall observations,
  interp_scalar_operator_runtime_error ScalarCase observations =
  case_runtime_error observations.
```

## `interp_predicate_lt_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1045`](../ScalarPredicateFacts.v#L1045)

Purpose/direction: States the interp predicate strict-bound of order compare law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_lt_of_order_compare` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_lt_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateLt [left; right] =
  match ordering with Lt => true3 | Eq | Gt => false3 end.
```

## `interp_predicate_lte_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1055`](../ScalarPredicateFacts.v#L1055)

Purpose/direction: States the interp predicate lte of order compare law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_lte_of_order_compare` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_lte_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateLte [left; right] =
  match ordering with Gt => false3 | Eq | Lt => true3 end.
```

## `interp_predicate_gt_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1065`](../ScalarPredicateFacts.v#L1065)

Purpose/direction: States the interp predicate strict-lower-bound of order compare law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_gt_of_order_compare` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_gt_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGt [left; right] =
  match ordering with Gt => true3 | Eq | Lt => false3 end.
```

## `interp_predicate_gte_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1075`](../ScalarPredicateFacts.v#L1075)

Purpose/direction: States the interp predicate gte of order compare law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_gte_of_order_compare` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_gte_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGte [left; right] =
  match ordering with Lt => false3 | Eq | Gt => true3 end.
```

## `interp_predicate_eq_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1085`](../ScalarPredicateFacts.v#L1085)

Purpose/direction: States the interp predicate equality of order compare law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_eq_of_order_compare` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_eq_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateEq [left; right] =
  match ordering with Eq => true3 | Lt | Gt => false3 end.
```

## `interp_predicate_neq_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1095`](../ScalarPredicateFacts.v#L1095)

Purpose/direction: States the interp predicate disequality of order compare law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_neq_of_order_compare` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_neq_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateNeq [left; right] =
  match ordering with Eq => false3 | Lt | Gt => true3 end.
```

## `interp_predicate_eq_neq_dual_on_ordered_values`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1105`](../ScalarPredicateFacts.v#L1105)

Purpose/direction: States the interp predicate equality disequality dual on ordered values law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_eq_neq_dual_on_ordered_values` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_eq_neq_dual_on_ordered_values : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateNeq [left; right] =
  negb3 (NullValues.interp_predicate PredicateEq [left; right]).
```

## `interp_predicate_lt_true_iff_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1116`](../ScalarPredicateFacts.v#L1116)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_lt_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateLt [left; right] = true3 <->
   ordering = Lt).
```

## `interp_predicate_lte_true_iff_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1126`](../ScalarPredicateFacts.v#L1126)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_lte_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateLte [left; right] = true3 <->
   ordering <> Gt).
```

## `interp_predicate_gt_true_iff_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1136`](../ScalarPredicateFacts.v#L1136)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_gt_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateGt [left; right] = true3 <->
   ordering = Gt).
```

## `interp_predicate_gte_true_iff_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1146`](../ScalarPredicateFacts.v#L1146)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_gte_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateGte [left; right] = true3 <->
   ordering <> Lt).
```

## `interp_predicate_eq_true_iff_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1156`](../ScalarPredicateFacts.v#L1156)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_eq_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateEq [left; right] = true3 <->
   ordering = Eq).
```

## `interp_predicate_neq_true_iff_of_order_compare`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1166`](../ScalarPredicateFacts.v#L1166)

Purpose/direction: Gives necessary and sufficient conditions for scalar-predicate semantics.

Applicability: Use in either direction to invert or construct a goal about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_neq_true_iff_of_order_compare : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  (NullValues.interp_predicate PredicateNeq [left; right] = true3 <->
   ordering <> Eq).
```

## `interp_predicate_lt_gte_dual_on_ordered_values`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1176`](../ScalarPredicateFacts.v#L1176)

Purpose/direction: States the interp predicate strict-bound gte dual on ordered values law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_lt_gte_dual_on_ordered_values` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_lt_gte_dual_on_ordered_values : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGte [left; right] =
  negb3 (NullValues.interp_predicate PredicateLt [left; right]).
```

## `interp_predicate_lte_gt_dual_on_ordered_values`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1187`](../ScalarPredicateFacts.v#L1187)

Purpose/direction: States the interp predicate lte strict-lower-bound dual on ordered values law for scalar-predicate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_predicate_lte_gt_dual_on_ordered_values` direction for scalar-predicate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`

```rocq
Lemma interp_predicate_lte_gt_dual_on_ordered_values : forall left right ordering,
  NullPredicates.order_value_compare left right = Some ordering ->
  NullValues.interp_predicate PredicateGt [left; right] =
  negb3 (NullValues.interp_predicate PredicateLte [left; right]).
```

## `interp_ordered_comparison_congr`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1198`](../ScalarPredicateFacts.v#L1198)

Purpose/direction: Transports or composes scalar-predicate semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about scalar-predicate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`, `equivalence`, `congruence`

```rocq
Lemma interp_ordered_comparison_congr :
  forall predicate left1 right1 left2 right2 ordering,
    ordered_comparison_predicate predicate = true ->
    NullPredicates.order_value_compare left1 right1 = Some ordering ->
    NullPredicates.order_value_compare left2 right2 = Some ordering ->
    NullValues.interp_predicate predicate [left1; right1] =
    NullValues.interp_predicate predicate [left2; right2].
```

## `scalar_predicate_runtime_error_is_children`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1213`](../ScalarPredicateFacts.v#L1213)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_predicate_runtime_error_is_children : forall predicate observations,
  interp_scalar_operator_runtime_error
    (ScalarPredicateValue predicate) observations =
  first_observation_error observations.
```

## `scalar_boolean_runtime_error_is_children`

Source: [`theories/FormalSQL/ScalarPredicateFacts.v:1223`](../ScalarPredicateFacts.v#L1223)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for scalar-predicate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for scalar-predicate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `scalar predicate semantics`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_boolean_runtime_error_is_children : forall operator observations,
  interp_scalar_operator_runtime_error (ScalarBoolean operator) observations =
  first_observation_error observations.
```
