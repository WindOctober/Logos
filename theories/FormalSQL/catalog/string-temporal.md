# String and temporal values

Route here for: CHAR/VARCHAR/TEXT, LIKE, substring, DATE/TIME/TIMESTAMP/TIMESTAMPTZ.

This focused catalog contains 80 declarations routed at declaration granularity from `StringTemporalFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `string_typmod_descriptor_roundtrip`

Source: [`theories/FormalSQL/StringTemporalFacts.v:12`](../StringTemporalFacts.v#L12)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Proves the stated cast or representation round trip for string semantics.

Applicability: Use when the goal or a hypothesis matches the `string_typmod_descriptor_roundtrip` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `typmod`, `precision/scale`, `string`, `VARCHAR`

```rocq
Lemma string_typmod_descriptor_roundtrip : forall typmod,
  (match typmod with
   | StringVarcharN width | StringChar width => (0 < width)%nat
   | StringText | StringVarchar | StringBpchar => True
   end) ->
  string_typmod_from_codes
    (string_typmod_tag typmod) (string_typmod_length typmod) = Some typmod.
```

## `string_fits_bounded_typmod_from_length`

Source: [`theories/FormalSQL/StringTemporalFacts.v:33`](../StringTemporalFacts.v#L33)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates string semantics to the exact list length or bag cardinality shown below.

Applicability: Use when the goal or a hypothesis matches the `string_fits_bounded_typmod_from_length` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `typmod`, `precision/scale`, `string`, `VARCHAR`

```rocq
Lemma string_fits_bounded_typmod_from_length :
  forall typmod width value length,
    (typmod = StringVarcharN width \/ typmod = StringChar width) ->
    utf8_character_length value = Some length ->
    string_fits_typmod typmod value = Nat.leb length width.
```

## `string_fits_unbounded_typmod_from_length`

Source: [`theories/FormalSQL/StringTemporalFacts.v:43`](../StringTemporalFacts.v#L43)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates string semantics to the exact list length or bag cardinality shown below.

Applicability: Use when the goal or a hypothesis matches the `string_fits_unbounded_typmod_from_length` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `typmod`, `precision/scale`, `string`, `VARCHAR`

```rocq
Lemma string_fits_unbounded_typmod_from_length :
  forall typmod value length,
    (typmod = StringText \/ typmod = StringVarchar \/ typmod = StringBpchar) ->
    utf8_character_length value = Some length ->
    string_fits_typmod typmod value = true.
```

## `string_assignment_coerce_textual_success_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:56`](../StringTemporalFacts.v#L56)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_assignment_coerce_textual_success_iff :
  forall typmod value result,
    (typmod = StringText \/ typmod = StringVarchar) ->
    string_assignment_coerce typmod value = Some result <->
    string_is_valid_utf8 value = true /\ result = value.
```

## `string_assignment_coerce_bpchar_success_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:77`](../StringTemporalFacts.v#L77)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_assignment_coerce_bpchar_success_iff :
  forall value result,
    string_assignment_coerce StringBpchar value = Some result <->
    string_is_valid_utf8 value = true /\
    result = string_canonical_value StringBpchar value.
```

## `string_assignment_coerce_varchar_n_success_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:91`](../StringTemporalFacts.v#L91)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_assignment_coerce_varchar_n_success_iff :
  forall width value length result,
    utf8_character_length value = Some length ->
    string_assignment_coerce (StringVarcharN width) value = Some result <->
    (Nat.leb length width = true /\ result = value) \/
    (Nat.leb length width = false /\
     string_all_spaces (string_drop width value) = true /\
     result = string_take width value).
```

## `string_assignment_coerce_char_success_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:115`](../StringTemporalFacts.v#L115)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_assignment_coerce_char_success_iff :
  forall width value length result,
    utf8_character_length value = Some length ->
    string_assignment_coerce (StringChar width) value = Some result <->
    (Nat.leb length width = true /\
     result = string_canonical_value (StringChar width) value) \/
    (Nat.leb length width = false /\
     string_all_spaces (string_drop width value) = true /\
     result = string_canonical_value (StringChar width) value).
```

## `interp_string_cast_and_coercion_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:140`](../StringTemporalFacts.v#L140)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp string cast and coercion nonnull law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_string_cast_and_coercion_nonnull` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `typmod`, `precision/scale`, `string`, `VARCHAR`

```rocq
Lemma interp_string_cast_and_coercion_nonnull :
  forall source target value tag length,
    string_typmod_from_codes tag length = Some target ->
    interp_cast_string_explicit
      [Value_string (StringValue source (Some value));
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string
        (StringValue target (Some (string_cast_value source target value))) /\
    interp_coerce_string_implicit
      [Value_string (StringValue source (Some value));
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string
        (StringValue target (Some (string_cast_value source target value))).
```

## `interp_string_cast_and_coercion_null`

Source: [`theories/FormalSQL/StringTemporalFacts.v:159`](../StringTemporalFacts.v#L159)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for string semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_string_cast_and_coercion_null` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `typmod`, `precision/scale`, `string`, `VARCHAR`

```rocq
Lemma interp_string_cast_and_coercion_null :
  forall source target tag length,
    string_typmod_from_codes tag length = Some target ->
    interp_cast_string_explicit
      [Value_string (StringValue source None);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue target None) /\
    interp_coerce_string_implicit
      [Value_string (StringValue source None);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue target None).
```

## `interp_string_cast_invalid_descriptor`

Source: [`theories/FormalSQL/StringTemporalFacts.v:176`](../StringTemporalFacts.v#L176)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp string cast invalid descriptor law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_string_cast_invalid_descriptor` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `typmod`, `precision/scale`, `string`, `VARCHAR`

```rocq
Lemma interp_string_cast_invalid_descriptor :
  forall source payload tag length,
    string_typmod_from_codes tag length = None ->
    interp_cast_string_explicit
      [Value_string (StringValue source payload);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue StringText None) /\
    interp_coerce_string_implicit
      [Value_string (StringValue source payload);
       Value_Z (Some tag); Value_Z (Some length)] =
      Value_string (StringValue StringText None).
```

## `string_cast_and_coercion_local_runtime_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:194`](../StringTemporalFacts.v#L194)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for string semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_cast_and_coercion_local_runtime_safe : forall cast values,
  (cast = ScalarCastStringExplicit \/ cast = ScalarCoerceStringImplicit) ->
  scalar_operator_local_runtime_error (ScalarCast cast) values = None.
```

## `string_to_int32_cast_success`

Source: [`theories/FormalSQL/StringTemporalFacts.v:201`](../StringTemporalFacts.v#L201)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for string semantics.

Applicability: Use when the goal or a hypothesis matches the `string_to_int32_cast_success` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `INTEGER`, `int32`, `string`, `VARCHAR`

```rocq
Lemma string_to_int32_cast_success : forall source input result,
  parse_text_int32 (string_cast_source_value source input) =
    TextIntegerValue result ->
  interp_scalar_operator (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] =
      Value_int32 (Some result) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] = None.
```

## `string_to_int64_cast_success`

Source: [`theories/FormalSQL/StringTemporalFacts.v:218`](../StringTemporalFacts.v#L218)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for string semantics.

Applicability: Use when the goal or a hypothesis matches the `string_to_int64_cast_success` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `BIGINT`, `int64`, `string`, `VARCHAR`

```rocq
Lemma string_to_int64_cast_success : forall source input result,
  parse_text_int64 (string_cast_source_value source input) =
    TextIntegerValue result ->
  interp_scalar_operator (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] =
      Value_int64 (Some result) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] = None.
```

## `string_to_int32_cast_invalid`

Source: [`theories/FormalSQL/StringTemporalFacts.v:235`](../StringTemporalFacts.v#L235)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the string to int32 cast invalid law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `INTEGER`, `int32`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_to_int32_cast_invalid : forall source input,
  parse_text_int32 (string_cast_source_value source input) =
    TextIntegerInvalid ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] =
      Some (DataException InvalidTextRepresentation).
```

## `string_to_int64_cast_invalid`

Source: [`theories/FormalSQL/StringTemporalFacts.v:249`](../StringTemporalFacts.v#L249)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the string to int64 cast invalid law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `BIGINT`, `int64`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_to_int64_cast_invalid : forall source input,
  parse_text_int64 (string_cast_source_value source input) =
    TextIntegerInvalid ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] =
      Some (DataException InvalidTextRepresentation).
```

## `string_to_int32_cast_out_of_range`

Source: [`theories/FormalSQL/StringTemporalFacts.v:263`](../StringTemporalFacts.v#L263)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Connects the displayed range/representability premise to string semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `INTEGER`, `int32`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_to_int32_cast_out_of_range : forall source input,
  parse_text_int32 (string_cast_source_value source input) =
    TextIntegerOutOfRange ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source (Some input))] =
      Some (DataException NumericValueOutOfRange).
```

## `string_to_int64_cast_out_of_range`

Source: [`theories/FormalSQL/StringTemporalFacts.v:277`](../StringTemporalFacts.v#L277)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Connects the displayed range/representability premise to string semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `BIGINT`, `int64`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_to_int64_cast_out_of_range : forall source input,
  parse_text_int64 (string_cast_source_value source input) =
    TextIntegerOutOfRange ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source (Some input))] =
      Some (DataException NumericValueOutOfRange).
```

## `string_to_integer_casts_preserve_null`

Source: [`theories/FormalSQL/StringTemporalFacts.v:291`](../StringTemporalFacts.v#L291)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for string semantics.

Applicability: Use when the goal or a hypothesis matches the `string_to_integer_casts_preserve_null` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `INTEGER`, `int32`, `BIGINT`, `int64`, `string`, `VARCHAR`

```rocq
Lemma string_to_integer_casts_preserve_null : forall source,
  interp_scalar_operator (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source None)] = Value_int32 None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue source None)] = None /\
  interp_scalar_operator (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source None)] = Value_int64 None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue source None)] = None.
```

## `string_concat_payload_empty`

Source: [`theories/FormalSQL/StringTemporalFacts.v:306`](../StringTemporalFacts.v#L306)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for string semantics.

Applicability: Use when the goal or a hypothesis matches the `string_concat_payload_empty` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_concat_payload_empty :
  string_concat_payload [] = Some EmptyString.
```

## `string_concat_payload_nonnull_cons_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:310`](../StringTemporalFacts.v#L310)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_concat_payload_nonnull_cons_iff :
  forall typmod value rest result,
    string_concat_payload
      (Value_string (StringValue typmod (Some value)) :: rest) = Some result <->
    exists suffix,
      string_concat_payload rest = Some suffix /\
      result = String.append (string_cast_source_value typmod value) suffix.
```

## `string_concat_payload_null_cons`

Source: [`theories/FormalSQL/StringTemporalFacts.v:328`](../StringTemporalFacts.v#L328)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for string semantics.

Applicability: Use when the goal or a hypothesis matches the `string_concat_payload_null_cons` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma string_concat_payload_null_cons : forall typmod rest,
  string_concat_payload (Value_string (StringValue typmod None) :: rest) = None.
```

## `interp_string_concat_nonnull_cons`

Source: [`theories/FormalSQL/StringTemporalFacts.v:332`](../StringTemporalFacts.v#L332)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp string concat nonnull cons law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_string_concat_nonnull_cons` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma interp_string_concat_nonnull_cons :
  forall typmod value rest suffix,
    string_concat_payload rest = Some suffix ->
    interp_string_concat
      (Value_string (StringValue typmod (Some value)) :: rest) =
    Value_string
      (StringValue StringText
        (Some (String.append (string_cast_source_value typmod value) suffix))).
```

## `interp_string_concat_null_cons`

Source: [`theories/FormalSQL/StringTemporalFacts.v:350`](../StringTemporalFacts.v#L350)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for string semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_string_concat_null_cons` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma interp_string_concat_null_cons : forall typmod rest,
  interp_string_concat (Value_string (StringValue typmod None) :: rest) =
  Value_string (StringValue StringText None).
```

## `string_concat_local_runtime_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:355`](../StringTemporalFacts.v#L355)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for string semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_concat_local_runtime_safe : forall values,
  scalar_operator_local_runtime_error ScalarStringConcat values = None.
```

## `string_map_append`

Source: [`theories/FormalSQL/StringTemporalFacts.v:359`](../StringTemporalFacts.v#L359)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the string map append law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `string_map_append` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_map_append : forall mapping left right,
  string_map mapping (String.append left right) =
  String.append (string_map mapping left) (string_map mapping right).
```

## `string_map_length`

Source: [`theories/FormalSQL/StringTemporalFacts.v:369`](../StringTemporalFacts.v#L369)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates string semantics to the exact list length or bag cardinality shown below.

Applicability: Use when the goal or a hypothesis matches the `string_map_length` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_map_length : forall mapping value,
  String.length (string_map mapping value) = String.length value.
```

## `interp_string_case_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:378`](../StringTemporalFacts.v#L378)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp string case nonnull law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_string_case_nonnull` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `CASE`, `conditional expression`, `string`, `VARCHAR`

```rocq
Lemma interp_string_case_nonnull : forall operation typmod value,
  interp_scalar_operator (ScalarStringCase operation)
    [Value_string (StringValue typmod (Some value))] =
  Value_string
    (StringValue StringText
      (Some
        (string_map
          (match operation with
           | ScalarUpper => ascii_to_upper
           | ScalarLower => ascii_to_lower
           end) value))).
```

## `interp_string_case_null`

Source: [`theories/FormalSQL/StringTemporalFacts.v:393`](../StringTemporalFacts.v#L393)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for string semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_string_case_null` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `CASE`, `conditional expression`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma interp_string_case_null : forall operation typmod,
  interp_scalar_operator (ScalarStringCase operation)
    [Value_string (StringValue typmod None)] =
  Value_string (StringValue StringText None).
```

## `string_case_local_runtime_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:401`](../StringTemporalFacts.v#L401)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for string semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `CASE`, `conditional expression`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma string_case_local_runtime_safe : forall operation values,
  scalar_operator_local_runtime_error (ScalarStringCase operation) values =
  None.
```

## `string_prefix_refl`

Source: [`theories/FormalSQL/StringTemporalFacts.v:408`](../StringTemporalFacts.v#L408)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes reflexivity for string semantics.

Applicability: Use to orient, transport, or compose a semantic relation about string semantics.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`, `equivalence`, `congruence`

```rocq
Lemma string_prefix_refl : forall value,
  String.prefix value value = true.
```

## `string_like_prefix_physical_refl`

Source: [`theories/FormalSQL/StringTemporalFacts.v:419`](../StringTemporalFacts.v#L419)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes reflexivity for string semantics.

Applicability: Use to orient, transport, or compose a semantic relation about string semantics.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`, `equivalence`, `congruence`

```rocq
Lemma string_like_prefix_physical_refl : forall typmod value,
  string_like_prefix typmod value (string_physical_value typmod value) = true.
```

## `interp_like_prefix_true_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:426`](../StringTemporalFacts.v#L426)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `string`, `VARCHAR`

```rocq
Lemma interp_like_prefix_true_iff :
  forall input_typmod input prefix_typmod prefix,
    NullValues.interp_predicate PredicateLikePrefix
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue prefix_typmod (Some prefix))] = true3 <->
    string_like_prefix input_typmod input prefix = true.
```

## `interp_like_prefix_false_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:442`](../StringTemporalFacts.v#L442)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `string`, `VARCHAR`

```rocq
Lemma interp_like_prefix_false_iff :
  forall input_typmod input prefix_typmod prefix,
    NullValues.interp_predicate PredicateLikePrefix
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue prefix_typmod (Some prefix))] = false3 <->
    string_like_prefix input_typmod input prefix = false.
```

## `interp_like_percent_true_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:458`](../StringTemporalFacts.v#L458)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `string`, `VARCHAR`

```rocq
Lemma interp_like_percent_true_iff :
  forall input_typmod input pattern_typmod pattern,
    NullValues.interp_predicate PredicateLikePercent
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue pattern_typmod (Some pattern))] = true3 <->
    string_like_percent input_typmod input pattern = true.
```

## `interp_like_percent_false_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:474`](../StringTemporalFacts.v#L474)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `string`, `VARCHAR`

```rocq
Lemma interp_like_percent_false_iff :
  forall input_typmod input pattern_typmod pattern,
    NullValues.interp_predicate PredicateLikePercent
      [Value_string (StringValue input_typmod (Some input));
       Value_string (StringValue pattern_typmod (Some pattern))] = false3 <->
    string_like_percent input_typmod input pattern = false.
```

## `interp_substring_nonnegative_valid`

Source: [`theories/FormalSQL/StringTemporalFacts.v:490`](../StringTemporalFacts.v#L490)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp substring nonnegative valid law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_substring_nonnegative_valid` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `INTEGER`, `int32`, `string`, `VARCHAR`

```rocq
Lemma interp_substring_nonnegative_valid : forall typmod input start count,
  1 <= int32_value start ->
  0 <= int32_value count ->
  interp_substring_nonnegative
    [Value_string (StringValue typmod (Some input));
     Value_int32 (Some start); Value_int32 (Some count)] =
  Value_string
    (StringValue StringText
      (Some
        (string_substring_nonnegative typmod input
          (Z.to_nat (int32_value start - 1))
          (Z.to_nat (int32_value count))))).
```

## `interp_substring_nonnegative_null`

Source: [`theories/FormalSQL/StringTemporalFacts.v:512`](../StringTemporalFacts.v#L512)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for string semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_substring_nonnegative_null` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `string`, `VARCHAR`

```rocq
Lemma interp_substring_nonnegative_null : forall typmod start count,
  interp_substring_nonnegative
    [Value_string (StringValue typmod None); start; count] =
  Value_string (StringValue StringText None).
```

## `interp_substring_nonnegative_invalid`

Source: [`theories/FormalSQL/StringTemporalFacts.v:520`](../StringTemporalFacts.v#L520)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp substring nonnegative invalid law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_substring_nonnegative_invalid` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `INTEGER`, `int32`, `string`, `VARCHAR`

```rocq
Lemma interp_substring_nonnegative_invalid : forall typmod input start count,
  (int32_value start < 1 \/ int32_value count < 0) ->
  interp_substring_nonnegative
    [Value_string (StringValue typmod (Some input));
     Value_int32 (Some start); Value_int32 (Some count)] =
  Value_string (StringValue StringText None).
```

## `substring_nonnegative_local_runtime_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:537`](../StringTemporalFacts.v#L537)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for string semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for string semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma substring_nonnegative_local_runtime_safe : forall values,
  scalar_operator_local_runtime_error ScalarSubstringNonnegative values = None.
```

## `string_comparison_values_swap`

Source: [`theories/FormalSQL/StringTemporalFacts.v:541`](../StringTemporalFacts.v#L541)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the string comparison values swap law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `string_comparison_values_swap` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma string_comparison_values_swap :
  forall left_typmod left right_typmod right,
    string_comparison_values right_typmod right left_typmod left =
    let '(left_value, right_value) :=
      string_comparison_values left_typmod left right_typmod right in
    (right_value, left_value).
```

## `sql_string_compare_eq_iff_semantic_values`

Source: [`theories/FormalSQL/StringTemporalFacts.v:552`](../StringTemporalFacts.v#L552)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma sql_string_compare_eq_iff_semantic_values :
  forall left_typmod left right_typmod right,
    sql_string_compare left_typmod left right_typmod right = Eq <->
    let '(left_value, right_value) :=
      string_comparison_values left_typmod left right_typmod right in
    left_value = right_value.
```

## `sql_string_eqb_true_iff_semantic_values`

Source: [`theories/FormalSQL/StringTemporalFacts.v:569`](../StringTemporalFacts.v#L569)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for string semantics.

Applicability: Use in either direction to invert or construct a goal about string semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma sql_string_eqb_true_iff_semantic_values :
  forall left_typmod left right_typmod right,
    sql_string_eqb left_typmod left right_typmod right = true <->
    let '(left_value, right_value) :=
      string_comparison_values left_typmod left right_typmod right in
    left_value = right_value.
```

## `sql_string_compare_opposite`

Source: [`theories/FormalSQL/StringTemporalFacts.v:587`](../StringTemporalFacts.v#L587)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the sql string compare opposite law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `sql_string_compare_opposite` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma sql_string_compare_opposite :
  forall left_typmod left right_typmod right,
    sql_string_compare left_typmod left right_typmod right =
    CompOpp (sql_string_compare right_typmod right left_typmod left).
```

## `sql_string_eqb_symmetric`

Source: [`theories/FormalSQL/StringTemporalFacts.v:602`](../StringTemporalFacts.v#L602)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Reverses a proved string semantics relation.

Applicability: Use when the goal or a hypothesis matches the `sql_string_eqb_symmetric` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma sql_string_eqb_symmetric :
  forall left_typmod left right_typmod right,
    sql_string_eqb left_typmod left right_typmod right =
    sql_string_eqb right_typmod right left_typmod left.
```

## `order_value_compare_string_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:614`](../StringTemporalFacts.v#L614)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the order value compare string nonnull law for string semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `order_value_compare_string_nonnull` direction for string semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `string`, `VARCHAR`

```rocq
Lemma order_value_compare_string_nonnull :
  forall left_typmod left right_typmod right,
    NullPredicates.order_value_compare
      (Value_string (StringValue left_typmod (Some left)))
      (Value_string (StringValue right_typmod (Some right))) =
    Some (sql_string_compare left_typmod left right_typmod right).
```

## `date_checked_some_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:624`](../StringTemporalFacts.v#L624)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma date_checked_some_iff : forall date,
  date_checked date = Some date <-> date_in_range_bool date = true.
```

## `date_checked_none_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:632`](../StringTemporalFacts.v#L632)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma date_checked_none_iff : forall date,
  date_checked date = None <-> date_in_range_bool date = false.
```

## `timestamp_checked_some_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:640`](../StringTemporalFacts.v#L640)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma timestamp_checked_some_iff : forall timestamp,
  timestamp_checked timestamp = Some timestamp <->
  timestamp_in_range_bool timestamp = true.
```

## `timestamp_checked_none_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:649`](../StringTemporalFacts.v#L649)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma timestamp_checked_none_iff : forall timestamp,
  timestamp_checked timestamp = None <->
  timestamp_in_range_bool timestamp = false.
```

## `order_value_compare_date_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:658`](../StringTemporalFacts.v#L658)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the order value compare date nonnull law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `order_value_compare_date_nonnull` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma order_value_compare_date_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_date (Some left)) (Value_date (Some right)) =
  Some (Z.compare left right).
```

## `order_value_compare_time_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:666`](../StringTemporalFacts.v#L666)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the order value compare time nonnull law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `order_value_compare_time_nonnull` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma order_value_compare_time_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_time (Some left)) (Value_time (Some right)) =
  Some (Z.compare left right).
```

## `order_value_compare_timestamp_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:674`](../StringTemporalFacts.v#L674)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the order value compare timestamp nonnull law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `order_value_compare_timestamp_nonnull` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma order_value_compare_timestamp_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_timestamp (Some left)) (Value_timestamp (Some right)) =
  Some (Z.compare left right).
```

## `order_value_compare_timestamptz_nonnull`

Source: [`theories/FormalSQL/StringTemporalFacts.v:682`](../StringTemporalFacts.v#L682)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the order value compare timestamptz nonnull law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `order_value_compare_timestamptz_nonnull` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma order_value_compare_timestamptz_nonnull : forall left right,
  NullPredicates.order_value_compare
    (Value_timestamptz (Some left)) (Value_timestamptz (Some right)) =
  Some (Z.compare left right).
```

## `cast_date_to_timestamp_checked_finite`

Source: [`theories/FormalSQL/StringTemporalFacts.v:690`](../StringTemporalFacts.v#L690)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the cast date to timestamp checked finite law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `cast_date_to_timestamp_checked_finite` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma cast_date_to_timestamp_checked_finite : forall date,
  date_is_neg_infinity_bool date = false ->
  date_is_pos_infinity_bool date = false ->
  timestamp_in_range_bool (cast_date_to_timestamp date) = true ->
  cast_date_to_timestamp_checked date = Some (cast_date_to_timestamp date).
```

## `cast_timestamp_to_date_checked_finite`

Source: [`theories/FormalSQL/StringTemporalFacts.v:702`](../StringTemporalFacts.v#L702)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the cast timestamp to date checked finite law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `cast_timestamp_to_date_checked_finite` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma cast_timestamp_to_date_checked_finite : forall timestamp,
  timestamp_is_neg_infinity_bool timestamp = false ->
  timestamp_is_pos_infinity_bool timestamp = false ->
  date_in_range_bool (cast_timestamp_to_date timestamp) = true ->
  cast_timestamp_to_date_checked timestamp = Some (cast_timestamp_to_date timestamp).
```

## `scalar_cast_date_to_timestamp_success_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:714`](../StringTemporalFacts.v#L714)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_date_to_timestamp_success_safe : forall date timestamp,
  cast_date_to_timestamp_checked date = Some timestamp ->
  interp_scalar_operator (ScalarCast ScalarCastDateToTimestamp)
    [Value_date (Some date)] = Value_timestamp (Some timestamp) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastDateToTimestamp) [Value_date (Some date)] = None.
```

## `scalar_cast_timestamp_to_date_success_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:728`](../StringTemporalFacts.v#L728)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_timestamp_to_date_success_safe : forall timestamp date,
  cast_timestamp_to_date_checked timestamp = Some date ->
  interp_scalar_operator (ScalarCast ScalarCastTimestampToDate)
    [Value_timestamp (Some timestamp)] = Value_date (Some date) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastTimestampToDate) [Value_timestamp (Some timestamp)] =
  None.
```

## `scalar_cast_date_to_timestamp_failure_overflow`

Source: [`theories/FormalSQL/StringTemporalFacts.v:743`](../StringTemporalFacts.v#L743)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_date_to_timestamp_failure_overflow : forall date,
  cast_date_to_timestamp_checked date = None ->
  interp_scalar_operator (ScalarCast ScalarCastDateToTimestamp)
    [Value_date (Some date)] = Value_timestamp None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastDateToTimestamp) [Value_date (Some date)] =
  datetime_field_overflow.
```

## `scalar_cast_timestamp_to_date_failure_overflow`

Source: [`theories/FormalSQL/StringTemporalFacts.v:758`](../StringTemporalFacts.v#L758)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_cast_timestamp_to_date_failure_overflow : forall timestamp,
  cast_timestamp_to_date_checked timestamp = None ->
  interp_scalar_operator (ScalarCast ScalarCastTimestampToDate)
    [Value_timestamp (Some timestamp)] = Value_date None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastTimestampToDate) [Value_timestamp (Some timestamp)] =
  datetime_field_overflow.
```

## `scalar_temporal_casts_null_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:773`](../StringTemporalFacts.v#L773)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_temporal_casts_null_safe :
  interp_scalar_operator (ScalarCast ScalarCastDateToTimestamp)
    [Value_date None] = Value_timestamp None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastDateToTimestamp) [Value_date None] = None /\
  interp_scalar_operator (ScalarCast ScalarCastTimestampToDate)
    [Value_timestamp None] = Value_date None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastTimestampToDate) [Value_timestamp None] = None.
```

## `checked_temporal_casts_preserve_infinities`

Source: [`theories/FormalSQL/StringTemporalFacts.v:784`](../StringTemporalFacts.v#L784)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the indicated operator preserves the displayed temporal semantics property.

Applicability: Use when the goal or a hypothesis matches the `checked_temporal_casts_preserve_infinities` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma checked_temporal_casts_preserve_infinities :
  cast_date_to_timestamp_checked postgres_date_neg_infinity =
    Some postgres_timestamp_neg_infinity /\
  cast_date_to_timestamp_checked postgres_date_pos_infinity =
    Some postgres_timestamp_pos_infinity /\
  cast_timestamp_to_date_checked postgres_timestamp_neg_infinity =
    Some postgres_date_neg_infinity /\
  cast_timestamp_to_date_checked postgres_timestamp_pos_infinity =
    Some postgres_date_pos_infinity.
```

## `interp_extract_year_date_finite`

Source: [`theories/FormalSQL/StringTemporalFacts.v:817`](../StringTemporalFacts.v#L817)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp extract year date finite law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_extract_year_date_finite` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NUMERIC`, `DECIMAL`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_extract_year_date_finite : forall date,
  date_is_neg_infinity_bool date = false ->
  date_is_pos_infinity_bool date = false ->
  interp_extract_year_date [Value_date (Some date)] =
  Value_numeric (Some (numeric_of_Z (date_extract_year date))).
```

## `interp_extract_year_date_infinity`

Source: [`theories/FormalSQL/StringTemporalFacts.v:827`](../StringTemporalFacts.v#L827)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp extract year date infinity law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_extract_year_date_infinity` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_extract_year_date_infinity : forall date result,
  (date = postgres_date_neg_infinity /\ result = NumericNegInfinity) \/
  (date = postgres_date_pos_infinity /\ result = NumericPosInfinity) ->
  interp_extract_year_date [Value_date (Some date)] =
  Value_numeric (Some result).
```

## `interp_extract_month_date_finite`

Source: [`theories/FormalSQL/StringTemporalFacts.v:842`](../StringTemporalFacts.v#L842)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp extract month date finite law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_extract_month_date_finite` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NUMERIC`, `DECIMAL`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_extract_month_date_finite : forall date,
  date_is_infinity_bool date = false ->
  interp_extract_month_date [Value_date (Some date)] =
  Value_numeric (Some (numeric_of_Z (date_extract_month date))).
```

## `interp_extract_month_date_infinity`

Source: [`theories/FormalSQL/StringTemporalFacts.v:851`](../StringTemporalFacts.v#L851)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp extract month date infinity law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_extract_month_date_infinity` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NUMERIC`, `DECIMAL`, `floating point`, `special value`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_extract_month_date_infinity : forall date,
  date_is_infinity_bool date = true ->
  interp_extract_month_date [Value_date (Some date)] = Value_numeric None.
```

## `interp_extract_date_null`

Source: [`theories/FormalSQL/StringTemporalFacts.v:859`](../StringTemporalFacts.v#L859)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for temporal semantics.

Applicability: Use when the goal or a hypothesis matches the `interp_extract_date_null` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_extract_date_null : forall part,
  interp_scalar_operator (ScalarExtractDate part) [Value_date None] =
  Value_numeric None.
```

## `extract_date_local_runtime_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:866`](../StringTemporalFacts.v#L866)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma extract_date_local_runtime_safe : forall part values,
  scalar_operator_local_runtime_error (ScalarExtractDate part) values = None.
```

## `interp_date_lt_timestamp_true_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:872`](../StringTemporalFacts.v#L872)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_lt_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp = Lt.
```

## `interp_date_lt_timestamp_false_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:884`](../StringTemporalFacts.v#L884)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_lt_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp <> Lt.
```

## `interp_date_lte_timestamp_true_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:896`](../StringTemporalFacts.v#L896)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_lte_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp <> Gt.
```

## `interp_date_lte_timestamp_false_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:908`](../StringTemporalFacts.v#L908)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_lte_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateLteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp = Gt.
```

## `interp_date_gt_timestamp_true_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:920`](../StringTemporalFacts.v#L920)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_gt_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp = Gt.
```

## `interp_date_gt_timestamp_false_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:932`](../StringTemporalFacts.v#L932)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_gt_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGtTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp <> Gt.
```

## `interp_date_gte_timestamp_true_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:944`](../StringTemporalFacts.v#L944)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_gte_timestamp_true_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = true3 <->
  date_cmp_timestamp_internal date timestamp <> Lt.
```

## `interp_date_gte_timestamp_false_iff`

Source: [`theories/FormalSQL/StringTemporalFacts.v:956`](../StringTemporalFacts.v#L956)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for temporal semantics.

Applicability: Use in either direction to invert or construct a goal about temporal semantics.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `predicate`, `Bool3`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma interp_date_gte_timestamp_false_iff : forall date timestamp,
  NullValues.interp_predicate PredicateDateGteTimestamp
    [Value_date (Some date); Value_timestamp (Some timestamp)] = false3 <->
  date_cmp_timestamp_internal date timestamp = Lt.
```

## `timestamp_scalar_add_checked_success`

Source: [`theories/FormalSQL/StringTemporalFacts.v:980`](../StringTemporalFacts.v#L980)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for temporal semantics.

Applicability: Use when the goal or a hypothesis matches the `timestamp_scalar_add_checked_success` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma timestamp_scalar_add_checked_success : forall unit timestamp amount result,
  timestamp_checked_operation unit timestamp amount = Some result ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    Value_timestamp (Some result) /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] = None.
```

## `timestamp_scalar_add_checked_failure`

Source: [`theories/FormalSQL/StringTemporalFacts.v:994`](../StringTemporalFacts.v#L994)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma timestamp_scalar_add_checked_failure : forall unit timestamp amount,
  timestamp_checked_operation unit timestamp amount = None ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    Value_timestamp None /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    datetime_field_overflow.
```

## `timestamp_scalar_add_null_safe`

Source: [`theories/FormalSQL/StringTemporalFacts.v:1009`](../StringTemporalFacts.v#L1009)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for temporal semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for temporal semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `runtime`, `scalar`

Search aliases: `string/temporal scalar semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma timestamp_scalar_add_null_safe : forall unit timestamp amount,
  (timestamp = None \/ amount = None) ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp timestamp; Value_Z amount] = Value_timestamp None /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp timestamp; Value_Z amount] = None.
```

## `timestamp_checked_operation_infinity`

Source: [`theories/FormalSQL/StringTemporalFacts.v:1021`](../StringTemporalFacts.v#L1021)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the timestamp checked operation infinity law for temporal semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `timestamp_checked_operation_infinity` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `floating point`, `special value`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma timestamp_checked_operation_infinity : forall unit timestamp amount,
  timestamp_is_infinity_bool timestamp = true ->
  timestamp_checked_operation unit timestamp amount = Some timestamp.
```

## `timestamp_scalar_add_preserves_infinity`

Source: [`theories/FormalSQL/StringTemporalFacts.v:1037`](../StringTemporalFacts.v#L1037)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the indicated operator preserves the displayed temporal semantics property.

Applicability: Use when the goal or a hypothesis matches the `timestamp_scalar_add_preserves_infinity` direction for temporal semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `string/temporal scalar semantics`, `floating point`, `special value`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`

```rocq
Lemma timestamp_scalar_add_preserves_infinity : forall unit timestamp amount,
  timestamp_is_infinity_bool timestamp = true ->
  interp_scalar_operator (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] =
    Value_timestamp (Some timestamp) /\
  scalar_operator_local_runtime_error (ScalarTimestampAdd unit)
    [Value_timestamp (Some timestamp); Value_Z (Some amount)] = None.
```
