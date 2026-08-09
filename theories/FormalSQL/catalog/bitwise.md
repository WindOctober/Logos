# Bitwise scalar and aggregate facts

Route here for: integer bit operations, shifts, BIT_AND/BIT_OR aggregate laws.

This focused catalog contains 47 declarations routed at declaration granularity from `BitwiseFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `int32_from_twos_complement_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:37`](../BitwiseFacts.v#L37)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_from_twos_complement_as_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_from_twos_complement_as_word : forall z,
  int32_from_twos_complement z = int32_from_word (bits.of_Z 32 z).
```

## `int64_from_twos_complement_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:47`](../BitwiseFacts.v#L47)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_from_twos_complement_as_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_from_twos_complement_as_word : forall z,
  int64_from_twos_complement z = int64_from_word (bits.of_Z 64 z).
```

## `int32_from_twos_complement_value`

Source: [`theories/FormalSQL/BitwiseFacts.v:57`](../BitwiseFacts.v#L57)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int32 from twos complement value law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_from_twos_complement_value` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_from_twos_complement_value : forall x,
  int32_from_twos_complement (int32_value x) = x.
```

## `int64_from_twos_complement_value`

Source: [`theories/FormalSQL/BitwiseFacts.v:68`](../BitwiseFacts.v#L68)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int64 from twos complement value law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int64_from_twos_complement_value` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_from_twos_complement_value : forall x,
  int64_from_twos_complement (int64_value x) = x.
```

## `int32_from_word_to_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:79`](../BitwiseFacts.v#L79)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int32 from word to word law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_from_word_to_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_from_word_to_word : forall x,
  int32_from_word (int32_to_word x) = x.
```

## `int64_from_word_to_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:87`](../BitwiseFacts.v#L87)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int64 from word to word law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int64_from_word_to_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_from_word_to_word : forall x,
  int64_from_word (int64_to_word x) = x.
```

## `int32_to_word_from_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:95`](../BitwiseFacts.v#L95)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int32 to word from word law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_to_word_from_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_to_word_from_word : forall word,
  int32_to_word (int32_from_word word) = word.
```

## `int64_to_word_from_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:104`](../BitwiseFacts.v#L104)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the int64 to word from word law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int64_to_word_from_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_to_word_from_word : forall word,
  int64_to_word (int64_from_word word) = word.
```

## `bits_of_Z_land`

Source: [`theories/FormalSQL/BitwiseFacts.v:113`](../BitwiseFacts.v#L113)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the bits of z land law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `bits_of_Z_land` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `bitwise semantics`

```rocq
Lemma bits_of_Z_land : forall n x y,
  0 <= n ->
  bits.of_Z n (Z.land x y) =
    Zmod.and (bits.of_Z n x) (bits.of_Z n y).
```

## `bits_of_Z_lor`

Source: [`theories/FormalSQL/BitwiseFacts.v:133`](../BitwiseFacts.v#L133)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the bits of z lor law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `bits_of_Z_lor` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `bitwise semantics`

```rocq
Lemma bits_of_Z_lor : forall n x y,
  0 <= n ->
  bits.of_Z n (Z.lor x y) =
    Zmod.or (bits.of_Z n x) (bits.of_Z n y).
```

## `int32_bit_and_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:153`](../BitwiseFacts.v#L153)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_as_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_as_word : forall x y,
  int32_bit_and x y =
    int32_from_word (Zmod.and (int32_to_word x) (int32_to_word y)).
```

## `int32_bit_or_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:166`](../BitwiseFacts.v#L166)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_as_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_as_word : forall x y,
  int32_bit_or x y =
    int32_from_word (Zmod.or (int32_to_word x) (int32_to_word y)).
```

## `int64_bit_and_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:179`](../BitwiseFacts.v#L179)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_as_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_as_word : forall x y,
  int64_bit_and x y =
    int64_from_word (Zmod.and (int64_to_word x) (int64_to_word y)).
```

## `int64_bit_or_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:192`](../BitwiseFacts.v#L192)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_as_word` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_as_word : forall x y,
  int64_bit_or x y =
    int64_from_word (Zmod.or (int64_to_word x) (int64_to_word y)).
```

## `int32_bit_and_associative`

Source: [`theories/FormalSQL/BitwiseFacts.v:205`](../BitwiseFacts.v#L205)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_associative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_associative : forall x y z,
  int32_bit_and x (int32_bit_and y z) =
  int32_bit_and (int32_bit_and x y) z.
```

## `int32_bit_or_associative`

Source: [`theories/FormalSQL/BitwiseFacts.v:213`](../BitwiseFacts.v#L213)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_associative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_associative : forall x y z,
  int32_bit_or x (int32_bit_or y z) =
  int32_bit_or (int32_bit_or x y) z.
```

## `int64_bit_and_associative`

Source: [`theories/FormalSQL/BitwiseFacts.v:221`](../BitwiseFacts.v#L221)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_associative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_associative : forall x y z,
  int64_bit_and x (int64_bit_and y z) =
  int64_bit_and (int64_bit_and x y) z.
```

## `int64_bit_or_associative`

Source: [`theories/FormalSQL/BitwiseFacts.v:229`](../BitwiseFacts.v#L229)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_associative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_associative : forall x y z,
  int64_bit_or x (int64_bit_or y z) =
  int64_bit_or (int64_bit_or x y) z.
```

## `int32_bit_and_commutative`

Source: [`theories/FormalSQL/BitwiseFacts.v:237`](../BitwiseFacts.v#L237)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_commutative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_commutative : forall x y,
  int32_bit_and x y = int32_bit_and y x.
```

## `int32_bit_or_commutative`

Source: [`theories/FormalSQL/BitwiseFacts.v:244`](../BitwiseFacts.v#L244)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_commutative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_commutative : forall x y,
  int32_bit_or x y = int32_bit_or y x.
```

## `int64_bit_and_commutative`

Source: [`theories/FormalSQL/BitwiseFacts.v:251`](../BitwiseFacts.v#L251)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_commutative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_commutative : forall x y,
  int64_bit_and x y = int64_bit_and y x.
```

## `int64_bit_or_commutative`

Source: [`theories/FormalSQL/BitwiseFacts.v:258`](../BitwiseFacts.v#L258)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_commutative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_commutative : forall x y,
  int64_bit_or x y = int64_bit_or y x.
```

## `int32_bit_and_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:265`](../BitwiseFacts.v#L265)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_idempotent : forall x, int32_bit_and x x = x.
```

## `int32_bit_or_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:271`](../BitwiseFacts.v#L271)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_idempotent : forall x, int32_bit_or x x = x.
```

## `int64_bit_and_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:277`](../BitwiseFacts.v#L277)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_idempotent : forall x, int64_bit_and x x = x.
```

## `int64_bit_or_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:283`](../BitwiseFacts.v#L283)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_idempotent : forall x, int64_bit_or x x = x.
```

## `int32_bit_and_closed`

Source: [`theories/FormalSQL/BitwiseFacts.v:289`](../BitwiseFacts.v#L289)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed closure property for bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_closed` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_closed : forall x y,
  int32_min <= int32_value (int32_bit_and x y) <= int32_max.
```

## `int32_bit_or_closed`

Source: [`theories/FormalSQL/BitwiseFacts.v:293`](../BitwiseFacts.v#L293)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed closure property for bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_closed` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_closed : forall x y,
  int32_min <= int32_value (int32_bit_or x y) <= int32_max.
```

## `int64_bit_and_closed`

Source: [`theories/FormalSQL/BitwiseFacts.v:297`](../BitwiseFacts.v#L297)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed closure property for bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_closed` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_closed : forall x y,
  int64_min <= int64_value (int64_bit_and x y) <= int64_max.
```

## `int64_bit_or_closed`

Source: [`theories/FormalSQL/BitwiseFacts.v:301`](../BitwiseFacts.v#L301)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed closure property for bitwise scalar and aggregate semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_closed` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_closed : forall x y,
  int64_min <= int64_value (int64_bit_or x y) <= int64_max.
```

## `combine_nullable_state_associative`

Source: [`theories/FormalSQL/BitwiseFacts.v:314`](../BitwiseFacts.v#L314)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `combine_nullable_state_associative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `bitwise semantics`

```rocq
Lemma combine_nullable_state_associative : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  forall x y z,
    combine_nullable_state op x (combine_nullable_state op y z) =
    combine_nullable_state op (combine_nullable_state op x y) z.
```

## `combine_nullable_state_commutative`

Source: [`theories/FormalSQL/BitwiseFacts.v:324`](../BitwiseFacts.v#L324)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `combine_nullable_state_commutative` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `bitwise semantics`

```rocq
Lemma combine_nullable_state_commutative : forall A (op : A -> A -> A),
  (forall x y, op x y = op y x) ->
  forall x y,
    combine_nullable_state op x y = combine_nullable_state op y x.
```

## `fold_nullable_state_partition`

Source: [`theories/FormalSQL/BitwiseFacts.v:333`](../BitwiseFacts.v#L333)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fold nullable state partition law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fold_nullable_state_partition` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `bitwise semantics`

```rocq
Lemma fold_nullable_state_partition : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  forall left right,
    fold_nullable_state op (left ++ right) =
    combine_nullable_state op
      (fold_nullable_state op left) (fold_nullable_state op right).
```

## `fold_nullable_state_permutation`

Source: [`theories/FormalSQL/BitwiseFacts.v:353`](../BitwiseFacts.v#L353)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared bitwise scalar and aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bitwise scalar and aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `bitwise semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma fold_nullable_state_permutation : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  (forall x y, op x y = op y x) ->
  forall left right,
    Permutation left right ->
    fold_nullable_state op left = fold_nullable_state op right.
```

## `fold_nullable_state_adjacent_duplicate`

Source: [`theories/FormalSQL/BitwiseFacts.v:375`](../BitwiseFacts.v#L375)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the fold nullable state adjacent duplicate law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `fold_nullable_state_adjacent_duplicate` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `bitwise semantics`

```rocq
Lemma fold_nullable_state_adjacent_duplicate : forall A (op : A -> A -> A),
  (forall x y z, op x (op y z) = op (op x y) z) ->
  (forall x, op x x = x) ->
  forall prefix suffix x,
    fold_nullable_state op (prefix ++ x :: x :: suffix) =
    fold_nullable_state op (prefix ++ x :: suffix).
```

## `int32_bit_and_fold_partition`

Source: [`theories/FormalSQL/BitwiseFacts.v:396`](../BitwiseFacts.v#L396)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed bitwise scalar and aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_fold_partition` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_fold_partition : forall left right,
  fold_nullable_state int32_bit_and (left ++ right) =
  combine_nullable_state int32_bit_and
    (fold_nullable_state int32_bit_and left)
    (fold_nullable_state int32_bit_and right).
```

## `int32_bit_or_fold_partition`

Source: [`theories/FormalSQL/BitwiseFacts.v:403`](../BitwiseFacts.v#L403)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed bitwise scalar and aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_fold_partition` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_fold_partition : forall left right,
  fold_nullable_state int32_bit_or (left ++ right) =
  combine_nullable_state int32_bit_or
    (fold_nullable_state int32_bit_or left)
    (fold_nullable_state int32_bit_or right).
```

## `int64_bit_and_fold_partition`

Source: [`theories/FormalSQL/BitwiseFacts.v:410`](../BitwiseFacts.v#L410)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed bitwise scalar and aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_fold_partition` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_fold_partition : forall left right,
  fold_nullable_state int64_bit_and (left ++ right) =
  combine_nullable_state int64_bit_and
    (fold_nullable_state int64_bit_and left)
    (fold_nullable_state int64_bit_and right).
```

## `int64_bit_or_fold_partition`

Source: [`theories/FormalSQL/BitwiseFacts.v:417`](../BitwiseFacts.v#L417)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the fold or transition state to the displayed bitwise scalar and aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_fold_partition` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_fold_partition : forall left right,
  fold_nullable_state int64_bit_or (left ++ right) =
  combine_nullable_state int64_bit_or
    (fold_nullable_state int64_bit_or left)
    (fold_nullable_state int64_bit_or right).
```

## `int32_bit_and_fold_permutation`

Source: [`theories/FormalSQL/BitwiseFacts.v:424`](../BitwiseFacts.v#L424)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared bitwise scalar and aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bitwise scalar and aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_bit_and_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int32_bit_and left =
  fold_nullable_state int32_bit_and right.
```

## `int32_bit_or_fold_permutation`

Source: [`theories/FormalSQL/BitwiseFacts.v:433`](../BitwiseFacts.v#L433)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared bitwise scalar and aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bitwise scalar and aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_bit_or_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int32_bit_or left =
  fold_nullable_state int32_bit_or right.
```

## `int64_bit_and_fold_permutation`

Source: [`theories/FormalSQL/BitwiseFacts.v:442`](../BitwiseFacts.v#L442)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared bitwise scalar and aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bitwise scalar and aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int64_bit_and_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int64_bit_and left =
  fold_nullable_state int64_bit_and right.
```

## `int64_bit_or_fold_permutation`

Source: [`theories/FormalSQL/BitwiseFacts.v:451`](../BitwiseFacts.v#L451)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared bitwise scalar and aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bitwise scalar and aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int64_bit_or_fold_permutation : forall left right,
  Permutation left right ->
  fold_nullable_state int64_bit_or left =
  fold_nullable_state int64_bit_or right.
```

## `int32_bit_and_fold_distinct_invariant`

Source: [`theories/FormalSQL/BitwiseFacts.v:460`](../BitwiseFacts.v#L460)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Preserves the declared bitwise scalar and aggregate semantics result across the indicated transformation.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_fold_distinct_invariant` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `DISTINCT`, `duplicate elimination`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int32_bit_and (prefix ++ x :: x :: suffix) =
  fold_nullable_state int32_bit_and (prefix ++ x :: suffix).
```

## `int32_bit_or_fold_distinct_invariant`

Source: [`theories/FormalSQL/BitwiseFacts.v:468`](../BitwiseFacts.v#L468)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Preserves the declared bitwise scalar and aggregate semantics result across the indicated transformation.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_fold_distinct_invariant` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `DISTINCT`, `duplicate elimination`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int32_bit_or (prefix ++ x :: x :: suffix) =
  fold_nullable_state int32_bit_or (prefix ++ x :: suffix).
```

## `int64_bit_and_fold_distinct_invariant`

Source: [`theories/FormalSQL/BitwiseFacts.v:476`](../BitwiseFacts.v#L476)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Preserves the declared bitwise scalar and aggregate semantics result across the indicated transformation.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_fold_distinct_invariant` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `DISTINCT`, `duplicate elimination`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int64_bit_and (prefix ++ x :: x :: suffix) =
  fold_nullable_state int64_bit_and (prefix ++ x :: suffix).
```

## `int64_bit_or_fold_distinct_invariant`

Source: [`theories/FormalSQL/BitwiseFacts.v:484`](../BitwiseFacts.v#L484)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Preserves the declared bitwise scalar and aggregate semantics result across the indicated transformation.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_fold_distinct_invariant` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `DISTINCT`, `duplicate elimination`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_fold_distinct_invariant : forall prefix suffix x,
  fold_nullable_state int64_bit_or (prefix ++ x :: x :: suffix) =
  fold_nullable_state int64_bit_or (prefix ++ x :: suffix).
```
