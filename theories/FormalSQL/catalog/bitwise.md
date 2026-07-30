# Bitwise scalar and aggregate facts

Route here for: integer bit operations, shifts, BIT_AND/BIT_OR aggregate laws.

This focused catalog contains 43 declarations routed at declaration granularity from `BitwiseFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `int32_from_twos_complement_as_word`

Source: [`theories/FormalSQL/BitwiseFacts.v:37`](../BitwiseFacts.v#L37)

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

Purpose/direction: States the int64 from twos complement value law for bitwise scalar and aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int64_from_twos_complement_value` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_from_twos_complement_value : forall x,
  int64_from_twos_complement (int64_value x) = x.
```

## `bits_of_Z_land`

Source: [`theories/FormalSQL/BitwiseFacts.v:79`](../BitwiseFacts.v#L79)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:99`](../BitwiseFacts.v#L99)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:119`](../BitwiseFacts.v#L119)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:132`](../BitwiseFacts.v#L132)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:145`](../BitwiseFacts.v#L145)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:158`](../BitwiseFacts.v#L158)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:171`](../BitwiseFacts.v#L171)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:179`](../BitwiseFacts.v#L179)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:187`](../BitwiseFacts.v#L187)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:195`](../BitwiseFacts.v#L195)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:203`](../BitwiseFacts.v#L203)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:210`](../BitwiseFacts.v#L210)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:217`](../BitwiseFacts.v#L217)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:224`](../BitwiseFacts.v#L224)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:231`](../BitwiseFacts.v#L231)

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_and_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_and_idempotent : forall x, int32_bit_and x x = x.
```

## `int32_bit_or_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:237`](../BitwiseFacts.v#L237)

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int32_bit_or_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `INTEGER`, `int32`, `bitwise`

```rocq
Lemma int32_bit_or_idempotent : forall x, int32_bit_or x x = x.
```

## `int64_bit_and_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:243`](../BitwiseFacts.v#L243)

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_and_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_and_idempotent : forall x, int64_bit_and x x = x.
```

## `int64_bit_or_idempotent`

Source: [`theories/FormalSQL/BitwiseFacts.v:249`](../BitwiseFacts.v#L249)

Purpose/direction: Establishes idempotence for the declared bitwise scalar and aggregate semantics operator.

Applicability: Use when the goal or a hypothesis matches the `int64_bit_or_idempotent` direction for bitwise scalar and aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `bitwise semantics`, `BIGINT`, `int64`, `bitwise`

```rocq
Lemma int64_bit_or_idempotent : forall x, int64_bit_or x x = x.
```

## `int32_bit_and_closed`

Source: [`theories/FormalSQL/BitwiseFacts.v:255`](../BitwiseFacts.v#L255)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:259`](../BitwiseFacts.v#L259)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:263`](../BitwiseFacts.v#L263)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:267`](../BitwiseFacts.v#L267)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:280`](../BitwiseFacts.v#L280)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:290`](../BitwiseFacts.v#L290)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:299`](../BitwiseFacts.v#L299)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:319`](../BitwiseFacts.v#L319)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:341`](../BitwiseFacts.v#L341)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:362`](../BitwiseFacts.v#L362)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:369`](../BitwiseFacts.v#L369)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:376`](../BitwiseFacts.v#L376)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:383`](../BitwiseFacts.v#L383)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:390`](../BitwiseFacts.v#L390)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:399`](../BitwiseFacts.v#L399)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:408`](../BitwiseFacts.v#L408)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:417`](../BitwiseFacts.v#L417)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:426`](../BitwiseFacts.v#L426)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:434`](../BitwiseFacts.v#L434)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:442`](../BitwiseFacts.v#L442)

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

Source: [`theories/FormalSQL/BitwiseFacts.v:450`](../BitwiseFacts.v#L450)

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
