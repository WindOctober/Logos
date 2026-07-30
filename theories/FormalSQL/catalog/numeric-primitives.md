# NUMERIC primitive semantics

Route here for: NUMERIC representation, precision/scale, division, rounding, AVG states.

This focused catalog contains 122 declarations routed at declaration granularity from `NumericFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `numeric_avg_scale_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:15`](../NumericFacts.v#L15)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_scale_transition_commutes` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_scale_transition_commutes : forall scale state left right,
  numeric_avg_scale_transition scale
    (numeric_avg_scale_transition scale state left)
    right =
  numeric_avg_scale_transition scale
    (numeric_avg_scale_transition scale state right)
    left.
```

## `numeric_sum_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:39`](../NumericFacts.v#L39)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_transition_commutes` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_transition_commutes : forall state left right,
  numeric_sum_transition
    (numeric_sum_transition state left) right =
  numeric_sum_transition
    (numeric_sum_transition state right) left.
```

## `fold_left_permutation_of_commuting_steps`

Source: [`theories/FormalSQL/NumericFacts.v:57`](../NumericFacts.v#L57)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma fold_left_permutation_of_commuting_steps :
  forall (state item : Type) (step : state -> item -> state),
    (forall current left right,
      step (step current left) right = step (step current right) left) ->
    forall left right initial,
      Permutation left right ->
      fold_left step left initial = fold_left step right initial.
```

## `numeric_scale_stats_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:76`](../NumericFacts.v#L76)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_scale_stats_transition_commutes` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_scale_stats_transition_commutes : forall scale state left right,
  numeric_scale_stats_transition scale
    (numeric_scale_stats_transition scale state left) right =
  numeric_scale_stats_transition scale
    (numeric_scale_stats_transition scale state right) left.
```

## `numeric_scale_stats_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:91`](../NumericFacts.v#L91)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_scale_stats_fold_permutation : forall scale left right initial,
  Permutation left right ->
  fold_left (numeric_scale_stats_transition scale) left initial =
  fold_left (numeric_scale_stats_transition scale) right initial.
```

## `numeric_avg_scale_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:104`](../NumericFacts.v#L104)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_avg_scale_fold_permutation : forall scale left right initial,
  Permutation left right ->
  fold_left (numeric_avg_scale_transition scale)
    left initial =
  fold_left (numeric_avg_scale_transition scale)
    right initial.
```

## `numeric_sum_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:119`](../NumericFacts.v#L119)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_sum_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left numeric_sum_transition left initial =
  fold_left numeric_sum_transition right initial.
```

## `int32_avg_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:131`](../NumericFacts.v#L131)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int32_avg_transition_commutes` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`

```rocq
Lemma int32_avg_transition_commutes : forall state left right,
  int32_avg_transition (int32_avg_transition state left) right =
  int32_avg_transition (int32_avg_transition state right) left.
```

## `int64_avg_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:140`](../NumericFacts.v#L140)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int64_avg_transition_commutes` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma int64_avg_transition_commutes : forall state left right,
  int64_avg_transition (int64_avg_transition state left) right =
  int64_avg_transition (int64_avg_transition state right) left.
```

## `integer_stats_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:152`](../NumericFacts.v#L152)

Purpose/direction: Relates the fold or transition state to the displayed typed numeric semantics result.

Applicability: Use when the goal or a hypothesis matches the `integer_stats_transition_commutes` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`

```rocq
Lemma integer_stats_transition_commutes : forall state left right,
  integer_stats_transition (integer_stats_transition state left) right =
  integer_stats_transition (integer_stats_transition state right) left.
```

## `int32_sum_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:163`](../NumericFacts.v#L163)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int32_sum_transition_commutes` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`

```rocq
Lemma int32_sum_transition_commutes : forall state left right,
  (state + int32_value left) + int32_value right =
  (state + int32_value right) + int32_value left.
```

## `int32_sum_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:168`](../NumericFacts.v#L168)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_sum_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left (fun state next => state + int32_value next) left initial =
  fold_left (fun state next => state + int32_value next) right initial.
```

## `int32_avg_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:179`](../NumericFacts.v#L179)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_avg_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left int32_avg_transition left initial =
  fold_left int32_avg_transition right initial.
```

## `int64_avg_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:190`](../NumericFacts.v#L190)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int64_avg_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left int64_avg_transition left initial =
  fold_left int64_avg_transition right initial.
```

## `integer_stats_fold_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:201`](../NumericFacts.v#L201)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma integer_stats_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left integer_stats_transition left initial =
  fold_left integer_stats_transition right initial.
```

## `z_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:236`](../NumericFacts.v#L236)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `z_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`

```rocq
Lemma z_values_as_flat_map : forall values,
  z_values values = flat_map z_value_projection values.
```

## `int32_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:244`](../NumericFacts.v#L244)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_values_as_flat_map : forall values,
  int32_values values = flat_map int32_value_projection values.
```

## `int64_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:252`](../NumericFacts.v#L252)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_values_as_flat_map : forall values,
  int64_values values = flat_map int64_value_projection values.
```

## `numeric_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:260`](../NumericFacts.v#L260)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_values_as_flat_map : forall values,
  numeric_values values = flat_map numeric_value_projection values.
```

## `int32_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:268`](../NumericFacts.v#L268)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_values_permutation : forall left right,
  Permutation left right ->
  Permutation (int32_values left) (int32_values right).
```

## `int64_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:276`](../NumericFacts.v#L276)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int64_values_permutation : forall left right,
  Permutation left right ->
  Permutation (int64_values left) (int64_values right).
```

## `numeric_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:284`](../NumericFacts.v#L284)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_values_permutation : forall left right,
  Permutation left right ->
  Permutation (numeric_values left) (numeric_values right).
```

## `z_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:292`](../NumericFacts.v#L292)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma z_values_permutation : forall left right,
  Permutation left right ->
  Permutation (z_values left) (z_values right).
```

## `forallb_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:300`](../NumericFacts.v#L300)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma forallb_permutation : forall (A : Type) (predicate : A -> bool) left right,
  Permutation left right -> forallb predicate left = forallb predicate right.
```

## `fold_nonempty_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:313`](../NumericFacts.v#L313)

Purpose/direction: States the exact empty-input or empty-result law for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma fold_nonempty_permutation : forall (A : Type) (operation : A -> A -> A),
  (forall left right, operation left right = operation right left) ->
  (forall first second third,
    operation (operation first second) third =
    operation first (operation second third)) ->
  forall left right,
    Permutation left right ->
    fold_nonempty operation left = fold_nonempty operation right.
```

## `ordered_minimum_commutative`

Source: [`theories/FormalSQL/NumericFacts.v:347`](../NumericFacts.v#L347)

Purpose/direction: Establishes commutativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `ordered_minimum_commutative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`

```rocq
Lemma ordered_minimum_commutative : forall (A : Type) (order : Oset.Rcd A),
  forall left right,
    ordered_minimum order left right = ordered_minimum order right left.
```

## `ordered_minimum_associative`

Source: [`theories/FormalSQL/NumericFacts.v:360`](../NumericFacts.v#L360)

Purpose/direction: Establishes associativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `ordered_minimum_associative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`

```rocq
Lemma ordered_minimum_associative : forall (A : Type) (order : Oset.Rcd A),
  forall first second third,
    ordered_minimum order (ordered_minimum order first second) third =
    ordered_minimum order first (ordered_minimum order second third).
```

## `ordered_maximum_commutative`

Source: [`theories/FormalSQL/NumericFacts.v:402`](../NumericFacts.v#L402)

Purpose/direction: Establishes commutativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `ordered_maximum_commutative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`

```rocq
Lemma ordered_maximum_commutative : forall (A : Type) (order : Oset.Rcd A),
  forall left right,
    ordered_maximum order left right = ordered_maximum order right left.
```

## `ordered_maximum_associative`

Source: [`theories/FormalSQL/NumericFacts.v:415`](../NumericFacts.v#L415)

Purpose/direction: Establishes associativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `ordered_maximum_associative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`

```rocq
Lemma ordered_maximum_associative : forall (A : Type) (order : Oset.Rcd A),
  forall first second third,
    ordered_maximum order (ordered_maximum order first second) third =
    ordered_maximum order first (ordered_maximum order second third).
```

## `numeric_minimum_is_ordered_minimum`

Source: [`theories/FormalSQL/NumericFacts.v:466`](../NumericFacts.v#L466)

Purpose/direction: States the numeric minimum is ordered minimum law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_minimum_is_ordered_minimum` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_minimum_is_ordered_minimum : forall left right,
  numeric_min left right = ordered_minimum Onumeric left right.
```

## `numeric_maximum_is_ordered_maximum`

Source: [`theories/FormalSQL/NumericFacts.v:470`](../NumericFacts.v#L470)

Purpose/direction: States the numeric maximum is ordered maximum law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_maximum_is_ordered_maximum` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_maximum_is_ordered_maximum : forall left right,
  numeric_max left right = ordered_maximum Onumeric left right.
```

## `numeric_min_commutative`

Source: [`theories/FormalSQL/NumericFacts.v:474`](../NumericFacts.v#L474)

Purpose/direction: Establishes commutativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_min_commutative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_min_commutative : forall left right,
  numeric_min left right = numeric_min right left.
```

## `numeric_min_associative`

Source: [`theories/FormalSQL/NumericFacts.v:481`](../NumericFacts.v#L481)

Purpose/direction: Establishes associativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_min_associative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_min_associative : forall first second third,
  numeric_min (numeric_min first second) third =
    numeric_min first (numeric_min second third).
```

## `numeric_max_commutative`

Source: [`theories/FormalSQL/NumericFacts.v:489`](../NumericFacts.v#L489)

Purpose/direction: Establishes commutativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_max_commutative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_max_commutative : forall left right,
  numeric_max left right = numeric_max right left.
```

## `numeric_max_associative`

Source: [`theories/FormalSQL/NumericFacts.v:496`](../NumericFacts.v#L496)

Purpose/direction: Establishes associativity for the declared typed numeric semantics operator.

Applicability: Use when the goal or a hypothesis matches the `numeric_max_associative` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_max_associative : forall first second third,
  numeric_max (numeric_max first second) third =
    numeric_max first (numeric_max second third).
```

## `checked_fold_nonempty_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:504`](../NumericFacts.v#L504)

Purpose/direction: States the exact empty-input or empty-result law for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma checked_fold_nonempty_permutation :
  forall (A B : Type) (predicate : value -> bool)
    (extract : list value -> list A) (operation : A -> A -> A)
    (wrap : option A -> B) left right,
    Permutation left right ->
    Permutation (extract left) (extract right) ->
    (forall first second, operation first second = operation second first) ->
    (forall first second third,
      operation (operation first second) third =
      operation first (operation second third)) ->
    (if forallb predicate left
     then wrap (fold_nonempty operation (extract left))
     else wrap None) =
    (if forallb predicate right
     then wrap (fold_nonempty operation (extract right))
     else wrap None).
```

## `interp_min_z_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:528`](../NumericFacts.v#L528)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_min_z_permutation : forall left right,
  Permutation left right -> interp_min_z left = interp_min_z right.
```

## `interp_max_z_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:538`](../NumericFacts.v#L538)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_max_z_permutation : forall left right,
  Permutation left right -> interp_max_z left = interp_max_z right.
```

## `interp_min_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:548`](../NumericFacts.v#L548)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_min_int32_permutation : forall left right,
  Permutation left right -> interp_min_int32 left = interp_min_int32 right.
```

## `interp_max_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:558`](../NumericFacts.v#L558)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_max_int32_permutation : forall left right,
  Permutation left right -> interp_max_int32 left = interp_max_int32 right.
```

## `interp_min_int64_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:568`](../NumericFacts.v#L568)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_min_int64_permutation : forall left right,
  Permutation left right -> interp_min_int64 left = interp_min_int64 right.
```

## `interp_max_int64_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:578`](../NumericFacts.v#L578)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_max_int64_permutation : forall left right,
  Permutation left right -> interp_max_int64 left = interp_max_int64 right.
```

## `interp_min_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:588`](../NumericFacts.v#L588)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_min_numeric_permutation : forall left right,
  Permutation left right -> interp_min_numeric left = interp_min_numeric right.
```

## `interp_max_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:598`](../NumericFacts.v#L598)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_max_numeric_permutation : forall left right,
  Permutation left right -> interp_max_numeric left = interp_max_numeric right.
```

## `interp_sum_int32_as_int64_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:608`](../NumericFacts.v#L608)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_sum_int32_as_int64_permutation : forall left right,
  Permutation left right ->
  interp_sum_int32_as_int64 left = interp_sum_int32_as_int64 right.
```

## `sum_int32_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:624`](../NumericFacts.v#L624)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma sum_int32_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_int32_runtime_error left = sum_int32_runtime_error right.
```

## `interp_avg_int32_as_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:640`](../NumericFacts.v#L640)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_int32_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_avg_int32_as_numeric left = interp_avg_int32_as_numeric right.
```

## `numeric_div_by_Z_success_has_scale`

Source: [`theories/FormalSQL/NumericFacts.v:656`](../NumericFacts.v#L656)

Purpose/direction: Inverts or constructs the successful evaluation branch for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_div_by_Z_success_has_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_div_by_Z_success_has_scale :
  forall sum count average,
    numeric_div_by_Z (numeric_of_Z sum) count = Some average ->
    exists scale,
      numeric_pg_div_scale
        (numeric_of_Z sum) 0 (numeric_of_Z count) 0 = Some scale.
```

## `interp_avg_int32_value_dscale_coherent`

Source: [`theories/FormalSQL/NumericFacts.v:678`](../NumericFacts.v#L678)

Purpose/direction: States the interp avg int32 value dscale coherent law for numeric aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_avg_int32_value_dscale_coherent` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma interp_avg_int32_value_dscale_coherent :
  forall observations,
    forallb is_int32_value observations = true ->
    match int32_avg_numeric_with_scale (int32_values observations) with
    | None =>
        interp_avg_int32_as_numeric observations = Value_numeric None /\
        interp_numeric_aggregate_display_scale
          NumericAverageInt32 observations = Value_Z None
    | Some (average, scale) =>
        interp_avg_int32_as_numeric observations =
          Value_numeric (Some average) /\
        interp_numeric_aggregate_display_scale
          NumericAverageInt32 observations = Value_Z (Some scale)
    end.
```

## `interp_avg_int64_as_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:725`](../NumericFacts.v#L725)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_int64_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_avg_int64_as_numeric left = interp_avg_int64_as_numeric right.
```

## `interp_sum_int64_as_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:741`](../NumericFacts.v#L741)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_sum_int64_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_sum_int64_as_numeric left = interp_sum_int64_as_numeric right.
```

## `sum_int64_numeric_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:753`](../NumericFacts.v#L753)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma sum_int64_numeric_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_int64_numeric_runtime_error left =
  sum_int64_numeric_runtime_error right.
```

## `interp_sum_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:766`](../NumericFacts.v#L766)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_sum_numeric_permutation : forall left right,
  Permutation left right ->
  interp_sum_numeric left = interp_sum_numeric right.
```

## `sum_numeric_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:778`](../NumericFacts.v#L778)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma sum_numeric_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_numeric_runtime_error left = sum_numeric_runtime_error right.
```

## `interp_integer_statistic_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:790`](../NumericFacts.v#L790)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_integer_statistic_permutation : forall left right variance sample,
  Permutation left right ->
  interp_integer_statistic left variance sample =
  interp_integer_statistic right variance sample.
```

## `interp_var_pop_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:800`](../NumericFacts.v#L800)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_var_pop_int32_permutation : forall left right,
  Permutation left right ->
  interp_var_pop_int32 left = interp_var_pop_int32 right.
```

## `interp_var_samp_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:811`](../NumericFacts.v#L811)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_var_samp_int32_permutation : forall left right,
  Permutation left right ->
  interp_var_samp_int32 left = interp_var_samp_int32 right.
```

## `interp_stddev_pop_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:822`](../NumericFacts.v#L822)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_stddev_pop_int32_permutation : forall left right,
  Permutation left right ->
  interp_stddev_pop_int32 left = interp_stddev_pop_int32 right.
```

## `interp_stddev_samp_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:833`](../NumericFacts.v#L833)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_stddev_samp_int32_permutation : forall left right,
  Permutation left right ->
  interp_stddev_samp_int32 left = interp_stddev_samp_int32 right.
```

## `int32_avg_numeric_with_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:844`](../NumericFacts.v#L844)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_avg_numeric_with_scale_permutation : forall left right,
  Permutation left right ->
  int32_avg_numeric_with_scale left = int32_avg_numeric_with_scale right.
```

## `int32_stddev_samp_numeric_with_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:856`](../NumericFacts.v#L856)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_stddev_samp_numeric_with_scale_permutation : forall left right,
  Permutation left right ->
  int32_stddev_samp_numeric_with_scale left =
  int32_stddev_samp_numeric_with_scale right.
```

## `int32_numeric_aggregate_with_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:867`](../NumericFacts.v#L867)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_numeric_aggregate_with_scale_permutation :
  forall aggregate left right,
  Permutation left right ->
  int32_numeric_aggregate_with_scale aggregate left =
  int32_numeric_aggregate_with_scale aggregate right.
```

## `interp_numeric_aggregate_display_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:878`](../NumericFacts.v#L878)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_numeric_aggregate_display_scale_permutation :
  forall aggregate left right,
  Permutation left right ->
  interp_numeric_aggregate_display_scale aggregate left =
  interp_numeric_aggregate_display_scale aggregate right.
```

## `interp_stddev_samp_numeric_fixed_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:893`](../NumericFacts.v#L893)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_stddev_samp_numeric_fixed_permutation :
  forall precision scale left right,
  Permutation left right ->
  interp_stddev_samp_numeric_fixed precision scale left =
  interp_stddev_samp_numeric_fixed precision scale right.
```

## `interp_avg_numeric_fixed_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:915`](../NumericFacts.v#L915)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_numeric_fixed_permutation : forall precision scale left right,
  Permutation left right ->
  interp_avg_numeric_fixed precision scale left =
  interp_avg_numeric_fixed precision scale right.
```

## `avg_numeric_fixed_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:936`](../NumericFacts.v#L936)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma avg_numeric_fixed_runtime_error_permutation :
  forall precision scale left right,
  Permutation left right ->
  avg_numeric_fixed_runtime_error precision scale left =
  avg_numeric_fixed_runtime_error precision scale right.
```

## `stddev_samp_numeric_fixed_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:958`](../NumericFacts.v#L958)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma stddev_samp_numeric_fixed_runtime_error_permutation :
  forall precision scale left right,
  Permutation left right ->
  stddev_samp_numeric_fixed_runtime_error precision scale left =
  stddev_samp_numeric_fixed_runtime_error precision scale right.
```

## `interp_avg_numeric_at_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:980`](../NumericFacts.v#L980)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_numeric_at_scale_permutation : forall scale left right,
  Permutation left right ->
  interp_avg_numeric_at_scale scale left = interp_avg_numeric_at_scale scale right.
```

## `avg_numeric_at_scale_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:995`](../NumericFacts.v#L995)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma avg_numeric_at_scale_runtime_error_permutation : forall scale left right,
  Permutation left right ->
  avg_numeric_at_scale_runtime_error scale left =
  avg_numeric_at_scale_runtime_error scale right.
```

## `distinct_values_membership`

Source: [`theories/FormalSQL/NumericFacts.v:1014`](../NumericFacts.v#L1014)

Purpose/direction: Relates membership or occurrence evidence to typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `distinct_values_membership` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `DISTINCT`, `duplicate elimination`

```rocq
Lemma distinct_values_membership : forall value values,
  In value (distinct_values values) <-> In value values.
```

## `distinct_values_nodup`

Source: [`theories/FormalSQL/NumericFacts.v:1027`](../NumericFacts.v#L1027)

Purpose/direction: Establishes the displayed duplicate-freedom property for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma distinct_values_nodup : forall values, NoDup (distinct_values values).
```

## `distinct_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1037`](../NumericFacts.v#L1037)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma distinct_values_permutation : forall left right,
  Permutation left right ->
  Permutation (distinct_values left) (distinct_values right).
```

## `exact_sum_aggregate_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1051`](../NumericFacts.v#L1051)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma exact_sum_aggregate_permutation :
  forall function left right,
    In function
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
```

## `exact_sum_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1077`](../NumericFacts.v#L1077)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma exact_sum_runtime_error_permutation :
  forall function left right,
    In function
      [Aggregate AggregateSumInt32;
       DistinctAggregate AggregateSumInt32;
       Aggregate AggregateSumInt64Numeric;
       DistinctAggregate AggregateSumInt64Numeric;
       Aggregate AggregateSumNumeric;
       DistinctAggregate AggregateSumNumeric] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
```

## `fixed_numeric_aggregate_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1104`](../NumericFacts.v#L1104)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma fixed_numeric_aggregate_permutation :
  forall precision scale function left right,
    In function
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
```

## `fixed_numeric_aggregate_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1125`](../NumericFacts.v#L1125)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma fixed_numeric_aggregate_runtime_error_permutation :
  forall precision scale function left right,
    In function
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
```

## `numeric_average_at_scale_aggregate_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1147`](../NumericFacts.v#L1147)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_average_at_scale_aggregate_permutation :
  forall scale function left right,
    In function
      [Aggregate (AggregateAverageNumericAtScale scale);
       DistinctAggregate (AggregateAverageNumericAtScale scale)] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
```

## `numeric_average_at_scale_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1163`](../NumericFacts.v#L1163)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_average_at_scale_runtime_error_permutation :
  forall scale function left right,
    In function
      [Aggregate (AggregateAverageNumericAtScale scale);
       DistinctAggregate (AggregateAverageNumericAtScale scale)] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
```

## `integral_numeric_aggregate_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:1180`](../NumericFacts.v#L1180)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma integral_numeric_aggregate_permutation :
  forall function left right,
    In function
      [Aggregate AggregateAverageInt32Numeric;
       DistinctAggregate AggregateAverageInt32Numeric;
       Aggregate (AggregateNumericDisplayScale NumericAverageInt32);
       Aggregate (AggregateNumericDisplayScale NumericStddevSampleInt32);
       Aggregate AggregateAverageInt64Numeric;
       DistinctAggregate AggregateAverageInt64Numeric;
       Aggregate AggregateVariancePopulationInt32;
       DistinctAggregate AggregateVariancePopulationInt32;
       Aggregate AggregateVarianceSampleInt32;
       DistinctAggregate AggregateVarianceSampleInt32;
       Aggregate AggregateStddevPopulationInt32;
       DistinctAggregate AggregateStddevPopulationInt32;
       Aggregate AggregateStddevSampleInt32;
       DistinctAggregate AggregateStddevSampleInt32] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
```

## `numeric_integer_stddev_samp_with_scale_forgets_scale`

Source: [`theories/FormalSQL/NumericFacts.v:1214`](../NumericFacts.v#L1214)

Purpose/direction: States the numeric integer stddev samp with scale forgets scale law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_integer_stddev_samp_with_scale_forgets_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`

```rocq
Theorem numeric_integer_stddev_samp_with_scale_forgets_scale :
  forall count sum sum_squares,
    (match numeric_integer_stddev_samp_with_scale count sum sum_squares with
     | Some (value, _) => Some value
     | None => None
     end) =
    numeric_integer_statistic count sum sum_squares false true.
```

## `int32_avg_fold_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1242`](../NumericFacts.v#L1242)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int32_avg_fold_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`

```rocq
Lemma int32_avg_fold_count_exact : forall values count sum,
  fst (fold_left int32_avg_transition values (count, sum)) =
    count + Z.of_nat (List.length values).
```

## `int64_avg_fold_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1251`](../NumericFacts.v#L1251)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int64_avg_fold_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma int64_avg_fold_count_exact : forall values count sum,
  fst (fold_left int64_avg_transition values (count, sum)) =
    count + Z.of_nat (List.length values).
```

## `integer_stats_fold_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1260`](../NumericFacts.v#L1260)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `integer_stats_fold_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`

```rocq
Lemma integer_stats_fold_count_exact : forall values count sum sum_squares,
  fst (fold_left integer_stats_transition values
    (count, (sum, sum_squares))) =
    count + Z.of_nat (List.length values).
```

## `integer_stats_fold_interval_invariant`

Source: [`theories/FormalSQL/NumericFacts.v:1271`](../NumericFacts.v#L1271)

Purpose/direction: Preserves symbolic lower-sum and upper-square interval bounds through the exact logical integer-statistics fold.

Applicability: Use for the exact logical Z-valued statistics state under the displayed symbolic interval/count hypotheses.  These bounds alone do not justify NUMERIC division, square-root rounding, comparison, or runtime safety.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `aggregate fold`, `interval invariant`, `integer statistics`

```rocq
Lemma integer_stats_fold_interval_invariant :
  forall (values : list Z) lower upper count sum sum_squares,
    0 <= lower ->
    count * lower <= sum ->
    sum_squares <= upper * sum ->
    Forall (fun value => lower <= value <= upper) values ->
    let '(final_count, (final_sum, final_sum_squares)) :=
      fold_left integer_stats_transition values
        (count, (sum, sum_squares)) in
    final_count * lower <= final_sum /\
    final_sum_squares <= upper * final_sum.
```

## `integer_stats_initial_interval_bounds`

Source: [`theories/FormalSQL/NumericFacts.v:1297`](../NumericFacts.v#L1297)

Purpose/direction: Preserves symbolic lower-sum and upper-square interval bounds through the exact logical integer-statistics fold.

Applicability: Use for the exact logical Z-valued statistics state under the displayed symbolic interval/count hypotheses.  These bounds alone do not justify NUMERIC division, square-root rounding, comparison, or runtime safety.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `temporal`, `DATE`, `TIME`, `TIMESTAMP`, `aggregate fold`, `interval bounds`, `integer statistics`

```rocq
Lemma integer_stats_initial_interval_bounds :
  forall (values : list Z) lower upper final_count final_sum
      final_sum_squares,
    0 <= lower ->
    Forall (fun value => lower <= value <= upper) values ->
    fold_left integer_stats_transition values (0, (0, 0)) =
      (final_count, (final_sum, final_sum_squares)) ->
    final_count * lower <= final_sum /\
    final_sum_squares <= upper * final_sum.
```

## `bounded_integer_stats_sum_positive`

Source: [`theories/FormalSQL/NumericFacts.v:1317`](../NumericFacts.v#L1317)

Purpose/direction: Derives strict positivity of the logical integer-statistics sum from a positive symbolic lower bound and a nonempty fold count.

Applicability: Use for the exact logical Z-valued statistics state under the displayed symbolic interval/count hypotheses.  These bounds alone do not justify NUMERIC division, square-root rounding, comparison, or runtime safety.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `aggregate sum`, `positivity`, `integer statistics`

```rocq
Lemma bounded_integer_stats_sum_positive :
  forall (values : list Z) lower upper count sum sum_squares,
    0 < lower ->
    Forall (fun value => lower <= value <= upper) values ->
    fold_left integer_stats_transition values (0, (0, 0)) =
      (count, (sum, sum_squares)) ->
    1 <= count ->
    0 < sum.
```

## `numeric_avg_scale_transition_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1334`](../NumericFacts.v#L1334)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_scale_transition_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_scale_transition_total_count_exact :
  forall scale state next,
    numeric_avg_scale_total_count
      (numeric_avg_scale_transition scale state next) =
    numeric_avg_scale_total_count state + 1.
```

## `numeric_avg_scale_fold_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1349`](../NumericFacts.v#L1349)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_scale_fold_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_scale_fold_total_count_exact : forall scale values state,
  numeric_avg_scale_total_count
    (fold_left (numeric_avg_scale_transition scale) values state) =
  numeric_avg_scale_total_count state + Z.of_nat (List.length values).
```

## `numeric_sum_transition_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1359`](../NumericFacts.v#L1359)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_transition_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_transition_total_count_exact : forall state next,
  numeric_sum_total_count (numeric_sum_transition state next) =
    numeric_sum_total_count state + 1.
```

## `numeric_sum_fold_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1371`](../NumericFacts.v#L1371)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_fold_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_fold_total_count_exact : forall values state,
  numeric_sum_total_count (fold_left numeric_sum_transition values state) =
    numeric_sum_total_count state + Z.of_nat (List.length values).
```

## `numeric_scale_stats_transition_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1380`](../NumericFacts.v#L1380)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_scale_stats_transition_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_scale_stats_transition_total_count_exact :
  forall scale state next,
    numeric_scale_stats_total_count
      (numeric_scale_stats_transition scale state next) =
    numeric_scale_stats_total_count state + 1.
```

## `numeric_scale_stats_fold_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1392`](../NumericFacts.v#L1392)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_scale_stats_fold_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_scale_stats_fold_total_count_exact : forall scale values state,
  numeric_scale_stats_total_count
    (fold_left (numeric_scale_stats_transition scale) values state) =
  numeric_scale_stats_total_count state + Z.of_nat (List.length values).
```

## `integral_average_runtime_error_totality_certificate`

Source: [`theories/FormalSQL/NumericFacts.v:1402`](../NumericFacts.v#L1402)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem integral_average_runtime_error_totality_certificate : forall values,
  avg_int32_numeric_runtime_error values = None /\
  avg_int64_numeric_runtime_error values = None.
```

## `numeric_aggregate_display_scale_runtime_error_totality_certificate`

Source: [`theories/FormalSQL/NumericFacts.v:1407`](../NumericFacts.v#L1407)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for numeric aggregate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem numeric_aggregate_display_scale_runtime_error_totality_certificate :
  forall aggregate values,
  numeric_aggregate_display_scale_runtime_error aggregate values = None.
```

## `integer_statistic_runtime_error_totality_certificate`

Source: [`theories/FormalSQL/NumericFacts.v:1412`](../NumericFacts.v#L1412)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem integer_statistic_runtime_error_totality_certificate : forall values,
  integer_statistic_runtime_error values = None.
```

## `numeric_compare_refl`

Source: [`theories/FormalSQL/NumericFacts.v:1421`](../NumericFacts.v#L1421)

Purpose/direction: Establishes reflexivity for typed numeric semantics.

Applicability: Use to orient, transport, or compose a semantic relation about typed numeric semantics.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `equivalence`, `congruence`

```rocq
Lemma numeric_compare_refl :
  forall value,
    numeric_compare value value = Eq.
```

## `numeric_eqb_refl`

Source: [`theories/FormalSQL/NumericFacts.v:1429`](../NumericFacts.v#L1429)

Purpose/direction: Establishes reflexivity for typed numeric semantics.

Applicability: Use to orient, transport, or compose a semantic relation about typed numeric semantics.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `equivalence`, `congruence`

```rocq
Lemma numeric_eqb_refl :
  forall value,
    numeric_eqb value value = true.
```

## `numeric_cast_typmod_result`

Source: [`theories/FormalSQL/NumericFacts.v:1439`](../NumericFacts.v#L1439)

Purpose/direction: States the numeric cast typmod result law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_cast_typmod_result` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_cast_typmod_result :
  forall value precision scale result,
    numeric_cast_typmod value precision scale = Some result ->
    result = numeric_round_to_scale value scale.
```

## `numeric_avg_fixed_attested_finite_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1454`](../NumericFacts.v#L1454)

Purpose/direction: States the numeric avg fixed attested finite exact law for numeric aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_fixed_attested_finite_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_avg_fixed_attested_finite_exact :
  forall precision scale q,
    numeric_cast_typmod (NumericFinite q) precision scale =
      Some (NumericFinite q) ->
    numeric_of_scaled (numeric_finite_rounded_coeff q scale) scale =
      NumericFinite q.
```

## `numeric_avg_attested_scale_finite_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1471`](../NumericFacts.v#L1471)

Purpose/direction: States the numeric avg attested scale finite exact law for numeric aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_attested_scale_finite_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_attested_scale_finite_exact :
  forall scale q,
    numeric_round_to_scale (NumericFinite q) scale = NumericFinite q ->
    numeric_of_scaled (numeric_finite_rounded_coeff q scale) scale =
      NumericFinite q.
```

## `finite_numeric_div_by_zero`

Source: [`theories/FormalSQL/NumericFacts.v:1482`](../NumericFacts.v#L1482)

Purpose/direction: States the finite numeric div by zero law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `finite_numeric_div_by_zero` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma finite_numeric_div_by_zero :
  forall value,
    numeric_div_at_scales (NumericFinite value) 0 numeric_zero 0 = None.
```

## `numeric_to_int32_checked_result_in_range`

Source: [`theories/FormalSQL/NumericFacts.v:1492`](../NumericFacts.v#L1492)

Purpose/direction: Connects the displayed range/representability premise to typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_to_int32_checked_result_in_range` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma numeric_to_int32_checked_result_in_range :
  forall value result,
    numeric_to_int32_checked value = Some result ->
    int32_min <= int32_value result <= int32_max.
```

## `finite_decimal_numeric_division_total`

Source: [`theories/FormalSQL/NumericFacts.v:1506`](../NumericFacts.v#L1506)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `finite_decimal_numeric_division_total` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma finite_decimal_numeric_division_total :
  forall left right left_scale right_scale
    left_coeff left_decimal_scale right_coeff right_decimal_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_decimal_parts (NumericFinite left) =
      Some (left_coeff, left_decimal_scale) ->
    numeric_decimal_parts (NumericFinite right) =
      Some (right_coeff, right_decimal_scale) ->
    exists result,
      numeric_div_at_scales
        (NumericFinite left) left_scale
        (NumericFinite right) right_scale = Some result.
```

## `numeric_positive_is_nonzero`

Source: [`theories/FormalSQL/NumericFacts.v:1529`](../NumericFacts.v#L1529)

Purpose/direction: States the numeric positive is nonzero law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_positive_is_nonzero` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_positive_is_nonzero :
  forall value,
    numeric_compare numeric_zero value = Lt ->
    numeric_eqb value numeric_zero = false.
```

## `finite_numeric_division_runtime_error_none`

Source: [`theories/FormalSQL/NumericFacts.v:1550`](../NumericFacts.v#L1550)

Purpose/direction: Establishes the explicit runtime-safety direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma finite_numeric_division_runtime_error_none :
  forall left right left_scale right_scale result,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result ->
    numeric_runtime_fits_bool result = true ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      None.
```

## `numeric_positive_from_integer_lower_bound`

Source: [`theories/FormalSQL/NumericFacts.v:1572`](../NumericFacts.v#L1572)

Purpose/direction: States the numeric positive from integer lower bound law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_positive_from_integer_lower_bound` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma numeric_positive_from_integer_lower_bound :
  forall lower value,
    1 <= lower ->
    (numeric_compare (numeric_of_Z lower) value = Lt \/
     numeric_compare (numeric_of_Z lower) value = Eq) ->
    numeric_compare numeric_zero value = Lt.
```

## `numeric_round_quot_nonnegative_half_ulp`

Source: [`theories/FormalSQL/NumericFacts.v:1603`](../NumericFacts.v#L1603)

Purpose/direction: Exposes the exact nonnegative PostgreSQL NUMERIC rounding or square-root midpoint branch together with its half-unit fixed-point bound.

Applicability: Use only under the displayed nonnegative input and scale premises.  The coefficient shape is not itself a SQL comparison or runtime-safety result.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `NUMERIC rounding`, `half ULP`, `nonnegative`

```rocq
Lemma numeric_round_quot_nonnegative_half_ulp :
  forall numerator denominator,
    0 <= numerator ->
    0 < denominator ->
    2 * numerator - denominator <=
      2 * numeric_round_quot numerator denominator * denominator <=
    2 * numerator + denominator.
```

## `numeric_pg_div_scale_display_valid`

Source: [`theories/FormalSQL/NumericFacts.v:1639`](../NumericFacts.v#L1639)

Purpose/direction: Connects PostgreSQL-selected NUMERIC division scale and rounding to a fixed-point strict comparison, retaining the explicit half-ULP margin.

Applicability: Use with the exact selected-scale equation and explicit fixed-point half-ULP margin.  Supply denominator nonzero, scale validity, and result fit premises; do not infer them from rational order alone.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `NUMERIC division`, `display scale`, `runtime boundary`

```rocq
Lemma numeric_pg_div_scale_display_valid :
  forall left left_scale right right_scale result_scale,
    numeric_pg_div_scale left left_scale right right_scale =
      Some result_scale ->
    numeric_display_scale_valid_bool result_scale = true.
```

## `numeric_of_scaled_compare_lt`

Source: [`theories/FormalSQL/NumericFacts.v:1678`](../NumericFacts.v#L1678)

Purpose/direction: Connects PostgreSQL-selected NUMERIC division scale and rounding to a fixed-point strict comparison, retaining the explicit half-ULP margin.

Applicability: Use with the exact selected-scale equation and explicit fixed-point half-ULP margin.  Supply denominator nonzero, scale validity, and result fit premises; do not infer them from rational order alone.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `NUMERIC comparison`, `cross scale`, `strict order`

```rocq
Lemma numeric_of_scaled_compare_lt :
  forall left_coeff left_scale right_coeff right_scale,
    0 <= left_scale ->
    0 <= right_scale ->
    left_coeff * Z.pow 10 right_scale <
      right_coeff * Z.pow 10 left_scale ->
    numeric_compare
      (numeric_of_scaled left_coeff left_scale)
      (numeric_of_scaled right_coeff right_scale) = Lt.
```

## `numeric_round_to_scale_nonnegative_half_ulp`

Source: [`theories/FormalSQL/NumericFacts.v:1729`](../NumericFacts.v#L1729)

Purpose/direction: Exposes the exact nonnegative PostgreSQL NUMERIC rounding or square-root midpoint branch together with its half-unit fixed-point bound.

Applicability: Use only under the displayed nonnegative input and scale premises.  The coefficient shape is not itself a SQL comparison or runtime-safety result.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `NUMERIC rounding`, `display scale`, `half ULP`

```rocq
Lemma numeric_round_to_scale_nonnegative_half_ulp :
  forall q scale,
    let scaled := this (Qcmult q (numeric_scale_factor scale)) in
    0 <= Qnum scaled ->
    let coefficient :=
      numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)) in
    numeric_round_to_scale (NumericFinite q) scale =
      numeric_of_scaled coefficient scale /\
    2 * Qnum scaled - Zpos (Qden scaled) <=
      2 * coefficient * Zpos (Qden scaled) <=
    2 * Qnum scaled + Zpos (Qden scaled).
```

## `finite_numeric_division_result_rounding`

Source: [`theories/FormalSQL/NumericFacts.v:1751`](../NumericFacts.v#L1751)

Purpose/direction: Connects PostgreSQL-selected NUMERIC division scale and rounding to a fixed-point strict comparison, retaining the explicit half-ULP margin.

Applicability: Use with the exact selected-scale equation and explicit fixed-point half-ULP margin.  Supply denominator nonzero, scale validity, and result fit premises; do not infer them from rational order alone.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `NUMERIC division`, `rounding`, `selected scale`

```rocq
Lemma finite_numeric_division_result_rounding :
  forall left right left_scale right_scale result_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_pg_div_scale
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result_scale ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale =
    Some
      (numeric_round_to_scale
        (NumericFinite (Qcdiv left right)) result_scale).
```

## `finite_numeric_division_strict_margin`

Source: [`theories/FormalSQL/NumericFacts.v:1775`](../NumericFacts.v#L1775)

Purpose/direction: Connects PostgreSQL-selected NUMERIC division scale and rounding to a fixed-point strict comparison, retaining the explicit half-ULP margin.

Applicability: Use with the exact selected-scale equation and explicit fixed-point half-ULP margin.  Supply denominator nonzero, scale validity, and result fit premises; do not infer them from rational order alone.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `NUMERIC division`, `strict margin`, `runtime error`

```rocq
Theorem finite_numeric_division_strict_margin :
  forall left right left_scale right_scale result_scale
      threshold_coeff threshold_scale,
    let quotient := Qcdiv left right in
    let scaled := this (Qcmult quotient
      (numeric_scale_factor result_scale)) in
    let result_coeff :=
      numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)) in
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_pg_div_scale
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result_scale ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    0 <= threshold_scale ->
    0 <= Qnum scaled ->
    (2 * Qnum scaled + Zpos (Qden scaled)) *
        Z.pow 10 threshold_scale <
      2 * threshold_coeff * Zpos (Qden scaled) *
        Z.pow 10 result_scale ->
    numeric_runtime_fits_bool
      (numeric_of_scaled result_coeff result_scale) = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale =
        Some (numeric_of_scaled result_coeff result_scale) /\
    numeric_compare
      (numeric_of_scaled result_coeff result_scale)
      (numeric_of_scaled threshold_coeff threshold_scale) = Lt /\
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      None.
```

## `finite_numeric_division_runtime_error_zero_divisor`

Source: [`theories/FormalSQL/NumericFacts.v:1846`](../NumericFacts.v#L1846)

Purpose/direction: Classifies the displayed finite NUMERIC division failure as the exact PostgreSQL DivisionByZero or NumericValueOutOfRange category.

Applicability: Use for the exact displayed failure branch and preserve evaluation reachability.  These categories are complementary to, not interchangeable with, a generic no-error premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `NUMERIC division`, `DivisionByZero`, `runtime error`

```rocq
Lemma finite_numeric_division_runtime_error_zero_divisor :
  forall left right left_scale right_scale,
    numeric_eqb (NumericFinite right) numeric_zero = true ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException DivisionByZero).
```

## `finite_numeric_division_runtime_error_invalid_scale`

Source: [`theories/FormalSQL/NumericFacts.v:1859`](../NumericFacts.v#L1859)

Purpose/direction: Classifies the displayed finite NUMERIC division failure as the exact PostgreSQL DivisionByZero or NumericValueOutOfRange category.

Applicability: Use for the exact displayed failure branch and preserve evaluation reachability.  These categories are complementary to, not interchangeable with, a generic no-error premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`, `NUMERIC division`, `NumericValueOutOfRange`, `display scale`

```rocq
Lemma finite_numeric_division_runtime_error_invalid_scale :
  forall left right left_scale right_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    (numeric_display_scale_valid_bool left_scale = false \/
     numeric_display_scale_valid_bool right_scale = false) ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
```

## `finite_numeric_division_runtime_error_missing_result`

Source: [`theories/FormalSQL/NumericFacts.v:1878`](../NumericFacts.v#L1878)

Purpose/direction: Classifies the displayed finite NUMERIC division failure as the exact PostgreSQL DivisionByZero or NumericValueOutOfRange category.

Applicability: Use for the exact displayed failure branch and preserve evaluation reachability.  These categories are complementary to, not interchangeable with, a generic no-error premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `NUMERIC division`, `NumericValueOutOfRange`, `runtime error`

```rocq
Lemma finite_numeric_division_runtime_error_missing_result :
  forall left right left_scale right_scale,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = None ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
```

## `finite_numeric_division_runtime_error_result_out_of_range`

Source: [`theories/FormalSQL/NumericFacts.v:1897`](../NumericFacts.v#L1897)

Purpose/direction: Classifies the displayed finite NUMERIC division failure as the exact PostgreSQL DivisionByZero or NumericValueOutOfRange category.

Applicability: Use for the exact displayed failure branch and preserve evaluation reachability.  These categories are complementary to, not interchangeable with, a generic no-error premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `NUMERIC division`, `NumericValueOutOfRange`, `runtime error`

```rocq
Lemma finite_numeric_division_runtime_error_result_out_of_range :
  forall left right left_scale right_scale result,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result ->
    numeric_runtime_fits_bool result = false ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
```

## `numeric_sqrt_at_scale_half_ulp_shape`

Source: [`theories/FormalSQL/NumericFacts.v:1923`](../NumericFacts.v#L1923)

Purpose/direction: Exposes the exact nonnegative PostgreSQL NUMERIC rounding or square-root midpoint branch together with its half-unit fixed-point bound.

Applicability: Use only under the displayed nonnegative input and scale premises.  The coefficient shape is not itself a SQL comparison or runtime-safety result.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `NUMERIC square root`, `half ULP`, `midpoint`

```rocq
Lemma numeric_sqrt_at_scale_half_ulp_shape :
  forall q scale,
    0 <= scale ->
    let raw := this q in
    0 <= Qnum raw ->
    let factor := Z.pow 10 scale in
    let numerator := Qnum raw * factor * factor in
    let denominator := Zpos (Qden raw) in
    let lower := Z.sqrt (Z.div numerator denominator) in
    let midpoint_twice := 2 * lower + 1 in
    let coefficient :=
      if denominator * midpoint_twice * midpoint_twice <=? 4 * numerator
      then lower + 1
      else lower in
    numeric_sqrt_at_scale (NumericFinite q) scale =
      Some (numeric_of_scaled coefficient scale) /\
    0 <= lower /\
    denominator * lower * lower <= numerator /\
    numerator < denominator * (lower + 1) * (lower + 1) /\
    ((coefficient = lower /\
      4 * numerator <
        denominator * midpoint_twice * midpoint_twice) \/
     (coefficient = lower + 1 /\
      denominator * midpoint_twice * midpoint_twice <= 4 * numerator)).
```

## `numeric_integer_stddev_samp_positive_success_iff`

Source: [`theories/FormalSQL/NumericFacts.v:2012`](../NumericFacts.v#L2012)

Purpose/direction: Decomposes the positive/nonempty integral aggregate finalizer into its exact selected-scale NUMERIC division and, for STDDEV_SAMP, square-root path.

Applicability: Use only after proving the positive sample numerator or nonempty AVG fold/count premise.  Compose rounding, comparison, and runtime categories through the separate NUMERIC interfaces.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `STDDEV_SAMP`, `NUMERIC square root`, `selected scale`

```rocq
Theorem numeric_integer_stddev_samp_positive_success_iff :
  forall count sum sum_squares stddev scale,
    2 <= count ->
    0 < count * sum_squares - sum * sum ->
    (numeric_integer_stddev_samp_with_scale count sum sum_squares =
      Some (stddev, scale) <->
     exists variance,
       numeric_pg_div_scale
         (numeric_of_Z (count * sum_squares - sum * sum)) 0
         (numeric_of_Z (count * (count - 1))) 0 = Some scale /\
       numeric_div_at_scales
         (numeric_of_Z (count * sum_squares - sum * sum)) 0
         (numeric_of_Z (count * (count - 1))) 0 = Some variance /\
       numeric_sqrt_at_scale variance scale = Some stddev).
```

## `int32_avg_numeric_with_scale_success_iff`

Source: [`theories/FormalSQL/NumericFacts.v:2060`](../NumericFacts.v#L2060)

Purpose/direction: Decomposes the positive/nonempty integral aggregate finalizer into its exact selected-scale NUMERIC division and, for STDDEV_SAMP, square-root path.

Applicability: Use only after proving the positive sample numerator or nonempty AVG fold/count premise.  Compose rounding, comparison, and runtime categories through the separate NUMERIC interfaces.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `AVG`, `NUMERIC division`, `selected scale`

```rocq
Theorem int32_avg_numeric_with_scale_success_iff :
  forall values count sum average scale,
    values <> [] ->
    fold_left int32_avg_transition values (0, 0) = (count, sum) ->
    (int32_avg_numeric_with_scale values = Some (average, scale) <->
     numeric_pg_div_scale
       (numeric_of_Z sum) 0 (numeric_of_Z count) 0 = Some scale /\
     numeric_div_at_scales
       (numeric_of_Z sum) 0 (numeric_of_Z count) 0 = Some average).
```

## `numeric_of_scaled_compare_not_gt`

Source: [`theories/FormalSQL/NumericFacts.v:2100`](../NumericFacts.v#L2100)

Purpose/direction: Transports a non-strict cross-scale coefficient bound to a NUMERIC comparison that cannot be Gt while preserving the observable Eq case.

Applicability: Use with nonnegative coefficients and the displayed cross-multiplied non-strict bound.  The result excludes only Gt and deliberately retains Eq.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `NUMERIC comparison`, `cross scale`, `not greater`, `equality preserved`

```rocq
Lemma numeric_of_scaled_compare_not_gt :
  forall left_coeff left_scale right_coeff right_scale,
    0 <= left_scale ->
    0 <= right_scale ->
    left_coeff * Z.pow 10 right_scale <=
      right_coeff * Z.pow 10 left_scale ->
    numeric_compare
      (numeric_of_scaled left_coeff left_scale)
      (numeric_of_scaled right_coeff right_scale) <> Gt.
```

## `positive_numeric_of_scaled_nonzero`

Source: [`theories/FormalSQL/NumericFacts.v:2147`](../NumericFacts.v#L2147)

Purpose/direction: States the positive numeric of scaled nonzero law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `positive_numeric_of_scaled_nonzero` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma positive_numeric_of_scaled_nonzero :
  forall coefficient scale,
    0 <= scale ->
    0 < coefficient ->
    numeric_eqb (numeric_of_scaled coefficient scale) numeric_zero = false.
```

## `numeric_runtime_fits_from_decimal_parts`

Source: [`theories/FormalSQL/NumericFacts.v:2160`](../NumericFacts.v#L2160)

Purpose/direction: States the numeric runtime fits from decimal parts law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `scalar`

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma numeric_runtime_fits_from_decimal_parts :
  forall value coefficient scale,
    numeric_decimal_parts value = Some (coefficient, scale) ->
    numeric_display_scale_valid_bool scale = true ->
    numeric_integer_digit_count coefficient scale <=
      postgres_numeric_max_integer_digits ->
    numeric_runtime_fits_bool value = true.
```
