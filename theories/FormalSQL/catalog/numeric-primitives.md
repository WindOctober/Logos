# NUMERIC primitive semantics

Route here for: NUMERIC representation, precision/scale, division, rounding, AVG states.

This focused catalog contains 81 declarations routed at declaration granularity from `NumericFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `numeric_avg_scale_transition_commutes`

Source: [`theories/FormalSQL/NumericFacts.v:15`](../NumericFacts.v#L15)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_scale_transition_commutes` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

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

Cross-index: `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `scalar` (rank 52)

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

Cross-index: `scalar` (rank 52)

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

Cross-index: `scalar` (rank 52)

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

Cross-index: `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma integer_stats_fold_permutation : forall left right initial,
  Permutation left right ->
  fold_left integer_stats_transition left initial =
  fold_left integer_stats_transition right initial.
```

## `int32_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:230`](../NumericFacts.v#L230)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `int32_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_values_as_flat_map : forall values,
  int32_values values = flat_map int32_value_projection values.
```

## `int64_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:238`](../NumericFacts.v#L238)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `int64_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `BIGINT`, `int64`

```rocq
Lemma int64_values_as_flat_map : forall values,
  int64_values values = flat_map int64_value_projection values.
```

## `numeric_values_as_flat_map`

Source: [`theories/FormalSQL/NumericFacts.v:246`](../NumericFacts.v#L246)

Purpose/direction: Bridges the two displayed representations of typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_values_as_flat_map` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_values_as_flat_map : forall values,
  numeric_values values = flat_map numeric_value_projection values.
```

## `int32_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:254`](../NumericFacts.v#L254)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_values_permutation : forall left right,
  Permutation left right ->
  Permutation (int32_values left) (int32_values right).
```

## `int64_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:262`](../NumericFacts.v#L262)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int64_values_permutation : forall left right,
  Permutation left right ->
  Permutation (int64_values left) (int64_values right).
```

## `numeric_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:270`](../NumericFacts.v#L270)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma numeric_values_permutation : forall left right,
  Permutation left right ->
  Permutation (numeric_values left) (numeric_values right).
```

## `forallb_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:278`](../NumericFacts.v#L278)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma forallb_permutation : forall (A : Type) (predicate : A -> bool) left right,
  Permutation left right -> forallb predicate left = forallb predicate right.
```

## `interp_sum_int32_as_int64_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:289`](../NumericFacts.v#L289)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_sum_int32_as_int64_permutation : forall left right,
  Permutation left right ->
  interp_sum_int32_as_int64 left = interp_sum_int32_as_int64 right.
```

## `sum_int32_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:305`](../NumericFacts.v#L305)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma sum_int32_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_int32_runtime_error left = sum_int32_runtime_error right.
```

## `interp_avg_int32_as_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:321`](../NumericFacts.v#L321)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_int32_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_avg_int32_as_numeric left = interp_avg_int32_as_numeric right.
```

## `numeric_div_by_Z_success_has_scale`

Source: [`theories/FormalSQL/NumericFacts.v:337`](../NumericFacts.v#L337)

Purpose/direction: Inverts or constructs the successful evaluation branch for typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_div_by_Z_success_has_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:359`](../NumericFacts.v#L359)

Purpose/direction: States the interp avg int32 value dscale coherent law for numeric aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_avg_int32_value_dscale_coherent` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:406`](../NumericFacts.v#L406)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_int64_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_avg_int64_as_numeric left = interp_avg_int64_as_numeric right.
```

## `interp_sum_int64_as_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:422`](../NumericFacts.v#L422)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_sum_int64_as_numeric_permutation : forall left right,
  Permutation left right ->
  interp_sum_int64_as_numeric left = interp_sum_int64_as_numeric right.
```

## `sum_int64_numeric_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:434`](../NumericFacts.v#L434)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `BIGINT`, `int64`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma sum_int64_numeric_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_int64_numeric_runtime_error left =
  sum_int64_numeric_runtime_error right.
```

## `interp_sum_numeric_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:447`](../NumericFacts.v#L447)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_sum_numeric_permutation : forall left right,
  Permutation left right ->
  interp_sum_numeric left = interp_sum_numeric right.
```

## `sum_numeric_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:459`](../NumericFacts.v#L459)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma sum_numeric_runtime_error_permutation : forall left right,
  Permutation left right ->
  sum_numeric_runtime_error left = sum_numeric_runtime_error right.
```

## `interp_integer_statistic_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:471`](../NumericFacts.v#L471)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_integer_statistic_permutation : forall left right variance sample,
  Permutation left right ->
  interp_integer_statistic left variance sample =
  interp_integer_statistic right variance sample.
```

## `interp_var_pop_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:481`](../NumericFacts.v#L481)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_var_pop_int32_permutation : forall left right,
  Permutation left right ->
  interp_var_pop_int32 left = interp_var_pop_int32 right.
```

## `interp_var_samp_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:492`](../NumericFacts.v#L492)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_var_samp_int32_permutation : forall left right,
  Permutation left right ->
  interp_var_samp_int32 left = interp_var_samp_int32 right.
```

## `interp_stddev_pop_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:503`](../NumericFacts.v#L503)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_stddev_pop_int32_permutation : forall left right,
  Permutation left right ->
  interp_stddev_pop_int32 left = interp_stddev_pop_int32 right.
```

## `interp_stddev_samp_int32_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:514`](../NumericFacts.v#L514)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_stddev_samp_int32_permutation : forall left right,
  Permutation left right ->
  interp_stddev_samp_int32 left = interp_stddev_samp_int32 right.
```

## `int32_avg_numeric_with_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:525`](../NumericFacts.v#L525)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_avg_numeric_with_scale_permutation : forall left right,
  Permutation left right ->
  int32_avg_numeric_with_scale left = int32_avg_numeric_with_scale right.
```

## `int32_stddev_samp_numeric_with_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:537`](../NumericFacts.v#L537)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_stddev_samp_numeric_with_scale_permutation : forall left right,
  Permutation left right ->
  int32_stddev_samp_numeric_with_scale left =
  int32_stddev_samp_numeric_with_scale right.
```

## `int32_numeric_aggregate_with_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:548`](../NumericFacts.v#L548)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `INTEGER`, `int32`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma int32_numeric_aggregate_with_scale_permutation :
  forall aggregate left right,
  Permutation left right ->
  int32_numeric_aggregate_with_scale aggregate left =
  int32_numeric_aggregate_with_scale aggregate right.
```

## `interp_numeric_aggregate_display_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:559`](../NumericFacts.v#L559)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_numeric_aggregate_display_scale_permutation :
  forall aggregate left right,
  Permutation left right ->
  interp_numeric_aggregate_display_scale aggregate left =
  interp_numeric_aggregate_display_scale aggregate right.
```

## `interp_stddev_samp_numeric_fixed_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:574`](../NumericFacts.v#L574)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_stddev_samp_numeric_fixed_permutation :
  forall precision scale left right,
  Permutation left right ->
  interp_stddev_samp_numeric_fixed precision scale left =
  interp_stddev_samp_numeric_fixed precision scale right.
```

## `interp_avg_numeric_fixed_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:596`](../NumericFacts.v#L596)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_numeric_fixed_permutation : forall precision scale left right,
  Permutation left right ->
  interp_avg_numeric_fixed precision scale left =
  interp_avg_numeric_fixed precision scale right.
```

## `avg_numeric_fixed_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:617`](../NumericFacts.v#L617)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma avg_numeric_fixed_runtime_error_permutation :
  forall precision scale left right,
  Permutation left right ->
  avg_numeric_fixed_runtime_error precision scale left =
  avg_numeric_fixed_runtime_error precision scale right.
```

## `stddev_samp_numeric_fixed_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:639`](../NumericFacts.v#L639)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma stddev_samp_numeric_fixed_runtime_error_permutation :
  forall precision scale left right,
  Permutation left right ->
  stddev_samp_numeric_fixed_runtime_error precision scale left =
  stddev_samp_numeric_fixed_runtime_error precision scale right.
```

## `interp_avg_numeric_at_scale_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:661`](../NumericFacts.v#L661)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma interp_avg_numeric_at_scale_permutation : forall scale left right,
  Permutation left right ->
  interp_avg_numeric_at_scale scale left = interp_avg_numeric_at_scale scale right.
```

## `avg_numeric_at_scale_runtime_error_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:676`](../NumericFacts.v#L676)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma avg_numeric_at_scale_runtime_error_permutation : forall scale left right,
  Permutation left right ->
  avg_numeric_at_scale_runtime_error scale left =
  avg_numeric_at_scale_runtime_error scale right.
```

## `distinct_values_membership`

Source: [`theories/FormalSQL/NumericFacts.v:695`](../NumericFacts.v#L695)

Purpose/direction: Relates membership or occurrence evidence to typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `distinct_values_membership` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `DISTINCT`, `duplicate elimination`

```rocq
Lemma distinct_values_membership : forall value values,
  In value (distinct_values values) <-> In value values.
```

## `distinct_values_nodup`

Source: [`theories/FormalSQL/NumericFacts.v:708`](../NumericFacts.v#L708)

Purpose/direction: Establishes the displayed duplicate-freedom property for typed numeric semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 52), `scalar` (rank 52)

Search aliases: `numeric semantics`, `DISTINCT`, `duplicate elimination`, `multiplicity`

```rocq
Lemma distinct_values_nodup : forall values, NoDup (distinct_values values).
```

## `distinct_values_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:718`](../NumericFacts.v#L718)

Purpose/direction: Shows that the declared typed numeric semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

Search aliases: `numeric semantics`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma distinct_values_permutation : forall left right,
  Permutation left right ->
  Permutation (distinct_values left) (distinct_values right).
```

## `exact_sum_aggregate_permutation`

Source: [`theories/FormalSQL/NumericFacts.v:732`](../NumericFacts.v#L732)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:758`](../NumericFacts.v#L758)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

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

Source: [`theories/FormalSQL/NumericFacts.v:785`](../NumericFacts.v#L785)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:806`](../NumericFacts.v#L806)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

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

Source: [`theories/FormalSQL/NumericFacts.v:828`](../NumericFacts.v#L828)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:844`](../NumericFacts.v#L844)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 52), `bag` (rank 44), `scalar` (rank 40)

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

Source: [`theories/FormalSQL/NumericFacts.v:861`](../NumericFacts.v#L861)

Purpose/direction: Shows that the declared numeric aggregate semantics result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about numeric aggregate semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 44), `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:895`](../NumericFacts.v#L895)

Purpose/direction: States the numeric integer stddev samp with scale forgets scale law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_integer_stddev_samp_with_scale_forgets_scale` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 50)

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

Source: [`theories/FormalSQL/NumericFacts.v:923`](../NumericFacts.v#L923)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int32_avg_fold_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`

```rocq
Lemma int32_avg_fold_count_exact : forall values count sum,
  fst (fold_left int32_avg_transition values (count, sum)) =
    count + Z.of_nat (List.length values).
```

## `int64_avg_fold_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:932`](../NumericFacts.v#L932)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `int64_avg_fold_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `BIGINT`, `int64`

```rocq
Lemma int64_avg_fold_count_exact : forall values count sum,
  fst (fold_left int64_avg_transition values (count, sum)) =
    count + Z.of_nat (List.length values).
```

## `integer_stats_fold_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:941`](../NumericFacts.v#L941)

Purpose/direction: Relates the fold or transition state to the displayed numeric aggregate semantics result.

Applicability: Use when the goal or a hypothesis matches the `integer_stats_fold_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `INTEGER`, `int32`

```rocq
Lemma integer_stats_fold_count_exact : forall values count sum sum_squares,
  fst (fold_left integer_stats_transition values
    (count, (sum, sum_squares))) =
    count + Z.of_nat (List.length values).
```

## `numeric_avg_scale_transition_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:952`](../NumericFacts.v#L952)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_scale_transition_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_scale_transition_total_count_exact :
  forall scale state next,
    numeric_avg_scale_total_count
      (numeric_avg_scale_transition scale state next) =
    numeric_avg_scale_total_count state + 1.
```

## `numeric_avg_scale_fold_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:967`](../NumericFacts.v#L967)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_scale_fold_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_scale_fold_total_count_exact : forall scale values state,
  numeric_avg_scale_total_count
    (fold_left (numeric_avg_scale_transition scale) values state) =
  numeric_avg_scale_total_count state + Z.of_nat (List.length values).
```

## `numeric_sum_transition_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:977`](../NumericFacts.v#L977)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_transition_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_transition_total_count_exact : forall state next,
  numeric_sum_total_count (numeric_sum_transition state next) =
    numeric_sum_total_count state + 1.
```

## `numeric_sum_fold_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:989`](../NumericFacts.v#L989)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_sum_fold_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_sum_fold_total_count_exact : forall values state,
  numeric_sum_total_count (fold_left numeric_sum_transition values state) =
    numeric_sum_total_count state + Z.of_nat (List.length values).
```

## `numeric_scale_stats_transition_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:998`](../NumericFacts.v#L998)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_scale_stats_transition_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_scale_stats_transition_total_count_exact :
  forall scale state next,
    numeric_scale_stats_total_count
      (numeric_scale_stats_transition scale state next) =
    numeric_scale_stats_total_count state + 1.
```

## `numeric_scale_stats_fold_total_count_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1010`](../NumericFacts.v#L1010)

Purpose/direction: Establishes totality of the indicated numeric aggregate semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `numeric_scale_stats_fold_total_count_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_scale_stats_fold_total_count_exact : forall scale values state,
  numeric_scale_stats_total_count
    (fold_left (numeric_scale_stats_transition scale) values state) =
  numeric_scale_stats_total_count state + Z.of_nat (List.length values).
```

## `integral_average_runtime_error_totality_certificate`

Source: [`theories/FormalSQL/NumericFacts.v:1020`](../NumericFacts.v#L1020)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 50), `scalar` (rank 38)

Search aliases: `numeric semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem integral_average_runtime_error_totality_certificate : forall values,
  avg_int32_numeric_runtime_error values = None /\
  avg_int64_numeric_runtime_error values = None.
```

## `numeric_aggregate_display_scale_runtime_error_totality_certificate`

Source: [`theories/FormalSQL/NumericFacts.v:1025`](../NumericFacts.v#L1025)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for numeric aggregate semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for numeric aggregate semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain every typmod/precision/scale and representability condition.

Cross-index: `runtime` (rank 50), `scalar` (rank 38)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem numeric_aggregate_display_scale_runtime_error_totality_certificate :
  forall aggregate values,
  numeric_aggregate_display_scale_runtime_error aggregate values = None.
```

## `integer_statistic_runtime_error_totality_certificate`

Source: [`theories/FormalSQL/NumericFacts.v:1030`](../NumericFacts.v#L1030)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 50), `scalar` (rank 38)

Search aliases: `numeric semantics`, `INTEGER`, `int32`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem integer_statistic_runtime_error_totality_certificate : forall values,
  integer_statistic_runtime_error values = None.
```

## `numeric_compare_refl`

Source: [`theories/FormalSQL/NumericFacts.v:1039`](../NumericFacts.v#L1039)

Purpose/direction: Establishes reflexivity for typed numeric semantics.

Applicability: Use to orient, transport, or compose a semantic relation about typed numeric semantics.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `equivalence`, `congruence`

```rocq
Lemma numeric_compare_refl :
  forall value,
    numeric_compare value value = Eq.
```

## `numeric_eqb_refl`

Source: [`theories/FormalSQL/NumericFacts.v:1047`](../NumericFacts.v#L1047)

Purpose/direction: Establishes reflexivity for typed numeric semantics.

Applicability: Use to orient, transport, or compose a semantic relation about typed numeric semantics.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `equivalence`, `congruence`

```rocq
Lemma numeric_eqb_refl :
  forall value,
    numeric_eqb value value = true.
```

## `numeric_cast_typmod_result`

Source: [`theories/FormalSQL/NumericFacts.v:1057`](../NumericFacts.v#L1057)

Purpose/direction: States the numeric cast typmod result law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_cast_typmod_result` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_cast_typmod_result :
  forall value precision scale result,
    numeric_cast_typmod value precision scale = Some result ->
    result = numeric_round_to_scale value scale.
```

## `numeric_avg_fixed_attested_finite_exact`

Source: [`theories/FormalSQL/NumericFacts.v:1072`](../NumericFacts.v#L1072)

Purpose/direction: States the numeric avg fixed attested finite exact law for numeric aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_fixed_attested_finite_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:1089`](../NumericFacts.v#L1089)

Purpose/direction: States the numeric avg attested scale finite exact law for numeric aggregate semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_avg_attested_scale_finite_exact` direction for numeric aggregate semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `aggregate`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma numeric_avg_attested_scale_finite_exact :
  forall scale q,
    numeric_round_to_scale (NumericFinite q) scale = NumericFinite q ->
    numeric_of_scaled (numeric_finite_rounded_coeff q scale) scale =
      NumericFinite q.
```

## `finite_numeric_div_by_zero`

Source: [`theories/FormalSQL/NumericFacts.v:1100`](../NumericFacts.v#L1100)

Purpose/direction: States the finite numeric div by zero law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `finite_numeric_div_by_zero` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma finite_numeric_div_by_zero :
  forall value,
    numeric_div_at_scales (NumericFinite value) 0 numeric_zero 0 = None.
```

## `numeric_to_int32_checked_result_in_range`

Source: [`theories/FormalSQL/NumericFacts.v:1110`](../NumericFacts.v#L1110)

Purpose/direction: Connects the displayed range/representability premise to typed numeric semantics.

Applicability: Use when the goal or a hypothesis matches the `numeric_to_int32_checked_result_in_range` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma numeric_to_int32_checked_result_in_range :
  forall value result,
    numeric_to_int32_checked value = Some result ->
    int32_min <= int32_value result <= int32_max.
```

## `finite_decimal_numeric_division_total`

Source: [`theories/FormalSQL/NumericFacts.v:1124`](../NumericFacts.v#L1124)

Purpose/direction: Establishes totality of the indicated typed numeric semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `finite_decimal_numeric_division_total` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/NumericFacts.v:1147`](../NumericFacts.v#L1147)

Purpose/direction: States the numeric positive is nonzero law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_positive_is_nonzero` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`

```rocq
Lemma numeric_positive_is_nonzero :
  forall value,
    numeric_compare numeric_zero value = Lt ->
    numeric_eqb value numeric_zero = false.
```

## `finite_numeric_division_runtime_error_none`

Source: [`theories/FormalSQL/NumericFacts.v:1168`](../NumericFacts.v#L1168)

Purpose/direction: Establishes the explicit runtime-safety direction for typed numeric semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for typed numeric semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 40), `scalar` (rank 40)

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

Source: [`theories/FormalSQL/NumericFacts.v:1190`](../NumericFacts.v#L1190)

Purpose/direction: States the numeric positive from integer lower bound law for typed numeric semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `numeric_positive_from_integer_lower_bound` direction for typed numeric semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

Search aliases: `numeric semantics`, `NUMERIC`, `DECIMAL`, `INTEGER`, `int32`

```rocq
Lemma numeric_positive_from_integer_lower_bound :
  forall lower value,
    1 <= lower ->
    (numeric_compare (numeric_of_Z lower) value = Lt \/
     numeric_compare (numeric_of_Z lower) value = Eq) ->
    numeric_compare numeric_zero value = Lt.
```
