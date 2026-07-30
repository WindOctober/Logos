# Ordered observations and slicing

Route here for: exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT.

This focused catalog contains 94 declarations routed at declaration granularity from `OrderedObservationTransportFacts.v`, `OrderedQueryFacts.v`, `SqlQueryContexts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `tuple_list_semantic_rel_app`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:65`](../OrderedObservationTransportFacts.v#L65)

Purpose/direction: States the tuple list semantic rel app law for ordered query equivalence, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tuple_list_semantic_rel_app` direction for ordered query equivalence; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`

Search aliases: `ordered query semantics`

```rocq
Lemma tuple_list_semantic_rel_app :
  forall (T : Tuple.Rcd) left left' right right',
    tuple_list_semantic_rel T left left' ->
    tuple_list_semantic_rel T right right' ->
    tuple_list_semantic_rel T (left ++ right) (left' ++ right').
```

## `prefix_scan_observation_app`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:99`](../OrderedObservationTransportFacts.v#L99)

Purpose/direction: States the prefix scan observation app law for window/rank evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `prefix_scan_observation_app` direction for window/rank evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`

```rocq
Lemma prefix_scan_observation_app :
  forall (T : Tuple.Rcd) (A : Type)
      (observe : A -> list A -> option (tuple T)) prefix left right,
    prefix_scan_observation observe prefix (left ++ right) =
    prefix_scan_observation observe prefix left ++
      prefix_scan_observation observe (prefix ++ left) right.
```

## `prefix_scan_observation_tail_transport`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:137`](../OrderedObservationTransportFacts.v#L137)

Purpose/direction: Transports the displayed hypotheses and conclusion for window/rank evaluation.

Applicability: Use when the goal or a hypothesis matches the `prefix_scan_observation_tail_transport` direction for window/rank evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`

```rocq
Theorem prefix_scan_observation_tail_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (observe : A -> list A -> option (tuple T))
      left_prefix right_prefix rows,
    prefix_scan_tail_semantic_rel observe
      left_prefix right_prefix rows ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe left_prefix rows)
      (prefix_scan_observation observe right_prefix rows).
```

## `prefix_scan_observation_adjacent_peer`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:183`](../OrderedObservationTransportFacts.v#L183)

Purpose/direction: States the prefix scan observation adjacent peer law for window/rank evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `prefix_scan_observation_adjacent_peer` direction for window/rank evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`

```rocq
Theorem prefix_scan_observation_adjacent_peer :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      prefix first second tail,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer first second ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe prefix (first :: second :: tail))
      (prefix_scan_observation observe prefix (second :: first :: tail)).
```

## `prefix_scan_observation_adjacent_peer_transport`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:223`](../OrderedObservationTransportFacts.v#L223)

Purpose/direction: Transports the displayed hypotheses and conclusion for window/rank evaluation.

Applicability: Use when the goal or a hypothesis matches the `prefix_scan_observation_adjacent_peer_transport` direction for window/rank evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`

```rocq
Theorem prefix_scan_observation_adjacent_peer_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      prefix before first second after,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer first second ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe prefix
        (before ++ first :: second :: after))
      (prefix_scan_observation observe prefix
        (before ++ second :: first :: after)).
```

## `prefix_scan_observation_peer_transport`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:247`](../OrderedObservationTransportFacts.v#L247)

Purpose/direction: Transports the post-filter semantic row observation of a cumulative prefix scan across every caller-certified adjacent peer permutation.

Applicability: Use only after proving the adjacent-peer contract for every allowed swap: the two affected post-filter observations and every later observed prefix must agree semantically.  The outcome form additionally requires exact error-category equivalence and does not equate hidden window rows.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `window prefix`, `peer permutation`, `filter observation`, `ties`

```rocq
Theorem prefix_scan_observation_peer_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      prefix left right,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer_order_permutation peer left right ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe prefix left)
      (prefix_scan_observation observe prefix right).
```

## `partitioned_prefix_scan_observation_peer_transport`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:285`](../OrderedObservationTransportFacts.v#L285)

Purpose/direction: Applies tie-aware prefix-observation transport independently to aligned partition blocks, resetting the cumulative prefix at each boundary.

Applicability: Use only after proving the adjacent-peer contract for every allowed swap: the two affected post-filter observations and every later observed prefix must agree semantically.  The outcome form additionally requires exact error-category equivalence and does not equate hidden window rows.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `partitioned window`, `peer permutation`, `prefix reset`, `filter observation`

```rocq
Theorem partitioned_prefix_scan_observation_peer_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      left_blocks right_blocks,
    prefix_scan_adjacent_peer_contract peer observe ->
    Forall2 (peer_order_permutation peer) left_blocks right_blocks ->
    tuple_list_semantic_rel T
      (partitioned_prefix_scan_observation observe left_blocks)
      (partitioned_prefix_scan_observation observe right_blocks).
```

## `prefix_scan_outcome_peer_transport_iff`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:322`](../OrderedObservationTransportFacts.v#L322)

Purpose/direction: Lifts peer-order prefix-observation transport to exact success/error outcomes only after the two evaluation schedules' error categories are equated explicitly.

Applicability: Use only after proving the adjacent-peer contract for every allowed swap: the two affected post-filter observations and every later observed prefix must agree semantically.  The outcome form additionally requires exact error-category equivalence and does not equate hidden window rows.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `window prefix`, `peer permutation`, `runtime error`, `exact outcome`

```rocq
Theorem prefix_scan_outcome_peer_transport_iff :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      (left_errors right_errors : sql_runtime_error -> Prop)
      left right,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer_order_permutation peer left right ->
    (forall error, left_errors error <-> right_errors error) ->
    forall outcome,
      prefix_scan_outcome_observation observe left_errors left outcome <->
      prefix_scan_outcome_observation observe right_errors right outcome.
```

## `partitioned_prefix_scan_outcome_peer_transport_iff`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:360`](../OrderedObservationTransportFacts.v#L360)

Purpose/direction: Lifts aligned partition-block peer transport to exact outcome observations under an explicit equality of the two schedules' runtime-error categories.

Applicability: Use only after proving the adjacent-peer contract for every allowed swap: the two affected post-filter observations and every later observed prefix must agree semantically.  The outcome form additionally requires exact error-category equivalence and does not equate hidden window rows.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `partitioned window`, `peer permutation`, `runtime error`, `exact outcome`

```rocq
Theorem partitioned_prefix_scan_outcome_peer_transport_iff :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      (left_errors right_errors : sql_runtime_error -> Prop)
      left_blocks right_blocks,
    prefix_scan_adjacent_peer_contract peer observe ->
    Forall2 (peer_order_permutation peer) left_blocks right_blocks ->
    (forall error, left_errors error <-> right_errors error) ->
    forall outcome,
      partitioned_prefix_scan_outcome_observation
        observe left_errors left_blocks outcome <->
      partitioned_prefix_scan_outcome_observation
        observe right_errors right_blocks outcome.
```

## `ordered_rows_total_map`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:412`](../OrderedObservationTransportFacts.v#L412)

Purpose/direction: Establishes totality of the indicated ordered query equivalence operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `ordered_rows_total_map` direction for ordered query equivalence; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`

Search aliases: `ordered query semantics`

```rocq
Theorem ordered_rows_total_map :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (rows : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    ordered_rows value_is_null left_keys rows ->
    ordered_rows value_is_null right_keys (map mapping rows).
```

## `ordered_rows_total_map_reflect`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:436`](../OrderedObservationTransportFacts.v#L436)

Purpose/direction: Establishes totality of the indicated ordered query equivalence operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `ordered_rows_total_map_reflect` direction for ordered query equivalence; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`

Search aliases: `ordered query semantics`

```rocq
Lemma ordered_rows_total_map_reflect :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (input output : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    tuple_list_semantic_rel T output (map mapping input) ->
    ordered_rows value_is_null right_keys output ->
    ordered_rows value_is_null left_keys input.
```

## `order_by_rows_total_map`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:471`](../OrderedObservationTransportFacts.v#L471)

Purpose/direction: Establishes totality of the indicated ordered query observation operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `order_by_rows_total_map` direction for ordered query observation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Theorem order_by_rows_total_map :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (input ordered : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    order_by_rows value_is_null left_keys input ordered ->
    order_by_rows value_is_null right_keys
      (map mapping input) (map mapping ordered).
```

## `order_by_rows_total_map_preimage`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:509`](../OrderedObservationTransportFacts.v#L509)

Purpose/direction: Pulls every legal ordered representative of a total mapped bag back to a source ordering, preserving occurrences even when the map is non-injective.

Applicability: Use only with a semantic row map that preserves and reflects the complete ORDER BY comparison, including NULL placement and ties.  The result ranges over every legal representative; the outcome form still requires exact child/join/projection/order error equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `total functional map`, `legal ties`, `multiplicity`

```rocq
Theorem order_by_rows_total_map_preimage :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (input output : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    order_by_rows value_is_null right_keys (map mapping input) output ->
    exists ordered,
      order_by_rows value_is_null left_keys input ordered /\
      ordered_rows_equiv T output (map mapping ordered).
```

## `map_firstn_exact`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:544`](../OrderedObservationTransportFacts.v#L544)

Purpose/direction: States the map firstn exact law for ordered slicing, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `map_firstn_exact` direction for ordered slicing; do not reverse or strengthen the displayed conclusion.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma map_firstn_exact :
  forall (A B : Type) (mapping : A -> B) count rows,
    map mapping (firstn count rows) = firstn count (map mapping rows).
```

## `total_map_order_fetch_observation_iff`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:577`](../OrderedObservationTransportFacts.v#L577)

Purpose/direction: Equates all legal ORDER BY/FETCH observations before and after a total semantic row map whose order-key comparison is preserved and reflected.

Applicability: Use only with a semantic row map that preserves and reflects the complete ORDER BY comparison, including NULL placement and ties.  The result ranges over every legal representative; the outcome form still requires exact child/join/projection/order error equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `ORDER BY`, `total functional map`, `all legal observations`

```rocq
Theorem total_map_order_fetch_observation_iff :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (count : nat) (input output : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    map_after_order_fetch_observation
      value_is_null mapping left_keys count input output <->
    order_fetch_after_map_observation
      value_is_null mapping right_keys count input output.
```

## `total_map_order_fetch_outcome_observation_iff`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:640`](../OrderedObservationTransportFacts.v#L640)

Purpose/direction: Adds an explicit exact error relation to total-map ORDER BY/FETCH observation transport; it does not infer error safety from the successful mapping law.

Applicability: Use only with a semantic row map that preserves and reflects the complete ORDER BY comparison, including NULL placement and ties.  The result ranges over every legal representative; the outcome form still requires exact child/join/projection/order error equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `ORDER BY`, `runtime error`, `all legal observations`

```rocq
Theorem total_map_order_fetch_outcome_observation_iff :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (count : nat) (input : list (tuple T))
      (left_errors right_errors : sql_runtime_error -> Prop),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    (forall error, left_errors error <-> right_errors error) ->
    forall outcome,
      map_after_order_fetch_outcome_observation
        value_is_null mapping left_keys count input left_errors outcome <->
      order_fetch_after_map_outcome_observation
        value_is_null mapping right_keys count input right_errors outcome.
```

## `ordered_rows_equiv_skipn`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:22`](../OrderedQueryFacts.v#L22)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_skipn :
  forall (T : Tuple.Rcd) count (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (skipn count left) (skipn count right).
```

## `ordered_rows_equiv_firstn`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:40`](../OrderedQueryFacts.v#L40)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_firstn :
  forall (T : Tuple.Rcd) count (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (firstn count left) (firstn count right).
```

## `query_expr_values_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:171`](../OrderedQueryFacts.v#L171)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query equivalence.

Applicability: Use when the goal or a hypothesis matches the `query_expr_values_has_success` direction for ordered query equivalence; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `ordered`

Search aliases: `ordered query semantics`

```rocq
Lemma query_expr_values_has_success :
  forall env outputs values,
    query_has_success env (QExpr_Values outputs values).
```

## `query_rank_success_bags_congr_extensional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:524`](../OrderedQueryFacts.v#L524)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_rank_success_bags_congr_extensional :
  forall env left_partition left_order left_attribute left_value
      right_partition right_order right_attribute right_value left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    unary_bag_relation_equiv
      (@query_rank_bag_relation T value_is_null
        left_partition left_order left_attribute left_value)
      (@query_rank_bag_relation T value_is_null
        right_partition right_order right_attribute right_value) ->
    rel_equiv
      (success_bags env
        (QExpr_Rank left_partition left_order left_attribute left_value left))
      (success_bags env
        (QExpr_Rank
          right_partition right_order right_attribute right_value right)).
```

## `query_window_success_bags_congr_extensional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:550`](../OrderedQueryFacts.v#L550)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_window_success_bags_congr_extensional :
  forall env left_partition left_order left_items
      right_partition right_order right_items left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    unary_bag_relation_equiv
      (@query_window_bag_relation T symbol_runtime_error
        aggregate_runtime_error value_is_null env
        left_partition left_order left_items)
      (@query_window_bag_relation T symbol_runtime_error
        aggregate_runtime_error value_is_null env
        right_partition right_order right_items) ->
    rel_equiv
      (success_bags env
        (QExpr_Window left_partition left_order left_items left))
      (success_bags env
        (QExpr_Window right_partition right_order right_items right)).
```

## `query_expr_set_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:709`](../OrderedQueryFacts.v#L709)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL bag/set operations.

Applicability: Use when the goal or a hypothesis matches the `query_expr_set_has_success` direction for SQL bag/set operations; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `set operation`

```rocq
Lemma query_expr_set_has_success :
  forall env operation left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_Set operation left right).
```

## `ordered_rows_equiv_filter`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1978`](../OrderedQueryFacts.v#L1978)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `filter`, `ordered`

Search aliases: `ordered query semantics`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_filter :
  forall (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    forall left right,
      ordered_rows_equiv T left right ->
      ordered_rows_equiv T
        (List.filter keep left) (List.filter keep right).
```

## `eval_query_expr_distinct_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2092`](../OrderedQueryFacts.v#L2092)

Purpose/direction: Gives necessary and sufficient conditions for ordered query equivalence.

Applicability: Use in either direction to invert or construct a goal about ordered query equivalence.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_distinct_error_iff :
  forall env input error,
    eval_query env (QExpr_Distinct input) (SqlError error) <->
    eval_query env input (SqlError error).
```

## `query_expr_distinct_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2105`](../OrderedQueryFacts.v#L2105)

Purpose/direction: Establishes the explicit runtime-safety direction for ordered query equivalence.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_distinct_runtime_safe :
  forall env input,
    query_safe env input ->
    query_safe env (QExpr_Distinct input).
```

## `query_expr_distinct_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2116`](../OrderedQueryFacts.v#L2116)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query equivalence.

Applicability: Use when the goal or a hypothesis matches the `query_expr_distinct_has_success` direction for ordered query equivalence; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`

```rocq
Lemma query_expr_distinct_has_success :
  forall env input,
    query_has_success env input ->
    query_has_success env (QExpr_Distinct input).
```

## `query_expr_distinct_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2130`](../OrderedQueryFacts.v#L2130)

Purpose/direction: States the query expr distinct has outcome law for ordered query equivalence, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_distinct_has_outcome :
  forall env input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Distinct input) outcome.
```

## `query_expr_distinct_global_typed_inert_reset`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2148`](../OrderedQueryFacts.v#L2148)

Purpose/direction: States the query expr distinct global typed inert reset law for ordered query equivalence, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; keep schema/integrity conformance premises explicit.

Cross-index: `bag`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `schema conformance`, `typing`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_distinct_global_typed_inert_reset :
  forall input,
    query_expr_order_behavior input = BagReset ->
    (forall env bag,
      query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null
        env input bag ->
      bag_eq T (query_distinct_bag bag) bag) ->
    query_global_typed_outcome_equiv (QExpr_Distinct input) input.
```

## `eval_query_expr_rank_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2184`](../OrderedQueryFacts.v#L2184)

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_rank_error_iff :
  forall env partition_keys order_keys rank_attribute rank_value input error,
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlError error) <->
    eval_query env input (SqlError error) \/
    (error = DataException NumericValueOutOfRange /\
     exists input_rows,
       eval_query env input (SqlSuccess input_rows) /\
       @query_rank_rows_outcome T value_is_null
         partition_keys order_keys rank_attribute rank_value
         (query_rank_bag_rows (query_rows_bag input_rows))
         (query_rank_bag_rows (query_rows_bag input_rows)) = None).
```

## `eval_query_expr_window_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2209`](../OrderedQueryFacts.v#L2209)

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_window_error_iff :
  forall env partition_keys order_keys items input error,
    eval_query env
      (QExpr_Window partition_keys order_keys items input)
      (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows ordered_input,
      eval_query env input (SqlSuccess input_rows) /\
      order_by_rows value_is_null (partition_keys ++ order_keys)
        (query_rank_bag_rows (query_rows_bag input_rows)) ordered_input /\
      @query_window_rows_outcome T symbol_runtime_error
        aggregate_runtime_error value_is_null env partition_keys items
        None 0 nil ordered_input = Some (SqlError error).
```

## `query_expr_order_by_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2238`](../OrderedQueryFacts.v#L2238)

Purpose/direction: Establishes the explicit runtime-safety direction for ordered query observation.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_order_by_runtime_safe :
  forall env keys input,
    query_safe env input ->
    query_safe env (QExpr_OrderBy keys input).
```

## `query_expr_order_by_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2251`](../OrderedQueryFacts.v#L2251)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when the goal or a hypothesis matches the `query_expr_order_by_has_success` direction for ordered query observation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma query_expr_order_by_has_success :
  forall env keys input,
    query_has_success env input ->
    query_has_success env (QExpr_OrderBy keys input).
```

## `query_expr_order_by_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2260`](../OrderedQueryFacts.v#L2260)

Purpose/direction: States the query expr order by has outcome law for ordered query observation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_order_by_has_outcome :
  forall env keys input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_OrderBy keys input) outcome.
```

## `query_expr_offset_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2273`](../OrderedQueryFacts.v#L2273)

Purpose/direction: Establishes the explicit runtime-safety direction for ordered slicing.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_offset_runtime_safe :
  forall env count input,
    query_safe env input ->
    query_safe env (QExpr_Offset count input).
```

## `query_expr_offset_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2286`](../OrderedQueryFacts.v#L2286)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered slicing.

Applicability: Use when the goal or a hypothesis matches the `query_expr_offset_has_success` direction for ordered slicing; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`

```rocq
Lemma query_expr_offset_has_success :
  forall env count input,
    query_has_success env input ->
    query_has_success env (QExpr_Offset count input).
```

## `query_expr_offset_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2296`](../OrderedQueryFacts.v#L2296)

Purpose/direction: States the query expr offset has outcome law for ordered slicing, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_offset_has_outcome :
  forall env count input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Offset count input) outcome.
```

## `query_expr_fetch_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2309`](../OrderedQueryFacts.v#L2309)

Purpose/direction: Establishes the explicit runtime-safety direction for ordered slicing.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_fetch_runtime_safe :
  forall env count input,
    query_safe env input ->
    query_safe env (QExpr_Fetch count input).
```

## `query_expr_fetch_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2322`](../OrderedQueryFacts.v#L2322)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered slicing.

Applicability: Use when the goal or a hypothesis matches the `query_expr_fetch_has_success` direction for ordered slicing; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma query_expr_fetch_has_success :
  forall env count input,
    query_has_success env input ->
    query_has_success env (QExpr_Fetch count input).
```

## `query_expr_fetch_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2332`](../OrderedQueryFacts.v#L2332)

Purpose/direction: States the query expr fetch has outcome law for ordered slicing, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_fetch_has_outcome :
  forall env count input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Fetch count input) outcome.
```

## `eval_query_expr_offset_zero_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2348`](../OrderedQueryFacts.v#L2348)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`

```rocq
Lemma eval_query_expr_offset_zero_iff :
  forall env input outcome,
    eval_query env (QExpr_Offset 0 input) outcome <->
    eval_query env input outcome.
```

## `eval_query_expr_fetch_zero_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2363`](../OrderedQueryFacts.v#L2363)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_zero_success_iff :
  forall env input output,
    eval_query env (QExpr_Fetch 0 input) (SqlSuccess output) <->
    output = nil /\ query_has_success env input.
```

## `query_expr_fetch_zero_annihilator_outcome_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2380`](../OrderedQueryFacts.v#L2380)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_fetch_zero_annihilator_outcome_equiv_safe :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_safe env left ->
    query_safe env right ->
    query_has_success env left ->
    query_has_success env right ->
    query_outcome_equiv env
      (QExpr_Fetch 0 left) (QExpr_Fetch 0 right).
```

## `eval_query_expr_offset_offset_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2416`](../OrderedQueryFacts.v#L2416)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`

```rocq
Lemma eval_query_expr_offset_offset_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Offset outer (QExpr_Offset inner input)) outcome <->
    eval_query env (QExpr_Offset (outer + inner) input) outcome.
```

## `eval_query_expr_fetch_fetch_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2446`](../OrderedQueryFacts.v#L2446)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_fetch_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Fetch outer (QExpr_Fetch inner input)) outcome <->
    eval_query env (QExpr_Fetch (Nat.min outer inner) input) outcome.
```

## `eval_query_expr_offset_fetch_comm_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2476`](../OrderedQueryFacts.v#L2476)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_offset_fetch_comm_iff :
  forall env offset count input outcome,
    eval_query env
      (QExpr_Offset offset (QExpr_Fetch count input)) outcome <->
    eval_query env
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)) outcome.
```

## `eval_query_expr_fetch_offset_comm_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2514`](../OrderedQueryFacts.v#L2514)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_offset_comm_iff :
  forall env count offset input outcome,
    eval_query env
      (QExpr_Fetch count (QExpr_Offset offset input)) outcome <->
    eval_query env
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)) outcome.
```

## `eval_query_expr_offset_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2552`](../OrderedQueryFacts.v#L2552)

Purpose/direction: Relates ordered slicing to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `ordered query semantics`, `OFFSET`, `cardinality`

```rocq
Lemma eval_query_expr_offset_success_length :
  forall env offset input output,
    eval_query env (QExpr_Offset offset input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows - offset.
```

## `eval_query_expr_fetch_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2566`](../OrderedQueryFacts.v#L2566)

Purpose/direction: Relates ordered slicing to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `cardinality`

```rocq
Lemma eval_query_expr_fetch_success_length :
  forall env count input output,
    eval_query env (QExpr_Fetch count input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = Nat.min count (length input_rows).
```

## `eval_query_expr_order_by_success_occurrences`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2797`](../OrderedQueryFacts.v#L2797)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`

```rocq
Lemma eval_query_expr_order_by_success_occurrences :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      forall row,
        Oeset.nb_occ (OTuple T) row output =
        Oeset.nb_occ (OTuple T) row input_rows.
```

## `eval_query_expr_order_by_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2820`](../OrderedQueryFacts.v#L2820)

Purpose/direction: Relates ordered query observation to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`, `cardinality`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `cardinality`

```rocq
Lemma eval_query_expr_order_by_success_length :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows.
```

## `eval_query_expr_order_by_success_ordered`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2841`](../OrderedQueryFacts.v#L2841)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when the goal or a hypothesis matches the `eval_query_expr_order_by_success_ordered` direction for ordered query observation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_expr_order_by_success_ordered :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    ordered_rows value_is_null keys output.
```

## `query_order_by_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2856`](../OrderedQueryFacts.v#L2856)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_order_by_success_bags :
  forall env keys input,
    rel_equiv
      (success_bags env (QExpr_OrderBy keys input))
      (success_bags env input).
```

## `query_order_by_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2884`](../OrderedQueryFacts.v#L2884)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_order_by_success_bags_functional :
  forall env keys input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_OrderBy keys input) first ->
      success_bags env (QExpr_OrderBy keys input) second ->
      bag_eq T first second.
```

## `query_order_by_success_bags_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2904`](../OrderedQueryFacts.v#L2904)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_order_by_success_bags_congr :
  forall env left_keys right_keys left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_OrderBy left_keys left))
      (success_bags env (QExpr_OrderBy right_keys right)).
```

## `query_offset_success_bags_congr_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2983`](../OrderedQueryFacts.v#L2983)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_offset_success_bags_congr_closed :
  forall env count left right,
    BagClosed T (fun rows => eval_query env left (SqlSuccess rows)) ->
    BagClosed T (fun rows => eval_query env right (SqlSuccess rows)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_Offset count left))
      (success_bags env (QExpr_Offset count right)).
```

## `query_fetch_success_bags_congr_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3003`](../OrderedQueryFacts.v#L3003)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_fetch_success_bags_congr_closed :
  forall env count left right,
    BagClosed T (fun rows => eval_query env left (SqlSuccess rows)) ->
    BagClosed T (fun rows => eval_query env right (SqlSuccess rows)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_Fetch count left))
      (success_bags env (QExpr_Fetch count right)).
```

## `query_same_rows_as_bag_length_le_one_ordered_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3026`](../OrderedQueryFacts.v#L3026)

Purpose/direction: Provides the stated reusable upper bound for ordered query equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`, `ordered`, `cardinality`

Search aliases: `ordered query semantics`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_same_rows_as_bag_length_le_one_ordered_equiv :
  forall left right,
    @query_same_rows_as_bag T left (query_rows_bag right) ->
    (length right <= 1)%nat ->
    ordered_rows_equiv T left right.
```

## `query_expr_order_by_outcome_equiv_of_success_length_le_one`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3062`](../OrderedQueryFacts.v#L3062)

Purpose/direction: Provides the stated reusable upper bound for ordered query observation.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `cardinality`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `cardinality`, `equivalence`, `congruence`

```rocq
Theorem query_expr_order_by_outcome_equiv_of_success_length_le_one :
  forall env keys input,
    (exists outcome, eval_query env input outcome) ->
    (forall rows,
      eval_query env input (SqlSuccess rows) ->
      (length rows <= 1)%nat) ->
    query_outcome_equiv env (QExpr_OrderBy keys input) input.
```

## `eval_query_expr_order_by_order_by_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3108`](../OrderedQueryFacts.v#L3108)

Purpose/direction: Gives necessary and sufficient conditions for ordered query observation.

Applicability: Use in either direction to invert or construct a goal about ordered query observation.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_expr_order_by_order_by_iff :
  forall env outer_keys inner_keys input outcome,
    eval_query env
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input)) outcome <->
    eval_query env (QExpr_OrderBy outer_keys input) outcome.
```

## `query_expr_offset_zero_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3156`](../OrderedQueryFacts.v#L3156)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered`, `schema`

Search aliases: `ordered query semantics`, `OFFSET`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_zero_global_typed_equiv :
  forall input,
    query_global_typed_outcome_equiv (QExpr_Offset 0 input) input.
```

## `query_expr_offset_offset_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3164`](../OrderedQueryFacts.v#L3164)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered`, `schema`

Search aliases: `ordered query semantics`, `OFFSET`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_offset_global_typed_equiv :
  forall outer inner input,
    query_global_typed_outcome_equiv
      (QExpr_Offset outer (QExpr_Offset inner input))
      (QExpr_Offset (outer + inner) input).
```

## `query_expr_fetch_fetch_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3174`](../OrderedQueryFacts.v#L3174)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered`, `schema`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_fetch_global_typed_equiv :
  forall outer inner input,
    query_global_typed_outcome_equiv
      (QExpr_Fetch outer (QExpr_Fetch inner input))
      (QExpr_Fetch (Nat.min outer inner) input).
```

## `query_expr_offset_fetch_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3184`](../OrderedQueryFacts.v#L3184)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered`, `schema`

Search aliases: `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_fetch_global_typed_equiv :
  forall offset count input,
    query_global_typed_outcome_equiv
      (QExpr_Offset offset (QExpr_Fetch count input))
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)).
```

## `query_expr_fetch_offset_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3194`](../OrderedQueryFacts.v#L3194)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered`, `schema`

Search aliases: `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_offset_global_typed_equiv :
  forall count offset input,
    query_global_typed_outcome_equiv
      (QExpr_Fetch count (QExpr_Offset offset input))
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)).
```

## `query_expr_order_by_order_by_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3204`](../OrderedQueryFacts.v#L3204)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered`, `schema`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_order_by_global_typed_equiv :
  forall outer_keys inner_keys input,
    query_global_typed_outcome_equiv
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input))
      (QExpr_OrderBy outer_keys input).
```

## `query_expr_distinct_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3218`](../OrderedQueryFacts.v#L3218)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_distinct_outcome_equiv_congr :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_expr_order_by_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3278`](../OrderedQueryFacts.v#L3278)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_outcome_equiv_congr :
  forall env keys left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_offset_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3338`](../OrderedQueryFacts.v#L3338)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_outcome_equiv_congr :
  forall env offset left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
```

## `query_expr_fetch_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3381`](../OrderedQueryFacts.v#L3381)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_outcome_equiv_congr :
  forall env count left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `query_expr_rank_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3424`](../OrderedQueryFacts.v#L3424)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_rank_outcome_equiv_congr :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value right).
```

## `query_expr_window_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3553`](../OrderedQueryFacts.v#L3553)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_window_outcome_equiv_congr :
  forall env partition_keys order_keys items left right,
    query_outcome_equiv env left right ->
    (exists outcome,
      eval_query env
        (QExpr_Window partition_keys order_keys items left) outcome) ->
    (exists outcome,
      eval_query env
        (QExpr_Window partition_keys order_keys items right) outcome) ->
    query_outcome_equiv env
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
```

## `query_expr_order_by_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3660`](../OrderedQueryFacts.v#L3660)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_equiv_congr :
  forall env keys left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_rank_equiv_congr_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3684`](../OrderedQueryFacts.v#L3684)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_rank_equiv_congr_safe :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    query_equiv env left right ->
    query_safe env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left) ->
    query_safe env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value right) ->
    query_has_success env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left) ->
    query_equiv env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value right).
```

## `query_expr_window_equiv_congr_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3716`](../OrderedQueryFacts.v#L3716)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_window_equiv_congr_safe :
  forall env partition_keys order_keys items left right,
    query_equiv env left right ->
    query_safe env (QExpr_Window partition_keys order_keys items left) ->
    query_safe env (QExpr_Window partition_keys order_keys items right) ->
    query_has_success env
      (QExpr_Window partition_keys order_keys items left) ->
    query_equiv env
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
```

## `query_expr_offset_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3744`](../OrderedQueryFacts.v#L3744)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_equiv_congr :
  forall env offset left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
```

## `query_expr_fetch_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3785`](../OrderedQueryFacts.v#L3785)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_equiv_congr :
  forall env count left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `ordered_rows_equiv_of_Forall2`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3962`](../OrderedQueryFacts.v#L3962)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_of_Forall2 :
  forall left right,
    Forall2
      (fun left_row right_row =>
        Oeset.compare (OTuple T) left_row right_row = Eq)
      left right ->
    ordered_rows_equiv T left right.
```

## `ordered_rows_equiv_map_projection`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3979`](../OrderedQueryFacts.v#L3979)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `projection`, `ordered`

Search aliases: `ordered query semantics`, `projection`, `SELECT list`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_map_projection :
  forall env select_list left right,
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        left)
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        right).
```

## `ordered_rows_equiv_map_two_projections`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4021`](../OrderedQueryFacts.v#L4021)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_map_two_projections :
  forall env left_select right_select rows,
    (forall row,
      In row rows ->
      Oeset.compare (OTuple T)
        (projection T (env_t T env row) (@Select_List T left_select))
        (projection T (env_t T env row) (@Select_List T right_select)) = Eq) ->
    ordered_rows_equiv T
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T left_select))
        rows)
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T right_select))
        rows).
```

## `query_distinct_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5488`](../OrderedQueryFacts.v#L5488)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query equivalence.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_distinct_success_bags_functional :
  forall env input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Distinct input) first ->
      success_bags env (QExpr_Distinct input) second ->
      bag_eq T first second.
```

## `query_rank_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5522`](../OrderedQueryFacts.v#L5522)

Purpose/direction: Inverts or constructs the successful evaluation branch for window/rank evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_rank_success_bags_functional :
  forall env partition_keys order_keys rank_attribute rank_value input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env
        (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
        first ->
      success_bags env
        (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
        second ->
      bag_eq T first second.
```

## `position_rows_from_values`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5580`](../OrderedQueryFacts.v#L5580)

Purpose/direction: Characterizes zero-based positions and inclusive prefixes of an arbitrary occurrence list, preserving empty inputs and duplicate rows.

Applicability: Use as an intrinsic list/position or comparator-run fact.  Connect it to QExpr_Rank/QExpr_Window only after proving the authoritative legal ordering, aggregate/runtime-error, and BagClosed boundary premises.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `position`, `window prefix`, `duplicates`

```rocq
Theorem position_rows_from_values :
  forall (A : Type) position (rows : list A),
    map snd (position_rows_from position rows) = rows.
```

## `position_rows_from_filter_le_prefix`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5615`](../OrderedQueryFacts.v#L5615)

Purpose/direction: Characterizes zero-based positions and inclusive prefixes of an arbitrary occurrence list, preserving empty inputs and duplicate rows.

Applicability: Use as an intrinsic list/position or comparator-run fact.  Connect it to QExpr_Rank/QExpr_Window only after proving the authoritative legal ordering, aggregate/runtime-error, and BagClosed boundary premises.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `filter`, `ordered`

Search aliases: `ordered query semantics`, `filter`, `WHERE`, `window`, `PARTITION BY`, `position`, `prefix`, `ROWS frame`, `duplicates`

```rocq
Theorem position_rows_from_filter_le_prefix :
  forall (A : Type) start cutoff (rows : list A),
    map snd
      (filter (fun numbered => Nat.leb (fst numbered) cutoff)
        (position_rows_from start rows)) =
    firstn (S cutoff - start) rows.
```

## `partition_runs_by_compare_exact_well_formed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5710`](../OrderedQueryFacts.v#L5710)

Purpose/direction: Partitions an occurrence list into exact adjacent comparator-equal runs and proves both concatenation and boundary inequality without using Rocq equality on SQL rows.

Applicability: Use as an intrinsic list/position or comparator-run fact.  Connect it to QExpr_Rank/QExpr_Window only after proving the authoritative legal ordering, aggregate/runtime-error, and BagClosed boundary premises.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `partition`, `peer ties`, `semantic comparator`

```rocq
Theorem partition_runs_by_compare_exact_well_formed :
  forall (A : Type) (compare : A -> A -> comparison) rows,
    concat (partition_runs_by_compare compare rows) = rows /\
    compare_partition_blocks_well_formed compare
      (partition_runs_by_compare compare rows).
```

## `rows_key_aligned_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5780`](../OrderedQueryFacts.v#L5780)

Purpose/direction: Transports heterogeneous relational order-key alignment through the displayed positional or total deterministic list consumer.

Applicability: Use only with a semantic key relation.  Filter decisions must be key-determined and maps total/deterministic; this interface does not equate peer payload order, bags, volatile expressions, or SQL errors.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`, `cardinality`

Search aliases: `ordered query semantics`, `cardinality`, `ordered alignment`, `order key`, `position`

```rocq
Theorem rows_key_aligned_length :
  forall (A B LeftKey RightKey : Type)
      (key_rel : LeftKey -> RightKey -> Prop)
      (left_key : A -> LeftKey) (right_key : B -> RightKey) left right,
    rows_key_aligned key_rel left_key right_key left right ->
    length left = length right.
```

## `rows_key_aligned_firstn`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5792`](../OrderedQueryFacts.v#L5792)

Purpose/direction: Transports heterogeneous relational order-key alignment through the displayed positional or total deterministic list consumer.

Applicability: Use only with a semantic key relation.  Filter decisions must be key-determined and maps total/deterministic; this interface does not equate peer payload order, bags, volatile expressions, or SQL errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `ordered alignment`, `ties`

```rocq
Theorem rows_key_aligned_firstn :
  forall (A B LeftKey RightKey : Type) count
      (key_rel : LeftKey -> RightKey -> Prop)
      (left_key : A -> LeftKey) (right_key : B -> RightKey) left right,
    rows_key_aligned key_rel left_key right_key left right ->
    rows_key_aligned key_rel left_key right_key
      (firstn count left) (firstn count right).
```

## `rows_key_aligned_skipn`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5811`](../OrderedQueryFacts.v#L5811)

Purpose/direction: Transports heterogeneous relational order-key alignment through the displayed positional or total deterministic list consumer.

Applicability: Use only with a semantic key relation.  Filter decisions must be key-determined and maps total/deterministic; this interface does not equate peer payload order, bags, volatile expressions, or SQL errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `OFFSET`, `ordered alignment`, `ties`

```rocq
Theorem rows_key_aligned_skipn :
  forall (A B LeftKey RightKey : Type) count
      (key_rel : LeftKey -> RightKey -> Prop)
      (left_key : A -> LeftKey) (right_key : B -> RightKey) left right,
    rows_key_aligned key_rel left_key right_key left right ->
    rows_key_aligned key_rel left_key right_key
      (skipn count left) (skipn count right).
```

## `rows_key_aligned_total_map_transport`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5862`](../OrderedQueryFacts.v#L5862)

Purpose/direction: Transports heterogeneous relational order-key alignment through the displayed positional or total deterministic list consumer.

Applicability: Use only with a semantic key relation.  Filter decisions must be key-determined and maps total/deterministic; this interface does not equate peer payload order, bags, volatile expressions, or SQL errors.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `ordered`

Search aliases: `ordered query semantics`, `ordered alignment`, `total projection`, `order key`

```rocq
Theorem rows_key_aligned_total_map_transport :
  forall (A B C D LeftKey RightKey LeftOutputKey RightOutputKey : Type)
      (input_key_rel : LeftKey -> RightKey -> Prop)
      (output_key_rel : LeftOutputKey -> RightOutputKey -> Prop)
      (left_key : A -> LeftKey) (right_key : B -> RightKey)
      (left_output_key : C -> LeftOutputKey)
      (right_output_key : D -> RightOutputKey)
      (left_map : A -> C) (right_map : B -> D),
    (forall left_row right_row,
      input_key_rel (left_key left_row) (right_key right_row) ->
      output_key_rel
        (left_output_key (left_map left_row))
        (right_output_key (right_map right_row))) ->
    forall left right,
      rows_key_aligned input_key_rel left_key right_key left right ->
      rows_key_aligned output_key_rel left_output_key right_output_key
        (map left_map left) (map right_map right).
```

## `query_expr_rank_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1206`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1206)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_rank_global_typed_congr :
  forall partition_keys order_keys rank_attribute rank_value input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input').
```

## `query_expr_window_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1238`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1238)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_window_global_typed_congr :
  forall partition_keys order_keys items input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Window partition_keys order_keys items input)
      (QExpr_Window partition_keys order_keys items input').
```

## `query_expr_distinct_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1277`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1277)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_distinct_global_typed_congr :
  forall first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Distinct first) (QExpr_Distinct second).
```

## `query_expr_order_by_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1291`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1291)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_global_typed_congr :
  forall keys first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_OrderBy keys first) (QExpr_OrderBy keys second).
```

## `query_expr_offset_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1305`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1305)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_global_typed_congr :
  forall offset first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Offset offset first) (QExpr_Offset offset second).
```

## `query_expr_fetch_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1319`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1319)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_global_typed_congr :
  forall count first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Fetch count first) (QExpr_Fetch count second).
```
