# Ordered observations and slicing

Route here for: exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT.

This focused catalog contains 94 declarations routed at declaration granularity from `OrderedObservationTransportFacts.v`, `OrderedQueryFacts.v`, `SqlQueryContexts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `tuple_list_semantic_rel_app`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:65`](../OrderedObservationTransportFacts.v#L65)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `peer_order_permutation_implies_Permutation`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:226`](../OrderedObservationTransportFacts.v#L226)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Forgets peer-swap justification from a peer-order permutation to obtain an ordinary occurrence-preserving list permutation.

Applicability: Use when only multiplicity, length, or ordinary permutation facts are needed from a legal peer reorder; the converse is intentionally unavailable.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `bag`, `ordered`

Search aliases: `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma peer_order_permutation_implies_Permutation :
  forall (A : Type) (peer : A -> A -> Prop) left right,
    peer_order_permutation peer left right ->
    Permutation left right.
```

## `prefix_scan_observation_adjacent_peer_transport`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:239`](../OrderedObservationTransportFacts.v#L239)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:263`](../OrderedObservationTransportFacts.v#L263)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:301`](../OrderedObservationTransportFacts.v#L301)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:338`](../OrderedObservationTransportFacts.v#L338)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:376`](../OrderedObservationTransportFacts.v#L376)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:428`](../OrderedObservationTransportFacts.v#L428)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:452`](../OrderedObservationTransportFacts.v#L452)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:487`](../OrderedObservationTransportFacts.v#L487)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:525`](../OrderedObservationTransportFacts.v#L525)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:560`](../OrderedObservationTransportFacts.v#L560)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:593`](../OrderedObservationTransportFacts.v#L593)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:656`](../OrderedObservationTransportFacts.v#L656)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:169`](../OrderedQueryFacts.v#L169)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:508`](../OrderedQueryFacts.v#L508)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:534`](../OrderedQueryFacts.v#L534)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:693`](../OrderedQueryFacts.v#L693)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1855`](../OrderedQueryFacts.v#L1855)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1969`](../OrderedQueryFacts.v#L1969)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered query equivalence.

Applicability: Use in either direction to invert or construct a goal about ordered query equivalence.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_distinct_error_iff :
  forall env input error,
    eval_query env (QExpr_Distinct input) (SqlError error) <->
    eval_query env input (SqlError error).
```

## `query_expr_distinct_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1982`](../OrderedQueryFacts.v#L1982)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1993`](../OrderedQueryFacts.v#L1993)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2007`](../OrderedQueryFacts.v#L2007)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr distinct has outcome law for ordered query equivalence, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_distinct_has_outcome :
  forall env input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Distinct input) outcome.
```

## `eval_query_expr_rank_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2020`](../OrderedQueryFacts.v#L2020)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2045`](../OrderedQueryFacts.v#L2045)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2074`](../OrderedQueryFacts.v#L2074)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2087`](../OrderedQueryFacts.v#L2087)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2096`](../OrderedQueryFacts.v#L2096)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr order by has outcome law for ordered query observation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_order_by_has_outcome :
  forall env keys input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_OrderBy keys input) outcome.
```

## `query_expr_offset_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2109`](../OrderedQueryFacts.v#L2109)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2122`](../OrderedQueryFacts.v#L2122)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2132`](../OrderedQueryFacts.v#L2132)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr offset has outcome law for ordered slicing, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_offset_has_outcome :
  forall env count input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Offset count input) outcome.
```

## `query_expr_fetch_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2145`](../OrderedQueryFacts.v#L2145)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2158`](../OrderedQueryFacts.v#L2158)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2168`](../OrderedQueryFacts.v#L2168)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr fetch has outcome law for ordered slicing, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_fetch_has_outcome :
  forall env count input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Fetch count input) outcome.
```

## `eval_query_expr_offset_zero_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2184`](../OrderedQueryFacts.v#L2184)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`

```rocq
Lemma eval_query_expr_offset_zero_iff :
  forall env input outcome,
    eval_query env (QExpr_Offset 0 input) outcome <->
    eval_query env input outcome.
```

## `eval_query_expr_fetch_zero_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2199`](../OrderedQueryFacts.v#L2199)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_zero_success_iff :
  forall env input output,
    eval_query env (QExpr_Fetch 0 input) (SqlSuccess output) <->
    output = nil /\ query_has_success env input.
```

## `eval_query_expr_offset_offset_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2213`](../OrderedQueryFacts.v#L2213)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`

```rocq
Lemma eval_query_expr_offset_offset_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Offset outer (QExpr_Offset inner input)) outcome <->
    eval_query env (QExpr_Offset (outer + inner) input) outcome.
```

## `eval_query_expr_fetch_fetch_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2243`](../OrderedQueryFacts.v#L2243)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_fetch_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Fetch outer (QExpr_Fetch inner input)) outcome <->
    eval_query env (QExpr_Fetch (Nat.min outer inner) input) outcome.
```

## `eval_query_expr_offset_fetch_comm_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2273`](../OrderedQueryFacts.v#L2273)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_offset_fetch_comm_iff :
  forall env offset count input outcome,
    eval_query env
      (QExpr_Offset offset (QExpr_Fetch count input)) outcome <->
    eval_query env
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)) outcome.
```

## `eval_query_expr_fetch_offset_comm_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2311`](../OrderedQueryFacts.v#L2311)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_offset_comm_iff :
  forall env count offset input outcome,
    eval_query env
      (QExpr_Fetch count (QExpr_Offset offset input)) outcome <->
    eval_query env
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)) outcome.
```

## `eval_query_expr_offset_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2349`](../OrderedQueryFacts.v#L2349)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates ordered slicing to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `cardinality`

```rocq
Lemma eval_query_expr_offset_success_length :
  forall env offset input output,
    eval_query env (QExpr_Offset offset input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows - offset.
```

## `eval_query_expr_fetch_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2363`](../OrderedQueryFacts.v#L2363)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates ordered slicing to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`, `cardinality`

```rocq
Lemma eval_query_expr_fetch_success_length :
  forall env count input output,
    eval_query env (QExpr_Fetch count input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = Nat.min count (length input_rows).
```

## `eval_query_expr_order_by_success_occurrences`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2594`](../OrderedQueryFacts.v#L2594)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2617`](../OrderedQueryFacts.v#L2617)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates ordered query observation to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `cardinality`

```rocq
Lemma eval_query_expr_order_by_success_length :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows.
```

## `eval_query_expr_order_by_success_ordered`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2638`](../OrderedQueryFacts.v#L2638)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when the goal or a hypothesis matches the `eval_query_expr_order_by_success_ordered` direction for ordered query observation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_expr_order_by_success_ordered :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    ordered_rows value_is_null keys output.
```

## `query_order_by_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2653`](../OrderedQueryFacts.v#L2653)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_order_by_success_bags :
  forall env keys input,
    rel_equiv
      (success_bags env (QExpr_OrderBy keys input))
      (success_bags env input).
```

## `query_order_by_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2681`](../OrderedQueryFacts.v#L2681)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2701`](../OrderedQueryFacts.v#L2701)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_order_by_success_bags_congr :
  forall env left_keys right_keys left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_OrderBy left_keys left))
      (success_bags env (QExpr_OrderBy right_keys right)).
```

## `query_offset_success_bags_congr_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2780`](../OrderedQueryFacts.v#L2780)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2800`](../OrderedQueryFacts.v#L2800)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2823`](../OrderedQueryFacts.v#L2823)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `eval_query_expr_order_by_order_by_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2861`](../OrderedQueryFacts.v#L2861)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for ordered query observation.

Applicability: Use in either direction to invert or construct a goal about ordered query observation.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_expr_order_by_order_by_iff :
  forall env outer_keys inner_keys input outcome,
    eval_query env
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input)) outcome <->
    eval_query env (QExpr_OrderBy outer_keys input) outcome.
```

## `query_expr_distinct_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2909`](../OrderedQueryFacts.v#L2909)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_distinct_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_distinct_outcome_equiv_congr :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_expr_order_by_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2969`](../OrderedQueryFacts.v#L2969)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_order_by_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_outcome_equiv_congr :
  forall env keys left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_offset_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3029`](../OrderedQueryFacts.v#L3029)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_offset_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_outcome_equiv_congr :
  forall env offset left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
```

## `query_expr_fetch_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3072`](../OrderedQueryFacts.v#L3072)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_fetch_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_outcome_equiv_congr :
  forall env count left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `query_expr_rank_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3115`](../OrderedQueryFacts.v#L3115)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_rank_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3244`](../OrderedQueryFacts.v#L3244)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_window_possible_outcome_equiv_congr_uniform` for the public result.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

## `ordered_rows_equiv_of_Forall2`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3433`](../OrderedQueryFacts.v#L3433)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `query_distinct_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4070`](../OrderedQueryFacts.v#L4070)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4104`](../OrderedQueryFacts.v#L4104)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `eval_query_expr_distinct_possible_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4266`](../OrderedQueryFacts.v#L4266)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for ordered query equivalence.

Applicability: Use in either direction to invert or construct a goal about ordered query equivalence.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_distinct_possible_error_iff :
  forall env input error,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Distinct input) (SqlError error) <->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env input (SqlError error).
```

## `eval_query_expr_order_by_possible_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4284`](../OrderedQueryFacts.v#L4284)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for ordered query observation.

Applicability: Use in either direction to invert or construct a goal about ordered query observation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_order_by_possible_error_iff :
  forall env keys input error,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_OrderBy keys input) (SqlError error) <->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env input (SqlError error).
```

## `eval_query_expr_offset_possible_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4302`](../OrderedQueryFacts.v#L4302)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `OFFSET`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_offset_possible_error_iff :
  forall env count input error,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Offset count input) (SqlError error) <->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env input (SqlError error).
```

## `eval_query_expr_fetch_possible_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4320`](../OrderedQueryFacts.v#L4320)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `FETCH`, `LIMIT`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_fetch_possible_error_iff :
  forall env count input error,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Fetch count input) (SqlError error) <->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env input (SqlError error).
```

## `query_expr_distinct_possible_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4338`](../OrderedQueryFacts.v#L4338)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_distinct_possible_outcome_equiv_congr :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_expr_order_by_possible_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4414`](../OrderedQueryFacts.v#L4414)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_possible_outcome_equiv_congr :
  forall env keys left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_rank_possible_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4485`](../OrderedQueryFacts.v#L4485)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_rank_possible_outcome_equiv_congr :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value right).
```

## `query_expr_offset_possible_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4631`](../OrderedQueryFacts.v#L4631)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_possible_outcome_equiv_congr :
  forall env count left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset count left) (QExpr_Offset count right).
```

## `query_expr_fetch_possible_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4683`](../OrderedQueryFacts.v#L4683)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_possible_outcome_equiv_congr :
  forall env count left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `position_rows_from_values`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4753`](../OrderedQueryFacts.v#L4753)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4788`](../OrderedQueryFacts.v#L4788)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4883`](../OrderedQueryFacts.v#L4883)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4953`](../OrderedQueryFacts.v#L4953)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4965`](../OrderedQueryFacts.v#L4965)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4984`](../OrderedQueryFacts.v#L4984)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5035`](../OrderedQueryFacts.v#L5035)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1407`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1407)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_rank_global_typed_congr :
  forall partition_keys order_keys rank_attribute rank_value input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input').
```

## `query_expr_window_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1439`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1439)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_window_global_typed_congr :
  forall partition_keys order_keys items input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Window partition_keys order_keys items input)
      (QExpr_Window partition_keys order_keys items input').
```

## `query_expr_distinct_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1478`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1478)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_distinct_global_typed_congr :
  forall first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Distinct first) (QExpr_Distinct second).
```

## `query_expr_order_by_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1492`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1492)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_global_typed_congr :
  forall keys first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_OrderBy keys first) (QExpr_OrderBy keys second).
```

## `query_expr_offset_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1506`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1506)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_global_typed_congr :
  forall offset first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Offset offset first) (QExpr_Offset offset second).
```

## `query_expr_fetch_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1520`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1520)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `ordered`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_global_typed_congr :
  forall count first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Fetch count first) (QExpr_Fetch count second).
```

## `query_window_rows_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5438`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5438)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines the constructor-local successful-bag and runtime-error relation on one actual ordered child row list.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_window_rows_bag_outcomes
    (env : Env.env T)
    (partition_keys order_keys : list (SqlOrder.sort_key T))
    (items : list (query_window_item T))
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        @query_window_bag_relation T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          partition_keys order_keys items (rows_bag T rows) output_bag
    | SqlError error =>
        exists ordered_rows,
          @order_by_rows T value_is_null (partition_keys ++ order_keys)
            (query_rank_bag_rows (rows_bag T rows)) ordered_rows /\
          @query_window_rows_outcome T symbol_runtime_error
            aggregate_runtime_error value_is_null env partition_keys items
            None 0 nil ordered_rows = Some (SqlError error)
    end.
```

## `eval_unary_window_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5512`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5512)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_unary_window_error_iff :
  forall schedule env partition_keys order_keys items input error,
    eval_unary_sem_query schedule env
      (QExpr_Window partition_keys order_keys items input) (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows ordered_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @order_by_rows T value_is_null (partition_keys ++ order_keys)
        (query_rank_bag_rows (rows_bag T input_rows)) ordered_rows /\
      @query_window_rows_outcome T symbol_runtime_error
        aggregate_runtime_error value_is_null env partition_keys items
        None 0 nil ordered_rows = Some (SqlError error).
```

## `query_window_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5736`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5736)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled unary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about window/rank evaluation.

Important premises: No semantic premise is hidden: this is the exact fixed-schedule characterization of the displayed constructor-local relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_window_scheduled_bag_outcomes_characterization :
  forall schedule env partition_keys order_keys items input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Window partition_keys order_keys items input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_reset_query schedule env input)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          partition_keys order_keys items)).
```

## `query_window_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5994`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5994)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports one child bag/error relation under a matched schedule pair using the exact reachable-list local contract.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: Supply complete child bag/error equivalence under the matched schedule pair and the exact reachable-list `scheduled_local_rows_to_bag_contract`.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `fixed Boolean schedule`, `foundation`, `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_window_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_partition left_order left_items
      right_partition right_order right_items left right,
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
      (@query_window_rows_bag_outcomes T symbol_runtime_error
        aggregate_runtime_error value_is_null env
        left_partition left_order left_items)
      (@query_window_rows_bag_outcomes T symbol_runtime_error
        aggregate_runtime_error value_is_null env
        right_partition right_order right_items) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Window left_partition left_order left_items left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Window right_partition right_order right_items right)).
```

## `query_expr_window_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6434`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6434)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about window/rank evaluation.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `window`, `PARTITION BY`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_window_possible_bag_schedule_transport :
  forall env
      left_partition left_order left_items
      right_partition right_order right_items left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    map (@qwi_attribute T) left_items = map (@qwi_attribute T) right_items ->
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
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          left_partition left_order left_items)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          right_partition right_order right_items)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Window left_partition left_order left_items left)
      (QExpr_Window right_partition right_order right_items right).
```

## `query_expr_window_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6478`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6478)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `ordered query semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_window_possible_bag_outcome_equiv :
  forall env
      left_partition left_order left_items
      right_partition right_order right_items left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    map (@qwi_attribute T) left_items = map (@qwi_attribute T) right_items ->
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
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          left_partition left_order left_items)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          right_partition right_order right_items)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Window left_partition left_order left_items left)
      (QExpr_Window right_partition right_order right_items right).
```
