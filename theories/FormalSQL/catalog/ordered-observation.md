# Ordered observations and slicing

Route here for: exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT.

This focused catalog contains 38 declarations routed at declaration granularity from `OrderedQueryFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `ordered_rows_equiv_skipn`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:20`](../OrderedQueryFacts.v#L20)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 30)

Search aliases: `ordered query semantics`, `OFFSET`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_skipn :
  forall (T : Tuple.Rcd) count (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (skipn count left) (skipn count right).
```

## `ordered_rows_equiv_firstn`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:38`](../OrderedQueryFacts.v#L38)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 30)

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_firstn :
  forall (T : Tuple.Rcd) count (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (firstn count left) (firstn count right).
```

## `eval_query_expr_distinct_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:578`](../OrderedQueryFacts.v#L578)

Purpose/direction: Gives necessary and sufficient conditions for ordered query equivalence.

Applicability: Use in either direction to invert or construct a goal about ordered query equivalence.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 48), `ordered` (rank 36)

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_distinct_error_iff :
  forall env input error,
    eval_query env (QExpr_Distinct input) (SqlError error) <->
    eval_query env input (SqlError error).
```

## `eval_query_expr_rank_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:588`](../OrderedQueryFacts.v#L588)

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime` (rank 48), `ordered` (rank 36)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:613`](../OrderedQueryFacts.v#L613)

Purpose/direction: Gives necessary and sufficient conditions for window/rank evaluation.

Applicability: Use in either direction to invert or construct a goal about window/rank evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `runtime` (rank 48), `ordered` (rank 36)

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

## `eval_query_expr_offset_zero_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:641`](../OrderedQueryFacts.v#L641)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 26)

Search aliases: `ordered query semantics`, `OFFSET`

```rocq
Lemma eval_query_expr_offset_zero_iff :
  forall env input outcome,
    eval_query env (QExpr_Offset 0 input) outcome <->
    eval_query env input outcome.
```

## `eval_query_expr_fetch_zero_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:656`](../OrderedQueryFacts.v#L656)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 28)

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_zero_success_iff :
  forall env input output,
    eval_query env (QExpr_Fetch 0 input) (SqlSuccess output) <->
    output = nil /\ query_has_success env input.
```

## `eval_query_expr_offset_offset_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:670`](../OrderedQueryFacts.v#L670)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 26)

Search aliases: `ordered query semantics`, `OFFSET`

```rocq
Lemma eval_query_expr_offset_offset_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Offset outer (QExpr_Offset inner input)) outcome <->
    eval_query env (QExpr_Offset (outer + inner) input) outcome.
```

## `eval_query_expr_fetch_fetch_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:700`](../OrderedQueryFacts.v#L700)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 28)

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_expr_fetch_fetch_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Fetch outer (QExpr_Fetch inner input)) outcome <->
    eval_query env (QExpr_Fetch (Nat.min outer inner) input) outcome.
```

## `eval_query_expr_offset_fetch_comm_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:730`](../OrderedQueryFacts.v#L730)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 26)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:768`](../OrderedQueryFacts.v#L768)

Purpose/direction: Gives necessary and sufficient conditions for ordered slicing.

Applicability: Use in either direction to invert or construct a goal about ordered slicing.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 26)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:806`](../OrderedQueryFacts.v#L806)

Purpose/direction: Relates ordered slicing to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 26), `cardinality` (rank 44)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:820`](../OrderedQueryFacts.v#L820)

Purpose/direction: Relates ordered slicing to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 28), `cardinality` (rank 44)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:837`](../OrderedQueryFacts.v#L837)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it.

Cross-index: `bag` (rank 52), `ordered` (rank 24)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:860`](../OrderedQueryFacts.v#L860)

Purpose/direction: Relates ordered query observation to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 24), `cardinality` (rank 44)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:881`](../OrderedQueryFacts.v#L881)

Purpose/direction: Inverts or constructs the successful evaluation branch for ordered query observation.

Applicability: Use when the goal or a hypothesis matches the `eval_query_expr_order_by_success_ordered` direction for ordered query observation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 24)

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_expr_order_by_success_ordered :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    ordered_rows value_is_null keys output.
```

## `query_same_rows_as_bag_length_le_one_ordered_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:895`](../OrderedQueryFacts.v#L895)

Purpose/direction: Provides the stated reusable upper bound for ordered query equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 52), `ordered` (rank 36), `cardinality` (rank 40)

Search aliases: `ordered query semantics`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_same_rows_as_bag_length_le_one_ordered_equiv :
  forall left right,
    @query_same_rows_as_bag T left (query_rows_bag right) ->
    (length right <= 1)%nat ->
    ordered_rows_equiv T left right.
```

## `query_expr_order_by_outcome_equiv_of_success_length_le_one`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:931`](../OrderedQueryFacts.v#L931)

Purpose/direction: Provides the stated reusable upper bound for ordered query observation.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 38), `runtime` (rank 50), `ordered` (rank 20), `cardinality` (rank 38)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:977`](../OrderedQueryFacts.v#L977)

Purpose/direction: Gives necessary and sufficient conditions for ordered query observation.

Applicability: Use in either direction to invert or construct a goal about ordered query observation.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `ordered` (rank 24)

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_expr_order_by_order_by_iff :
  forall env outer_keys inner_keys input outcome,
    eval_query env
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input)) outcome <->
    eval_query env (QExpr_OrderBy outer_keys input) outcome.
```

## `query_expr_offset_zero_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1025`](../OrderedQueryFacts.v#L1025)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 26), `schema` (rank 52)

Search aliases: `ordered query semantics`, `OFFSET`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_zero_global_typed_equiv :
  forall input,
    query_global_typed_outcome_equiv (QExpr_Offset 0 input) input.
```

## `query_expr_offset_offset_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1033`](../OrderedQueryFacts.v#L1033)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 26), `schema` (rank 52)

Search aliases: `ordered query semantics`, `OFFSET`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_offset_global_typed_equiv :
  forall outer inner input,
    query_global_typed_outcome_equiv
      (QExpr_Offset outer (QExpr_Offset inner input))
      (QExpr_Offset (outer + inner) input).
```

## `query_expr_fetch_fetch_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1043`](../OrderedQueryFacts.v#L1043)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 28), `schema` (rank 52)

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_fetch_global_typed_equiv :
  forall outer inner input,
    query_global_typed_outcome_equiv
      (QExpr_Fetch outer (QExpr_Fetch inner input))
      (QExpr_Fetch (Nat.min outer inner) input).
```

## `query_expr_offset_fetch_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1053`](../OrderedQueryFacts.v#L1053)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 26), `schema` (rank 52)

Search aliases: `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_fetch_global_typed_equiv :
  forall offset count input,
    query_global_typed_outcome_equiv
      (QExpr_Offset offset (QExpr_Fetch count input))
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)).
```

## `query_expr_fetch_offset_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1063`](../OrderedQueryFacts.v#L1063)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 26), `schema` (rank 52)

Search aliases: `ordered query semantics`, `OFFSET`, `FETCH`, `LIMIT`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_offset_global_typed_equiv :
  forall count offset input,
    query_global_typed_outcome_equiv
      (QExpr_Fetch count (QExpr_Offset offset input))
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)).
```

## `query_expr_order_by_order_by_global_typed_equiv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1073`](../OrderedQueryFacts.v#L1073)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: retain exact order whenever the declaration observes it; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 24), `schema` (rank 52)

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_order_by_global_typed_equiv :
  forall outer_keys inner_keys input,
    query_global_typed_outcome_equiv
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input))
      (QExpr_OrderBy outer_keys input).
```

## `query_expr_distinct_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1087`](../OrderedQueryFacts.v#L1087)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `runtime` (rank 52), `ordered` (rank 22)

Search aliases: `ordered query semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_distinct_outcome_equiv_congr :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_expr_order_by_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1147`](../OrderedQueryFacts.v#L1147)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `runtime` (rank 52), `ordered` (rank 22)

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_outcome_equiv_congr :
  forall env keys left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_offset_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1207`](../OrderedQueryFacts.v#L1207)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `runtime` (rank 52), `ordered` (rank 22)

Search aliases: `ordered query semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_outcome_equiv_congr :
  forall env offset left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
```

## `query_expr_fetch_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1250`](../OrderedQueryFacts.v#L1250)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `runtime` (rank 52), `ordered` (rank 22)

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_outcome_equiv_congr :
  forall env count left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `query_expr_rank_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1293`](../OrderedQueryFacts.v#L1293)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `runtime` (rank 52), `ordered` (rank 22)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1422`](../OrderedQueryFacts.v#L1422)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 42), `runtime` (rank 52), `ordered` (rank 22)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1529`](../OrderedQueryFacts.v#L1529)

Purpose/direction: Transports or composes ordered query observation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query observation.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 24)

Search aliases: `ordered query semantics`, `ORDER BY`, `ordered observation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_order_by_equiv_congr :
  forall env keys left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_rank_equiv_congr_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1553`](../OrderedQueryFacts.v#L1553)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `ordered` (rank 36)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1585`](../OrderedQueryFacts.v#L1585)

Purpose/direction: Transports or composes window/rank evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about window/rank evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `ordered` (rank 36)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1613`](../OrderedQueryFacts.v#L1613)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 26)

Search aliases: `ordered query semantics`, `OFFSET`, `equivalence`, `congruence`

```rocq
Lemma query_expr_offset_equiv_congr :
  forall env offset left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
```

## `query_expr_fetch_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1654`](../OrderedQueryFacts.v#L1654)

Purpose/direction: Transports or composes ordered slicing across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered slicing.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 28)

Search aliases: `ordered query semantics`, `FETCH`, `LIMIT`, `equivalence`, `congruence`

```rocq
Lemma query_expr_fetch_equiv_congr :
  forall env count left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `ordered_rows_equiv_of_Forall2`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1835`](../OrderedQueryFacts.v#L1835)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `ordered` (rank 30)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1852`](../OrderedQueryFacts.v#L1852)

Purpose/direction: Transports or composes ordered query equivalence across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about ordered query equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `projection` (rank 52), `ordered` (rank 30)

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
