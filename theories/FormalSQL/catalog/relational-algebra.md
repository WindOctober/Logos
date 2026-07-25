# Bags, occurrences, projection, and relational algebra

Route here for: bag/list abstraction, multiplicity, filter/project/join/set operators.

This focused catalog contains 184 declarations routed at declaration granularity from `GroupedFilterOutcomeFacts.v`, `NumericRegroupFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`, `RelationalAlgebraFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `formula_pred_acceptance_exact_safe`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:426`](../GroupedFilterOutcomeFacts.v#L426)

Purpose/direction: Builds an exact SQL TRUE-acceptance contract for an interpreted scalar predicate from explicit argument runtime safety.

Applicability: Use for `FExpr_Pred` only after proving its authoritative `first_runtime_error` classifier is `None`; the decision is `Bool.is_true`, not an equality between SQL FALSE and UNKNOWN.

Important premises: The displayed `first_runtime_error ... arguments = None` premise is mandatory; retain the authoritative predicate interpreter and use `Bool.is_true` only for filter acceptance.

Cross-index: `runtime` (rank 52), `filter` (rank 24), `scalar` (rank 52)

Search aliases: `relational algebra`, `filter`, `WHERE`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma formula_pred_acceptance_exact_safe :
  forall env predicate arguments,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    formula_acceptance_exact_at env (FExpr_Pred predicate arguments)
      (Bool.is_true (B T)
        (interp_predicate T predicate
          (map (@interp_aggterm T env) arguments))).
```

## `eval_filter_rows_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:646`](../GroupedFilterOutcomeFacts.v#L646)

Purpose/direction: Characterizes row-filter outcomes exactly as successful `List.filter` under per-row exact-acceptance/no-error contracts.

Applicability: Use after proving `formula_acceptance_exact_at` for every input occurrence; the result preserves list order and duplicates and the premise excludes formula errors.

Important premises: Supply the displayed per-row `formula_acceptance_exact_at` contract, including its successful observation and no-error components; do not replace `List.filter` by a set abstraction.

Cross-index: `filter` (rank 22)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Theorem eval_filter_rows_acceptance_exact :
  forall env formula rows keep,
    (forall row,
      In row rows ->
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    forall outcome,
      eval_filter_rows env formula rows outcome <->
      outcome = SqlSuccess (List.filter keep rows).
```

## `filter_formula_observation_equiv_at_sym`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:760`](../GroupedFilterOutcomeFacts.v#L760)

Purpose/direction: Reverses a proved relational algebra relation.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma filter_formula_observation_equiv_at_sym :
  forall left_env left_formula right_env right_formula,
    filter_formula_observation_equiv_at
      left_env left_formula right_env right_formula ->
    filter_formula_observation_equiv_at
      right_env right_formula left_env left_formula.
```

## `eval_filter_rows_ordered_outcome_congr_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:798`](../GroupedFilterOutcomeFacts.v#L798)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 52), `runtime` (rank 52), `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_ordered_outcome_congr_forward :
  forall left_env left_formula left_rows left_outcome,
    eval_filter_rows left_env left_formula left_rows left_outcome ->
    forall right_env right_formula right_rows,
      ordered_rows_equiv T left_rows right_rows ->
      (forall left_row right_row,
        Oeset.compare (OTuple T) left_row right_row = Eq ->
        filter_formula_observation_equiv_at
          (env_t T left_env left_row) left_formula
          (env_t T right_env right_row) right_formula) ->
      exists right_outcome,
        eval_filter_rows right_env right_formula right_rows right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
```

## `eval_filter_rows_ordered_outcome_congr`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:885`](../GroupedFilterOutcomeFacts.v#L885)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 16), `runtime` (rank 16), `filter` (rank 8)

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem eval_filter_rows_ordered_outcome_congr :
  forall left_env left_formula left_rows
      right_env right_formula right_rows,
    ordered_rows_equiv T left_rows right_rows ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    (exists left_outcome,
      eval_filter_rows left_env left_formula left_rows left_outcome) ->
    outcome_relation_equiv (ordered_rows_equiv T)
      (eval_filter_rows left_env left_formula left_rows)
      (eval_filter_rows right_env right_formula right_rows).
```

## `query_expr_filter_outcome_congr_extensional_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:958`](../GroupedFilterOutcomeFacts.v#L958)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 52), `runtime` (rank 52), `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_outcome_congr_extensional_forward :
  forall env left_formula right_formula left_input right_input,
    @query_expr_outcome_observation_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    forall left_outcome,
      eval_query env (QExpr_Filter left_formula left_input) left_outcome ->
      exists right_outcome,
        eval_query env (QExpr_Filter right_formula right_input) right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
```

## `query_expr_filter_outcome_congr_extensional`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1029`](../GroupedFilterOutcomeFacts.v#L1029)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 10), `runtime` (rank 10), `filter` (rank 0)

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_outcome_congr_extensional :
  forall env left_formula right_formula left_input right_input,
    query_outcome_equiv env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    (exists left_outcome,
      eval_query env (QExpr_Filter left_formula left_input) left_outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_formula left_input)
      (QExpr_Filter right_formula right_input).
```

## `query_set_union_occurrence_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1083`](../NumericRegroupFacts.v#L1083)

Purpose/direction: Relates membership or occurrence evidence to SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_occurrence_exact : forall left right row,
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row
    (query_set_bag Union left right) =
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right)%N.
```

## `query_bag_duplicate_free_of_rows_NoDupA`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1097`](../NumericRegroupFacts.v#L1097)

Purpose/direction: Establishes the displayed duplicate-freedom property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_duplicate_free_of_rows_NoDupA : forall rows,
  NoDupA
    (fun first second => Oeset.compare (OTuple T) first second = Eq)
    rows ->
  query_bag_duplicate_free (rows_bag T rows).
```

## `query_bag_duplicate_free_transport`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1112`](../NumericRegroupFacts.v#L1112)

Purpose/direction: Transports the displayed hypotheses and conclusion for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_duplicate_free_transport : forall left right,
  bag_eq T left right ->
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right.
```

## `query_bags_disjoint_sym`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1167`](../NumericRegroupFacts.v#L1167)

Purpose/direction: Reverses a proved bag multiplicity relation.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_bags_disjoint_sym : forall left right,
  query_bags_disjoint left right -> query_bags_disjoint right left.
```

## `query_set_union_duplicate_free`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1174`](../NumericRegroupFacts.v#L1174)

Purpose/direction: States the query set union duplicate free law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_duplicate_free : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  query_bag_duplicate_free (query_set_bag Union left right).
```

## `query_set_union_disjoint_right`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1193`](../NumericRegroupFacts.v#L1193)

Purpose/direction: States the query set union disjoint right law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_disjoint_right : forall first second third,
  query_bags_disjoint first third ->
  query_bags_disjoint second third ->
  query_bags_disjoint (query_set_bag Union first second) third.
```

## `query_distinct_bag_inert`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1211`](../NumericRegroupFacts.v#L1211)

Purpose/direction: States the query distinct bag inert law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_inert : forall bag,
  query_bag_duplicate_free bag ->
  bag_eq T (query_distinct_bag bag) bag.
```

## `query_distinct_bag_occurrence_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1236`](../NumericRegroupFacts.v#L1236)

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_occurrence_exact : forall bag row,
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row
    (query_distinct_bag bag) =
  if Febag.mem (SqlQuerySemantics.BTupleT T) row bag then 1%N else 0%N.
```

## `query_duplicate_free_support_bag_eq`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1259`](../NumericRegroupFacts.v#L1259)

Purpose/direction: States the query duplicate free support bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 26)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_duplicate_free_support_bag_eq :
  forall left right : bagT,
    query_bag_duplicate_free left ->
    query_bag_duplicate_free right ->
    (forall row,
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left = 0%N <->
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right = 0%N) ->
    bag_eq T left right.
```

## `query_distinct_union_inert`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1291`](../NumericRegroupFacts.v#L1291)

Purpose/direction: States the query distinct union inert law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 35)

Search aliases: `relational algebra`, `set operation`, `UNION`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_distinct_union_inert : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  bag_eq T
    (query_distinct_bag (query_set_bag Union left right))
    (query_set_bag Union left right).
```

## `query_bag_filter_occurrence_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1310`](../NumericRegroupFacts.v#L1310)

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 30), `bag` (rank 36)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_occurrence_exact :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool)
      (bag : Febag.bag (SqlQuerySemantics.BTupleT T)),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (Febag.filter (Fecol.CBag (CTuple T)) keep bag) =
      if keep row
      then Febag.nb_occ (Fecol.CBag (CTuple T)) row bag
      else 0%N.
```

## `query_bag_filter_duplicate_free`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1333`](../NumericRegroupFacts.v#L1333)

Purpose/direction: States the query bag filter duplicate free law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 30), `bag` (rank 36)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_duplicate_free :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool)
      (bag : Febag.bag (SqlQuerySemantics.BTupleT T)),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    query_bag_duplicate_free bag ->
    query_bag_duplicate_free
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag).
```

## `query_expr_cross_join_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:354`](../OrderedQueryFacts.v#L354)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when the goal or a hypothesis matches the `query_expr_cross_join_has_success` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 24)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`

```rocq
Lemma query_expr_cross_join_has_success :
  forall env left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_CrossJoin left right).
```

## `eval_query_expr_project_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:953`](../OrderedQueryFacts.v#L953)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `projection` (rank 36)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma eval_query_expr_project_success_iff :
  forall env select_list input output,
    eval_query env (QExpr_Project select_list input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list input_rows = SqlSuccess output.
```

## `eval_query_expr_filter_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:988`](../OrderedQueryFacts.v#L988)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_query_expr_filter_success_iff :
  forall env formula input output,
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlSuccess output).
```

## `eval_query_expr_filter_success_Forall_accepted`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1006`](../OrderedQueryFacts.v#L1006)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `eval_query_expr_filter_success_Forall_accepted` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_query_expr_filter_success_Forall_accepted :
  forall env formula input output (property : tuple T -> Prop),
    (forall input_rows row truth,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = true ->
      property row) ->
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) ->
    Forall property output.
```

## `query_expr_project_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1029`](../OrderedQueryFacts.v#L1029)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_project_success_Forall` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma query_expr_project_success_Forall :
  forall env select_list input
      (input_property output_property : tuple T -> Prop),
    query_success_Forall env input input_property ->
    (forall row,
      input_property row ->
      output_property
        (projection T (env_t T env row) (@Select_List T select_list))) ->
    query_success_Forall env
      (QExpr_Project select_list input) output_property.
```

## `query_expr_filter_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1053`](../OrderedQueryFacts.v#L1053)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_filter_success_Forall` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma query_expr_filter_success_Forall :
  forall env formula input (property : tuple T -> Prop),
    query_success_Forall env input property ->
    query_success_Forall env (QExpr_Filter formula input) property.
```

## `query_expr_union_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1088`](../OrderedQueryFacts.v#L1088)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 8)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_union_success_Forall :
  forall env left right (property : tuple T -> Prop),
    query_expr_sort left =S= query_expr_sort right ->
    tuple_property_semantic_invariant property ->
    query_success_Forall env left property ->
    query_success_Forall env right property ->
    query_success_Forall env (QExpr_Set Union left right) property.
```

## `query_expr_cross_join_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1125`](../OrderedQueryFacts.v#L1125)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 8), `bag` (rank 10)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_cross_join_success_Forall :
  forall env left right (property : tuple T -> Prop),
    tuple_property_semantic_invariant property ->
    (forall left_rows right_rows,
      eval_query env left (SqlSuccess left_rows) ->
      eval_query env right (SqlSuccess right_rows) ->
      Forall property
        (Febag.elements (Fecol.CBag (CTuple T))
          (query_cross_join_bag
            (rows_bag T left_rows) (rows_bag T right_rows)))) ->
    query_success_Forall env (QExpr_CrossJoin left right) property.
```

## `query_filter_success_bags_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1226`](../OrderedQueryFacts.v#L1226)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 28), `bag` (rank 34)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_filter_success_bags_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    rel_equiv
      (success_bags env (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
```

## `query_expr_filter_has_success_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1325`](../OrderedQueryFacts.v#L1325)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_filter_has_success_exact` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma query_expr_filter_has_success_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    query_has_success env input ->
    query_has_success env (QExpr_Filter formula input).
```

## `query_filter_success_bags_functional_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1352`](../OrderedQueryFacts.v#L1352)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 28), `bag` (rank 34)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_filter_success_bags_functional_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Filter formula input) first ->
      success_bags env (QExpr_Filter formula input) second ->
      bag_eq T first second.
```

## `query_expr_filter_bag_closed_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1424`](../OrderedQueryFacts.v#L1424)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 2), `bag` (rank 6)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_filter_bag_closed_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    BagClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_Filter formula input) (SqlSuccess rows)).
```

## `eval_filter_rows_always_true_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2709`](../OrderedQueryFacts.v#L2709)

Purpose/direction: Characterizes successful filtering when every reached formula evaluation succeeds with SQL TRUE.

Applicability: Use only after proving every reached predicate outcome is exactly `SqlSuccess true3`; errors and UNKNOWN are not covered.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 28)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_filter_rows_always_true_iff :
  forall env formula rows,
    (forall row,
      In row rows ->
      forall outcome,
        @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null (env_t T env row) formula outcome <->
        outcome = SqlSuccess (Bool.true (B T))) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula rows outcome <->
      outcome = SqlSuccess rows.
```

## `relational_permutation_map_inv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2811`](../OrderedQueryFacts.v#L2811)

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma relational_permutation_map_inv :
  forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) output input,
    _permut R output (map f input) ->
    exists reordered,
      Permutation input reordered /\
      Forall2 R output (map f reordered).
```

## `projected_rows_same_as_mapped_bag`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3125`](../OrderedQueryFacts.v#L3125)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma projected_rows_same_as_mapped_bag :
  forall env select_list rows bag,
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        bag).
```

## `mapped_bag_rows_have_projection_preimage`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3157`](../OrderedQueryFacts.v#L3157)

Purpose/direction: States the mapped bag rows have projection preimage law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 36), `bag` (rank 36)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma mapped_bag_rows_have_projection_preimage :
  forall env select_list bag output,
    query_same_rows_as_bag output
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        bag) ->
    exists input_rows,
      query_same_rows_as_bag input_rows bag /\
      ordered_rows_equiv T output
        (map
          (fun row =>
            projection T (env_t T env row) (@Select_List T select_list))
          input_rows).
```

## `query_project_success_bags_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3215`](../OrderedQueryFacts.v#L3215)

Purpose/direction: Characterizes the possible successful bags of a locally safe projection as a multiplicity-preserving bag map of child bags.

Applicability: Use after proving scalar SELECT evaluation safe for every row; this is an exact possible-bag characterization, not an ordered-row result.

Important premises: Prove the displayed SELECT-list runtime-error equation for every row; respect `bag_eq` and duplicate multiplicity in both directions.

Cross-index: `runtime` (rank 50), `projection` (rank 6), `bag` (rank 34)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_success_bags_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    rel_equiv
      (success_bags env (QExpr_Project select_list input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T (query_project_bag env select_list input_bag) output).
```

## `query_project_bag_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3384`](../OrderedQueryFacts.v#L3384)

Purpose/direction: Transports input bag equality through the declared projection bag map.

Applicability: Use to map an existing input `bag_eq` through one fixed projection.

Important premises: Supply the displayed input `bag_eq`; the environment and SELECT list stay fixed.

Cross-index: `projection` (rank 26), `bag` (rank 24)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_project_bag_congr :
  forall env select_list left right,
    bag_eq T left right ->
    bag_eq T
      (query_project_bag env select_list left)
      (query_project_bag env select_list right).
```

## `query_table_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3399`](../OrderedQueryFacts.v#L3399)

Purpose/direction: Shows that a base table has one possible successful bag modulo bag equality.

Applicability: Use as the generic base case for possible-bag functionality of a table.

Important premises: Supply two possible successful bags for the same environment, outputs, and table.

Cross-index: `bag` (rank 22)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_table_success_bags_functional :
  forall env outputs table first second,
    success_bags env (QExpr_Table outputs table) first ->
    success_bags env (QExpr_Table outputs table) second ->
    bag_eq T first second.
```

## `project_rows_success_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3583`](../OrderedQueryFacts.v#L3583)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `project_rows_success_exact` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 36)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma project_rows_success_exact :
  forall env select_list rows output,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows = SqlSuccess output ->
    output =
      map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows.
```

## `query_project_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3612`](../OrderedQueryFacts.v#L3612)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 34), `bag` (rank 34)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_success_bags_functional :
  forall env select_list input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Project select_list input) first ->
      success_bags env (QExpr_Project select_list input) second ->
      bag_eq T first second.
```

## `query_set_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3684`](../OrderedQueryFacts.v#L3684)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 34)

Search aliases: `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_set_success_bags_functional :
  forall env operation left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Set operation left right) first ->
      success_bags env (QExpr_Set operation left right) second ->
      bag_eq T first second.
```

## `query_cross_join_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3724`](../OrderedQueryFacts.v#L3724)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 22), `bag` (rank 34)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_cross_join_success_bags_functional :
  forall env left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_CrossJoin left right) first ->
      success_bags env (QExpr_CrossJoin left right) second ->
      bag_eq T first second.
```

## `tnull_row_eq_refl`

Source: [`theories/FormalSQL/ProofAgentFacade.v:48`](../ProofAgentFacade.v#L48)

Purpose/direction: Exposes the displayed equivalence law for the facade's semantic TNull row equality without reopening ordered-set internals.

Applicability: Use to compose generated row correspondences through the facade's semantic equality; this is not Leibniz tuple equality.

Important premises: No premises beyond the displayed row.

Cross-index: `facade` (rank 8), `projection` (rank 10)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_refl :
  forall row, TNullRowEq row row.
```

## `tnull_row_eq_sym`

Source: [`theories/FormalSQL/ProofAgentFacade.v:55`](../ProofAgentFacade.v#L55)

Purpose/direction: Exposes the displayed equivalence law for the facade's semantic TNull row equality without reopening ordered-set internals.

Applicability: Use to compose generated row correspondences through the facade's semantic equality; this is not Leibniz tuple equality.

Important premises: Supply the displayed semantic TNull row equality in the forward direction.

Cross-index: `facade` (rank 8), `projection` (rank 10)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_sym :
  forall left right,
    TNullRowEq left right ->
    TNullRowEq right left.
```

## `tnull_row_eq_trans`

Source: [`theories/FormalSQL/ProofAgentFacade.v:64`](../ProofAgentFacade.v#L64)

Purpose/direction: Exposes the displayed equivalence law for the facade's semantic TNull row equality without reopening ordered-set internals.

Applicability: Use to compose generated row correspondences through the facade's semantic equality; this is not Leibniz tuple equality.

Important premises: Supply both displayed semantic TNull row equalities through the same intermediate row; do not replace them by Leibniz equality.

Cross-index: `facade` (rank 2), `projection` (rank 4)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_trans :
  forall first second third,
    TNullRowEq first second ->
    TNullRowEq second third ->
    TNullRowEq first third.
```

## `tnull_select_lookup_head`

Source: [`theories/FormalSQL/ProofAgentFacade.v:229`](../ProofAgentFacade.v#L229)

Purpose/direction: States the tnull select lookup head law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_head` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `facade` (rank 16), `projection` (rank 16)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_head :
  forall items expression attribute,
    TNullSelectLookup
      (SelectList (SelectAs expression attribute :: items)) attribute =
    Some expression.
```

## `tnull_select_lookup_cons_other`

Source: [`theories/FormalSQL/ProofAgentFacade.v:245`](../ProofAgentFacade.v#L245)

Purpose/direction: States the tnull select lookup cons other law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_cons_other` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `projection` (rank 16)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_cons_other :
  forall items head_expression head_attribute attribute,
    Oset.eq_bool (OAtt TNull) attribute head_attribute = false ->
    TNullSelectLookup
      (SelectList (SelectAs head_expression head_attribute :: items))
      attribute =
    TNullSelectLookup (SelectList items) attribute.
```

## `tnull_select_lookup_retained`

Source: [`theories/FormalSQL/ProofAgentFacade.v:269`](../ProofAgentFacade.v#L269)

Purpose/direction: States the tnull select lookup retained law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_retained` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 4), `projection` (rank 2)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_retained :
  forall env select attribute expression row,
    TNullSelectLookup select attribute = Some expression ->
    attribute inS
      TNullRowLabels (TNullProjectRow env select row) /\
    TNullRowValue (TNullProjectRow env select row) attribute =
      Interp.interp_aggterm TNull (env_t TNull env row) expression.
```

## `tnull_select_lookup_some_iff_projected_label`

Source: [`theories/FormalSQL/ProofAgentFacade.v:331`](../ProofAgentFacade.v#L331)

Purpose/direction: Relates successful first-match SELECT lookup exactly to membership of the corresponding projected output label.

Applicability: Use in either direction between first-match lookup and projected label presence; repeated aliases do not authorize choosing a later SELECT item.

Important premises: No alias-uniqueness premise is required: the statement follows the authoritative first-match SELECT lookup and exact projected-label membership test.

Cross-index: `facade` (rank 6), `projection` (rank 4)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_some_iff_projected_label :
  forall env select attribute row,
    (exists expression,
      TNullSelectLookup select attribute = Some expression) <->
    attribute inS TNullRowLabels (TNullProjectRow env select row).
```

## `tnull_select_lookup_none_iff_projected_label_absent`

Source: [`theories/FormalSQL/ProofAgentFacade.v:378`](../ProofAgentFacade.v#L378)

Purpose/direction: Relates failed first-match SELECT lookup exactly to Boolean absence of the corresponding projected output label.

Applicability: Use in either direction to prove concrete lookup failure or output label absence without unfolding projection-label construction.

Important premises: No alias-uniqueness premise is required: the statement follows the authoritative first-match SELECT lookup and exact projected-label membership test.

Cross-index: `facade` (rank 6), `projection` (rank 4)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_none_iff_projected_label_absent :
  forall env select attribute row,
    TNullSelectLookup select attribute = None <->
    (attribute inS? TNullRowLabels (TNullProjectRow env select row)) = false.
```

## `tnull_select_lookup_direct_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:413`](../ProofAgentFacade.v#L413)

Purpose/direction: States the tnull select lookup direct value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_direct_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 6), `projection` (rank 4)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_direct_value :
  forall env select source target row,
    TNullSelectLookup select target = Some (AExpr (Dot source)) ->
    source inS TNullRowLabels row ->
    TNullRowValue (TNullProjectRow env select row) target =
    TNullRowValue row source.
```

## `tnull_select_lookup_constant_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:435`](../ProofAgentFacade.v#L435)

Purpose/direction: States the tnull select lookup constant value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_constant_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 8), `projection` (rank 6)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_constant_value :
  forall env select target value row,
    TNullSelectLookup select target = Some (AExpr (Constant value)) ->
    TNullRowValue (TNullProjectRow env select row) target = value.
```

## `tnull_select_lookup_direct_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:452`](../ProofAgentFacade.v#L452)

Purpose/direction: States the tnull select lookup direct compose law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_direct_compose` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 2), `projection` (rank 2)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_direct_compose :
  forall env first second source middle target row,
    TNullSelectLookup first middle = Some (AExpr (Dot source)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    source inS TNullRowLabels row ->
    target inS
      TNullRowLabels
        (TNullProjectRow env second (TNullProjectRow env first row)) /\
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    TNullRowValue row source.
```

## `tnull_select_lookup_constant_direct_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:487`](../ProofAgentFacade.v#L487)

Purpose/direction: States the tnull select lookup constant direct compose law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_constant_direct_compose` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 2), `projection` (rank 2)

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_constant_direct_compose :
  forall env first second value middle target row,
    TNullSelectLookup first middle = Some (AExpr (Constant value)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    target inS
      TNullRowLabels
        (TNullProjectRow env second (TNullProjectRow env first row)) /\
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    value.
```

## `tnull_direct_projection_preserves_attribute`

Source: [`theories/FormalSQL/ProofAgentFacade.v:518`](../ProofAgentFacade.v#L518)

Purpose/direction: Shows that the indicated operator preserves the displayed relational algebra property.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_preserves_attribute` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `facade` (rank 16), `projection` (rank 16), `schema` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `schema conformance`, `typing`

```rocq
Lemma tnull_direct_projection_preserves_attribute :
  forall (env : TNullEnvironment) (select : TNullSelectList)
      (attribute : TNullAttribute) (row : TNullRow),
    select_list_directly_selects_attr select attribute ->
    select_list_has_unique_outputs select ->
    attribute inS TNullRowLabels row ->
    TNullRowValue (TNullProjectRow env select row) attribute =
    TNullRowValue row attribute.
```

## `tnull_direct_projection_alias_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:537`](../ProofAgentFacade.v#L537)

Purpose/direction: Reads an aliased direct SELECT output exactly as its present source attribute under unique output aliases, preserving NULL values.

Applicability: Use to reduce `dot` at a renamed projection output after proving the literal direct SELECT item, unique output aliases, and source attribute presence in the input row.

Important premises: The displayed direct `source -> target` item and output uniqueness are mandatory; source presence prevents lookup from falling through to the outer environment.

Cross-index: `facade` (rank 16), `projection` (rank 4)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_alias_value :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (row : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels row ->
    TNullRowValue
      (TNullProjectRow env (@_Select_List TNull items) row) target =
    TNullRowValue row source.
```

## `tnull_direct_projection_alias_retained`

Source: [`theories/FormalSQL/ProofAgentFacade.v:571`](../ProofAgentFacade.v#L571)

Purpose/direction: States the tnull direct projection alias retained law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_alias_retained` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `projection` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_alias_retained :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (row : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels row ->
    target inS
      TNullRowLabels
        (TNullProjectRow env (@_Select_List TNull items) row) /\
    TNullRowValue
      (TNullProjectRow env (@_Select_List TNull items) row) target =
    TNullRowValue row source.
```

## `tnull_direct_projection_alias_reflects_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:603`](../ProofAgentFacade.v#L603)

Purpose/direction: States the tnull direct projection alias reflects value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_alias_reflects_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `projection` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_alias_reflects_value :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (left right : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels left ->
    source inS TNullRowLabels right ->
    TNullRowEq
      (TNullProjectRow env (@_Select_List TNull items) left)
      (TNullProjectRow env (@_Select_List TNull items) right) ->
    TNullRowValue left source = TNullRowValue right source.
```

## `tnull_projected_alias_int32_primary_key_matches_at_most_one`

Source: [`theories/FormalSQL/ProofAgentFacade.v:641`](../ProofAgentFacade.v#L641)

Purpose/direction: States the tnull projected alias int32 primary key matches at most one law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projected_alias_int32_primary_key_matches_at_most_one` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `facade` (rank 16), `schema` (rank 2), `scalar` (rank 16)

Search aliases: `relational algebra`, `INTEGER`, `int32`, `integrity constraint`, `key`

```rocq
Lemma tnull_projected_alias_int32_primary_key_matches_at_most_one :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      source_name target_name (fixed : TNullValue)
      (raw_rows projected_rows : list TNullRow) (raw_bag : TNullRowBag),
    Forall
      (row_attribute_present_conforms (Attr_int32 source_name)) raw_rows ->
    primary_key_conforms [Attr_int32 source_name] raw_rows ->
    In
      (SelectAs (DotInt32 source_name) (AttrInt32 target_name))
      items ->
    select_list_has_unique_outputs (SelectList items) ->
    value_conforms_attribute (Attr_int32 source_name) fixed ->
    @query_same_rows_as_bag TNull raw_rows raw_bag ->
    @query_same_rows_as_bag TNull projected_rows
      (@query_project_bag TNull env (SelectList items) raw_bag) ->
    (List.length
      (filter
        (fun row =>
          postgres_int32_equal_true fixed
            (TNullRowValue row (Attr_int32 target_name)))
        projected_rows) <= 1)%nat.
```

## `tnull_direct_projection_row_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:824`](../ProofAgentFacade.v#L824)

Purpose/direction: States the tnull direct projection row equality law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_row_eq` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_row_eq :
  forall (env : TNullEnvironment) (select : TNullSelectList)
      (row : TNullRow),
    select_list_has_unique_outputs select ->
    (forall attribute,
      attribute inS TNullRowLabels row ->
      select_list_directly_selects_attr select attribute) ->
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select row))
      (TNullRowLabels row) ->
    TNullRowEq (TNullProjectRow env select row) row.
```

## `tnull_row_permut_implies_rows_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:854`](../ProofAgentFacade.v#L854)

Purpose/direction: States the tnull row permut implies rows bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 6)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_row_permut_implies_rows_bag_eq :
  forall left right,
    TNullRowPermut left right ->
    TNullBagEq (TNullRowsBag left) (TNullRowsBag right).
```

## `tnull_double_projection_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:867`](../ProofAgentFacade.v#L867)

Purpose/direction: States the tnull double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 6)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_double_projection_bag_eq :
  forall env outer_left inner_left outer_right inner_right bag,
    (forall row,
      TNullRowEq
        (TNullProjectRow env outer_left
          (TNullProjectRow env inner_left row))
        (TNullProjectRow env outer_right
          (TNullProjectRow env inner_right row))) ->
    TNullBagEq
      (TNullBagMap
        (fun row => TNullProjectRow env outer_left row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner_left row) bag))
      (TNullBagMap
        (fun row => TNullProjectRow env outer_right row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner_right row) bag)).
```

## `tnull_map_theta_join_total_functional`

Source: [`theories/FormalSQL/ProofAgentFacade.v:909`](../ProofAgentFacade.v#L909)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_theta_join_total_functional :
  forall (B : Type)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> B) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (TNullThetaJoinRows join accept left right) =
    map emit left.
```

## `tnull_map_left_join_total_functional`

Source: [`theories/FormalSQL/ProofAgentFacade.v:932`](../ProofAgentFacade.v#L932)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_left_join_total_functional` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_left_join_total_functional :
  forall (B : Type)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> B) (pad : TNullRow -> TNullRow)
      left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left -> project (pad left_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (TNullLeftJoinRows join accept pad left right) =
    map emit left.
```

## `tnull_map_theta_join_total_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:962`](../ProofAgentFacade.v#L962)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional_permut` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_theta_join_total_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit left).
```

## `tnull_map_theta_join_total_functional_permut_accepted`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1019`](../ProofAgentFacade.v#L1019)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional_permut_accepted` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_theta_join_total_functional_permut_accepted :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit left).
```

## `tnull_map_theta_join_functional_permut_filter_exists`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1085`](../ProofAgentFacade.v#L1085)

Purpose/direction: States the tnull map theta join functional permut filter exists law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_functional_permut_filter_exists` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `filter` (rank 10), `join` (rank 6)

Search aliases: `relational algebra`, `join`, `filter`, `WHERE`

```rocq
Lemma tnull_map_theta_join_functional_permut_filter_exists :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit
        (filter
          (fun left_row => existsb (accept left_row) right) left)).
```

## `tnull_map_left_join_total_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1111`](../ProofAgentFacade.v#L1111)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_left_join_total_functional_permut` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_left_join_total_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (pad : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      TNullRowEq (project (pad left_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullLeftJoinRows join accept pad left right))
      (map emit left).
```

## `tnull_map_left_join_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1145`](../ProofAgentFacade.v#L1145)

Purpose/direction: Identifies a projected at-most-one LEFT JOIN with the mapped left input up to semantic permutation, retaining unmatched and duplicate left occurrences without a total-match premise.

Applicability: Use when each left occurrence has zero or one accepted right occurrence and matched and padded rows project to the same direct left result; semantic permutation preserves duplicate left rows.

Important premises: Retain both matched and padded projection equalities and the per-left at-most-one bound.  No foreign-key totality premise is required; the conclusion is occurrence-preserving permutation.

Cross-index: `facade` (rank 6), `join` (rank 8)

Search aliases: `relational algebra`, `functional LEFT JOIN`, `at-most-one match`, `nullable unmatched key`, `left multiplicity`, `join`

```rocq
Lemma tnull_map_left_join_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (pad : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      TNullRowEq (project (pad left_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullLeftJoinRows join accept pad left right))
      (map emit left).
```

## `tnull_row_eq_of_labels_and_values`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1170`](../ProofAgentFacade.v#L1170)

Purpose/direction: States the tnull row equality of labels and values law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_row_eq_of_labels_and_values` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`

```rocq
Lemma tnull_row_eq_of_labels_and_values :
  forall left right,
    TNullAttributeSetEq (TNullRowLabels left) (TNullRowLabels right) ->
    (forall attribute,
      attribute inS TNullRowLabels left ->
      TNullRowValue left attribute = TNullRowValue right attribute) ->
    TNullRowEq left right.
```

## `tnull_project_row_eq_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1188`](../ProofAgentFacade.v#L1188)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `equivalence`, `congruence`

```rocq
Lemma tnull_project_row_eq_congr :
  forall env select left right,
    TNullRowEq left right ->
    TNullRowEq
      (TNullProjectRow env select left)
      (TNullProjectRow env select right).
```

## `tnull_projected_select_item_reflects_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1206`](../ProofAgentFacade.v#L1206)

Purpose/direction: States the tnull projected select item reflects value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projected_select_item_reflects_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16)

Search aliases: `relational algebra`

```rocq
Lemma tnull_projected_select_item_reflects_value :
  forall env items expression attribute left right,
    In (@Select_As TNull expression attribute) items ->
    select_list_has_unique_outputs (SelectList items) ->
    TNullRowEq
      (TNullProjectRow env (SelectList items) left)
      (TNullProjectRow env (SelectList items) right) ->
    Interp.interp_aggterm TNull (env_t TNull env left) expression =
    Interp.interp_aggterm TNull (env_t TNull env right) expression.
```

## `tnull_project_rows_select_columns_success`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1465`](../ProofAgentFacade.v#L1465)

Purpose/direction: Computes direct-column projection of a row list as an exact ordered successful map, discharging all projection-local scalar errors.

Applicability: Use only for `SelectColumns`; it proves projection-local safety and the exact ordered row map, independently of any child-query outcome.

Important premises: The SELECT list must have the displayed direct-column form; the exact ordered map conclusion does not cover arbitrary scalar expressions.

Cross-index: `facade` (rank 4), `runtime` (rank 8), `projection` (rank 2)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_project_rows_select_columns_success :
  forall env columns rows,
    @project_rows_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) rows =
    SqlSuccess
      (map
        (fun row => TNullProjectRow env (SelectColumns columns) row)
        rows).
```

## `tnull_projection_envs_eq_of_select_items`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1792`](../ProofAgentFacade.v#L1792)

Purpose/direction: States the tnull projection envs equality of select items law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projection_envs_eq_of_select_items` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 2), `projection` (rank 0)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_projection_envs_eq_of_select_items :
  forall (left_env right_env : Env.env TNull)
      (left_items right_items : list SelectItemT),
    Forall2
      (fun left right =>
        match left, right with
        | @Projection.Select_As _ left_expression left_attribute,
          @Projection.Select_As _ right_expression right_attribute =>
            left_attribute = right_attribute /\
            Interp.interp_aggterm TNull left_env left_expression =
            Interp.interp_aggterm TNull right_env right_expression
        end)
      left_items right_items ->
    TNullRowEq
      (Projection.projection TNull left_env
        (@Projection.Select_List TNull (SelectList left_items)))
      (Projection.projection TNull right_env
        (@Projection.Select_List TNull (SelectList right_items))).
```

## `tnull_projection_rows_eq_of_select_items`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1896`](../ProofAgentFacade.v#L1896)

Purpose/direction: States the tnull projection rows equality of select items law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projection_rows_eq_of_select_items` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `projection` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_projection_rows_eq_of_select_items :
  forall env left_row right_row
      (left_items right_items : list SelectItemT),
    Forall2
      (fun left right =>
        match left, right with
        | @Projection.Select_As _ left_expression left_attribute,
          @Projection.Select_As _ right_expression right_attribute =>
            left_attribute = right_attribute /\
            Interp.interp_aggterm TNull (env_t TNull env left_row)
              left_expression =
            Interp.interp_aggterm TNull (env_t TNull env right_row)
              right_expression
        end)
      left_items right_items ->
    TNullRowEq
      (TNullProjectRow env (SelectList left_items) left_row)
      (TNullProjectRow env (SelectList right_items) right_row).
```

## `tnull_direct_projection_row_eq_on_expected_labels`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1922`](../ProofAgentFacade.v#L1922)

Purpose/direction: States the tnull direct projection row equality on expected labels law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_row_eq_on_expected_labels` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_row_eq_on_expected_labels :
  forall env select expected row,
    select_list_has_unique_outputs select ->
    (forall attribute,
      attribute inS expected ->
      select_list_directly_selects_attr select attribute) ->
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select row)) expected ->
    TNullAttributeSetEq (TNullRowLabels row) expected ->
    TNullRowEq (TNullProjectRow env select row) row.
```

## `tnull_bag_map_ext`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1948`](../ProofAgentFacade.v#L1948)

Purpose/direction: States the tnull bag map ext law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_bag_map_ext :
  forall left_map right_map bag,
    (forall row,
      In row (Febag.elements TNullRowBagRecord bag) ->
      TNullRowEq (left_map row) (right_map row)) ->
    TNullBagEq
      (TNullBagMap left_map bag)
      (TNullBagMap right_map bag).
```

## `tnull_bag_map_identity`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1965`](../ProofAgentFacade.v#L1965)

Purpose/direction: States the tnull bag map identity law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_bag_map_identity :
  forall bag,
    TNullBagEq (TNullBagMap (fun row => row) bag) bag.
```

## `tnull_projection_bag_map_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1978`](../ProofAgentFacade.v#L1978)

Purpose/direction: States the tnull projection bag map compose law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_projection_bag_map_compose :
  forall env outer inner bag,
    TNullBagEq
      (TNullBagMap
        (fun row => TNullProjectRow env outer row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner row) bag))
      (TNullBagMap
        (fun row =>
          TNullProjectRow env outer (TNullProjectRow env inner row)) bag).
```

## `tnull_single_double_projection_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2022`](../ProofAgentFacade.v#L2022)

Purpose/direction: States the tnull single double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 6)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_single_double_projection_bag_eq :
  forall env single outer inner bag,
    (forall row,
      In row (Febag.elements TNullRowBagRecord bag) ->
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row))) ->
    TNullBagEq
      (TNullBagMap (fun row => TNullProjectRow env single row) bag)
      (TNullBagMap
        (fun row => TNullProjectRow env outer row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner row) bag)).
```

## `tnull_same_select_projection_labels`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2046`](../ProofAgentFacade.v#L2046)

Purpose/direction: States the tnull same select projection labels law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_same_select_projection_labels` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `facade` (rank 16), `projection` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_same_select_projection_labels :
  forall env select left right,
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select left))
      (TNullRowLabels (TNullProjectRow env select right)).
```

## `tnull_theta_join_by_witness`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2113`](../ProofAgentFacade.v#L2113)

Purpose/direction: States the tnull theta join by witness law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_theta_join_by_witness` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 16), `join` (rank 6)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_theta_join_by_witness :
  forall (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (left right : list TNullRow) (witness : bool),
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (witness = true ->
      forall left_row,
        In left_row left ->
        exists right_row,
          In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (length (filter (accept left_row) right) <= 1)%nat) ->
    (witness = false ->
      forall left_row right_row,
        In left_row left ->
        In right_row right ->
        accept left_row right_row = false) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (if witness then map emit left else nil).
```

## `tnull_total_functional_theta_project_nodup`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2174`](../ProofAgentFacade.v#L2174)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 10), `projection` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`

```rocq
Lemma tnull_total_functional_theta_project_nodup :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    NoDupA TNullRowEq (map emit left) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
```

## `tnull_total_functional_theta_project_nodup_accepted`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2209`](../ProofAgentFacade.v#L2209)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 10), `projection` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`

```rocq
Lemma tnull_total_functional_theta_project_nodup_accepted :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    NoDupA TNullRowEq (map emit left) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
```

## `tnull_functional_theta_project_nodup_of_key_reflection`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2249`](../ProofAgentFacade.v#L2249)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`

```rocq
Lemma tnull_functional_theta_project_nodup_of_key_reflection :
  forall (Key : Type) (key_relation : Key -> Key -> Prop)
      (key : TNullRow -> Key)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project : TNullRow -> TNullRow) left right,
    NoDupA key_relation (map key left) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (forall left_first left_second right_first right_second,
      In left_first left -> In left_second left ->
      In right_first right -> In right_second right ->
      accept left_first right_first = true ->
      accept left_second right_second = true ->
      TNullRowEq
        (project (join left_first right_first))
        (project (join left_second right_second)) ->
      key_relation (key left_first) (key left_second)) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
```

## `tnull_nodup_occ_le_one`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2295`](../ProofAgentFacade.v#L2295)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `multiplicity`

```rocq
Lemma tnull_nodup_occ_le_one :
  forall rows,
    NoDupA TNullRowEq rows ->
    forall row,
      (Oeset.nb_occ TNullRowOrder row rows <= 1)%N.
```

## `interp_direct_attribute_in_env_t`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:18`](../RelationalAlgebraFacts.v#L18)

Purpose/direction: States the interp direct attribute in env t law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_direct_attribute_in_env_t` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 52)

Search aliases: `relational algebra`, `schema conformance`, `typing`

```rocq
Lemma interp_direct_attribute_in_env_t :
  forall (T : Tuple.Rcd) env row attribute,
    attribute inS labels T row ->
    interp_aggterm T (env_t T env row)
      (@A_Expr T (@F_Dot T attribute)) =
    dot T row attribute.
```

## `list_support_rel_compose`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:47`](../RelationalAlgebraFacts.v#L47)

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 8)

Search aliases: `relational algebra`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_compose :
  forall A B C (R : A -> B -> Prop) (S : B -> C -> Prop)
      (U : A -> C -> Prop) left middle right,
    list_support_rel R left middle ->
    list_support_rel S middle right ->
    (forall x y z, R x y -> S y z -> U x z) ->
    list_support_rel U left right.
```

## `list_support_rel_map_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:73`](../RelationalAlgebraFacts.v#L73)

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 10), `bag` (rank 12)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_map_transport :
  forall A B C D (R : A -> B -> Prop) (S : C -> D -> Prop)
      (left_map : A -> C) (right_map : B -> D) left right,
    list_support_rel R left right ->
    (forall x y, R x y -> S (left_map x) (right_map y)) ->
    list_support_rel S (map left_map left) (map right_map right).
```

## `list_support_rel_map_iff`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:102`](../RelationalAlgebraFacts.v#L102)

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 12), `bag` (rank 14)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_map_iff :
  forall A B C D (R : B -> D -> Prop)
      (left_map : A -> B) (right_map : C -> D) left right,
    list_support_rel R (map left_map left) (map right_map right) <->
    list_support_rel
      (fun x y => R (left_map x) (right_map y)) left right.
```

## `list_support_rel_unmap_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:130`](../RelationalAlgebraFacts.v#L130)

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 14), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_unmap_left :
  forall A B C (R : B -> C -> Prop) (mapping : A -> B) left right,
    list_support_rel R (map mapping left) right ->
    list_support_rel (fun x y => R (mapping x) y) left right.
```

## `list_support_rel_map_left_with_witness`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:150`](../RelationalAlgebraFacts.v#L150)

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 14), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_map_left_with_witness :
  forall A B C (R : A -> C -> Prop) (mapping : A -> B) left right,
    list_support_rel R left right ->
    list_support_rel
      (fun mapped output =>
        exists original, mapped = mapping original /\ R original output)
      (map mapping left) right.
```

## `all_diff_map_key_NoDupA`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:175`](../RelationalAlgebraFacts.v#L175)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `all_diff_map_key_NoDupA` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`

```rocq
Lemma all_diff_map_key_NoDupA :
  forall (A B : Type) (key : A -> B) rows,
    ListFacts.all_diff (map key rows) ->
    SetoidList.NoDupA
      (fun left right => key left = key right) rows.
```

## `rel_equiv_refl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:195`](../RelationalAlgebraFacts.v#L195)

Purpose/direction: Establishes reflexivity for relational algebra.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_refl :
  forall (A : Type) (relation : A -> Prop),
    rel_equiv relation relation.
```

## `rel_equiv_sym`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:202`](../RelationalAlgebraFacts.v#L202)

Purpose/direction: Reverses a proved relational algebra relation.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_sym :
  forall (A : Type) (left right : A -> Prop),
    rel_equiv left right -> rel_equiv right left.
```

## `rel_equiv_trans`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:211`](../RelationalAlgebraFacts.v#L211)

Purpose/direction: Composes two relational algebra relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_trans :
  forall (A : Type) (first second third : A -> Prop),
    rel_equiv first second ->
    rel_equiv second third ->
    rel_equiv first third.
```

## `rel_incl_refl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:225`](../RelationalAlgebraFacts.v#L225)

Purpose/direction: Establishes reflexivity for relational algebra.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_incl_refl :
  forall (A : Type) (relation : A -> Prop),
    rel_incl relation relation.
```

## `rel_incl_trans`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:232`](../RelationalAlgebraFacts.v#L232)

Purpose/direction: Composes two relational algebra relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_incl_trans :
  forall (A : Type) (first second third : A -> Prop),
    rel_incl first second ->
    rel_incl second third ->
    rel_incl first third.
```

## `rel_equiv_iff_mutual_incl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:242`](../RelationalAlgebraFacts.v#L242)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_iff_mutual_incl :
  forall (A : Type) (left right : A -> Prop),
    rel_equiv left right <->
    rel_incl left right /\ rel_incl right left.
```

## `alpha_rel_incl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:256`](../RelationalAlgebraFacts.v#L256)

Purpose/direction: States the alpha rel incl law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `alpha_rel_incl` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`

```rocq
Lemma alpha_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_incl left right ->
    rel_incl (alpha T left) (alpha T right).
```

## `bag_closed_rel_equiv_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:266`](../RelationalAlgebraFacts.v#L266)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_closed_rel_equiv_transport :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    BagClosed T left ->
    BagClosed T right.
```

## `bag_closed_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:279`](../RelationalAlgebraFacts.v#L279)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_union :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows \/ right rows).
```

## `bag_closed_exists`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:295`](../RelationalAlgebraFacts.v#L295)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_exists :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => exists index, family index rows).
```

## `ordered_rows_equiv_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:310`](../RelationalAlgebraFacts.v#L310)

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `cardinality` (rank 44)

Search aliases: `relational algebra`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_length :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    length left = length right.
```

## `ordered_rows_equiv_occ`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:320`](../RelationalAlgebraFacts.v#L320)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_occ :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    forall row,
      Oeset.nb_occ (OTuple T) row left =
      Oeset.nb_occ (OTuple T) row right.
```

## `rows_bag_occ`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:332`](../RelationalAlgebraFacts.v#L332)

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_occ :
  forall (T : Tuple.Rcd) (rows : list (tuple T)) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T rows) =
    Oeset.nb_occ (OTuple T) row rows.
```

## `bag_eq_iff_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:342`](../RelationalAlgebraFacts.v#L342)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 26)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_eq_iff_occurrences :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right <->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right.
```

## `bag_eq_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:355`](../RelationalAlgebraFacts.v#L355)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 26), `cardinality` (rank 52)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_eq_cardinal :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
    Febag.cardinal (Fecol.CBag (CTuple T)) right.
```

## `bag_occurrences_disjoint_of_boolean_separator`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:372`](../RelationalAlgebraFacts.v#L372)

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 12)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_occurrences_disjoint_of_boolean_separator :
  forall (T : Tuple.Rcd)
      (left right : SqlBagAbstraction.bagT T)
      (separate : tuple T -> bool),
    (forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left <> 0%N ->
      separate row = false) ->
    (forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right <> 0%N ->
      separate row = true) ->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left = 0%N \/
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right = 0%N.
```

## `bag_filter_congr_on_support`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:412`](../RelationalAlgebraFacts.v#L412)

Purpose/direction: Transports finite-bag filtering across bag-equal inputs when two predicates agree on semantic tuple occurrences in the left support.

Applicability: Use when an environment-dependent row predicate has been proved equal to another predicate only on represented input rows; input bags need be semantically bag-equal, not Leibniz-equal.

Important premises: Retain input `bag_eq`, positive left multiplicity, semantic tuple equality, and cross-predicate agreement; no equality is required outside the represented left support.

Cross-index: `filter` (rank 30), `bag` (rank 20)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_filter_congr_on_support :
  forall (T : Tuple.Rcd)
      (left_keep right_keep : tuple T -> bool)
      (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    (forall left_row right_row,
      (Febag.nb_occ (Fecol.CBag (CTuple T)) left_row left >= 1)%N ->
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      left_keep left_row = right_keep right_row) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) left_keep left)
      (Febag.filter (Fecol.CBag (CTuple T)) right_keep right).
```

## `rows_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:430`](../RelationalAlgebraFacts.v#L430)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T)),
    Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T rows) =
    N.of_nat (length rows).
```

## `query_same_rows_as_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:440`](../RelationalAlgebraFacts.v#L440)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag rows bag ->
    Febag.cardinal (Fecol.CBag (CTuple T)) bag =
    N.of_nat (length rows).
```

## `query_same_rows_as_bag_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:454`](../RelationalAlgebraFacts.v#L454)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36), `cardinality` (rank 44)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_length :
  forall (T : Tuple.Rcd) (first second : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag first bag ->
    query_same_rows_as_bag second bag ->
    length first = length second.
```

## `query_same_rows_as_bag_iff_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:468`](../RelationalAlgebraFacts.v#L468)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_iff_occurrences :
  forall (T : Tuple.Rcd) (rows : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag rows bag <->
    forall row,
      Oeset.nb_occ (OTuple T) row rows =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
```

## `query_same_rows_as_bag_semantic_permut_elements`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:520`](../RelationalAlgebraFacts.v#L520)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_semantic_permut_elements :
  forall (T : Tuple.Rcd) rows bag,
    @query_same_rows_as_bag T rows bag ->
    _permut
      (fun left right => Oeset.compare (OTuple T) left right = Eq)
      rows (Febag.elements (Fecol.CBag (CTuple T)) bag).
```

## `query_same_rows_as_bag_Forall_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:540`](../RelationalAlgebraFacts.v#L540)

Purpose/direction: Transports the displayed hypotheses and conclusion for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_Forall_transport :
  forall (T : Tuple.Rcd) (property : tuple T -> Prop) first second bag,
    tuple_property_semantic_invariant property ->
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    Forall property first ->
    Forall property second.
```

## `query_same_rows_as_bag_filter`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:570`](../RelationalAlgebraFacts.v#L570)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 30), `bag` (rank 36)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_filter :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool) rows bag,
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    @query_same_rows_as_bag T rows bag ->
    @query_same_rows_as_bag T (filter keep rows)
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag).
```

## `query_canonical_rows_same_as_bag`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:596`](../RelationalAlgebraFacts.v#L596)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_canonical_rows_same_as_bag :
  forall (T : Tuple.Rcd) rows bag,
    @query_same_rows_as_bag T rows bag ->
    @query_same_rows_as_bag T (@query_canonical_rows T rows) bag.
```

## `query_canonical_rows_length_between`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:610`](../RelationalAlgebraFacts.v#L610)

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 44)

Search aliases: `relational algebra`, `cardinality`

```rocq
Lemma query_canonical_rows_length_between :
  forall (T : Tuple.Rcd) first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    List.length (@query_canonical_rows T first) =
    List.length (@query_canonical_rows T second).
```

## `query_canonical_rows_filter_permut`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:626`](../RelationalAlgebraFacts.v#L626)

Purpose/direction: States the query canonical rows filter permut law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 30), `bag` (rank 28)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_canonical_rows_filter_permut :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool) left right original,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    @query_same_rows_as_bag T left (rows_bag T original) ->
    @query_same_rows_as_bag T right
      (rows_bag T (List.filter keep original)) ->
    Oeset.permut (OTuple T)
      (List.filter keep (@query_canonical_rows T left))
      (@query_canonical_rows T right).
```

## `query_same_rows_as_filtered_bag_preimage`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:690`](../RelationalAlgebraFacts.v#L690)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_filtered_bag_preimage :
  forall (T : Tuple.Rcd) rows bag (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    @query_same_rows_as_bag T rows
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag) ->
    exists input_rows,
      @query_same_rows_as_bag T input_rows bag /\
      filter keep input_rows = rows.
```

## `double_projection_bag_eq`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:763`](../RelationalAlgebraFacts.v#L763)

Purpose/direction: States the double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 36), `bag` (rank 26)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma double_projection_bag_eq :
  forall (T : Tuple.Rcd) (env : Env.env T)
      (outer_left inner_left outer_right inner_right : _select_list T)
      (bag : SqlQuerySemantics.bagT T),
    (forall row,
      Oeset.compare (OTuple T)
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_left)))
          (@Select_List T outer_left))
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_right)))
          (@Select_List T outer_right)) = Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row => projection T (env_t T env row) (@Select_List T outer_left))
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          (fun row => projection T (env_t T env row) (@Select_List T inner_left))
          bag))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row => projection T (env_t T env row) (@Select_List T outer_right))
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          (fun row => projection T (env_t T env row) (@Select_List T inner_right))
          bag)).
```

## `oeset_nb_occ_of_NoDupA`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:860`](../RelationalAlgebraFacts.v#L860)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`

```rocq
Lemma oeset_nb_occ_of_NoDupA :
  forall (A : Type) (ordered : Oeset.Rcd A) values,
    SetoidList.NoDupA
      (fun left right => Oeset.compare ordered left right = Eq) values ->
    forall value,
      Oeset.nb_occ ordered value values =
      if Oeset.mem_bool ordered value values then 1%N else 0%N.
```

## `oeset_NoDupA_same_support_same_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:896`](../RelationalAlgebraFacts.v#L896)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`

```rocq
Lemma oeset_NoDupA_same_support_same_occurrences :
  forall (A : Type) (ordered : Oeset.Rcd A) left right,
    SetoidList.NoDupA
      (fun first second => Oeset.compare ordered first second = Eq) left ->
    SetoidList.NoDupA
      (fun first second => Oeset.compare ordered first second = Eq) right ->
    (forall value,
      Oeset.mem_bool ordered value left =
      Oeset.mem_bool ordered value right) ->
    forall value,
      Oeset.nb_occ ordered value left = Oeset.nb_occ ordered value right.
```

## `rows_bag_eq_of_nodup_support_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:918`](../RelationalAlgebraFacts.v#L918)

Purpose/direction: Establishes the displayed duplicate-freedom property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 26)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_eq_of_nodup_support_rel :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    SetoidList.NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left ->
    SetoidList.NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      right ->
    bag_eq T (rows_bag T left) (rows_bag T right).
```

## `alpha_membership_iff_occurrence_representative`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:970`](../RelationalAlgebraFacts.v#L970)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma alpha_membership_iff_occurrence_representative :
  forall (T : Tuple.Rcd) (observations : list (tuple T) -> Prop)
         (bag : SqlBagAbstraction.bagT T),
    alpha T observations bag <->
    exists rows,
      observations rows /\
      forall row,
        Oeset.nb_occ (OTuple T) row rows =
        Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
```

## `query_set_union_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1003`](../RelationalAlgebraFacts.v#L1003)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
```

## `query_set_union_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1016`](../RelationalAlgebraFacts.v#L1016)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_union_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1029`](../RelationalAlgebraFacts.v#L1029)

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Union left right)
             (query_set_bag Union right left).
```

## `query_set_union_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1040`](../RelationalAlgebraFacts.v#L1040)

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Union (query_set_bag Union first second) third)
      (query_set_bag Union first (query_set_bag Union second third)).
```

## `query_set_union_max_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1052`](../RelationalAlgebraFacts.v#L1052)

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag UnionMax left right)
             (query_set_bag UnionMax right left).
```

## `query_set_union_max_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1063`](../RelationalAlgebraFacts.v#L1063)

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (query_set_bag UnionMax first second) third)
      (query_set_bag UnionMax first
        (query_set_bag UnionMax second third)).
```

## `query_set_union_max_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1077`](../RelationalAlgebraFacts.v#L1077)

Purpose/direction: Establishes idempotence for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag UnionMax bag bag) bag.
```

## `query_set_union_max_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1087`](../RelationalAlgebraFacts.v#L1087)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
```

## `query_set_union_max_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1100`](../RelationalAlgebraFacts.v#L1100)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_inter_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1113`](../RelationalAlgebraFacts.v#L1113)

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Inter left right)
             (query_set_bag Inter right left).
```

## `query_set_inter_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1124`](../RelationalAlgebraFacts.v#L1124)

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Inter
        (query_set_bag Inter first second) third)
      (query_set_bag Inter first
        (query_set_bag Inter second third)).
```

## `query_set_inter_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1138`](../RelationalAlgebraFacts.v#L1138)

Purpose/direction: Establishes idempotence for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag Inter bag bag) bag.
```

## `query_set_inter_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1148`](../RelationalAlgebraFacts.v#L1148)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_inter_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1161`](../RelationalAlgebraFacts.v#L1161)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_union_max_inter_absorb`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1174`](../RelationalAlgebraFacts.v#L1174)

Purpose/direction: Establishes the displayed absorption law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_inter_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag UnionMax left (query_set_bag Inter left right))
      left.
```

## `query_set_inter_union_max_absorb`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1186`](../RelationalAlgebraFacts.v#L1186)

Purpose/direction: Establishes the displayed absorption law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_union_max_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Inter left (query_set_bag UnionMax left right))
      left.
```

## `query_set_diff_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1198`](../RelationalAlgebraFacts.v#L1198)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_diff_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1211`](../RelationalAlgebraFacts.v#L1211)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_diff_self_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1224`](../RelationalAlgebraFacts.v#L1224)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_self_empty :
  forall bag : bagT,
    bag_eq T (query_set_bag Diff bag bag)
             (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_diff_union_cancel_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1235`](../RelationalAlgebraFacts.v#L1235)

Purpose/direction: Establishes the displayed cancellation direction for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_union_cancel_right :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) right)
      left.
```

## `query_set_diff_union_cancel_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1247`](../RelationalAlgebraFacts.v#L1247)

Purpose/direction: Establishes the displayed cancellation direction for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_union_cancel_left :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) left)
      right.
```

## `query_cross_join_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1259`](../RelationalAlgebraFacts.v#L1259)

Purpose/direction: States the exact empty-input or empty-result law for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 24), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_cross_join_empty :
  forall bag : bagT,
    bag_eq T
      (query_cross_join_bag
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))) /\
    bag_eq T
      (query_cross_join_bag bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_natural_join_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1285`](../RelationalAlgebraFacts.v#L1285)

Purpose/direction: States the exact empty-input or empty-result law for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 26), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_natural_join_empty :
  forall (value_is_null : value T -> bool) (bag : bagT),
    bag_eq T
      (query_natural_join_bag value_is_null
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))) /\
    bag_eq T
      (query_natural_join_bag value_is_null bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_distinct_bag_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1312`](../RelationalAlgebraFacts.v#L1312)

Purpose/direction: States the exact empty-input or empty-result law for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_empty :
  bag_eq T
    (query_distinct_bag (Febag.empty (Fecol.CBag (CTuple T))))
    (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_distinct_bag_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1330`](../RelationalAlgebraFacts.v#L1330)

Purpose/direction: Establishes idempotence for the declared bag multiplicity operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_idempotent :
  forall bag : bagT,
    bag_eq T (query_distinct_bag (query_distinct_bag bag))
             (query_distinct_bag bag).
```

## `query_cross_join_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1348`](../RelationalAlgebraFacts.v#L1348)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 24), `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_cross_join_bag_cardinal :
  forall left right : bagT,
    Febag.cardinal (Fecol.CBag (CTuple T))
      (query_cross_join_bag left right) =
    (Febag.cardinal (Fecol.CBag (CTuple T)) left *
     Febag.cardinal (Fecol.CBag (CTuple T)) right)%N.
```

## `query_natural_join_bag_cardinal_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1382`](../RelationalAlgebraFacts.v#L1382)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 26), `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `join`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_natural_join_bag_cardinal_le :
  forall (value_is_null : value T -> bool) (left right : bagT),
    (Febag.cardinal (Fecol.CBag (CTuple T))
       (query_natural_join_bag value_is_null left right) <=
     Febag.cardinal (Fecol.CBag (CTuple T)) left *
     Febag.cardinal (Fecol.CBag (CTuple T)) right)%N.
```

## `query_join_matched_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1431`](../RelationalAlgebraFacts.v#L1431)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma query_join_matched_sources_length_le :
  forall (left : tuple T) rights flags,
    length (query_join_matched_sources T left rights flags) <= length rights.
```

## `query_join_left_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1440`](../RelationalAlgebraFacts.v#L1440)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Lemma query_join_left_sources_length_le :
  forall kind lefts rights matrix,
    length (query_join_left_sources T kind lefts rights matrix) <=
    match kind with
    | QueryJoinInner | QueryJoinRight => length lefts * length rights
    | QueryJoinLeft | QueryJoinFull =>
        length lefts * Nat.max 1 (length rights)
    | QueryJoinSemi | QueryJoinAnti => length lefts
    end.
```

## `query_join_unmatched_right_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1471`](../RelationalAlgebraFacts.v#L1471)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma query_join_unmatched_right_sources_length_le :
  forall index rights matrix,
    length
      (query_join_unmatched_right_sources_from T index rights matrix) <=
    length rights.
```

## `query_join_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1483`](../RelationalAlgebraFacts.v#L1483)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Lemma query_join_sources_length_le :
  forall kind lefts rights matrix,
    length (query_join_sources T kind lefts rights matrix) <=
    match kind with
    | QueryJoinInner => length lefts * length rights
    | QueryJoinLeft => length lefts * Nat.max 1 (length rights)
    | QueryJoinRight => length lefts * length rights + length rights
    | QueryJoinFull =>
        length lefts * Nat.max 1 (length rights) + length rights
    | QueryJoinSemi | QueryJoinAnti => length lefts
    end.
```

## `query_join_full_sources_member_iff`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1741`](../RelationalAlgebraFacts.v#L1741)

Purpose/direction: Gives necessary and sufficient conditions for outer-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 24)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `join`

```rocq
Theorem query_join_full_sources_member_iff :
  forall (matches : tuple T -> tuple T -> bool) lefts rights output,
    In output
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun left => map (matches left) rights) lefts)) <->
    (exists left right,
      In left lefts /\
      In right rights /\
      matches left right = true /\
      JoinSourceMatched T (join_tuple T left right) = output) \/
    (exists left,
      In left lefts /\
      (forall right, In right rights -> matches left right = false) /\
      JoinSourceLeft T left = output) \/
    (exists right,
      In right rights /\
      (forall left, In left lefts -> matches left right = false) /\
      JoinSourceRight T right = output).
```

## `query_join_full_projected_support_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1803`](../RelationalAlgebraFacts.v#L1803)

Purpose/direction: States the query join full projected support rel law for outer-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 24), `bag` (rank 34)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `join`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_join_full_projected_support_rel :
  forall (left_rel right_rel output_rel : tuple T -> tuple T -> Prop)
      (left_match right_match : tuple T -> tuple T -> bool)
      (left_emit right_emit : query_join_source T -> tuple T)
      left_rows left_rows' right_rows right_rows',
    list_support_rel left_rel left_rows left_rows' ->
    list_support_rel right_rel right_rows right_rows' ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      left_match left right = right_match left' right') ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      output_rel
        (left_emit
          (JoinSourceMatched T (join_tuple T left right)))
        (right_emit
          (JoinSourceMatched T (join_tuple T left' right')))) ->
    (forall left left',
      left_rel left left' ->
      output_rel
        (left_emit (JoinSourceLeft T left))
        (right_emit (JoinSourceLeft T left'))) ->
    (forall right right',
      right_rel right right' ->
      output_rel
        (left_emit (JoinSourceRight T right))
        (right_emit (JoinSourceRight T right'))) ->
    list_support_rel output_rel
      (map left_emit
        (query_join_sources T QueryJoinFull left_rows right_rows
          (map (fun left => map (left_match left) right_rows) left_rows)))
      (map right_emit
        (query_join_sources T QueryJoinFull left_rows' right_rows'
          (map
            (fun left => map (right_match left) right_rows') left_rows'))).
```

## `query_bag_filter_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1966`](../RelationalAlgebraFacts.v#L1966)

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 4), `bag` (rank 12)

Search aliases: `relational algebra`, `set operation`, `UNION`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_union :
  forall (keep : tuple T -> bool) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) keep
        (query_set_bag Union left right))
      (query_set_bag Union
        (Febag.filter (Fecol.CBag (CTuple T)) keep left)
        (Febag.filter (Fecol.CBag (CTuple T)) keep right)).
```

## `query_bag_map_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1989`](../RelationalAlgebraFacts.v#L1989)

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 12)

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_map_union :
  forall (mapping : tuple T -> tuple T) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping (query_set_bag Union left right))
      (query_set_bag Union
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping left)
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping right)).
```

## `query_bag_map_congr`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2031`](../RelationalAlgebraFacts.v#L2031)

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 12)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_bag_map_congr :
  forall (mapping : tuple T -> tuple T) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    bag_eq T left right ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping left)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping right).
```

## `query_bag_filter_commute`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2056`](../RelationalAlgebraFacts.v#L2056)

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 6), `bag` (rank 14)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_commute :
  forall (first second : tuple T -> bool) (bag : bagT),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      first left = first right) ->
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      second left = second right) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) first
        (Febag.filter (Fecol.CBag (CTuple T)) second bag))
      (Febag.filter (Fecol.CBag (CTuple T)) second
        (Febag.filter (Fecol.CBag (CTuple T)) first bag)).
```

## `query_bag_filter_map_fusion`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2083`](../RelationalAlgebraFacts.v#L2083)

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 2), `bag` (rank 10)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_map_fusion :
  forall (keep : tuple T -> bool) (mapping : tuple T -> tuple T) (bag : bagT),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      Oeset.compare (OTuple T) (mapping left) (mapping right) = Eq) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) keep
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping bag))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping
        (Febag.filter (Fecol.CBag (CTuple T))
          (fun row => keep (mapping row)) bag)).
```

## `query_bag_map_pairwise_equiv_of_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2119`](../RelationalAlgebraFacts.v#L2119)

Purpose/direction: Equates two mapped bags of equal cardinality when every reached left mapped row is semantically equal to every reached right one.

Applicability: Use for constant-observation projections after equal bag cardinality and pairwise equality on actual representatives are established.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 18), `cardinality` (rank 10)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_bag_map_pairwise_equiv_of_cardinal :
  forall (left_map right_map : tuple T -> tuple T) (left right : bagT),
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
      Febag.cardinal (Fecol.CBag (CTuple T)) right ->
    (forall left_row right_row,
      In left_row (Febag.elements (Fecol.CBag (CTuple T)) left) ->
      In right_row (Febag.elements (Fecol.CBag (CTuple T)) right) ->
      Oeset.compare (OTuple T) (left_map left_row) (right_map right_row) =
        Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        left_map left)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        right_map right).
```

## `query_cross_join_bag_singleton_right_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2171`](../RelationalAlgebraFacts.v#L2171)

Purpose/direction: Normalizes a CROSS JOIN with one right bag occurrence to the corresponding multiplicity-preserving row map of the left bag.

Applicability: Use only for a semantic singleton bag on the right; lift to a query outcome separately so child and projection errors remain observable.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 10), `bag` (rank 14)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_cross_join_bag_singleton_right_map :
  forall (left : bagT) right_row,
    bag_eq T
      (query_cross_join_bag left
        (Febag.singleton (Fecol.CBag (CTuple T)) right_row))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun left_row => join_tuple T left_row right_row) left).
```

## `eval_join_row_conditions_acceptance_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2345`](../RelationalAlgebraFacts.v#L2345)

Purpose/direction: Characterizes one left row's complete join-condition evaluation as the successful Boolean acceptance map over right rows.

Applicability: Use after establishing the exact acceptance contract for every right row that occurs in the displayed list; order and duplicates are retained by `map`.

Important premises: Supply `join_condition_acceptance_exact_at` for every right-row occurrence; the conclusion retains list order and duplicate flags.

Cross-index: `outcome` (rank 14), `runtime` (rank 14), `join` (rank 6)

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_join_row_conditions_acceptance_exact :
  forall env predicate left rights (accepted : tuple T -> bool),
    (forall right,
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted right)) ->
    forall outcome,
      @eval_join_row_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate left rights outcome <->
      outcome = SqlSuccess (map accepted rights).
```

## `eval_join_conditions_acceptance_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2398`](../RelationalAlgebraFacts.v#L2398)

Purpose/direction: Lifts pairwise exact join acceptance to the complete row-major successful condition matrix, excluding condition errors.

Applicability: Use after establishing exact acceptance for every reached left/right pair; the conclusion is the literal row-major matrix, not a bag.

Important premises: Supply `join_condition_acceptance_exact_at` for every reached pair from both input lists; the resulting matrix remains row-major.

Cross-index: `outcome` (rank 10), `runtime` (rank 10), `join` (rank 4)

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_join_conditions_acceptance_exact :
  forall env predicate lefts rights
      (accepted : tuple T -> tuple T -> bool),
    (forall left right,
      In left lefts ->
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)) ->
    forall outcome,
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate lefts rights outcome <->
      outcome =
        SqlSuccess
          (map (fun left => map (accepted left) rights) lefts).
```

## `project_join_sources_outcome_exact_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2467`](../RelationalAlgebraFacts.v#L2467)

Purpose/direction: Lifts exact projection of every reached matched or padded join source to one ordered successful map over the source list.

Applicability: Use after proving exact successful projection only for sources in the reached source list; matched and both NULL-padded source forms must remain covered.

Important premises: Supply exact successful projection for every source occurring in the source list; do not omit matched, left-padded, or right-padded constructors that can be reached.

Cross-index: `outcome` (rank 10), `runtime` (rank 10), `projection` (rank 4), `join` (rank 4)

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma project_join_sources_outcome_exact_map :
  forall env matched_select left_select right_select sources
      (emit : query_join_source T -> tuple T),
    (forall source,
      In source sources ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env
      matched_select left_select right_select sources =
    SqlSuccess (map emit sources).
```

## `eval_join_bag_safe_of_acceptance_projection_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2496`](../RelationalAlgebraFacts.v#L2496)

Purpose/direction: Combines total exact pair acceptance with exact matched/padded projection to construct a successful join bag and rule out every local join error for any modeled join kind.

Applicability: Use to discharge local join success and no-error obligations after providing total pairwise acceptance and total source-projection contracts; child-query errors are outside this bag-local theorem.

Important premises: Both universal contracts are mandatory: exact acceptance for every left/right pair and exact successful projection for every possible join source.  The conclusion is bag-local and does not establish child-query safety.

Cross-index: `outcome` (rank 2), `runtime` (rank 2), `projection` (rank 6), `join` (rank 0), `bag` (rank 6)

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_join_bag_safe_of_acceptance_projection_exact :
  forall env kind predicate matched_select left_select right_select
      (accepted : tuple T -> tuple T -> bool)
      (emit : query_join_source T -> tuple T)
      left_bag right_bag,
    (forall left right,
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)) ->
    (forall source,
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    (exists output_bag,
      @eval_join_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env kind predicate matched_select left_select right_select
        left_bag right_bag (SqlSuccess output_bag)) /\
    (forall error,
      ~ @eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          env kind predicate matched_select left_select right_select
          left_bag right_bag (SqlError error)).
```

## `eval_join_row_conditions_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2588`](../RelationalAlgebraFacts.v#L2588)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 26), `cardinality` (rank 44)

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma eval_join_row_conditions_success_length :
  forall env predicate left rights flags,
    @eval_join_row_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate left rights (SqlSuccess flags) ->
    length flags = length rights.
```

## `eval_join_conditions_success_dimensions`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2601`](../RelationalAlgebraFacts.v#L2601)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when the goal or a hypothesis matches the `eval_join_conditions_success_dimensions` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 26)

Search aliases: `relational algebra`, `join`

```rocq
Lemma eval_join_conditions_success_dimensions :
  forall env predicate lefts rights matrix,
    @eval_join_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate lefts rights (SqlSuccess matrix) ->
    length matrix = length lefts /\
    Forall (fun flags => length flags = length rights) matrix.
```

## `query_same_rows_as_bag_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2807`](../RelationalAlgebraFacts.v#L2807)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_map :
  forall (mapping : tuple T -> tuple T) rows bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map mapping rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping bag).
```

## `query_join_left_functional_projection_bag_on_representatives`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2842`](../RelationalAlgebraFacts.v#L2842)

Purpose/direction: States the query join left functional projection bag on representatives law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 34), `join` (rank 24), `bag` (rank 34)

Search aliases: `relational algebra`, `functional LEFT JOIN`, `at-most-one match`, `nullable unmatched key`, `left multiplicity`, `join`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_join_left_functional_projection_bag_on_representatives :
  forall env predicate matched_select left_select right_select
      (project emit : tuple T -> tuple T) left_bag right_bag joined_bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (project first) (project second) = Eq) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    (forall left_rows right_rows matrix,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate left_rows right_rows (SqlSuccess matrix) ->
      Forall
        (fun flags =>
          (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
        matrix) ->
    (forall left_rows right_rows left right output,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      In left left_rows ->
      In right right_rows ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceMatched T (join_tuple T left right)) =
      SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    (forall left_rows left output,
      query_same_rows_as_bag left_rows left_bag ->
      In left left_rows ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceLeft T left) = SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env QueryJoinLeft predicate matched_select left_select right_select
      left_bag right_bag (SqlSuccess joined_bag) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        project joined_bag)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        emit left_bag).
```

## `project_join_sources_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2944`](../RelationalAlgebraFacts.v#L2944)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 36), `join` (rank 26), `cardinality` (rank 44)

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma project_join_sources_success_length :
  forall env matched_select left_select right_select sources output,
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env matched_select left_select right_select
      sources = SqlSuccess output ->
    length output = length sources.
```

## `eval_join_bag_success_cardinal_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2964`](../RelationalAlgebraFacts.v#L2964)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 24), `bag` (rank 34), `cardinality` (rank 50)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_join_bag_success_cardinal_le :
  forall env kind predicate matched_select left_select right_select
         left_bag right_bag output_bag,
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env kind
      predicate matched_select left_select right_select left_bag right_bag
      (SqlSuccess output_bag) ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) output_bag <=
     match kind with
     | QueryJoinInner =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinLeft =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         N.max 1 (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag)
     | QueryJoinRight =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag +
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinFull =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         N.max 1 (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag) +
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinSemi | QueryJoinAnti =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag
     end)%N.
```

## `query_grouping_sets_actual_success_bags_congr`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3034`](../RelationalAlgebraFacts.v#L3034)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 44), `bag` (rank 36)

Search aliases: `relational algebra`, `grouping sets`, `GROUP BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_grouping_sets_actual_success_bags_congr :
  forall env grouping_sets left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_GroupingSets grouping_sets left))
      (success_bags env (QExpr_GroupingSets grouping_sets right)).
```

## `query_expr_equiv_implies_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3060`](../RelationalAlgebraFacts.v#L3060)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_implies_success_bags :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_expr_outcome_equiv_implies_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3077`](../RelationalAlgebraFacts.v#L3077)

Purpose/direction: Projects fixed-environment error-preserving ordered equivalence to equality of possible successful bags, including the error-only case.

Applicability: Use to forget successful row order at one environment; the theorem deliberately drops error observations, so retain a separate error proof when rebuilding parent outcome equivalence.

Important premises: Supply the exact fixed-environment child outcome equivalence; this conclusion preserves successful multiplicity but intentionally does not carry the error relation.

Cross-index: `outcome` (rank 46), `runtime` (rank 52), `bag` (rank 22)

Search aliases: `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_implies_success_bags :
  forall env left right,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_set_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3090`](../RelationalAlgebraFacts.v#L3090)

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_set_success_bags_congr_of_query_expr_equiv :
  forall env operation left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_Set operation left right))
      (success_bags env (QExpr_Set operation left' right')).
```

## `query_natural_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3114`](../RelationalAlgebraFacts.v#L3114)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 26), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_natural_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_NaturalJoin left right))
      (success_bags env (QExpr_NaturalJoin left' right')).
```

## `query_cross_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3132`](../RelationalAlgebraFacts.v#L3132)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 24), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_cross_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_CrossJoin left right))
      (success_bags env (QExpr_CrossJoin left' right')).
```

## `query_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3150`](../RelationalAlgebraFacts.v#L3150)

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 26), `bag` (rank 36)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_join_success_bags_congr_of_query_expr_equiv :
  forall env kind predicate matched_select left_select right_select
         left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left' right')).
```

## `query_cross_join_union_right_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3177`](../RelationalAlgebraFacts.v#L3177)

Purpose/direction: Distributes CROSS JOIN over right-hand UNION ALL at the possible-bag layer while preserving duplicate multiplicity.

Applicability: Use for right-hand UNION ALL distribution only after proving both displayed sort equalities and possible-bag functionality of the duplicated left child.

Important premises: Both set-operation sort equalities and pairwise possible-bag functionality of the duplicated left child are mandatory; UNION is multiplicity-preserving UNION ALL here.

Cross-index: `join` (rank 22), `bag` (rank 34)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_cross_join_union_right_success_bags :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    rel_equiv
      (success_bags env
        (QExpr_CrossJoin left (QExpr_Set Union first second)))
      (success_bags env
        (QExpr_Set Union
          (QExpr_CrossJoin left first)
          (QExpr_CrossJoin left second))).
```
