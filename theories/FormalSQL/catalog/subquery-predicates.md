# Predicate subqueries and correlation

Route here for: EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality.

This focused catalog contains 31 declarations routed at declaration granularity from `SubqueryFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `interp_exists_quant_not_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:21`](../SubqueryFacts.v#L21)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma interp_exists_quant_not_true_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    Bool.existsb Bool3 interpretation values <> true3 <->
    Forall (fun value => interpretation value <> true3) values.
```

## `interp_forall_quant_not_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:38`](../SubqueryFacts.v#L38)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma interp_forall_quant_not_false_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    Bool.forallb Bool3 interpretation values <> false3 <->
    Forall (fun value => interpretation value <> false3) values.
```

## `interp_exists_quant_unknown_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:56`](../SubqueryFacts.v#L56)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma interp_exists_quant_unknown_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    interp_quant Bool3 Exists_F interpretation values = unknown3 <->
    Exists (fun value => interpretation value = unknown3) values /\
    Forall (fun value => interpretation value <> true3) values.
```

## `interp_forall_quant_unknown_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:93`](../SubqueryFacts.v#L93)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma interp_forall_quant_unknown_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    interp_quant Bool3 Forall_F interpretation values = unknown3 <->
    Exists (fun value => interpretation value = unknown3) values /\
    Forall (fun value => interpretation value <> false3) values.
```

## `interp_quant_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:130`](../SubqueryFacts.v#L130)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `interp_quant_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma interp_quant_empty : forall (B : Bool.Rcd) which_quantifier
    (A : Type) (interpretation : A -> Bool.b B),
  interp_quant B which_quantifier interpretation [] =
  match which_quantifier with
  | Forall_F => Bool.true B
  | Exists_F => Bool.false B
  end.
```

## `quantified_rows_exists_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:196`](../SubqueryFacts.v#L196)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_exists_true_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Exists_F which_predicate arguments subquery rows =
      Bool.true (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.true (B T).
```

## `quantified_rows_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:209`](../SubqueryFacts.v#L209)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_exists_false_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Exists_F which_predicate arguments subquery rows =
      Bool.false (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.false (B T).
```

## `quantified_rows_forall_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:222`](../SubqueryFacts.v#L222)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_forall_true_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Forall_F which_predicate arguments subquery rows =
      Bool.true (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.true (B T).
```

## `quantified_rows_forall_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:235`](../SubqueryFacts.v#L235)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_forall_false_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Forall_F which_predicate arguments subquery rows =
      Bool.false (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.false (B T).
```

## `in_rows_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:248`](../SubqueryFacts.v#L248)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_true_iff : forall env select_items rows,
  in_rows_truth env select_items rows = Bool.true (B T) <->
  exists row,
    In row (query_canonical_rows rows) /\
    in_row_truth env select_items row = Bool.true (B T).
```

## `in_rows_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:258`](../SubqueryFacts.v#L258)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_false_iff : forall env select_items rows,
  in_rows_truth env select_items rows = Bool.false (B T) <->
  forall row,
    In row (query_canonical_rows rows) ->
    in_row_truth env select_items row = Bool.false (B T).
```

## `query_canonical_rows_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:268`](../SubqueryFacts.v#L268)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `query_canonical_rows_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma query_canonical_rows_empty :
  @query_canonical_rows T [] = [].
```

## `eval_formula_quant_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:275`](../SubqueryFacts.v#L275)

Purpose/direction: Gives necessary and sufficient conditions for scalar-subquery quantified-comparison evaluation.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime` (rank 48), `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `scalar subquery`, `SINGLE_VALUE`, `CardinalityViolation`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_formula_quant_error_iff :
  forall env which_quantifier which_predicate arguments subquery error,
    eval_formula env
      (FExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlError error) <->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = Some error \/
    (first_runtime_error
       (@eval_aggterm_runtime_error T
         symbol_runtime_error aggregate_runtime_error env)
       arguments = None /\
     eval_query env subquery (SqlError error)).
```

## `eval_formula_quant_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:299`](../SubqueryFacts.v#L299)

Purpose/direction: Gives necessary and sufficient conditions for scalar-subquery quantified-comparison evaluation.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `scalar subquery`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_formula_quant_success_iff :
  forall env which_quantifier which_predicate arguments subquery truth,
    eval_formula env
      (FExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlSuccess truth) <->
    exists rows,
      first_runtime_error
        (@eval_aggterm_runtime_error T
          symbol_runtime_error aggregate_runtime_error env)
        arguments = None /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = quantified_rows_truth env which_quantifier which_predicate
        arguments subquery rows.
```

## `eval_formula_quant_forall_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:320`](../SubqueryFacts.v#L320)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_quant_forall_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_formula_quant_forall_empty :
  forall env which_predicate arguments subquery,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env
      (FExpr_Quant Forall_F which_predicate arguments subquery)
      (SqlSuccess (Bool.true (B T))).
```

## `eval_formula_quant_exists_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:339`](../SubqueryFacts.v#L339)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_quant_exists_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_formula_quant_exists_empty :
  forall env which_predicate arguments subquery,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env
      (FExpr_Quant Exists_F which_predicate arguments subquery)
      (SqlSuccess (Bool.false (B T))).
```

## `eval_formula_in_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:358`](../SubqueryFacts.v#L358)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime` (rank 48), `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_formula_in_error_iff :
  forall env select_items subquery error,
    eval_formula env (FExpr_In select_items subquery) (SqlError error) <->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = Some error \/
    (first_runtime_error
       (@eval_select_runtime_error T
         symbol_runtime_error aggregate_runtime_error env)
       select_items = None /\
     eval_query env subquery (SqlError error)).
```

## `eval_formula_in_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:380`](../SubqueryFacts.v#L380)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma eval_formula_in_success_iff :
  forall env select_items subquery truth,
    eval_formula env (FExpr_In select_items subquery) (SqlSuccess truth) <->
    exists rows,
      first_runtime_error
        (@eval_select_runtime_error T
          symbol_runtime_error aggregate_runtime_error env)
        select_items = None /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = in_rows_truth env select_items rows.
```

## `eval_formula_in_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:398`](../SubqueryFacts.v#L398)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_in_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma eval_formula_in_empty :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env (FExpr_In select_items subquery)
      (SqlSuccess (Bool.false (B T))).
```

## `eval_formula_exists_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:416`](../SubqueryFacts.v#L416)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime` (rank 48), `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_formula_exists_error_iff : forall env subquery error,
  eval_formula env (FExpr_Exists subquery) (SqlError error) <->
  eval_query env subquery (SqlError error).
```

## `eval_formula_exists_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:425`](../SubqueryFacts.v#L425)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_formula_exists_success_iff : forall env subquery truth,
  eval_formula env (FExpr_Exists subquery) (SqlSuccess truth) <->
  (truth = Bool.false (B T) /\ eval_query env subquery (SqlSuccess [])) \/
  (truth = Bool.true (B T) /\
   exists row rows, eval_query env subquery (SqlSuccess (row :: rows))).
```

## `eval_formula_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:441`](../SubqueryFacts.v#L441)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_formula_exists_false_iff : forall env subquery,
  eval_formula env (FExpr_Exists subquery)
    (SqlSuccess (Bool.false (B T))) <->
  eval_query env subquery (SqlSuccess []).
```

## `eval_formula_exists_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:455`](../SubqueryFacts.v#L455)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 44)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_formula_exists_true_iff : forall env subquery,
  eval_formula env (FExpr_Exists subquery)
    (SqlSuccess (Bool.true (B T))) <->
  exists row rows, eval_query env subquery (SqlSuccess (row :: rows)).
```

## `eval_formula_quant_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:473`](../SubqueryFacts.v#L473)

Purpose/direction: Transports or composes scalar-subquery quantified-comparison evaluation across the declared equivalence.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: every explicit antecedent (`->`) in the declaration is required; this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `scalar subquery`, `subquery`, `quantified predicate`, `ANY/ALL`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_quant_subquery_congr :
  forall env which_quantifier which_predicate arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env
        (FExpr_Quant which_quantifier which_predicate arguments left) outcome <->
      eval_formula env
        (FExpr_Quant which_quantifier which_predicate arguments right) outcome.
```

## `eval_formula_in_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:500`](../SubqueryFacts.v#L500)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_in_subquery_congr :
  forall env select_items left right,
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env (FExpr_In select_items left) outcome <->
      eval_formula env (FExpr_In select_items right) outcome.
```

## `eval_formula_exists_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:522`](../SubqueryFacts.v#L522)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_exists_subquery_congr :
  forall env left right,
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env (FExpr_Exists left) outcome <->
      eval_formula env (FExpr_Exists right) outcome.
```

## `formula_expr_quant_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:546`](../SubqueryFacts.v#L546)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma formula_expr_quant_admissible_iff :
  forall which_quantifier which_predicate arguments subquery,
    @formula_expr_admissible T relname basesort
      (FExpr_Quant which_quantifier which_predicate arguments subquery) <->
    @query_expr_admissible T relname basesort subquery /\
    length arguments = 1%nat /\
    length (query_expr_outputs subquery) = 1%nat /\
    (length arguments + length (query_expr_outputs subquery))%nat =
      predicate_arity T which_predicate.
```

## `formula_expr_in_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:559`](../SubqueryFacts.v#L559)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma formula_expr_in_admissible_iff : forall select_items subquery,
  @formula_expr_admissible T relname basesort
    (FExpr_In select_items subquery) <->
  @query_expr_admissible T relname basesort subquery /\
  select_list_sort (_Select_List select_items) =S= query_expr_sort subquery /\
  query_in_positionally_aligned (_Select_List select_items)
    (query_expr_outputs subquery).
```

## `formula_expr_exists_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:570`](../SubqueryFacts.v#L570)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma formula_expr_exists_admissible_iff : forall subquery,
  @formula_expr_admissible T relname basesort (FExpr_Exists subquery) <->
  @query_expr_admissible T relname basesort subquery.
```

## `eval_formula_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:577`](../SubqueryFacts.v#L577)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context left) outcome <->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context right) outcome.
```

## `eval_query_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:593`](../SubqueryFacts.v#L593)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
```
