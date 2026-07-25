# Predicate subqueries and correlation

Route here for: EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality.

This focused catalog contains 53 declarations routed at declaration granularity from `SubqueryFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `interp_exists_quant_not_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:22`](../SubqueryFacts.v#L22)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:39`](../SubqueryFacts.v#L39)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:57`](../SubqueryFacts.v#L57)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:94`](../SubqueryFacts.v#L94)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:131`](../SubqueryFacts.v#L131)

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

## `rows_empty_decision_rel_permut`

Source: [`theories/FormalSQL/SubqueryFacts.v:151`](../SubqueryFacts.v#L151)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `rows_empty_decision_rel_permut` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma rows_empty_decision_rel_permut :
  forall (A B : Type) (R : A -> B -> Prop) left right,
    _permut R left right ->
    rows_empty_decision left = rows_empty_decision right.
```

## `rows_empty_decision_oeset_permut`

Source: [`theories/FormalSQL/SubqueryFacts.v:163`](../SubqueryFacts.v#L163)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `rows_empty_decision_oeset_permut` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 51)

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Corollary rows_empty_decision_oeset_permut :
  forall (A : Type) (order : Oeset.Rcd A) left right,
    Oeset.permut order left right ->
    rows_empty_decision left = rows_empty_decision right.
```

## `existsb_rel_permut`

Source: [`theories/FormalSQL/SubqueryFacts.v:177`](../SubqueryFacts.v#L177)

Purpose/direction: States the existsb rel permut law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `existsb_rel_permut` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma existsb_rel_permut :
  forall (A B : Type) (R : A -> B -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      left_predicate left_value = right_predicate right_value) ->
    _permut R left right ->
    existsb left_predicate left = existsb right_predicate right.
```

## `formula_expr_conj_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:246`](../SubqueryFacts.v#L246)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_conj_env_congr :
  forall left_env right_env operation left right,
    formula_expr_env_outcome_equiv left_env right_env left ->
    formula_expr_env_outcome_equiv left_env right_env right ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Conj operation left right).
```

## `formula_expr_not_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:295`](../SubqueryFacts.v#L295)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_not_env_congr :
  forall left_env right_env formula,
    formula_expr_env_outcome_equiv left_env right_env formula ->
    formula_expr_env_outcome_equiv left_env right_env (FExpr_Not formula).
```

## `formula_expr_pred_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:308`](../SubqueryFacts.v#L308)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_pred_env_congr_safe :
  forall left_env right_env predicate arguments,
    Env.equiv_env T left_env right_env ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      arguments = None ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      arguments = None ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Pred predicate arguments).
```

## `query_expr_table_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:350`](../SubqueryFacts.v#L350)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_expr_table_env_congr :
  forall left_env right_env attributes relation,
    query_expr_env_outcome_equiv left_env right_env
      (@QExpr_Table T relname attributes relation).
```

## `query_expr_cross_join_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:359`](../SubqueryFacts.v#L359)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 40), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `join`, `cross product`, `CROSS JOIN`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_env_congr :
  forall left_env right_env left right,
    query_expr_env_outcome_equiv left_env right_env left ->
    query_expr_env_outcome_equiv left_env right_env right ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_CrossJoin left right).
```

## `eval_filter_rows_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:410`](../SubqueryFacts.v#L410)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `filter` (rank 46), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_env_congr :
  forall left_env right_env formula,
    (forall row,
      formula_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    forall rows outcome,
      eval_filter_rows left_env formula rows outcome <->
      eval_filter_rows right_env formula rows outcome.
```

## `query_expr_filter_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:433`](../SubqueryFacts.v#L433)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `filter` (rank 46), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_env_congr :
  forall left_env right_env formula input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      formula_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Filter formula input).
```

## `project_rows_outcome_env_congr_safe_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:472`](../SubqueryFacts.v#L472)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 52), `runtime` (rank 52), `projection` (rank 52), `scalar` (rank 38)

Search aliases: `predicate subquery semantics`, `subquery`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma project_rows_outcome_env_congr_safe_exact :
  forall left_env right_env select_list rows,
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T left_env row) select_list = None) ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T right_env row) select_list = None) ->
    (forall row,
      Projection.projection T (Env.env_t T left_env row)
        (@Select_List T select_list) =
      Projection.projection T (Env.env_t T right_env row)
        (@Select_List T select_list)) ->
    project_rows left_env select_list rows =
    project_rows right_env select_list rows.
```

## `query_expr_project_env_congr_safe_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:498`](../SubqueryFacts.v#L498)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `projection` (rank 52), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_project_env_congr_safe_exact :
  forall left_env right_env select_list input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T left_env row) select_list = None) ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T right_env row) select_list = None) ->
    (forall row,
      Projection.projection T (Env.env_t T left_env row)
        (@Select_List T select_list) =
      Projection.projection T (Env.env_t T right_env row)
        (@Select_List T select_list)) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Project select_list input).
```

## `query_tuple_equal_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:575`](../SubqueryFacts.v#L575)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_tuple_equal_congr :
  forall left left' right right',
    Oeset.compare (OTuple T) left left' = Eq ->
    Oeset.compare (OTuple T) right right' = Eq ->
    @query_tuple_equal T unknown value_is_null left right =
    @query_tuple_equal T unknown value_is_null left' right'.
```

## `in_row_truth_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:642`](../SubqueryFacts.v#L642)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma in_row_truth_env_congr :
  forall left_env right_env select_items row,
    Env.equiv_env T left_env right_env ->
    in_row_truth left_env select_items row =
    in_row_truth right_env select_items row.
```

## `in_rows_truth_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:655`](../SubqueryFacts.v#L655)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `equivalence`, `congruence`

```rocq
Lemma in_rows_truth_env_congr :
  forall left_env right_env select_items rows,
    Env.equiv_env T left_env right_env ->
    in_rows_truth left_env select_items rows =
    in_rows_truth right_env select_items rows.
```

## `in_rows_acceptance_existsb`

Source: [`theories/FormalSQL/SubqueryFacts.v:676`](../SubqueryFacts.v#L676)

Purpose/direction: Reduces only the TRUE-acceptance observation of SQL IN over a row bag to an ordinary Boolean existence test, retaining the underlying FALSE/UNKNOWN distinction.

Applicability: Use after proving the per-candidate `Bool.is_true` decision.  The conclusion is suitable for WHERE or semijoin filtering only; it is not equality of the complete SQL Bool3 result.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter` (rank 0), `join` (rank 0), `scalar` (rank 2)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_acceptance_existsb :
  forall env select_items rows (accept : tuple T -> bool),
    (forall row,
      Bool.is_true (B T) (in_row_truth env select_items row) = accept row) ->
    Bool.is_true (B T) (in_rows_truth env select_items rows) =
    existsb accept rows.
```

## `query_same_rows_as_bag_empty_decision`

Source: [`theories/FormalSQL/SubqueryFacts.v:731`](../SubqueryFacts.v#L731)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag` (rank 52), `scalar` (rank 52)

Search aliases: `predicate subquery semantics`, `subquery`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_empty_decision :
  forall first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    rows_empty_decision first = rows_empty_decision second.
```

## `quantified_rows_exists_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:754`](../SubqueryFacts.v#L754)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:767`](../SubqueryFacts.v#L767)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:780`](../SubqueryFacts.v#L780)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:793`](../SubqueryFacts.v#L793)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:806`](../SubqueryFacts.v#L806)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:816`](../SubqueryFacts.v#L816)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:826`](../SubqueryFacts.v#L826)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:833`](../SubqueryFacts.v#L833)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:857`](../SubqueryFacts.v#L857)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:878`](../SubqueryFacts.v#L878)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:897`](../SubqueryFacts.v#L897)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:916`](../SubqueryFacts.v#L916)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:938`](../SubqueryFacts.v#L938)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:956`](../SubqueryFacts.v#L956)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:974`](../SubqueryFacts.v#L974)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:983`](../SubqueryFacts.v#L983)

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

## `eval_formula_exists_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1002`](../SubqueryFacts.v#L1002)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_formula left_env (FExpr_Exists subquery) outcome <->
      eval_formula right_env (FExpr_Exists subquery) outcome.
```

## `formula_expr_exists_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1032`](../SubqueryFacts.v#L1032)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_exists_env_congr :
  forall left_env right_env subquery,
    query_expr_env_outcome_equiv left_env right_env subquery ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Exists subquery).
```

## `eval_formula_in_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1046`](../SubqueryFacts.v#L1046)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_in_env_congr_safe :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    forall outcome,
      eval_formula left_env (FExpr_In select_items subquery) outcome <->
      eval_formula right_env (FExpr_In select_items subquery) outcome.
```

## `formula_expr_in_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1097`](../SubqueryFacts.v#L1097)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_in_env_congr_safe :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    query_expr_env_outcome_equiv left_env right_env subquery ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_In select_items subquery).
```

## `eval_formula_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1117`](../SubqueryFacts.v#L1117)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1131`](../SubqueryFacts.v#L1131)

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

## `formula_exists_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1160`](../SubqueryFacts.v#L1160)

Purpose/direction: Builds an exact EXISTS acceptance contract from inhabited child successes that agree on emptiness and from explicit absence of errors.

Applicability: Use at one fixed, possibly correlated environment after providing a child success, agreement of every child success on emptiness, and absence of every child SQL error.

Important premises: Retain child-success inhabitation, universal agreement on `rows_empty_decision`, the fixed environment, and exclusion of every error.

Cross-index: `runtime` (rank 50), `filter` (rank 38), `scalar` (rank 50)

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem formula_exists_acceptance_exact :
  forall env subquery empty,
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      rows_empty_decision rows = empty) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Exists subquery) (Datatypes.negb empty).
```

## `eval_formula_quant_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1204`](../SubqueryFacts.v#L1204)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1231`](../SubqueryFacts.v#L1231)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1253`](../SubqueryFacts.v#L1253)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1277`](../SubqueryFacts.v#L1277)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1290`](../SubqueryFacts.v#L1290)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1301`](../SubqueryFacts.v#L1301)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1308`](../SubqueryFacts.v#L1308)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context left) outcome <->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context right) outcome.
```

## `eval_query_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1324`](../SubqueryFacts.v#L1324)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar` (rank 42)

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
```
