# Runtime outcomes, verification modes, and rewrite specifications

Route here for: success/error outcomes, safe vs error-preserving equivalence, rewrite contracts.

This focused catalog contains 51 declarations routed at declaration granularity from `ErrorFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`, `RewriteSpec.v`, `VerificationConditions.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `query_runtime_error_not_equiv_left`

Source: [`theories/FormalSQL/ErrorFacts.v:12`](../ErrorFacts.v#L12)

Purpose/direction: Derives query non-equivalence from the displayed modeled runtime error on the indicated side.

Applicability: Use to close a non-equivalence goal after supplying the exact error or mismatch witness required by `query_runtime_error_not_equiv_left`; it does not assume equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the displayed runtime-error or mismatch witness; equivalence is the negated conclusion, not a premise.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `non-equivalence`, `mismatch witness`

```rocq
Lemma query_runtime_error_not_equiv_left :
  forall db q1 q2 error,
    query_runtime_error_in_state db q1 = Some error ->
    ~ query_equiv db q1 q2.
```

## `query_runtime_error_not_equiv_right`

Source: [`theories/FormalSQL/ErrorFacts.v:24`](../ErrorFacts.v#L24)

Purpose/direction: Derives query non-equivalence from the displayed modeled runtime error on the indicated side.

Applicability: Use to close a non-equivalence goal after supplying the exact error or mismatch witness required by `query_runtime_error_not_equiv_right`; it does not assume equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the displayed runtime-error or mismatch witness; equivalence is the negated conclusion, not a premise.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `non-equivalence`, `mismatch witness`

```rocq
Lemma query_runtime_error_not_equiv_right :
  forall db q1 q2 error,
    query_runtime_error_in_state db q2 = Some error ->
    ~ query_equiv db q1 q2.
```

## `query_expr_equiv_refl_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:99`](../OrderedQueryFacts.v#L99)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_refl_safe :
  forall env query,
    query_safe env query ->
    query_has_success env query ->
    query_equiv env query query.
```

## `query_expr_outcome_equiv_refl`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:114`](../OrderedQueryFacts.v#L114)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_refl :
  forall env query,
    (exists outcome, eval_query env query outcome) ->
    query_outcome_equiv env query query.
```

## `query_expr_outcome_equiv_of_eval_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:131`](../OrderedQueryFacts.v#L131)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 24), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_of_eval_iff :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists outcome, eval_query env left outcome) ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    query_outcome_equiv env left right.
```

## `query_expr_outcome_equiv_of_global_typed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:159`](../OrderedQueryFacts.v#L159)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 24), `runtime` (rank 36), `schema` (rank 52)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_of_global_typed :
  forall env left right,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    (exists outcome, eval_query env left outcome) ->
    query_outcome_equiv env left right.
```

## `query_expr_filter_outcome_equiv_of_global_acceptance`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:175`](../OrderedQueryFacts.v#L175)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 24), `runtime` (rank 36), `filter` (rank 44)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_outcome_equiv_of_global_acceptance :
  forall env left_formula right_formula input,
    @formula_expr_global_filter_outcome_equiv T relname basesort instance
      unknown contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null left_formula right_formula ->
    (exists outcome,
      eval_query env (QExpr_Filter left_formula input) outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input).
```

## `query_expr_bag_has_success_of_runtime_error_none`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:217`](../OrderedQueryFacts.v#L217)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 24), `bag` (rank 52)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_bag_has_success_of_runtime_error_none :
  forall env outputs query,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    query_has_success env (QExpr_Bag outputs query).
```

## `query_expr_bag_runtime_safe_of_runtime_error_none`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:238`](../OrderedQueryFacts.v#L238)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 24), `bag` (rank 52)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_bag_runtime_safe_of_runtime_error_none :
  forall env outputs query,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    query_safe env (QExpr_Bag outputs query).
```

## `query_expr_bag_safe_success_of_runtime_error_none`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:250`](../OrderedQueryFacts.v#L250)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 23), `bag` (rank 51)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_expr_bag_safe_success_of_runtime_error_none :
  forall env outputs query,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    query_safe env (QExpr_Bag outputs query) /\
    query_has_success env (QExpr_Bag outputs query).
```

## `query_expr_equiv_of_outcome_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:265`](../OrderedQueryFacts.v#L265)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_of_outcome_equiv_safe :
  forall env left right,
    query_outcome_equiv env left right ->
    query_safe env left ->
    query_safe env right ->
    query_has_success env left ->
    query_equiv env left right.
```

## `query_expr_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:284`](../OrderedQueryFacts.v#L284)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_sym :
  forall env left right,
    query_equiv env left right ->
    query_equiv env right left.
```

## `query_expr_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:313`](../OrderedQueryFacts.v#L313)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_trans :
  forall env first second third,
    query_equiv env first second ->
    query_equiv env second third ->
    query_equiv env first third.
```

## `query_expr_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:348`](../OrderedQueryFacts.v#L348)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_sym :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env right left.
```

## `query_expr_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:374`](../OrderedQueryFacts.v#L374)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_trans :
  forall env first second third,
    query_outcome_equiv env first second ->
    query_outcome_equiv env second third ->
    query_outcome_equiv env first third.
```

## `query_expr_global_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:418`](../OrderedQueryFacts.v#L418)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_sym :
  forall left right,
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null left right ->
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null right left.
```

## `query_expr_global_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:430`](../OrderedQueryFacts.v#L430)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_trans :
  forall first second third,
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null first second ->
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null second third ->
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null first third.
```

## `query_expr_global_typed_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:447`](../OrderedQueryFacts.v#L447)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36), `schema` (rank 52)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_sym :
  forall left right,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null left right ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null right left.
```

## `query_expr_global_typed_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:461`](../OrderedQueryFacts.v#L461)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36), `schema` (rank 52)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_trans :
  forall first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null first third.
```

## `query_expr_context_global_equiv_chain`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:479`](../OrderedQueryFacts.v#L479)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_context_global_equiv_chain :
  forall context first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null
      (plug_query_expr_context context first)
      (plug_query_expr_context context third).
```

## `eval_query_expr_project_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:519`](../OrderedQueryFacts.v#L519)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 32), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_project_error_iff :
  forall env select_list input error,
    eval_query env (QExpr_Project select_list input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list input_rows = SqlError error.
```

## `eval_query_expr_filter_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:554`](../OrderedQueryFacts.v#L554)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 32), `filter` (rank 44)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_filter_error_iff :
  forall env formula input error,
    eval_query env (QExpr_Filter formula input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlError error).
```

## `query_expr_filter_outcome_equiv_of_always_true`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1750`](../OrderedQueryFacts.v#L1750)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 22), `runtime` (rank 34), `filter` (rank 40)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_outcome_equiv_of_always_true :
  forall env formula input,
    (exists outcome, eval_query env input outcome) ->
    (forall rows,
      eval_query env input (SqlSuccess rows) ->
      forall row,
        In row rows ->
        forall outcome,
          @eval_formula_expr_outcome T relname basesort instance unknown
            contains_nulls symbol_runtime_error aggregate_runtime_error
            value_is_null (env_t T env row) formula outcome <->
          outcome = SqlSuccess (Bool.true (B T))) ->
    query_outcome_equiv env (QExpr_Filter formula input) input.
```

## `project_rows_outcome_all_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1894`](../OrderedQueryFacts.v#L1894)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 36), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma project_rows_outcome_all_safe :
  forall env select_list rows,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows =
    SqlSuccess
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows).
```

## `first_runtime_error_all_none`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1995`](../OrderedQueryFacts.v#L1995)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_all_none :
  forall (A : Type) (check : A -> option sql_runtime_error) values,
    (forall value, In value values -> check value = None) ->
    first_runtime_error check values = None.
```

## `bag_projection_runtime_error_none`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2008`](../OrderedQueryFacts.v#L2008)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 24), `projection` (rank 52), `bag` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_projection_runtime_error_none :
  forall env select_list input,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env input = None ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env
      (@Q_Pi T relname select_list input) = None.
```

## `query_expr_project_outcome_equiv_congr_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2030`](../OrderedQueryFacts.v#L2030)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 24), `runtime` (rank 34), `projection` (rank 50)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_project_outcome_equiv_congr_safe :
  forall env select_list left right,
    query_outcome_equiv env left right ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_outcome_equiv env
      (QExpr_Project select_list left)
      (QExpr_Project select_list right).
```

## `query_expr_project_bag_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2122`](../OrderedQueryFacts.v#L2122)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 34), `projection` (rank 50), `bag` (rank 40)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_project_bag_equiv_safe :
  forall env input_outputs select_list input,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env input = None ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_equiv env
      (QExpr_Project select_list (QExpr_Bag input_outputs input))
      (QExpr_Bag (select_list_outputs select_list)
        (@Q_Pi T relname select_list input)).
```

## `tnull_qexpr_bag_outcome_eq_of_runtime_and_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:533`](../ProofAgentFacade.v#L533)

Purpose/direction: Lifts exact output-signature equality, runtime-error equality, and FormalSQL bag equality to error-preserving TNull query-outcome equality.

Applicability: Use as the final high-level bridge after separately proving exact output signatures, equal runtime errors, and bag equality; it preserves errors and does not add order equality.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 2), `outcome` (rank 2), `runtime` (rank 2), `bag` (rank 6)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_qexpr_bag_outcome_eq_of_runtime_and_bag_eq :
  forall db env left_outputs right_outputs left right,
    left_outputs = right_outputs ->
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env right ->
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env right) ->
    TNullQueryExprOutcomeEq db env
      (QExpr_Bag left_outputs left)
      (QExpr_Bag right_outputs right).
```

## `tnull_cross_join_runtime_error_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:927`](../ProofAgentFacade.v#L927)

Purpose/direction: Lifts equality of child runtime errors through the displayed TNull relational operator.

Applicability: Use to transport child runtime-error equality through this operator; this is not a proof that either side is safe.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 16), `runtime` (rank 6), `join` (rank 4)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma tnull_cross_join_runtime_error_congr :
  forall db env left left' right right',
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env left' ->
    TNullQueryRuntimeError db env right =
      TNullQueryRuntimeError db env right' ->
    TNullQueryRuntimeError db env (CrossJoin left right) =
      TNullQueryRuntimeError db env (CrossJoin left' right').
```

## `tnull_pi_runtime_error_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:942`](../ProofAgentFacade.v#L942)

Purpose/direction: Lifts equality of child runtime errors through the displayed TNull relational operator.

Applicability: Use to transport child runtime-error equality through this operator; this is not a proof that either side is safe.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 16), `runtime` (rank 6), `projection` (rank 16)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma tnull_pi_runtime_error_congr :
  forall db env select left right,
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env right ->
    TNullProjectionScanRuntimeError db env select left =
      TNullProjectionScanRuntimeError db env select right ->
    TNullQueryRuntimeError db env (Pi select left) =
      TNullQueryRuntimeError db env (Pi select right).
```

## `tnull_sigma_runtime_error_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:961`](../ProofAgentFacade.v#L961)

Purpose/direction: Lifts equality of child runtime errors through the displayed TNull relational operator.

Applicability: Use to transport child runtime-error equality through this operator; this is not a proof that either side is safe.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 16), `runtime` (rank 6), `filter` (rank 10)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma tnull_sigma_runtime_error_congr :
  forall db env formula left right,
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env right ->
    TNullFilterScanRuntimeError db env formula left =
      TNullFilterScanRuntimeError db env formula right ->
    TNullQueryRuntimeError db env (Sigma formula left) =
      TNullQueryRuntimeError db env (Sigma formula right).
```

## `tnull_cross_join_runtime_error_none`

Source: [`theories/FormalSQL/ProofAgentFacade.v:980`](../ProofAgentFacade.v#L980)

Purpose/direction: Composes the displayed child and expression safety premises into absence of a TNull operator runtime error.

Applicability: Use to compose explicit no-error premises for this operator; do not infer a premise merely from successful bag equality.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade` (rank 7), `runtime` (rank 3), `join` (rank 3)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Corollary tnull_cross_join_runtime_error_none :
  forall db env left right,
    TNullQueryRuntimeError db env left = None ->
    TNullQueryRuntimeError db env right = None ->
    TNullQueryRuntimeError db env (CrossJoin left right) = None.
```

## `tnull_pi_runtime_error_none`

Source: [`theories/FormalSQL/ProofAgentFacade.v:992`](../ProofAgentFacade.v#L992)

Purpose/direction: Composes the displayed child and expression safety premises into absence of a TNull operator runtime error.

Applicability: Use to compose explicit no-error premises for this operator; do not infer a premise merely from successful bag equality.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 8), `runtime` (rank 4), `projection` (rank 16), `bag` (rank 16)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_pi_runtime_error_none :
  forall db env select input,
    TNullQueryRuntimeError db env input = None ->
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullSelectListRuntimeError (env_t TNull env row) select = None) ->
    TNullQueryRuntimeError db env (Pi select input) = None.
```

## `tnull_sigma_runtime_error_none`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1011`](../ProofAgentFacade.v#L1011)

Purpose/direction: Composes the displayed child and expression safety premises into absence of a TNull operator runtime error.

Applicability: Use to compose explicit no-error premises for this operator; do not infer a premise merely from successful bag equality.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 8), `runtime` (rank 4), `filter` (rank 10), `bag` (rank 16)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_sigma_runtime_error_none :
  forall db env formula input,
    TNullQueryRuntimeError db env input = None ->
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullFormulaRuntimeError db (env_t TNull env row) formula = None) ->
    TNullQueryRuntimeError db env (Sigma formula input) = None.
```

## `direct_projection_preserves_attr`

Source: [`theories/FormalSQL/RewriteSpec.v:43`](../RewriteSpec.v#L43)

Purpose/direction: Shows that the indicated operator preserves the displayed SQL verification and runtime outcomes property.

Applicability: Use when the goal or a hypothesis matches the `direct_projection_preserves_attr` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`

```rocq
Lemma direct_projection_preserves_attr :
  forall env s a,
    select_list_directly_selects_attr s a ->
    select_list_has_unique_outputs s ->
    projection_preserves_attr env s a.
```

## `eval_formula_in_env_eq_tuple`

Source: [`theories/FormalSQL/RewriteSpec.v:62`](../RewriteSpec.v#L62)

Purpose/direction: States the eval formula in env equality tuple law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_in_env_eq_tuple` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma eval_formula_in_env_eq_tuple :
  forall db env f t1 t2,
    t1 =t= t2 ->
    eval_formula_in_env db env t1 f = eval_formula_in_env db env t2 f.
```

## `sigma_outputs_satisfy_predicate`

Source: [`theories/FormalSQL/RewriteSpec.v:79`](../RewriteSpec.v#L79)

Purpose/direction: States the sigma outputs satisfy predicate law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `sigma_outputs_satisfy_predicate` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime` (rank 36), `filter` (rank 46), `scalar` (rank 52)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `predicate`, `Bool3`

```rocq
Lemma sigma_outputs_satisfy_predicate :
  forall db q f,
    query_satisfies db (Sigma f q) f.
```

## `sigma_outputs_satisfy_entailed`

Source: [`theories/FormalSQL/RewriteSpec.v:106`](../RewriteSpec.v#L106)

Purpose/direction: States the sigma outputs satisfy entailed law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `sigma_outputs_satisfy_entailed` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`

```rocq
Lemma sigma_outputs_satisfy_entailed :
  forall db q premise conclusion,
    query_entails db q premise conclusion ->
    query_satisfies db (Sigma premise q) conclusion.
```

## `pi_sigma_outputs_satisfy_preserved`

Source: [`theories/FormalSQL/RewriteSpec.v:139`](../RewriteSpec.v#L139)

Purpose/direction: Shows that the indicated operator preserves the displayed SQL verification and runtime outcomes property.

Applicability: Use when the goal or a hypothesis matches the `pi_sigma_outputs_satisfy_preserved` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `projection` (rank 52), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `projection`, `SELECT list`

```rocq
Lemma pi_sigma_outputs_satisfy_preserved :
  forall db q s f,
    select_list_preserves_formula_eval db s f ->
    query_satisfies db (Pi s (Sigma f q)) f.
```

## `pi_sigma_outputs_satisfy_entailed`

Source: [`theories/FormalSQL/RewriteSpec.v:158`](../RewriteSpec.v#L158)

Purpose/direction: States the pi sigma outputs satisfy entailed law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `pi_sigma_outputs_satisfy_entailed` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `projection` (rank 52), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `projection`, `SELECT list`

```rocq
Lemma pi_sigma_outputs_satisfy_entailed :
  forall db q s premise conclusion,
    select_list_preserves_formula_eval db s conclusion ->
    query_entails db q premise conclusion ->
    query_satisfies db (Pi s (Sigma premise q)) conclusion.
```

## `eval_and`

Source: [`theories/FormalSQL/RewriteSpec.v:178`](../RewriteSpec.v#L178)

Purpose/direction: States the eval and law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_and` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma eval_and :
  forall db env t p h,
    eval_formula_in_env db env t (And p h) =
    (eval_formula_in_env db env t p && eval_formula_in_env db env t h)%bool.
```

## `query_satisfies_conj_l`

Source: [`theories/FormalSQL/RewriteSpec.v:189`](../RewriteSpec.v#L189)

Purpose/direction: States the query satisfies conj l law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_satisfies_conj_l` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma query_satisfies_conj_l :
  forall db q p h,
    query_satisfies db q (And p h) ->
    query_satisfies db q p.
```

## `query_satisfies_conj_r`

Source: [`theories/FormalSQL/RewriteSpec.v:203`](../RewriteSpec.v#L203)

Purpose/direction: States the query satisfies conj r law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_satisfies_conj_r` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma query_satisfies_conj_r :
  forall db q p h,
    query_satisfies db q (And p h) ->
    query_satisfies db q h.
```

## `sigma_id_of_query_satisfies`

Source: [`theories/FormalSQL/RewriteSpec.v:217`](../RewriteSpec.v#L217)

Purpose/direction: States the sigma id of query satisfies law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `sigma_id_of_query_satisfies` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`

```rocq
Lemma sigma_id_of_query_satisfies :
  forall db q f,
    query_satisfies db q f ->
    query_succeeds db (Sigma f q) ->
    query_succeeds db q ->
    query_equiv db (Sigma f q) q.
```

## `sigma_drop_redundant_conjunct`

Source: [`theories/FormalSQL/RewriteSpec.v:268`](../RewriteSpec.v#L268)

Purpose/direction: States the sigma drop redundant conjunct law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `sigma_drop_redundant_conjunct` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`

```rocq
Lemma sigma_drop_redundant_conjunct :
  forall db q p h,
    query_satisfies db q h ->
    query_succeeds db (Sigma (And p h) q) ->
    query_succeeds db (Sigma p q) ->
    query_equiv db (Sigma (And p h) q) (Sigma p q).
```

## `andb3_indicator_mul_factor`

Source: [`theories/FormalSQL/RewriteSpec.v:301`](../RewriteSpec.v#L301)

Purpose/direction: States the andb3 indicator mul factor law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `andb3_indicator_mul_factor` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime` (rank 36), `scalar` (rank 52)

Search aliases: `verification and runtime semantics`, `predicate`, `Bool3`

```rocq
Lemma andb3_indicator_mul_factor :
  forall n outer_value inner_value,
    (n *
      (if match andb3 outer_value inner_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0))%N =
    (n *
      (if match inner_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0) *
      (if match outer_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0))%N.
```

## `sigma_sigma_merge`

Source: [`theories/FormalSQL/RewriteSpec.v:330`](../RewriteSpec.v#L330)

Purpose/direction: States the sigma sigma merge law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `sigma_sigma_merge` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`

```rocq
Lemma sigma_sigma_merge :
  forall db q outer inner,
    query_succeeds db (Sigma outer (Sigma inner q)) ->
    query_succeeds db (Sigma (And outer inner) q) ->
    query_equiv db (Sigma outer (Sigma inner q)) (Sigma (And outer inner) q).
```

## `condition_true_well_formed`

Source: [`theories/FormalSQL/VerificationConditions.v:193`](../VerificationConditions.v#L193)

Purpose/direction: States the condition true well formed law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `condition_true_well_formed` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma condition_true_well_formed :
  forall expected,
    verification_condition_well_formed expected ConditionTrue.
```

## `condition_true_holds`

Source: [`theories/FormalSQL/VerificationConditions.v:200`](../VerificationConditions.v#L200)

Purpose/direction: States the condition true holds law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `condition_true_holds` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma condition_true_holds :
  forall db,
    verification_condition_holds db ConditionTrue.
```

## `condition_true_is_derived`

Source: [`theories/FormalSQL/VerificationConditions.v:207`](../VerificationConditions.v#L207)

Purpose/direction: States the condition true is derived law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `condition_true_is_derived` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`

```rocq
Lemma condition_true_is_derived :
  forall expected constraints,
    precondition_source_obligation
      expected constraints PreconditionDerived ConditionTrue.
```
