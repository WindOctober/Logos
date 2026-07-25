# Runtime outcomes, verification modes, and rewrite specifications

Route here for: success/error outcomes, safe vs error-preserving equivalence, rewrite contracts.

This focused catalog contains 52 declarations routed at declaration granularity from `AggregateRuntimeFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`, `VerificationConditions.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `successful_outcome_equiv_implies_outcome_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1485`](../AggregateRuntimeFacts.v#L1485)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma successful_outcome_equiv_implies_outcome_equiv :
  forall (A : Type) (value_equiv : A -> A -> Prop) left right,
    successful_outcome_equiv value_equiv left right ->
    outcome_equiv value_equiv left right.
```

## `outcome_equiv_eq_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1494`](../AggregateRuntimeFacts.v#L1494)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_eq_iff : forall (A : Type) (left right : sql_outcome A),
  outcome_equiv eq left right <-> left = right.
```

## `outcome_equiv_symmetric`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1508`](../AggregateRuntimeFacts.v#L1508)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_symmetric :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall left right, value_equiv left right -> value_equiv right left) ->
    forall left right,
      outcome_equiv value_equiv left right ->
      outcome_equiv value_equiv right left.
```

## `outcome_equiv_transitive`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:1521`](../AggregateRuntimeFacts.v#L1521)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_transitive :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall left middle right,
      value_equiv left middle -> value_equiv middle right ->
      value_equiv left right) ->
    forall left middle right,
      outcome_equiv value_equiv left middle ->
      outcome_equiv value_equiv middle right ->
      outcome_equiv value_equiv left right.
```

## `query_expr_has_success_of_runtime_safe_and_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:113`](../OrderedQueryFacts.v#L113)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 30)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_has_success_of_runtime_safe_and_outcome :
  forall env query,
    query_safe env query ->
    (exists outcome, eval_query env query outcome) ->
    query_has_success env query.
```

## `query_expr_equiv_refl_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:127`](../OrderedQueryFacts.v#L127)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:142`](../OrderedQueryFacts.v#L142)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:159`](../OrderedQueryFacts.v#L159)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:187`](../OrderedQueryFacts.v#L187)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 24), `runtime` (rank 36), `schema` (rank 52)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_of_global_typed :
  forall env left right,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    (exists outcome, eval_query env left outcome) ->
    query_outcome_equiv env left right.
```

## `query_bag_closed_outcome_equiv_of_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:204`](../OrderedQueryFacts.v#L204)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 22), `runtime` (rank 34), `bag` (rank 50)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_bag_closed_outcome_equiv_of_success_bags :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    BagClosed T
      (fun rows => eval_query env first (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query env second (SqlSuccess rows)) ->
    (exists outcome, eval_query env first outcome) ->
    (exists outcome, eval_query env second outcome) ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    (forall error,
      eval_query env first (SqlError error) <->
      eval_query env second (SqlError error)) ->
    query_outcome_equiv env first second.
```

## `query_bag_reset_outcome_equiv_of_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:252`](../OrderedQueryFacts.v#L252)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 23), `runtime` (rank 35), `bag` (rank 51)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_bag_reset_outcome_equiv_of_success_bags :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_order_behavior first = BagReset ->
    query_expr_order_behavior second = BagReset ->
    (exists outcome, eval_query env first outcome) ->
    (exists outcome, eval_query env second outcome) ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    (forall error,
      eval_query env first (SqlError error) <->
      eval_query env second (SqlError error)) ->
    query_outcome_equiv env first second.
```

## `eval_query_expr_set_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:276`](../OrderedQueryFacts.v#L276)

Purpose/direction: Characterizes a set-operation error as a left error or as a right error reached after one successful left observation.

Applicability: Use to invert or construct the exact parent error schedule; a right-child error is observable only with the displayed left-success witness.

Important premises: Retain the existential successful left observation in the right-error arm; right errors do not bypass a left error-only execution.

Cross-index: `runtime` (rank 32)

Search aliases: `verification and runtime semantics`, `set operation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_set_error_iff :
  forall env operation left right error,
    eval_query env (QExpr_Set operation left right) (SqlError error) <->
    eval_query env left (SqlError error) \/
    exists left_rows,
      eval_query env left (SqlSuccess left_rows) /\
      eval_query env right (SqlError error).
```

## `eval_query_expr_cross_join_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:293`](../OrderedQueryFacts.v#L293)

Purpose/direction: Characterizes a CROSS JOIN error with its exact left-to-right child evaluation schedule.

Applicability: Use to invert or construct the exact parent error schedule; a right-child error is observable only with the displayed left-success witness.

Important premises: Retain the existential successful left observation in the right-error arm; right errors do not bypass a left error-only execution.

Cross-index: `runtime` (rank 32), `join` (rank 40)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_cross_join_error_iff :
  forall env left right error,
    eval_query env (QExpr_CrossJoin left right) (SqlError error) <->
    eval_query env left (SqlError error) \/
    exists left_rows,
      eval_query env left (SqlSuccess left_rows) /\
      eval_query env right (SqlError error).
```

## `query_expr_set_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:310`](../OrderedQueryFacts.v#L310)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL bag/set operations.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 30)

Search aliases: `verification and runtime semantics`, `set operation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_set_runtime_safe :
  forall env operation left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_Set operation left right).
```

## `query_expr_cross_join_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:323`](../OrderedQueryFacts.v#L323)

Purpose/direction: Establishes the explicit runtime-safety direction for join semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 30), `join` (rank 40)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_cross_join_runtime_safe :
  forall env left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_CrossJoin left right).
```

## `query_expr_set_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:371`](../OrderedQueryFacts.v#L371)

Purpose/direction: States the query expr set has outcome law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_set_has_outcome :
  forall env operation left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_Set operation left right) outcome.
```

## `query_expr_cross_join_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:392`](../OrderedQueryFacts.v#L392)

Purpose/direction: States the query expr cross join has outcome law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 36), `join` (rank 40)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_cross_join_has_outcome :
  forall env left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_CrossJoin left right) outcome.
```

## `query_expr_set_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:417`](../OrderedQueryFacts.v#L417)

Purpose/direction: Lifts two child outcome equivalences through a set-operation bag reset while preserving exact output schema and short-circuit errors.

Applicability: Use to lift two local child outcome equivalences through any modeled set operation; no safety or success premise is required, and sort mismatch behavior remains authoritative.

Important premises: Supply both displayed child outcome equivalences.  Do not assume set sort compatibility: matching sort-mismatch outcomes are preserved.

Cross-index: `outcome` (rank 26), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_set_outcome_equiv_congr :
  forall env operation left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
```

## `query_expr_cross_join_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:507`](../OrderedQueryFacts.v#L507)

Purpose/direction: Lifts two child outcome equivalences through CROSS JOIN's bag reset while preserving appended output schema, multiplicity, and errors.

Applicability: Use to lift two local child outcome equivalences through CROSS JOIN; no safety or success premise is required.

Important premises: Supply both displayed child outcome equivalences; no runtime-safety or successful-outcome premise may be silently added or inferred.

Cross-index: `outcome` (rank 26), `runtime` (rank 36), `join` (rank 22)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_outcome_equiv_congr :
  forall env left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_CrossJoin left right)
      (QExpr_CrossJoin left' right').
```

## `query_expr_filter_outcome_equiv_of_global_acceptance`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:596`](../OrderedQueryFacts.v#L596)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 24), `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_outcome_equiv_of_global_acceptance :
  forall env left_formula right_formula input,
    @formula_expr_global_filter_outcome_equiv T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null left_formula right_formula ->
    (exists outcome,
      eval_query env (QExpr_Filter left_formula input) outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input).
```

## `query_expr_equiv_of_outcome_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:720`](../OrderedQueryFacts.v#L720)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:739`](../OrderedQueryFacts.v#L739)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:768`](../OrderedQueryFacts.v#L768)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:803`](../OrderedQueryFacts.v#L803)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:829`](../OrderedQueryFacts.v#L829)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:873`](../OrderedQueryFacts.v#L873)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_sym :
  forall left right,
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null left right ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null right left.
```

## `query_expr_global_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:883`](../OrderedQueryFacts.v#L883)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_trans :
  forall first second third,
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null first second ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null second third ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null first third.
```

## `query_expr_global_typed_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:897`](../OrderedQueryFacts.v#L897)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36), `schema` (rank 52)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_sym :
  forall left right,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null left right ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null right left.
```

## `query_expr_global_typed_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:911`](../OrderedQueryFacts.v#L911)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 30), `runtime` (rank 36), `schema` (rank 52)

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_trans :
  forall first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null first third.
```

## `query_expr_context_global_equiv_chain`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:929`](../OrderedQueryFacts.v#L929)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 36)

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_context_global_equiv_chain :
  forall context first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null
      (plug_query_expr_context context first)
      (plug_query_expr_context context third).
```

## `eval_query_expr_project_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:969`](../OrderedQueryFacts.v#L969)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1148`](../OrderedQueryFacts.v#L1148)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 32), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_filter_error_iff :
  forall env formula input error,
    eval_query env (QExpr_Filter formula input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlError error).
```

## `eval_filter_rows_has_outcome_of_formula_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1171`](../OrderedQueryFacts.v#L1171)

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_filter_rows_has_outcome_of_formula_total :
  forall env formula rows,
    (forall row,
      In row rows ->
      exists outcome,
        @eval_formula_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          (env_t T env row) formula outcome) ->
    exists outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env formula rows outcome.
```

## `query_expr_filter_has_outcome_of_formula_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1200`](../OrderedQueryFacts.v#L1200)

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 36), `filter` (rank 46)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_filter_has_outcome_of_formula_total :
  forall env formula input,
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      forall row,
        In row input_rows ->
        exists outcome,
          @eval_formula_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            (env_t T env row) formula outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Filter formula input) outcome.
```

## `query_filter_error_iff_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1293`](../OrderedQueryFacts.v#L1293)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 30), `filter` (rank 44)

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem query_filter_error_iff_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall input_rows row,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
```

## `query_expr_filter_outcome_equiv_of_always_true`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2757`](../OrderedQueryFacts.v#L2757)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 22), `runtime` (rank 34), `filter` (rank 42)

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
          @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
            value_is_null (env_t T env row) formula outcome <->
          outcome = SqlSuccess (Bool.true (B T))) ->
    query_outcome_equiv env (QExpr_Filter formula input) input.
```

## `project_rows_outcome_all_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2928`](../OrderedQueryFacts.v#L2928)

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

## `query_expr_project_has_success_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2949`](../OrderedQueryFacts.v#L2949)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 36), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_project_has_success_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_has_success env input ->
    query_has_success env (QExpr_Project select_list input).
```

## `eval_query_expr_project_error_iff_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2970`](../OrderedQueryFacts.v#L2970)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 32), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_project_error_iff_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    forall error,
      eval_query env (QExpr_Project select_list input) (SqlError error) <->
      eval_query env input (SqlError error).
```

## `query_expr_project_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2991`](../OrderedQueryFacts.v#L2991)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 30), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_project_runtime_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_safe env input ->
    query_safe env (QExpr_Project select_list input).
```

## `query_expr_project_has_outcome_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3009`](../OrderedQueryFacts.v#L3009)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome` (rank 36), `runtime` (rank 36), `projection` (rank 52)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_project_has_outcome_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Project select_list input) outcome.
```

## `query_expr_project_select_lists_outcome_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3030`](../OrderedQueryFacts.v#L3030)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 28), `runtime` (rank 34), `projection` (rank 50)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_project_select_lists_outcome_equiv_safe :
  forall env left_select right_select input,
    select_list_outputs left_select = select_list_outputs right_select ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) left_select = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) right_select = None) ->
    (forall input_rows row,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      Oeset.compare (OTuple T)
        (projection T (env_t T env row) (@Select_List T left_select))
        (projection T (env_t T env row) (@Select_List T right_select)) = Eq) ->
    (exists outcome, eval_query env input outcome) ->
    query_outcome_equiv env
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
```

## `query_expr_project_bag_closed_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3278`](../OrderedQueryFacts.v#L3278)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime` (rank 34), `projection` (rank 2), `bag` (rank 6)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_project_bag_closed_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    BagClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_Project select_list input) (SqlSuccess rows)).
```

## `query_expr_project_outcome_equiv_of_success_bags_safe_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3341`](../OrderedQueryFacts.v#L3341)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome` (rank 22), `runtime` (rank 34), `projection` (rank 50), `bag` (rank 50)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_project_outcome_equiv_of_success_bags_safe_closed :
  forall env left_select right_select left_input right_input,
    query_expr_outputs (QExpr_Project left_select left_input) =
      query_expr_outputs (QExpr_Project right_select right_input) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) left_select = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) right_select = None) ->
    BagClosed T
      (fun rows => eval_query env left_input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query env right_input (SqlSuccess rows)) ->
    rel_equiv
      (success_bags env (QExpr_Project left_select left_input))
      (success_bags env (QExpr_Project right_select right_input)) ->
    (exists outcome,
      eval_query env (QExpr_Project left_select left_input) outcome) ->
    (exists outcome,
      eval_query env (QExpr_Project right_select right_input) outcome) ->
    (forall error,
      eval_query env (QExpr_Project left_select left_input)
        (SqlError error) <->
      eval_query env (QExpr_Project right_select right_input)
        (SqlError error)) ->
    query_outcome_equiv env
      (QExpr_Project left_select left_input)
      (QExpr_Project right_select right_input).
```

## `query_expr_cross_join_union_right_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3423`](../OrderedQueryFacts.v#L3423)

Purpose/direction: Assembles the right-hand CROSS JOIN/UNION ALL distribution law into a safe exact query equivalence with explicit runtime premises.

Applicability: Use after the two sort equalities, duplicated-left functionality, complete source/target safety, and source-success premises are all available.

Important premises: Retain both sort equalities, duplicated-left bag functionality, source and target safety, and the source-success witness.

Cross-index: `outcome` (rank 22), `runtime` (rank 34), `join` (rank 20), `bag` (rank 50)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_cross_join_union_right_equiv_safe :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    query_safe env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_safe env
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)) ->
    query_has_success env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_equiv env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
```

## `query_expr_cross_join_union_right_outcome_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3458`](../OrderedQueryFacts.v#L3458)

Purpose/direction: Assembles the right-hand CROSS JOIN/UNION ALL distribution law into a safe exact query equivalence with explicit runtime premises.

Applicability: Use after the two sort equalities, duplicated-left functionality, complete source/target safety, and source-success premises are all available.

Important premises: Retain both sort equalities, duplicated-left bag functionality, source and target safety, and the source-success witness.

Cross-index: `outcome` (rank 28), `runtime` (rank 34), `join` (rank 20), `bag` (rank 50)

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_cross_join_union_right_outcome_equiv_safe :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    query_safe env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_safe env
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)) ->
    query_has_success env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_outcome_equiv env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
```

## `query_expr_project_outcome_equiv_congr_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3491`](../OrderedQueryFacts.v#L3491)

Purpose/direction: Lifts a fixed-environment child outcome equivalence through one locally safe projection.

Applicability: Use to lift a child outcome equivalence at the same environment through the same SELECT list after proving per-row local safety.

Important premises: Supply the fixed-environment child outcome equivalence plus SELECT-list safety for every row; ordered output and errors remain observable.

Cross-index: `outcome` (rank 24), `runtime` (rank 34), `projection` (rank 22)

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

## `tnull_join_condition_pred_acceptance_exact_safe`

Source: [`theories/FormalSQL/ProofAgentFacade.v:91`](../ProofAgentFacade.v#L91)

Purpose/direction: Builds the generic exact join-acceptance contract for a runtime-safe TNull scalar predicate while preserving authoritative Bool3 semantics.

Applicability: Use for a `FExpr_Pred` join condition after proving its eager argument runtime-error classifier is `None`; FALSE and UNKNOWN remain distinct Bool3 results even though both reject the joined row.

Important premises: Retain the displayed `first_runtime_error ... arguments = None` premise at the exact joined-row environment; do not replace the authoritative predicate interpreter or identify FALSE with UNKNOWN.

Cross-index: `facade` (rank 0), `runtime` (rank 4), `filter` (rank 6), `join` (rank 2), `scalar` (rank 16)

Search aliases: `verification and runtime semantics`, `join`, `filter`, `WHERE`, `NULL`, `UNKNOWN`, `three-valued logic`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_join_condition_pred_acceptance_exact_safe :
  forall db env predicate arguments left right,
    first_runtime_error
      (@eval_aggterm_runtime_error TNull
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error
        (env_t TNull env (join_tuple TNull left right)))
      arguments = None ->
    @join_condition_acceptance_exact_at TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (FExpr_Pred predicate arguments) left right
      (Bool.is_true (B TNull)
        (NullValues.interp_predicate predicate
          (map
            (@Interp.interp_aggterm TNull
              (env_t TNull env (join_tuple TNull left right)))
            arguments))).
```

## `tnull_query_expr_project_select_columns_error_iff`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1487`](../ProofAgentFacade.v#L1487)

Purpose/direction: Shows that a direct-column query projection has exactly its child's error observations and introduces no projection-local error.

Applicability: Use to move an error observation across a `SelectColumns` query projection in either direction; no child error is discarded.

Important premises: The projection must have the displayed direct-column form.  Preserve the exact child error and fixed database/environment in both directions.

Cross-index: `facade` (rank 4), `outcome` (rank 4), `runtime` (rank 4), `projection` (rank 6)

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_project_select_columns_error_iff :
  forall db env columns input error,
    TNullQueryExprOutcome db env
      (QExpr_Project (SelectColumns columns) input) (SqlError error) <->
    TNullQueryExprOutcome db env input (SqlError error).
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
