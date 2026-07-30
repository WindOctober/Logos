# Runtime outcomes, verification modes, and rewrite specifications

Route here for: success/error outcomes, safe vs error-preserving equivalence, rewrite contracts.

This focused catalog contains 146 declarations routed at declaration granularity from `AggregateRuntimeFacts.v`, `CountermodelFacts.v`, `OrderedObservationTransportFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`, `SqlQueryContexts.v`, `VerificationConditions.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `successful_outcome_equiv_implies_outcome_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2194`](../AggregateRuntimeFacts.v#L2194)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma successful_outcome_equiv_implies_outcome_equiv :
  forall (A : Type) (value_equiv : A -> A -> Prop) left right,
    successful_outcome_equiv value_equiv left right ->
    outcome_equiv value_equiv left right.
```

## `outcome_equiv_eq_iff`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2203`](../AggregateRuntimeFacts.v#L2203)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_equiv_eq_iff : forall (A : Type) (left right : sql_outcome A),
  outcome_equiv eq left right <-> left = right.
```

## `outcome_equiv_symmetric`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2217`](../AggregateRuntimeFacts.v#L2217)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2230`](../AggregateRuntimeFacts.v#L2230)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

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

## `successful_relation_functional_map`

Source: [`theories/FormalSQL/CountermodelFacts.v:28`](../CountermodelFacts.v#L28)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when the goal or a hypothesis matches the `successful_relation_functional_map` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Theorem successful_relation_functional_map
    {A B : Type} (source_equiv : A -> A -> Prop)
    (target_equiv : B -> B -> Prop)
    (source : sql_outcome A -> Prop) (target : sql_outcome B -> Prop)
    (transform : A -> B) :
  (forall output,
    target (SqlSuccess output) ->
    exists input,
      source (SqlSuccess input) /\ output = transform input) ->
  (forall left right,
    source_equiv left right ->
    target_equiv (transform left) (transform right)) ->
  successful_relation_functional source_equiv source ->
  successful_relation_functional target_equiv target.
```

## `possible_bag_functional_rel_equiv`

Source: [`theories/FormalSQL/CountermodelFacts.v:53`](../CountermodelFacts.v#L53)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem possible_bag_functional_rel_equiv
    (T : Tuple.Rcd) (left right : SqlBagAbstraction.bagT T -> Prop) :
  rel_equiv left right ->
  @possible_bag_functional T left ->
  @possible_bag_functional T right.
```

## `query_success_bags_functional_of_unary_reset`

Source: [`theories/FormalSQL/CountermodelFacts.v:69`](../CountermodelFacts.v#L69)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_success_bags_functional_of_unary_reset
    (T : Tuple.Rcd) (parent_bags input_bags : SqlBagAbstraction.bagT T -> Prop)
    (operation : unary_bag_relation T) :
  rel_equiv parent_bags (lift_possible_bag_unary operation input_bags) ->
  unary_bag_relation_extensional operation ->
  @unary_bag_relation_functional T operation ->
  @possible_bag_functional T input_bags ->
  @possible_bag_functional T parent_bags.
```

## `query_success_bags_functional_of_binary_reset`

Source: [`theories/FormalSQL/CountermodelFacts.v:84`](../CountermodelFacts.v#L84)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_success_bags_functional_of_binary_reset
    (T : Tuple.Rcd)
    (parent_bags left_bags right_bags : SqlBagAbstraction.bagT T -> Prop)
    (operation : binary_bag_relation T) :
  rel_equiv parent_bags
    (lift_possible_bag_binary operation left_bags right_bags) ->
  binary_bag_relation_extensional operation ->
  @binary_bag_relation_functional T operation ->
  @possible_bag_functional T left_bags ->
  @possible_bag_functional T right_bags ->
  @possible_bag_functional T parent_bags.
```

## `outcome_relation_separation_of_left_success_property`

Source: [`theories/FormalSQL/CountermodelFacts.v:115`](../CountermodelFacts.v#L115)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem outcome_relation_separation_of_left_success_property
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) (property : A -> Prop) :
  observation_property_invariant value_equiv property ->
  forall left_value,
    left (SqlSuccess left_value) ->
    property left_value ->
    (forall right_value,
      right (SqlSuccess right_value) ->
      ~ property right_value) ->
    outcome_relation_separation value_equiv left right.
```

## `outcome_relation_separation_of_right_success_property`

Source: [`theories/FormalSQL/CountermodelFacts.v:137`](../CountermodelFacts.v#L137)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem outcome_relation_separation_of_right_success_property
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) (property : A -> Prop) :
  observation_property_invariant value_equiv property ->
  forall right_value,
    right (SqlSuccess right_value) ->
    property right_value ->
    (forall left_value,
      left (SqlSuccess left_value) ->
      ~ property left_value) ->
    outcome_relation_separation value_equiv left right.
```

## `outcome_relation_separation_of_left_error_absent`

Source: [`theories/FormalSQL/CountermodelFacts.v:160`](../CountermodelFacts.v#L160)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem outcome_relation_separation_of_left_error_absent
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) :
  forall error,
    left (SqlError error) ->
    ~ right (SqlError error) ->
    outcome_relation_separation value_equiv left right.
```

## `outcome_relation_separation_of_right_error_absent`

Source: [`theories/FormalSQL/CountermodelFacts.v:172`](../CountermodelFacts.v#L172)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem outcome_relation_separation_of_right_error_absent
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) :
  forall error,
    right (SqlError error) ->
    ~ left (SqlError error) ->
    outcome_relation_separation value_equiv left right.
```

## `ordered_rows_equiv_nb_occ`

Source: [`theories/FormalSQL/CountermodelFacts.v:187`](../CountermodelFacts.v#L187)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_nb_occ :
  forall (T : Tuple.Rcd) (row : tuple T) left right,
    ordered_rows_equiv T left right ->
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T left) =
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T right).
```

## `bag_not_eq_of_occurrence_difference`

Source: [`theories/FormalSQL/CountermodelFacts.v:204`](../CountermodelFacts.v#L204)

Purpose/direction: Relates membership or occurrence evidence to SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_not_eq_of_occurrence_difference :
  forall (T : Tuple.Rcd)
      (left right : SqlBagAbstraction.bagT T) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row left <>
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right ->
    ~ bag_eq T left right.
```

## `ordered_outcome_separation_of_left_success_bag_difference`

Source: [`theories/FormalSQL/CountermodelFacts.v:223`](../CountermodelFacts.v#L223)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem ordered_outcome_separation_of_left_success_bag_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall left_rows,
    left (SqlSuccess left_rows) ->
    (forall right_rows,
      right (SqlSuccess right_rows) ->
      ~ bag_eq T (rows_bag T left_rows) (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
```

## `ordered_outcome_separation_of_right_success_bag_difference`

Source: [`theories/FormalSQL/CountermodelFacts.v:240`](../CountermodelFacts.v#L240)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem ordered_outcome_separation_of_right_success_bag_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall right_rows,
    right (SqlSuccess right_rows) ->
    (forall left_rows,
      left (SqlSuccess left_rows) ->
      ~ bag_eq T (rows_bag T left_rows) (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
```

## `ordered_outcome_separation_of_left_success_occurrence_difference`

Source: [`theories/FormalSQL/CountermodelFacts.v:260`](../CountermodelFacts.v#L260)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem ordered_outcome_separation_of_left_success_occurrence_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall witness_row left_rows,
    left (SqlSuccess left_rows) ->
    (forall right_rows,
      right (SqlSuccess right_rows) ->
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T left_rows) <>
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
```

## `ordered_outcome_separation_of_right_success_occurrence_difference`

Source: [`theories/FormalSQL/CountermodelFacts.v:280`](../CountermodelFacts.v#L280)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem ordered_outcome_separation_of_right_success_occurrence_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall witness_row right_rows,
    right (SqlSuccess right_rows) ->
    (forall left_rows,
      left (SqlSuccess left_rows) ->
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T left_rows) <>
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
```

## `tnull_query_program_nth_separation_sound`

Source: [`theories/FormalSQL/CountermodelFacts.v:303`](../CountermodelFacts.v#L303)

Purpose/direction: States the tnull query program nth separation sound law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_program_nth_separation_sound` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Theorem tnull_query_program_nth_separation_sound :
  forall db env index left_program right_program left_query right_query,
    nth_error left_program index = Some left_query ->
    nth_error right_program index = Some right_query ->
    TNullQueryExprOutcomeSeparation db env left_query right_query ->
    ~ TNullQueryProgramOutcomeEq db env left_program right_program.
```

## `tuple_list_semantic_rel_refl`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:26`](../OrderedObservationTransportFacts.v#L26)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma tuple_list_semantic_rel_refl :
  forall (T : Tuple.Rcd) (rows : list (tuple T)),
    tuple_list_semantic_rel T rows rows.
```

## `tuple_list_semantic_rel_sym`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:35`](../OrderedObservationTransportFacts.v#L35)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma tuple_list_semantic_rel_sym :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    tuple_list_semantic_rel T left right ->
    tuple_list_semantic_rel T right left.
```

## `tuple_list_semantic_rel_trans`

Source: [`theories/FormalSQL/OrderedObservationTransportFacts.v:46`](../OrderedObservationTransportFacts.v#L46)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma tuple_list_semantic_rel_trans :
  forall (T : Tuple.Rcd) (first second third : list (tuple T)),
    tuple_list_semantic_rel T first second ->
    tuple_list_semantic_rel T second third ->
    tuple_list_semantic_rel T first third.
```

## `query_expr_has_success_of_runtime_safe_and_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:118`](../OrderedQueryFacts.v#L118)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_has_success_of_runtime_safe_and_outcome :
  forall env query,
    query_safe env query ->
    (exists outcome, eval_query env query outcome) ->
    query_has_success env query.
```

## `query_expr_has_outcome_of_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:132`](../OrderedQueryFacts.v#L132)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_has_outcome_of_success :
  forall env query,
    query_has_success env query ->
    exists outcome, eval_query env query outcome.
```

## `query_expr_table_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:144`](../OrderedQueryFacts.v#L144)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_table_runtime_safe :
  forall env outputs table,
    query_safe env (QExpr_Table outputs table).
```

## `query_expr_table_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:152`](../OrderedQueryFacts.v#L152)

Purpose/direction: States the query expr table has outcome law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_table_has_outcome :
  forall env outputs table,
    exists outcome, eval_query env (QExpr_Table outputs table) outcome.
```

## `query_expr_values_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:163`](../OrderedQueryFacts.v#L163)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_values_runtime_safe :
  forall env outputs values,
    query_safe env (QExpr_Values outputs values).
```

## `query_expr_values_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:181`](../OrderedQueryFacts.v#L181)

Purpose/direction: States the query expr values has outcome law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_values_has_outcome :
  forall env outputs values,
    exists outcome, eval_query env (QExpr_Values outputs values) outcome.
```

## `query_expr_error_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:193`](../OrderedQueryFacts.v#L193)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_error_has_outcome :
  forall env outputs error,
    exists outcome, eval_query env (QExpr_Error outputs error) outcome.
```

## `query_expr_equiv_refl_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:204`](../OrderedQueryFacts.v#L204)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_refl_safe :
  forall env query,
    query_safe env query ->
    query_has_success env query ->
    query_equiv env query query.
```

## `query_expr_outcome_equiv_refl`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:219`](../OrderedQueryFacts.v#L219)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_refl :
  forall env query,
    (exists outcome, eval_query env query outcome) ->
    query_outcome_equiv env query query.
```

## `query_expr_outcome_equiv_of_eval_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:236`](../OrderedQueryFacts.v#L236)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:264`](../OrderedQueryFacts.v#L264)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `schema`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:281`](../OrderedQueryFacts.v#L281)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `bag`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:329`](../OrderedQueryFacts.v#L329)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `bag`

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

## `query_unary_success_bags_congr_from_characterizations`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:355`](../OrderedQueryFacts.v#L355)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_unary_success_bags_congr_from_characterizations :
  forall env left_parent right_parent left_child right_child
      (left_operation right_operation : unary_bag_relation T),
    rel_equiv
      (success_bags env left_parent)
      (lift_possible_bag_unary left_operation
        (success_bags env left_child)) ->
    rel_equiv
      (success_bags env right_parent)
      (lift_possible_bag_unary right_operation
        (success_bags env right_child)) ->
    rel_equiv
      (success_bags env left_child)
      (success_bags env right_child) ->
    unary_bag_relation_equiv left_operation right_operation ->
    rel_equiv
      (success_bags env left_parent)
      (success_bags env right_parent).
```

## `query_binary_success_bags_congr_from_characterizations`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:384`](../OrderedQueryFacts.v#L384)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_binary_success_bags_congr_from_characterizations :
  forall env left_parent right_parent
      left_child left_child' right_child right_child'
      (left_operation right_operation : binary_bag_relation T),
    rel_equiv
      (success_bags env left_parent)
      (lift_possible_bag_binary left_operation
        (success_bags env left_child) (success_bags env right_child)) ->
    rel_equiv
      (success_bags env right_parent)
      (lift_possible_bag_binary right_operation
        (success_bags env left_child') (success_bags env right_child')) ->
    rel_equiv
      (success_bags env left_child)
      (success_bags env left_child') ->
    rel_equiv
      (success_bags env right_child)
      (success_bags env right_child') ->
    binary_bag_relation_equiv left_operation right_operation ->
    rel_equiv
      (success_bags env left_parent)
      (success_bags env right_parent).
```

## `query_set_success_bags_congr_extensional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:418`](../OrderedQueryFacts.v#L418)

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_set_success_bags_congr_extensional :
  forall env left_operation right_operation
      left left' right right',
    rel_equiv (success_bags env left) (success_bags env left') ->
    rel_equiv (success_bags env right) (success_bags env right') ->
    binary_bag_relation_equiv
      (query_set_bag_relation left_operation left right)
      (query_set_bag_relation right_operation left' right') ->
    rel_equiv
      (success_bags env (QExpr_Set left_operation left right))
      (success_bags env (QExpr_Set right_operation left' right')).
```

## `query_join_success_bags_congr_extensional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:440`](../OrderedQueryFacts.v#L440)

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `join`, `bag`

Search aliases: `verification and runtime semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_join_success_bags_congr_extensional :
  forall env
      left_kind left_predicate left_matched left_left_select left_right_select
      right_kind right_predicate right_matched right_left_select
      right_right_select left left' right right',
    rel_equiv (success_bags env left) (success_bags env left') ->
    rel_equiv (success_bags env right) (success_bags env right') ->
    binary_bag_relation_equiv
      (@query_join_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left_kind left_predicate
        left_matched left_left_select left_right_select)
      (@query_join_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env right_kind right_predicate
        right_matched right_left_select right_right_select) ->
    rel_equiv
      (success_bags env
        (QExpr_Join left_kind left_predicate
          left_matched left_left_select left_right_select left right))
      (success_bags env
        (QExpr_Join right_kind right_predicate
          right_matched right_left_select right_right_select left' right')).
```

## `eval_query_expr_set_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:646`](../OrderedQueryFacts.v#L646)

Purpose/direction: Characterizes a set-operation error as a left error or as a right error reached after one successful left observation.

Applicability: Use to invert or construct the exact parent error schedule; a right-child error is observable only with the displayed left-success witness.

Important premises: Retain the existential successful left observation in the right-error arm; right errors do not bypass a left error-only execution.

Cross-index: `runtime`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:663`](../OrderedQueryFacts.v#L663)

Purpose/direction: Characterizes a CROSS JOIN error with its exact left-to-right child evaluation schedule.

Applicability: Use to invert or construct the exact parent error schedule; a right-child error is observable only with the displayed left-success witness.

Important premises: Retain the existential successful left observation in the right-error arm; right errors do not bypass a left error-only execution.

Cross-index: `runtime`, `join`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:680`](../OrderedQueryFacts.v#L680)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL bag/set operations.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `set operation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_set_runtime_safe :
  forall env operation left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_Set operation left right).
```

## `query_expr_cross_join_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:693`](../OrderedQueryFacts.v#L693)

Purpose/direction: Establishes the explicit runtime-safety direction for join semantics.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `join`

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_cross_join_runtime_safe :
  forall env left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_CrossJoin left right).
```

## `query_expr_set_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:783`](../OrderedQueryFacts.v#L783)

Purpose/direction: States the query expr set has outcome law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_set_has_outcome :
  forall env operation left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_Set operation left right) outcome.
```

## `query_expr_cross_join_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:804`](../OrderedQueryFacts.v#L804)

Purpose/direction: States the query expr cross join has outcome law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_cross_join_has_outcome :
  forall env left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_CrossJoin left right) outcome.
```

## `query_expr_set_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:829`](../OrderedQueryFacts.v#L829)

Purpose/direction: Lifts two child outcome equivalences through a set-operation bag reset while preserving exact output schema and short-circuit errors.

Applicability: Use to lift two local child outcome equivalences through any modeled set operation; no safety or success premise is required, and sort mismatch behavior remains authoritative.

Important premises: Supply both displayed child outcome equivalences.  Do not assume set sort compatibility: matching sort-mismatch outcomes are preserved.

Cross-index: `outcome`, `runtime`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:919`](../OrderedQueryFacts.v#L919)

Purpose/direction: Lifts two child outcome equivalences through CROSS JOIN's bag reset while preserving appended output schema, multiplicity, and errors.

Applicability: Use to lift two local child outcome equivalences through CROSS JOIN; no safety or success premise is required.

Important premises: Supply both displayed child outcome equivalences; no runtime-safety or successful-outcome premise may be silently added or inferred.

Cross-index: `outcome`, `runtime`, `join`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1008`](../OrderedQueryFacts.v#L1008)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1132`](../OrderedQueryFacts.v#L1132)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1151`](../OrderedQueryFacts.v#L1151)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_sym :
  forall env left right,
    query_equiv env left right ->
    query_equiv env right left.
```

## `query_expr_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1180`](../OrderedQueryFacts.v#L1180)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_trans :
  forall env first second third,
    query_equiv env first second ->
    query_equiv env second third ->
    query_equiv env first third.
```

## `query_expr_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1215`](../OrderedQueryFacts.v#L1215)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_sym :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env right left.
```

## `query_expr_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1241`](../OrderedQueryFacts.v#L1241)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_trans :
  forall env first second third,
    query_outcome_equiv env first second ->
    query_outcome_equiv env second third ->
    query_outcome_equiv env first third.
```

## `query_expr_global_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1285`](../OrderedQueryFacts.v#L1285)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_sym :
  forall left right,
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null left right ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null right left.
```

## `query_expr_global_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1295`](../OrderedQueryFacts.v#L1295)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_trans :
  forall first second third,
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null first second ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null second third ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null first third.
```

## `query_expr_global_typed_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1309`](../OrderedQueryFacts.v#L1309)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `schema`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1323`](../OrderedQueryFacts.v#L1323)

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `schema`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1341`](../OrderedQueryFacts.v#L1341)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1417`](../OrderedQueryFacts.v#L1417)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1577`](../OrderedQueryFacts.v#L1577)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1600`](../OrderedQueryFacts.v#L1600)

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `filter`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1629`](../OrderedQueryFacts.v#L1629)

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `filter`

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

## `query_filter_success_bags_congr_extensional_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1726`](../OrderedQueryFacts.v#L1726)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `filter`, `bag`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_filter_success_bags_congr_extensional_exact :
  forall env left_formula right_formula left right
      (keep : tuple T -> bool),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) left_formula (keep row)) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) right_formula (keep row)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_Filter left_formula left))
      (success_bags env (QExpr_Filter right_formula right)).
```

## `query_filter_success_bags_congr_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1771`](../OrderedQueryFacts.v#L1771)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `filter`, `bag`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_filter_success_bags_congr_exact :
  forall env formula left right (keep : tuple T -> bool),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_Filter formula left))
      (success_bags env (QExpr_Filter formula right)).
```

## `query_filter_success_bags_congr_of_contract`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1814`](../OrderedQueryFacts.v#L1814)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `filter`, `bag`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_filter_success_bags_congr_of_contract :
  forall env left_formula right_formula left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    filter_success_bag_contract env left_formula right_formula ->
    rel_equiv
      (success_bags env (QExpr_Filter left_formula left))
      (success_bags env (QExpr_Filter right_formula right)).
```

## `query_filter_error_iff_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1831`](../OrderedQueryFacts.v#L1831)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

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

## `query_expr_filter_runtime_safe_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1890`](../OrderedQueryFacts.v#L1890)

Purpose/direction: States the query expr filter runtime safe exact law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_filter_runtime_safe_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    query_safe env input ->
    query_safe env (QExpr_Filter formula input).
```

## `query_expr_filter_has_outcome_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1911`](../OrderedQueryFacts.v#L1911)

Purpose/direction: States the query expr filter has outcome exact law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_filter_has_outcome_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Filter formula input) outcome.
```

## `query_list_transform_success_bags_congr_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2923`](../OrderedQueryFacts.v#L2923)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_list_transform_success_bags_congr_closed :
  forall env left_parent right_parent left right
      (transform : list (tuple T) -> list (tuple T)),
    (forall output,
      eval_query env left_parent (SqlSuccess output) <->
      exists input_rows,
        eval_query env left (SqlSuccess input_rows) /\
        output = transform input_rows) ->
    (forall output,
      eval_query env right_parent (SqlSuccess output) <->
      exists input_rows,
        eval_query env right (SqlSuccess input_rows) /\
        output = transform input_rows) ->
    (forall first second,
      ordered_rows_equiv T first second ->
      ordered_rows_equiv T (transform first) (transform second)) ->
    BagClosed T (fun rows => eval_query env left (SqlSuccess rows)) ->
    BagClosed T (fun rows => eval_query env right (SqlSuccess rows)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env left_parent)
      (success_bags env right_parent).
```

## `query_expr_filter_outcome_equiv_of_always_true`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3878`](../OrderedQueryFacts.v#L3878)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4049`](../OrderedQueryFacts.v#L4049)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `projection`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4070`](../OrderedQueryFacts.v#L4070)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4091`](../OrderedQueryFacts.v#L4091)

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4112`](../OrderedQueryFacts.v#L4112)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4130`](../OrderedQueryFacts.v#L4130)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`, `projection`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4151`](../OrderedQueryFacts.v#L4151)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`

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

## `row_map_rows_outcome_total_as`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4341`](../OrderedQueryFacts.v#L4341)

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma row_map_rows_outcome_total_as :
  forall row_map mapping rows,
    row_map_total_as row_map mapping ->
    @row_map_rows_outcome T row_map rows =
      SqlSuccess (map mapping rows).
```

## `query_row_map_bag_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4358`](../OrderedQueryFacts.v#L4358)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_row_map_bag_congr :
  forall mapping left right,
    row_mapping_semantic_proper mapping ->
    bag_eq T left right ->
    bag_eq T
      (query_row_map_bag mapping left)
      (query_row_map_bag mapping right).
```

## `query_row_map_success_bags_congr_extensional_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4418`](../OrderedQueryFacts.v#L4418)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_row_map_success_bags_congr_extensional_total :
  forall env left_outputs right_outputs left_row_map right_row_map
      left_mapping right_mapping left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    row_map_total_as left_row_map left_mapping ->
    row_map_total_as right_row_map right_mapping ->
    row_mapping_semantic_proper left_mapping ->
    row_mapping_semantic_proper right_mapping ->
    (forall input_bag,
      success_bags env left input_bag ->
      bag_eq T
        (query_row_map_bag left_mapping input_bag)
        (query_row_map_bag right_mapping input_bag)) ->
    rel_equiv
      (success_bags env (QExpr_RowMap left_outputs left_row_map left))
      (success_bags env (QExpr_RowMap right_outputs right_row_map right)).
```

## `query_row_map_success_bags_congr_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4462`](../OrderedQueryFacts.v#L4462)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_row_map_success_bags_congr_total :
  forall env outputs row_map mapping left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    row_map_total_as row_map mapping ->
    row_mapping_semantic_proper mapping ->
    rel_equiv
      (success_bags env (QExpr_RowMap outputs row_map left))
      (success_bags env (QExpr_RowMap outputs row_map right)).
```

## `query_row_map_success_bags_congr_of_contract`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4486`](../OrderedQueryFacts.v#L4486)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_row_map_success_bags_congr_of_contract :
  forall env outputs row_map left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    row_map_success_bag_contract row_map ->
    rel_equiv
      (success_bags env (QExpr_RowMap outputs row_map left))
      (success_bags env (QExpr_RowMap outputs row_map right)).
```

## `query_row_map_success_bags_congr_extensional_of_contract`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4551`](../OrderedQueryFacts.v#L4551)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_row_map_success_bags_congr_extensional_of_contract :
  forall env left_outputs right_outputs left_row_map right_row_map left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    row_map_success_bag_extensional_contract
      env left_row_map right_row_map left ->
    rel_equiv
      (success_bags env (QExpr_RowMap left_outputs left_row_map left))
      (success_bags env (QExpr_RowMap right_outputs right_row_map right)).
```

## `query_expr_project_bag_closed_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4642`](../OrderedQueryFacts.v#L4642)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `projection`, `bag`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4705`](../OrderedQueryFacts.v#L4705)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`, `bag`

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

## `query_project_success_bags_congr_extensional_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4782`](../OrderedQueryFacts.v#L4782)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_project_success_bags_congr_extensional_safe :
  forall env left_select right_select left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) left_select = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) right_select = None) ->
    project_success_bag_extensional_contract
      env left_select right_select left ->
    rel_equiv
      (success_bags env (QExpr_Project left_select left))
      (success_bags env (QExpr_Project right_select right)).
```

## `query_project_success_bags_congr_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4825`](../OrderedQueryFacts.v#L4825)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_project_success_bags_congr_safe :
  forall env select_list left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    rel_equiv
      (success_bags env (QExpr_Project select_list left))
      (success_bags env (QExpr_Project select_list right)).
```

## `query_project_success_bags_fusion_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4860`](../OrderedQueryFacts.v#L4860)

Purpose/direction: Uses three locally safe projections and their reachable-bag fusion contract to equate the possible successful bags of one and two Projects.

Applicability: Use after proving all three SELECT lists locally safe and the named fusion contract on every reachable child bag; errors and ordered observations are outside this success-bag theorem.

Important premises: Keep all three per-row SELECT safety premises and the exact reachable-bag fusion contract; the theorem does not establish error equivalence.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_success_bags_fusion_safe :
  forall env single outer inner input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) single = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) outer = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) inner = None) ->
    project_fusion_success_bag_contract env single outer inner input ->
    rel_equiv
      (success_bags env (QExpr_Project single input))
      (success_bags env
        (QExpr_Project outer (QExpr_Project inner input))).
```

## `query_project_success_bags_identity_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4912`](../OrderedQueryFacts.v#L4912)

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_success_bags_identity_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    (forall input_bag,
      success_bags env input input_bag ->
      bag_eq T (query_project_bag env select_list input_bag) input_bag) ->
    rel_equiv
      (success_bags env (QExpr_Project select_list input))
      (success_bags env input).
```

## `query_error_success_bags_empty`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4950`](../OrderedQueryFacts.v#L4950)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_error_success_bags_empty :
  forall env outputs error output,
    ~ success_bags env (QExpr_Error outputs error) output.
```

## `query_values_success_bags_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5002`](../OrderedQueryFacts.v#L5002)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_values_success_bags_congr :
  forall env left_outputs right_outputs left_values right_values,
    bag_eq T left_values right_values ->
    rel_equiv
      (success_bags env (QExpr_Values left_outputs left_values))
      (success_bags env (QExpr_Values right_outputs right_values)).
```

## `query_table_success_bags_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5023`](../OrderedQueryFacts.v#L5023)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_table_success_bags_congr :
  forall env left_outputs right_outputs left_table right_table,
    bag_eq T
      (@query_table_bag T relname basesort instance
        left_outputs left_table)
      (@query_table_bag T relname basesort instance
        right_outputs right_table) ->
    rel_equiv
      (success_bags env (QExpr_Table left_outputs left_table))
      (success_bags env (QExpr_Table right_outputs right_table)).
```

## `query_expr_cross_join_union_right_equiv_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5073`](../OrderedQueryFacts.v#L5073)

Purpose/direction: Assembles the right-hand CROSS JOIN/UNION ALL distribution law into a safe exact query equivalence with explicit runtime premises.

Applicability: Use after the two sort equalities, duplicated-left functionality, complete source/target safety, and source-success premises are all available.

Important premises: Retain both sort equalities, duplicated-left bag functionality, source and target safety, and the source-success witness.

Cross-index: `outcome`, `runtime`, `join`, `bag`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5108`](../OrderedQueryFacts.v#L5108)

Purpose/direction: Assembles the right-hand CROSS JOIN/UNION ALL distribution law into a safe exact query equivalence with explicit runtime premises.

Applicability: Use after the two sort equalities, duplicated-left functionality, complete source/target safety, and source-success premises are all available.

Important premises: Retain both sort equalities, duplicated-left bag functionality, source and target safety, and the source-success witness.

Cross-index: `outcome`, `runtime`, `join`, `bag`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5141`](../OrderedQueryFacts.v#L5141)

Purpose/direction: Lifts a fixed-environment child outcome equivalence through one locally safe projection.

Applicability: Use to lift a child outcome equivalence at the same environment through the same SELECT list after proving per-row local safety.

Important premises: Supply the fixed-environment child outcome equivalence plus SELECT-list safety for every row; ordered output and errors remain observable.

Cross-index: `outcome`, `runtime`, `projection`

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

## `query_expr_project_outcome_equiv_congr_extensional_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5234`](../OrderedQueryFacts.v#L5234)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_project_outcome_equiv_congr_extensional_safe :
  forall env left_select right_select left right,
    query_outcome_equiv env left right ->
    select_list_outputs left_select = select_list_outputs right_select ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) left_select = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) right_select = None) ->
    (forall input_rows row,
      eval_query env right (SqlSuccess input_rows) ->
      In row input_rows ->
      Oeset.compare (OTuple T)
        (projection T (env_t T env row) (@Select_List T left_select))
        (projection T (env_t T env row) (@Select_List T right_select)) = Eq) ->
    query_outcome_equiv env
      (QExpr_Project left_select left)
      (QExpr_Project right_select right).
```

## `position_rows_from_nth_error`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5594`](../OrderedQueryFacts.v#L5594)

Purpose/direction: Characterizes zero-based positions and inclusive prefixes of an arbitrary occurrence list, preserving empty inputs and duplicate rows.

Applicability: Use as an intrinsic list/position or comparator-run fact.  Connect it to QExpr_Rank/QExpr_Window only after proving the authoritative legal ordering, aggregate/runtime-error, and BagClosed boundary premises.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `position`, `indexed lookup`, `window`

```rocq
Theorem position_rows_from_nth_error :
  forall (A : Type) start (rows : list A) index,
    nth_error (position_rows_from start rows) index =
    option_map (fun row => (start + index, row)) (nth_error rows index).
```

## `tnull_join_condition_pred_acceptance_exact_safe`

Source: [`theories/FormalSQL/ProofAgentFacade.v:557`](../ProofAgentFacade.v#L557)

Purpose/direction: Builds the generic exact join-acceptance contract for a runtime-safe TNull scalar predicate while preserving authoritative Bool3 semantics.

Applicability: Use for a `FExpr_Pred` join condition after proving its eager argument runtime-error classifier is `None`; FALSE and UNKNOWN remain distinct Bool3 results even though both reject the joined row.

Important premises: Retain the displayed `first_runtime_error ... arguments = None` premise at the exact joined-row environment; do not replace the authoritative predicate interpreter or identify FALSE with UNKNOWN.

Cross-index: `facade`, `runtime`, `filter`, `join`, `scalar`

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

## `tnull_query_expr_outcome_separation_sound`

Source: [`theories/FormalSQL/ProofAgentFacade.v:644`](../ProofAgentFacade.v#L644)

Purpose/direction: States the tnull query expr outcome separation sound law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_outcome_separation_sound :
  forall db env left right,
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryExprOutcomeEq db env left right.
```

## `tnull_query_expr_outcome_separation_of_left_success_length_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:664`](../ProofAgentFacade.v#L664)

Purpose/direction: Relates SQL verification and runtime outcomes to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_outcome_separation_of_left_success_length_difference :
  forall db env left right left_rows,
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    (forall right_rows,
      TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
      List.length left_rows <> List.length right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `tnull_query_expr_outcome_separation_of_right_success_length_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:680`](../ProofAgentFacade.v#L680)

Purpose/direction: Relates SQL verification and runtime outcomes to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_outcome_separation_of_right_success_length_difference :
  forall db env left right right_rows,
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    (forall left_rows,
      TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
      List.length left_rows <> List.length right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `tnull_query_expr_outcome_separation_of_right_functional_observation_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:696`](../ProofAgentFacade.v#L696)

Purpose/direction: States the tnull query expr outcome separation of right functional observation difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_outcome_separation_of_right_functional_observation_difference :
  forall db env left right left_rows right_rows,
    TNullQueryExprObservationFunctional db env right ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullRowsObservationEq left_rows right_rows ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `tnull_query_expr_outcome_separation_of_left_functional_observation_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:713`](../ProofAgentFacade.v#L713)

Purpose/direction: States the tnull query expr outcome separation of left functional observation difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `facade`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_outcome_separation_of_left_functional_observation_difference :
  forall db env left right left_rows right_rows,
    TNullQueryExprObservationFunctional db env left ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullRowsObservationEq left_rows right_rows ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `tnull_query_expr_outcome_separation_of_right_functional_bag_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:735`](../ProofAgentFacade.v#L735)

Purpose/direction: States the tnull query expr outcome separation of right functional bag difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_query_expr_outcome_separation_of_right_functional_bag_difference :
  forall db env left right left_rows right_rows,
    TNullQuerySuccessBagFunctional db env right ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullBagEq (TNullRowsBag left_rows) (TNullRowsBag right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `tnull_query_expr_outcome_separation_of_left_functional_bag_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:759`](../ProofAgentFacade.v#L759)

Purpose/direction: States the tnull query expr outcome separation of left functional bag difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_query_expr_outcome_separation_of_left_functional_bag_difference :
  forall db env left right left_rows right_rows,
    TNullQuerySuccessBagFunctional db env left ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullBagEq (TNullRowsBag left_rows) (TNullRowsBag right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `tnull_query_expr_project_select_columns_error_iff`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2727`](../ProofAgentFacade.v#L2727)

Purpose/direction: Shows that a direct-column query projection has exactly its child's error observations and introduces no projection-local error.

Applicability: Use to move an error observation across a `SelectColumns` query projection in either direction; no child error is discarded.

Important premises: The projection must have the displayed direct-column form.  Preserve the exact child error and fixed database/environment in both directions.

Cross-index: `facade`, `outcome`, `runtime`, `projection`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_project_select_columns_error_iff :
  forall db env columns input error,
    TNullQueryExprOutcome db env
      (QExpr_Project (SelectColumns columns) input) (SqlError error) <->
    TNullQueryExprOutcome db env input (SqlError error).
```

## `condition_true_well_formed`

Source: [`theories/FormalSQL/VerificationConditions.v:210`](../VerificationConditions.v#L210)

Purpose/direction: States the condition true well formed law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `condition_true_well_formed` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma condition_true_well_formed :
  forall expected,
    verification_condition_well_formed expected ConditionTrue.
```

## `condition_true_holds`

Source: [`theories/FormalSQL/VerificationConditions.v:217`](../VerificationConditions.v#L217)

Purpose/direction: States the condition true holds law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `condition_true_holds` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma condition_true_holds :
  forall db,
    verification_condition_holds db ConditionTrue.
```

## `condition_true_is_derived`

Source: [`theories/FormalSQL/VerificationConditions.v:224`](../VerificationConditions.v#L224)

Purpose/direction: States the condition true is derived law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `condition_true_is_derived` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma condition_true_is_derived :
  forall expected constraints,
    precondition_source_obligation
      expected constraints PreconditionDerived ConditionTrue.
```

## `query_expr_global_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:179`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L179)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_refl :
  forall query, query_expr_global_outcome_equiv query query.
```

## `query_expr_global_cardinality_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:185`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L185)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_cardinality_outcome_equiv_refl :
  forall query, query_expr_global_cardinality_outcome_equiv query query.
```

## `query_expr_global_exists_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:191`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L191)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_exists_outcome_equiv_refl :
  forall query, query_expr_global_exists_outcome_equiv query query.
```

## `formula_expr_global_filter_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:197`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L197)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_global_filter_outcome_equiv_refl :
  forall formula,
    formula_expr_global_filter_outcome_equiv formula formula.
```

## `formula_expr_global_filter_outcome_equiv_sym`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:209`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L209)

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_global_filter_outcome_equiv_sym :
  forall left right,
    formula_expr_global_filter_outcome_equiv left right ->
    formula_expr_global_filter_outcome_equiv right left.
```

## `formula_expr_conj_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:228`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L228)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_conj_global_congr :
  forall operation first first' second second',
    formula_expr_global_outcome_equiv first first' ->
    formula_expr_global_outcome_equiv second second' ->
    formula_expr_global_outcome_equiv
      (FExpr_Conj operation first second) (FExpr_Conj operation first' second').
```

## `formula_expr_not_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:249`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L249)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_not_global_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    formula_expr_global_outcome_equiv (FExpr_Not first) (FExpr_Not second).
```

## `formula_expr_quant_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:261`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L261)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_quant_global_congr :
  forall quantifier predicate arguments first second,
    query_expr_global_typed_outcome_equiv first second ->
    formula_expr_global_outcome_equiv
      (FExpr_Quant quantifier predicate arguments first)
      (FExpr_Quant quantifier predicate arguments second).
```

## `formula_expr_in_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:284`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L284)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `IN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_in_global_congr :
  forall select_items first second,
    query_expr_global_outcome_equiv first second ->
    formula_expr_global_outcome_equiv
      (FExpr_In select_items first) (FExpr_In select_items second).
```

## `formula_expr_exists_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:304`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L304)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `EXISTS`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_exists_global_congr :
  forall first second,
    query_expr_global_exists_outcome_equiv first second ->
    formula_expr_global_outcome_equiv
      (FExpr_Exists first) (FExpr_Exists second).
```

## `formula_expr_global_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:319`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L319)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_global_outcome_equiv_refl :
  forall formula, formula_expr_global_outcome_equiv formula formula.
```

## `formula_expr_global_group_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:325`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L325)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`

Search aliases: `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_global_group_outcome_equiv_refl :
  forall formula, formula_expr_global_group_outcome_equiv formula formula.
```

## `formula_expr_conj_global_group_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:333`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L333)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`

Search aliases: `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_conj_global_group_congr :
  forall operation first first' second second',
    formula_expr_global_group_outcome_equiv first first' ->
    formula_expr_global_group_outcome_equiv second second' ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Conj operation first second)
      (FExpr_Conj operation first' second').
```

## `formula_expr_not_global_group_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:349`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L349)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`

Search aliases: `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_not_global_group_congr :
  forall first second,
    formula_expr_global_group_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Not first) (FExpr_Not second).
```

## `formula_expr_quant_global_group_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:361`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L361)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_quant_global_group_congr :
  forall quantifier predicate arguments first second,
    query_expr_global_typed_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Quant quantifier predicate arguments first)
      (FExpr_Quant quantifier predicate arguments second).
```

## `formula_expr_in_global_group_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:373`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L373)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `IN`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_in_global_group_congr :
  forall select_items first second,
    query_expr_global_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_In select_items first) (FExpr_In select_items second).
```

## `formula_expr_exists_global_group_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:384`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L384)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `grouping`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `EXISTS`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_exists_global_group_congr :
  forall first second,
    query_expr_global_exists_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Exists first) (FExpr_Exists second).
```

## `query_expr_global_typed_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:395`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L395)

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `schema`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_refl :
  forall query, query_expr_global_typed_outcome_equiv query query.
```

## `query_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1340`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1340)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_context_global_congr :
  (forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement')) /\
  (forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    formula_expr_global_group_outcome_equiv
      (plug_formula_expr_context context replacement)
      (plug_formula_expr_context context replacement')).
```

## `query_expr_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1416`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1416)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_context_global_congr :
  forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
```

## `formula_expr_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1426`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1426)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem formula_expr_context_global_congr :
  forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    formula_expr_global_outcome_equiv
      (plug_formula_expr_context context replacement)
      (plug_formula_expr_context context replacement').
```

## `query_expr_observation_equiv_of_outcome_rel_equiv_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1448`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1448)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_observation_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_observation_equiv T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null
      env first second.
```

## `query_expr_equiv_of_outcome_rel_equiv_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1473`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1473)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env first second.
```

## `query_expr_context_equiv_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1488`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1488)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_context_equiv_safe :
  forall context replacement replacement' env,
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement) ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement') ->
    query_expr_has_success env
      (plug_query_expr_context context replacement) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
```

## `query_bag_closed_equiv_of_success_bags_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1513`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1513)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_bag_closed_equiv_of_success_bags_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    BagClosed T
      (fun rows => eval_query env first (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query env second (SqlSuccess rows)) ->
    rel_equiv
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env first second.
```

## `query_bag_reset_equiv_of_success_bags_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1562`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1562)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_bag_reset_equiv_of_success_bags_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_order_behavior first = BagReset ->
    query_expr_order_behavior second = BagReset ->
    rel_equiv
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env first second.
```

## `query_distinct_equiv_of_local_success_rel_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1590`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1590)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `DISTINCT`, `duplicate elimination`, `equivalence`, `congruence`

```rocq
Theorem query_distinct_equiv_of_local_success_rel_equiv :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall left_rows,
      eval_query env left (SqlSuccess left_rows) ->
      exists right_rows,
        eval_query env right (SqlSuccess right_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      eval_query env right (SqlSuccess right_rows) ->
      exists left_rows,
        eval_query env left (SqlSuccess left_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    query_expr_runtime_safe env (QExpr_Distinct left) ->
    query_expr_runtime_safe env (QExpr_Distinct right) ->
    query_expr_has_success env (QExpr_Distinct left) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_distinct_local_list_equiv_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1627`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1627)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `runtime`

Search aliases: `verification and runtime semantics`, `DISTINCT`, `duplicate elimination`, `equivalence`, `congruence`

```rocq
Theorem query_distinct_local_list_equiv_congr :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Distinct left) (QExpr_Distinct right).
```

## `plug_possible_bag_context_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1701`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1701)

Purpose/direction: States the plug possible bag context extensional law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem plug_possible_bag_context_extensional :
  forall context replacement,
    possible_bag_context_well_formed context ->
    possible_bag_extensional T replacement ->
    possible_bag_extensional T
      (plug_possible_bag_context context replacement).
```

## `possible_bag_context_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1722`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1722)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem possible_bag_context_congr :
  forall context first second,
    rel_equiv first second ->
    rel_equiv
      (plug_possible_bag_context context first)
      (plug_possible_bag_context context second).
```

## `outcome_alpha_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1740`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1740)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_alpha_congr :
  forall (first second : sql_outcome (list tuple) -> Prop),
    rel_equiv first second ->
    rel_equiv (@outcome_alpha T first) (@outcome_alpha T second).
```

## `successful_relation_equiv_possible_bags_rel_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1754`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1754)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma successful_relation_equiv_possible_bags_rel_equiv :
  forall (first second : sql_outcome (list tuple) -> Prop),
    successful_relation_equiv (@ordered_rows_equiv T) first second ->
    rel_equiv
      (successful_possible_bags first)
      (successful_possible_bags second).
```

## `successful_possible_bags_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1780`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1780)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma successful_possible_bags_extensional :
  forall observations,
    possible_bag_extensional T (successful_possible_bags observations).
```

## `possible_bag_context_successful_plug_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1789`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1789)

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem possible_bag_context_successful_plug_extensional :
  forall context observations,
    possible_bag_context_well_formed context ->
    possible_bag_extensional T
      (plug_possible_bag_context context
        (successful_possible_bags observations)).
```

## `list_outcome_equiv_successful_possible_bags`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1801`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1801)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma list_outcome_equiv_successful_possible_bags :
  forall (first second : sql_outcome (list tuple) -> Prop),
    rel_equiv first second ->
    rel_equiv
      (successful_possible_bags first)
      (successful_possible_bags second).
```

## `list_outcome_equiv_possible_bag_context_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1812`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1812)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem list_outcome_equiv_possible_bag_context_congr :
  forall context (first second : sql_outcome (list tuple) -> Prop),
    rel_equiv first second ->
    rel_equiv
      (plug_possible_bag_context context (successful_possible_bags first))
      (plug_possible_bag_context context (successful_possible_bags second)).
```

## `list_outcome_equiv_possible_bag_query_boundary_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1831`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1831)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem list_outcome_equiv_possible_bag_query_boundary_congr :
  forall context (first second : sql_outcome (list tuple) -> Prop)
         first_sort second_sort,
    first_sort =S= second_sort ->
    rel_equiv first second ->
    possible_bag_query_boundary_equiv first_sort second_sort
      (plug_possible_bag_context context (successful_possible_bags first))
      (plug_possible_bag_context context (successful_possible_bags second)).
```

## `query_expr_equiv_possible_bag_context_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1845`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1845)

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_equiv_possible_bag_context_congr :
  forall env context first second,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env first second ->
    possible_bag_query_boundary_equiv
      (query_expr_sort first) (query_expr_sort second)
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env first)))
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env second))).
```
