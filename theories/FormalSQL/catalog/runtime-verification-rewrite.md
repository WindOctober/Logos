# Runtime outcomes, verification modes, and rewrite specifications

Route here for: success/error outcomes, safe vs error-preserving equivalence, rewrite contracts.

This focused catalog contains 291 declarations routed at declaration granularity from `AggregateRuntimeFacts.v`, `CountermodelFacts.v`, `OrderedObservationTransportFacts.v`, `OrderedQueryFacts.v`, `PossibleOutcomeFacts.v`, `ProofAgentFacade.v`, `SqlQueryContexts.v`, `VerificationConditions.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `successful_outcome_equiv_implies_outcome_equiv`

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2198`](../AggregateRuntimeFacts.v#L2198)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2207`](../AggregateRuntimeFacts.v#L2207)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2221`](../AggregateRuntimeFacts.v#L2221)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/AggregateRuntimeFacts.v:2234`](../AggregateRuntimeFacts.v#L2234)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query program nth separation sound law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_program_nth_separation_sound` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:126`](../OrderedQueryFacts.v#L126)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_has_success_of_runtime_safe_and_outcome :
  forall env query,
    query_safe env query ->
    (exists outcome, eval_query env query outcome) ->
    query_has_success env query.
```

## `query_expr_has_outcome_of_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:140`](../OrderedQueryFacts.v#L140)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_has_outcome_of_success :
  forall env query,
    query_has_success env query ->
    exists outcome, eval_query env query outcome.
```

## `query_expr_table_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:152`](../OrderedQueryFacts.v#L152)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:160`](../OrderedQueryFacts.v#L160)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr table has outcome law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_table_has_outcome :
  forall env outputs table,
    exists outcome, eval_query env (QExpr_Table outputs table) outcome.
```

## `query_expr_values_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:171`](../OrderedQueryFacts.v#L171)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:189`](../OrderedQueryFacts.v#L189)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr values has outcome law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_values_has_outcome :
  forall env outputs values,
    exists outcome, eval_query env (QExpr_Values outputs values) outcome.
```

## `query_expr_error_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:201`](../OrderedQueryFacts.v#L201)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_error_has_outcome :
  forall env outputs error,
    exists outcome, eval_query env (QExpr_Error outputs error) outcome.
```

## `query_expr_outcome_equiv_refl`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:209`](../OrderedQueryFacts.v#L209)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_refl` for the public result.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_refl :
  forall env query,
    (exists outcome, eval_query env query outcome) ->
    query_outcome_equiv env query query.
```

## `query_expr_outcome_equiv_of_eval_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:226`](../OrderedQueryFacts.v#L226)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_of_exact_schedule_transport` for the public result.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:254`](../OrderedQueryFacts.v#L254)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_of_uniform_global_typed` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_of_global_typed :
  forall env left right,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule left right ->
    (exists outcome, eval_query env left outcome) ->
    query_outcome_equiv env left right.
```

## `query_bag_closed_outcome_equiv_of_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:271`](../OrderedQueryFacts.v#L271)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_possible_bag_closed_outcome_equiv_of_success_bags` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule env first)
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule env second) ->
    (forall error,
      eval_query env first (SqlError error) <->
      eval_query env second (SqlError error)) ->
    query_outcome_equiv env first second.
```

## `query_bag_reset_outcome_equiv_of_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:321`](../OrderedQueryFacts.v#L321)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_possible_bag_closed_outcome_equiv_of_success_bags` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_bag_reset_outcome_equiv_of_success_bags :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_order_behavior first = BagReset ->
    query_expr_order_behavior second = BagReset ->
    (exists outcome, eval_query env first outcome) ->
    (exists outcome, eval_query env second outcome) ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule env first)
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule env second) ->
    (forall error,
      eval_query env first (SqlError error) <->
      eval_query env second (SqlError error)) ->
    query_outcome_equiv env first second.
```

## `query_unary_success_bags_congr_from_characterizations`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:349`](../OrderedQueryFacts.v#L349)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:378`](../OrderedQueryFacts.v#L378)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:412`](../OrderedQueryFacts.v#L412)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:434`](../OrderedQueryFacts.v#L434)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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
        boolean_schedule env left_kind left_predicate
        left_matched left_left_select left_right_select)
      (@query_join_bag_relation T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_kind right_predicate
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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:640`](../OrderedQueryFacts.v#L640)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes a set-operation error as a left error or as a right error reached after one successful left observation.

Applicability: Use to invert or construct the exact parent error schedule; a right-child error is observable only with the displayed left-success witness.

Important premises: Retain the existential successful left observation in the right-error arm; right errors do not bypass a left error-only execution.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `set operation`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:657`](../OrderedQueryFacts.v#L657)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes a CROSS JOIN error with its exact left-to-right child evaluation schedule.

Applicability: Use to invert or construct the exact parent error schedule; a right-child error is observable only with the displayed left-success witness.

Important premises: Retain the existential successful left observation in the right-error arm; right errors do not bypass a left error-only execution.

Cross-index: `scheduled`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:674`](../OrderedQueryFacts.v#L674)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:687`](../OrderedQueryFacts.v#L687)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:778`](../OrderedQueryFacts.v#L778)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr set has outcome law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_set_has_outcome :
  forall env operation left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_Set operation left right) outcome.
```

## `query_expr_cross_join_has_outcome`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:799`](../OrderedQueryFacts.v#L799)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr cross join has outcome law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_cross_join_has_outcome :
  forall env left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_CrossJoin left right) outcome.
```

## `query_expr_set_outcome_equiv_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:824`](../OrderedQueryFacts.v#L824)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_set_possible_outcome_equiv_congr_uniform` for the public result.

Purpose/direction: Lifts two child outcome equivalences through a set-operation bag reset while preserving exact output schema and short-circuit errors.

Applicability: Use to lift two local child outcome equivalences through any modeled set operation; no safety or success premise is required, and sort mismatch behavior remains authoritative.

Important premises: Supply both displayed child outcome equivalences.  Do not assume set sort compatibility: matching sort-mismatch outcomes are preserved.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:914`](../OrderedQueryFacts.v#L914)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_cross_join_possible_outcome_equiv_congr_uniform` for the public result.

Purpose/direction: Lifts two child outcome equivalences through CROSS JOIN's bag reset while preserving appended output schema, multiplicity, and errors.

Applicability: Use to lift two local child outcome equivalences through CROSS JOIN; no safety or success premise is required.

Important premises: Supply both displayed child outcome equivalences; no runtime-safety or successful-outcome premise may be silently added or inferred.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_outcome_equiv_congr :
  forall env left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_CrossJoin left right)
      (QExpr_CrossJoin left' right').
```

## `query_expr_filter_outcome_equiv_of_global_expression`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1002`](../OrderedQueryFacts.v#L1002)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_outcome_equiv_of_global_expression :
  forall env
      (left_predicate right_predicate : scalar_expr T relname ScalarResultBoolean)
      input,
    @scalar_expr_global_outcome_equiv T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule ScalarResultBoolean
      left_predicate right_predicate ->
    (exists outcome,
      eval_query env (QExpr_Filter left_predicate input) outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_predicate input)
      (QExpr_Filter right_predicate input).
```

## `query_expr_outcome_equiv_sym`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1129`](../OrderedQueryFacts.v#L1129)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_sym` for the public result.

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_sym :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env right left.
```

## `query_expr_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1155`](../OrderedQueryFacts.v#L1155)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_trans` for the public result.

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_trans :
  forall env first second third,
    query_outcome_equiv env first second ->
    query_outcome_equiv env second third ->
    query_outcome_equiv env first third.
```

## `query_expr_global_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1199`](../OrderedQueryFacts.v#L1199)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_trans` for the public result.

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_trans :
  forall first second third,
    query_expr_global_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule first second ->
    query_expr_global_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule second third ->
    query_expr_global_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule first third.
```

## `query_expr_global_typed_outcome_equiv_trans`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1219`](../OrderedQueryFacts.v#L1219)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_trans` for the public result.

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_trans :
  forall first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule first third.
```

## `query_expr_context_global_equiv_chain`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1237`](../OrderedQueryFacts.v#L1237)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_context_global_equiv_chain :
  forall context first second third,
    query_expr_global_demand_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (query_expr_context_demand context) first second ->
    query_expr_global_demand_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (query_expr_context_demand context) second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule
      (plug_query_expr_context context first)
      (plug_query_expr_context context third).
```

## `eval_query_expr_project_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1300`](../OrderedQueryFacts.v#L1300)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`, `projection`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_project_error_iff :
  forall env select_list input error,
    eval_query env (QExpr_Project select_list input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list input_rows (SqlError error).
```

## `eval_query_expr_filter_error_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1459`](../OrderedQueryFacts.v#L1459)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_filter_error_iff :
  forall env formula input error,
    eval_query env (QExpr_Filter formula input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule env formula input_rows
        (SqlError error).
```

## `eval_filter_rows_has_outcome_of_scalar_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1483`](../OrderedQueryFacts.v#L1483)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_filter_rows_has_outcome_of_scalar_total :
  forall env formula rows,
    (forall row,
      In row rows ->
      exists outcome,
        @eval_scalar_boolean_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule (env_t T env row) formula outcome) ->
    exists outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env formula rows outcome.
```

## `query_expr_filter_has_outcome_of_scalar_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1512`](../OrderedQueryFacts.v#L1512)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes totality of the indicated SQL verification and runtime outcomes operation under the shown premises.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_filter_has_outcome_of_scalar_total :
  forall env formula input,
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      forall row,
        In row input_rows ->
        exists outcome,
          @eval_scalar_boolean_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            boolean_schedule (env_t T env row) formula outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Filter formula input) outcome.
```

## `query_filter_success_bags_congr_extensional_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1610`](../OrderedQueryFacts.v#L1610)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_filter_success_bags_congr_extensional_exact :
  forall env left_formula right_formula left right
      (keep : tuple T -> bool),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) left_formula (keep row)) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) right_formula (keep row)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_Filter left_formula left))
      (success_bags env (QExpr_Filter right_formula right)).
```

## `query_filter_success_bags_congr_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1655`](../OrderedQueryFacts.v#L1655)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_filter_success_bags_congr_exact :
  forall env formula left right (keep : tuple T -> bool),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_Filter formula left))
      (success_bags env (QExpr_Filter formula right)).
```

## `query_filter_success_bags_congr_of_contract`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1699`](../OrderedQueryFacts.v#L1699)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1716`](../OrderedQueryFacts.v#L1716)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem query_filter_error_iff_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall input_rows row,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
```

## `query_expr_filter_runtime_safe_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1776`](../OrderedQueryFacts.v#L1776)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr filter runtime safe exact law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_filter_runtime_safe_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    query_safe env input ->
    query_safe env (QExpr_Filter formula input).
```

## `query_expr_filter_has_outcome_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1797`](../OrderedQueryFacts.v#L1797)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query expr filter has outcome exact law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_filter_has_outcome_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Filter formula input) outcome.
```

## `query_list_transform_success_bags_congr_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2810`](../OrderedQueryFacts.v#L2810)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3595`](../OrderedQueryFacts.v#L3595)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_filter_possible_outcome_equiv_of_always_true_uniform` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_outcome_equiv_of_always_true :
  forall env formula input,
    (exists outcome, eval_query env input outcome) ->
    (forall rows,
      eval_query env input (SqlSuccess rows) ->
      forall row,
        In row rows ->
        forall outcome,
          @eval_scalar_boolean_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
            value_is_null boolean_schedule (env_t T env row)
            formula outcome <->
          outcome = SqlSuccess (Bool.true (B T))) ->
    query_outcome_equiv env (QExpr_Filter formula input) input.
```

## `eval_project_rows_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3737`](../OrderedQueryFacts.v#L3737)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_project_rows_runtime_safe :
  forall env select_list rows,
    (forall row,
      In row rows ->
      scalar_select_values_runtime_safe_at
        (env_t T env row) select_list) ->
    forall error,
      ~ @eval_project_rows_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule env select_list rows (SqlError error).
```

## `query_expr_project_has_success_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3759`](../OrderedQueryFacts.v#L3759)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_project_has_success_safe :
  forall env select_list input,
    (forall row,
      scalar_select_values_has_success_at
        (env_t T env row) select_list) ->
    query_has_success env input ->
    query_has_success env (QExpr_Project select_list input).
```

## `query_expr_project_runtime_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3776`](../OrderedQueryFacts.v#L3776)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `projection`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_project_runtime_safe :
  forall env select_list input,
    (forall row,
      scalar_select_values_runtime_safe_at
        (env_t T env row) select_list) ->
    query_safe env input ->
    query_safe env (QExpr_Project select_list input).
```

## `eval_query_expr_project_error_iff_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3794`](../OrderedQueryFacts.v#L3794)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`, `projection`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_project_error_iff_safe :
  forall env select_list input,
    (forall row,
      scalar_select_values_runtime_safe_at
        (env_t T env row) select_list) ->
    forall error,
      eval_query env (QExpr_Project select_list input) (SqlError error) <->
      eval_query env input (SqlError error).
```

## `query_expr_project_has_outcome_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3814`](../OrderedQueryFacts.v#L3814)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes the explicit runtime-safety direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_project_has_outcome_safe :
  forall env select_list input,
    (forall row,
      scalar_select_values_has_success_at
        (env_t T env row) select_list) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Project select_list input) outcome.
```

## `row_map_rows_outcome_total_as`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3845`](../OrderedQueryFacts.v#L3845)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3862`](../OrderedQueryFacts.v#L3862)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3922`](../OrderedQueryFacts.v#L3922)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3966`](../OrderedQueryFacts.v#L3966)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3990`](../OrderedQueryFacts.v#L3990)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4055`](../OrderedQueryFacts.v#L4055)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

## `query_error_success_bags_empty`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4076`](../OrderedQueryFacts.v#L4076)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4128`](../OrderedQueryFacts.v#L4128)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_values_success_bags_congr :
  forall env left_outputs right_outputs left_values right_values,
    bag_eq T left_values right_values ->
    rel_equiv
      (success_bags env (QExpr_Values left_outputs left_values))
      (success_bags env (QExpr_Values right_outputs right_values)).
```

## `query_table_success_bags_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4149`](../OrderedQueryFacts.v#L4149)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4199`](../OrderedQueryFacts.v#L4199)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_cross_join_union_right_possible_outcome_equiv_safe_uniform` for the public result.

Purpose/direction: Assembles the right-hand CROSS JOIN/UNION ALL distribution law into a safe exact query equivalence with explicit runtime premises.

Applicability: Use after the two sort equalities, duplicated-left functionality, complete source/target safety, and source-success premises are all available.

Important premises: Retain both sort equalities, duplicated-left bag functionality, source and target safety, and the source-success witness.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4234`](../OrderedQueryFacts.v#L4234)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_cross_join_union_right_possible_outcome_equiv_safe_uniform` for the public result.

Purpose/direction: Assembles the right-hand CROSS JOIN/UNION ALL distribution law into a safe exact query equivalence with explicit runtime premises.

Applicability: Use after the two sort equalities, duplicated-left functionality, complete source/target safety, and source-success premises are all available.

Important premises: Retain both sort equalities, duplicated-left bag functionality, source and target safety, and the source-success witness.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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

## `query_possible_bag_closed_outcome_equiv_of_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4517`](../OrderedQueryFacts.v#L4517)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_possible_bag_closed_outcome_equiv_of_success_bags :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    BagClosed T
      (fun rows =>
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null env first (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null env second (SqlSuccess rows)) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env first outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env second outcome) ->
    rel_equiv
      (query_possible_success_bags env first)
      (query_possible_success_bags env second) ->
    (forall error,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env first (SqlError error) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env second (SqlError error)) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second.
```

## `position_rows_from_nth_error`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5080`](../OrderedQueryFacts.v#L5080)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `outcome_relation_equiv_transport_iff`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:23`](../PossibleOutcomeFacts.v#L23)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_relation_equiv_transport_iff :
  forall (A : Type) (value_equiv : A -> A -> Prop)
      (left left' right right' : sql_outcome A -> Prop),
    outcome_relation_equiv value_equiv left right ->
    (forall outcome, left outcome <-> left' outcome) ->
    (forall outcome, right outcome <-> right' outcome) ->
    outcome_relation_equiv value_equiv left' right'.
```

## `outcome_relation_equiv_exists_schedule_transport`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:60`](../PossibleOutcomeFacts.v#L60)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem outcome_relation_equiv_exists_schedule_transport :
  forall (Schedule A : Type) (default_schedule : Schedule)
      (value_equiv : A -> A -> Prop)
      (left right : Schedule -> sql_outcome A -> Prop),
    (forall left_schedule,
      exists right_schedule,
        outcome_relation_equiv value_equiv
          (left left_schedule) (right right_schedule)) ->
    (forall right_schedule,
      exists left_schedule,
        outcome_relation_equiv value_equiv
          (left left_schedule) (right right_schedule)) ->
    outcome_relation_equiv value_equiv
      (fun outcome => exists schedule, left schedule outcome)
      (fun outcome => exists schedule, right schedule outcome).
```

## `query_expr_possible_equiv_of_ordered_observations`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:128`](../PossibleOutcomeFacts.v#L128)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_equiv_of_ordered_observations :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess rows)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left (SqlError error)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right (SqlError error)) ->
    (forall left_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right
          (SqlSuccess right_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left
          (SqlSuccess left_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_possible_equiv_of_observations`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:174`](../PossibleOutcomeFacts.v#L174)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_equiv_of_observations :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess rows)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left (SqlError error)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right (SqlError error)) ->
    (forall rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess rows) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlSuccess rows)) ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_possible_outcome_equiv_of_observations`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:210`](../PossibleOutcomeFacts.v#L210)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_outcome_equiv_of_observations :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right outcome) ->
    (forall left_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right
          (SqlSuccess right_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left
          (SqlSuccess left_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    (forall error,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlError error) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlError error)) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `scalar_expr_uniform_global_outcome_equiv_refl`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:357`](../PossibleOutcomeFacts.v#L357)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_uniform_global_outcome_equiv_refl :
  forall kind (expression : scalar_expr T relname kind),
    scalar_expr_uniform_global_outcome_equiv expression expression.
```

## `scalar_value_expr_list_uniform_global_outcome_equiv_refl`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:364`](../PossibleOutcomeFacts.v#L364)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_value_expr_list_uniform_global_outcome_equiv_refl :
  forall expressions,
    scalar_value_expr_list_uniform_global_outcome_equiv
      expressions expressions.
```

## `scalar_value_expr_list_uniform_global_outcome_equiv_nil`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:373`](../PossibleOutcomeFacts.v#L373)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_value_expr_list_uniform_global_outcome_equiv_nil :
  scalar_value_expr_list_uniform_global_outcome_equiv nil nil.
```

## `scalar_value_expr_list_uniform_global_outcome_equiv_cons`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:377`](../PossibleOutcomeFacts.v#L377)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_value_expr_list_uniform_global_outcome_equiv_cons :
  forall left lefts right rights,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_value_expr_list_uniform_global_outcome_equiv lefts rights ->
    scalar_value_expr_list_uniform_global_outcome_equiv
      (left :: lefts) (right :: rights).
```

## `scalar_boolean_expr_list_uniform_global_outcome_equiv_nil`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:385`](../PossibleOutcomeFacts.v#L385)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_boolean_expr_list_uniform_global_outcome_equiv_nil :
  scalar_boolean_expr_list_uniform_global_outcome_equiv nil nil.
```

## `scalar_boolean_expr_list_uniform_global_outcome_equiv_cons`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:389`](../PossibleOutcomeFacts.v#L389)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_boolean_expr_list_uniform_global_outcome_equiv_cons :
  forall left lefts right rights,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv lefts rights ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv
      (left :: lefts) (right :: rights).
```

## `scalar_select_list_uniform_global_outcome_equiv_nil`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:397`](../PossibleOutcomeFacts.v#L397)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_uniform_global_outcome_equiv_nil :
  scalar_select_list_uniform_global_outcome_equiv nil nil.
```

## `scalar_select_list_uniform_global_outcome_equiv_cons`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:401`](../PossibleOutcomeFacts.v#L401)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_uniform_global_outcome_equiv_cons :
  forall left_expression left_attribute left_select
      right_expression right_attribute right_select,
    left_attribute = right_attribute ->
    scalar_expr_uniform_global_outcome_equiv
      left_expression right_expression ->
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    scalar_select_list_uniform_global_outcome_equiv
      ((left_expression, left_attribute) :: left_select)
      ((right_expression, right_attribute) :: right_select).
```

## `scalar_select_list_uniform_global_outcome_equiv_outputs`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:416`](../PossibleOutcomeFacts.v#L416)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_uniform_global_outcome_equiv_outputs :
  forall left right,
    scalar_select_list_uniform_global_outcome_equiv left right ->
    scalar_select_outputs left = scalar_select_outputs right.
```

## `scalar_select_list_uniform_global_outcome_equiv_values`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:426`](../PossibleOutcomeFacts.v#L426)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_uniform_global_outcome_equiv_values :
  forall left right,
    scalar_select_list_uniform_global_outcome_equiv left right ->
    scalar_value_expr_list_uniform_global_outcome_equiv
      (map fst left) (map fst right).
```

## `eval_scalar_values_outcome_uniform_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:437`](../PossibleOutcomeFacts.v#L437)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_values_outcome_uniform_congr :
  forall left right,
    scalar_value_expr_list_uniform_global_outcome_equiv left right ->
    forall schedule env outcome,
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left outcome <->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right outcome.
```

## `eval_scalar_boolean_operands_outcome_uniform_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:465`](../PossibleOutcomeFacts.v#L465)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_operands_outcome_uniform_congr :
  forall left right,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    forall schedule env operation outcome,
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env operation left outcome <->
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env operation right outcome.
```

## `insert_boolean_operand_uniform_Forall2`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:506`](../PossibleOutcomeFacts.v#L506)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: States the insert boolean operand uniform forall2 law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `insert_boolean_operand_uniform_Forall2` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma insert_boolean_operand_uniform_Forall2 :
  forall schedule sites left_expression right_expression left right,
    scalar_expr_uniform_global_outcome_equiv
      left_expression right_expression ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    Forall2 scalar_expr_uniform_global_outcome_equiv
      (@insert_boolean_operand T relname schedule sites left_expression left)
      (@insert_boolean_operand T relname schedule sites right_expression right).
```

## `schedule_boolean_operands_aux_uniform_Forall2`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:528`](../PossibleOutcomeFacts.v#L528)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: States the schedule boolean operands aux uniform forall2 law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `schedule_boolean_operands_aux_uniform_Forall2` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma schedule_boolean_operands_aux_uniform_Forall2 :
  forall schedule site_rows left right left_ordered right_ordered,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv
      left_ordered right_ordered ->
    Forall2 scalar_expr_uniform_global_outcome_equiv
      (@schedule_boolean_operands_aux T relname schedule
        site_rows left left_ordered)
      (@schedule_boolean_operands_aux T relname schedule
        site_rows right right_ordered).
```

## `schedule_boolean_operands_uniform_Forall2`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:552`](../PossibleOutcomeFacts.v#L552)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: States the schedule boolean operands uniform forall2 law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `schedule_boolean_operands_uniform_Forall2` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma schedule_boolean_operands_uniform_Forall2 :
  forall schedule site_rows left right,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    Forall2 scalar_expr_uniform_global_outcome_equiv
      (@schedule_boolean_operands T relname schedule site_rows left)
      (@schedule_boolean_operands T relname schedule site_rows right).
```

## `scalar_expr_call_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:565`](../PossibleOutcomeFacts.v#L565)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_call_uniform_global_congr :
  forall result_type operator left right,
    scalar_value_expr_list_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Call result_type operator left)
      (SExpr_Call result_type operator right).
```

## `scalar_expr_case_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:588`](../PossibleOutcomeFacts.v#L588)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `CASE`, `conditional expression`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_case_uniform_global_congr :
  forall result_type left_condition right_condition
      left_then right_then left_else right_else,
    scalar_expr_uniform_global_outcome_equiv
      left_condition right_condition ->
    scalar_expr_uniform_global_outcome_equiv left_then right_then ->
    scalar_expr_uniform_global_outcome_equiv left_else right_else ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Case result_type left_condition left_then left_else)
      (SExpr_Case result_type right_condition right_then right_else).
```

## `scalar_expr_bool_value_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:624`](../PossibleOutcomeFacts.v#L624)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_bool_value_uniform_global_congr :
  forall result_type embed left right,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_BoolValue result_type embed left)
      (SExpr_BoolValue result_type embed right).
```

## `scalar_expr_value_bool_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:637`](../PossibleOutcomeFacts.v#L637)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_value_bool_uniform_global_congr :
  forall decode left right,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_ValueBool decode left) (SExpr_ValueBool decode right).
```

## `scalar_expr_pred_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:649`](../PossibleOutcomeFacts.v#L649)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `predicate`, `Bool3`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_pred_uniform_global_congr :
  forall predicate left right,
    scalar_value_expr_list_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Pred predicate left) (SExpr_Pred predicate right).
```

## `scalar_expr_conj_list_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:671`](../PossibleOutcomeFacts.v#L671)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_conj_list_uniform_global_congr :
  forall site_rows operation left right,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_ConjList site_rows operation left)
      (SExpr_ConjList site_rows operation right).
```

## `scalar_expr_not_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:688`](../PossibleOutcomeFacts.v#L688)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_not_uniform_global_congr :
  forall left right,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Not left) (SExpr_Not right).
```

## `scalar_expr_subquery_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:709`](../PossibleOutcomeFacts.v#L709)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_subquery_uniform_global_congr :
  forall result_type null_value left right,
    query_expr_uniform_global_typed_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Subquery result_type null_value left)
      (SExpr_Subquery result_type null_value right).
```

## `scalar_expr_quant_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:727`](../PossibleOutcomeFacts.v#L727)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_quant_uniform_global_congr :
  forall quantifier predicate left_arguments right_arguments left right,
    scalar_value_expr_list_uniform_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_uniform_global_typed_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Quant quantifier predicate left_arguments left)
      (SExpr_Quant quantifier predicate right_arguments right).
```

## `scalar_expr_in_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:766`](../PossibleOutcomeFacts.v#L766)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `IN`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_in_uniform_global_congr :
  forall left_arguments right_arguments left right,
    scalar_value_expr_list_uniform_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_uniform_global_typed_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_In left_arguments left) (SExpr_In right_arguments right).
```

## `scalar_expr_exists_uniform_global_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:806`](../PossibleOutcomeFacts.v#L806)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `verification and runtime semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_exists_uniform_global_congr :
  forall left right,
    query_expr_uniform_global_exists_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Exists left) (SExpr_Exists right).
```

## `query_expr_possible_outcome_equiv_of_exact_schedule_transport`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:828`](../PossibleOutcomeFacts.v#L828)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_outcome_equiv_of_exact_schedule_transport :
  forall env left right
      (forward_schedule backward_schedule :
        (boolean_site -> boolean_evaluation_order) ->
        boolean_site -> boolean_evaluation_order),
    query_expr_outputs left = query_expr_outputs right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left outcome) ->
    (forall schedule outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left outcome ->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        (forward_schedule schedule) env right outcome) ->
    (forall schedule outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right outcome ->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        (backward_schedule schedule) env left outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:884`](../PossibleOutcomeFacts.v#L884)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall left_schedule,
      exists right_schedule,
        outcome_relation_equiv (@ordered_rows_equiv T)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right)) ->
    (forall right_schedule,
      exists left_schedule,
        outcome_relation_equiv (@ordered_rows_equiv T)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right)) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:918`](../PossibleOutcomeFacts.v#L918)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv :
  forall env left right,
    query_expr_uniform_scheduled_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_scheduled_outcome_equiv_implies_possible_of_independent`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:936`](../PossibleOutcomeFacts.v#L936)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_scheduled_outcome_equiv_implies_possible_of_independent :
  forall env left right fixed_schedule,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      fixed_schedule env left right ->
    query_expr_schedule_independent env left ->
    query_expr_schedule_independent env right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `boolean_schedule_reindex_complete_id`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:971`](../PossibleOutcomeFacts.v#L971)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: States the boolean schedule reindex complete id law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `boolean_schedule_reindex_complete_id` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scheduled`, `runtime`

Search aliases: `verification and runtime semantics`

```rocq
Lemma boolean_schedule_reindex_complete_id :
  boolean_schedule_reindex_complete (fun site => site).
```

## `eval_query_expr_possible_outcome_site_reindex_iff`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:979`](../PossibleOutcomeFacts.v#L979)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_possible_outcome_site_reindex_iff :
  forall (rename_site : boolean_site -> boolean_site),
    boolean_schedule_reindex_complete rename_site ->
    forall env query outcome,
      (exists schedule,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          (fun site => schedule (rename_site site)) env query outcome) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env query outcome.
```

## `query_expr_possible_outcome_equiv_of_uniform_global_typed`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1004`](../PossibleOutcomeFacts.v#L1004)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_outcome_equiv_of_uniform_global_typed :
  forall env left right,
    query_expr_uniform_global_typed_outcome_equiv left right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_distinct_possible_outcome_equiv_inert_reset`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1045`](../PossibleOutcomeFacts.v#L1045)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_distinct_possible_outcome_equiv_inert_reset :
  forall env input,
    query_expr_order_behavior input = BagReset ->
    (forall (schedule : boolean_site -> boolean_evaluation_order)
        current_env bag,
      @query_success_bags T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule current_env input bag ->
      bag_eq T (query_distinct_bag bag) bag) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env input outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Distinct input) input.
```

## `eval_project_rows_outcome_uniform_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1084`](../PossibleOutcomeFacts.v#L1084)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_project_rows_outcome_uniform_congr :
  forall left_select right_select,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    forall schedule env rows outcome,
      @eval_project_rows_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env left_select rows outcome <->
      @eval_project_rows_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env right_select rows outcome.
```

## `query_expr_filter_uniform_global_typed_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1130`](../PossibleOutcomeFacts.v#L1130)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `filter`, `schema`

Search aliases: `verification and runtime semantics`, `filter`, `WHERE`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_uniform_global_typed_congr :
  forall left_predicate right_predicate input,
    scalar_expr_uniform_global_outcome_equiv
      left_predicate right_predicate ->
    query_expr_uniform_global_typed_outcome_equiv
      (QExpr_Filter left_predicate input)
      (QExpr_Filter right_predicate input).
```

## `query_expr_project_uniform_global_typed_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1143`](../PossibleOutcomeFacts.v#L1143)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `schema`

Search aliases: `verification and runtime semantics`, `projection`, `SELECT list`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_project_uniform_global_typed_congr :
  forall left_select right_select input,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    query_expr_uniform_global_typed_outcome_equiv
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
```

## `query_expr_filter_predicate_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1167`](../PossibleOutcomeFacts.v#L1167)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `filter`, `WHERE`, `predicate`, `Bool3`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_predicate_possible_outcome_equiv :
  forall env left_predicate right_predicate input,
    scalar_expr_uniform_global_outcome_equiv
      left_predicate right_predicate ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter left_predicate input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_predicate input)
      (QExpr_Filter right_predicate input).
```

## `query_expr_project_select_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1187`](../PossibleOutcomeFacts.v#L1187)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `projection`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_project_select_possible_outcome_equiv :
  forall env left_select right_select input,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Project left_select input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
```

## `eval_groups_outcome_uniform_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1212`](../PossibleOutcomeFacts.v#L1212)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_groups_outcome_uniform_congr :
  forall left_select right_select group_terms left_having right_having,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    scalar_expr_uniform_global_outcome_equiv left_having right_having ->
    (forall current_env,
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    (forall current_env,
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env left_having =
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env right_having) ->
    forall schedule env groups outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select group_terms left_having groups outcome <->
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select group_terms right_having groups outcome.
```

## `eval_group_bag_outcome_exact_local_congr`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1372`](../PossibleOutcomeFacts.v#L1372)

Interface layer: Schedule-quantified transport foundation: compose it into a theorem whose conclusion is possible-outcome equivalence.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_group_bag_outcome_exact_local_congr :
  forall left_select right_select group_keys left_having right_having,
    (forall schedule env group_terms groups outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select group_terms left_having groups outcome <->
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select group_terms right_having groups outcome) ->
    forall schedule env input_bag outcome,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select group_keys left_having input_bag outcome <->
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select group_keys right_having input_bag outcome.
```

## `query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1412`](../PossibleOutcomeFacts.v#L1412)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `bag`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes :
  forall env left_select right_select left_group_keys right_group_keys
      left_having right_having input,
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall schedule current_env input_bag outcome,
      @eval_group_bag_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule current_env
        left_select left_group_keys left_having input_bag outcome <->
      @eval_group_bag_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule current_env
        right_select right_group_keys right_having input_bag outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select left_group_keys left_having input)
        outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select left_group_keys left_having input)
      (QExpr_Group right_select right_group_keys right_having input).
```

## `query_expr_group_possible_outcome_equiv_of_exact_local_outcomes`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1466`](../PossibleOutcomeFacts.v#L1466)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_possible_outcome_equiv_of_exact_local_outcomes :
  forall env left_select right_select group_keys left_having right_having input,
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall schedule current_env group_terms groups outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        current_env left_select group_terms left_having groups outcome <->
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        current_env right_select group_terms right_having groups outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select group_keys left_having input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select group_keys left_having input)
      (QExpr_Group right_select group_keys right_having input).
```

## `query_expr_group_clauses_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1495`](../PossibleOutcomeFacts.v#L1495)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_clauses_possible_outcome_equiv :
  forall env left_select right_select group_keys left_having right_having input,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    scalar_expr_uniform_global_outcome_equiv left_having right_having ->
    (forall current_env,
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    (forall current_env,
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env left_having =
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env right_having) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select group_keys left_having input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select group_keys left_having input)
      (QExpr_Group right_select group_keys right_having input).
```

## `query_expr_possible_outcome_equiv_refl`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1533`](../PossibleOutcomeFacts.v#L1533)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_outcome_equiv_refl :
  forall env query,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env query outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query query.
```

## `query_expr_possible_outcome_equiv_sym`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1550`](../PossibleOutcomeFacts.v#L1550)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_outcome_equiv_sym :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env right left.
```

## `query_expr_possible_outcome_equiv_trans`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1572`](../PossibleOutcomeFacts.v#L1572)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_outcome_equiv_trans :
  forall env first second third,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env second third ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first third.
```

## `query_expr_context_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1619`](../PossibleOutcomeFacts.v#L1619)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_context_possible_outcome_equiv :
  forall env (context : query_expr_context T relname) left right,
    query_expr_uniform_global_demand_equiv
      (query_expr_context_demand context) left right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (plug_query_expr_context context left) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (plug_query_expr_context context left)
      (plug_query_expr_context context right).
```

## `query_expr_filter_possible_outcome_equiv_of_uniform_expression`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1640`](../PossibleOutcomeFacts.v#L1640)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_possible_outcome_equiv_of_uniform_expression :
  forall env left_expression right_expression input,
    scalar_expr_uniform_global_outcome_equiv
      left_expression right_expression ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter left_expression input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_expression input)
      (QExpr_Filter right_expression input).
```

## `query_expr_group_possible_outcome_equiv_of_uniform_having`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1661`](../PossibleOutcomeFacts.v#L1661)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_possible_outcome_equiv_of_uniform_having :
  forall env select_list group_keys left_having right_having input,
    scalar_expr_uniform_global_group_outcome_equiv
      left_having right_having ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group select_list group_keys left_having input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group select_list group_keys left_having input)
      (QExpr_Group select_list group_keys right_having input).
```

## `query_expr_join_possible_outcome_equiv_of_uniform_predicate`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1685`](../PossibleOutcomeFacts.v#L1685)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `predicate`, `Bool3`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_join_possible_outcome_equiv_of_uniform_predicate :
  forall env kind left_predicate right_predicate
      matched_select left_select right_select left right,
    scalar_expr_uniform_global_outcome_equiv
      left_predicate right_predicate ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Join kind left_predicate matched_select left_select right_select
          left right) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Join kind left_predicate matched_select left_select right_select
        left right)
      (QExpr_Join kind right_predicate matched_select left_select right_select
        left right).
```

## `query_expr_filter_in_subquery_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1714`](../PossibleOutcomeFacts.v#L1714)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `subquery`, `IN`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Corollary query_expr_filter_in_subquery_possible_outcome_equiv :
  forall env arguments left_subquery right_subquery input,
    query_expr_uniform_global_typed_outcome_equiv
      left_subquery right_subquery ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter (SExpr_In arguments left_subquery) input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter (SExpr_In arguments left_subquery) input)
      (QExpr_Filter (SExpr_In arguments right_subquery) input).
```

## `query_expr_filter_exists_subquery_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1736`](../PossibleOutcomeFacts.v#L1736)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `subquery`, `EXISTS`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Corollary query_expr_filter_exists_subquery_possible_outcome_equiv :
  forall env left_subquery right_subquery input,
    query_expr_uniform_global_exists_outcome_equiv
      left_subquery right_subquery ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter (SExpr_Exists left_subquery) input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter (SExpr_Exists left_subquery) input)
      (QExpr_Filter (SExpr_Exists right_subquery) input).
```

## `query_expr_set_possible_outcome_equiv_congr_uniform`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1760`](../PossibleOutcomeFacts.v#L1760)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_set_possible_outcome_equiv_congr_uniform :
  forall env operation left left' right right',
    query_expr_uniform_scheduled_outcome_equiv env left left' ->
    query_expr_uniform_scheduled_outcome_equiv env right right' ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
```

## `query_expr_cross_join_possible_outcome_equiv_congr_uniform`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1775`](../PossibleOutcomeFacts.v#L1775)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `join`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_cross_join_possible_outcome_equiv_congr_uniform :
  forall env left left' right right',
    query_expr_uniform_scheduled_outcome_equiv env left left' ->
    query_expr_uniform_scheduled_outcome_equiv env right right' ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left right)
      (QExpr_CrossJoin left' right').
```

## `query_expr_group_possible_outcome_equiv_congr_uniform`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1790`](../PossibleOutcomeFacts.v#L1790)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_possible_outcome_equiv_congr_uniform :
  forall env select_list group_terms having left right,
    query_expr_uniform_scheduled_outcome_equiv env left right ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Group select_list group_terms having left) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
```

## `query_expr_window_possible_outcome_equiv_congr_uniform`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1811`](../PossibleOutcomeFacts.v#L1811)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_window_possible_outcome_equiv_congr_uniform :
  forall env partition_keys order_keys items left right,
    query_expr_uniform_scheduled_outcome_equiv env left right ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Window partition_keys order_keys items left) outcome) ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Window partition_keys order_keys items right) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
```

## `query_expr_offset_zero_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1842`](../PossibleOutcomeFacts.v#L1842)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_offset_zero_possible_outcome_equiv :
  forall env input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Offset 0 input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Offset 0 input) input.
```

## `query_expr_offset_offset_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1861`](../PossibleOutcomeFacts.v#L1861)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_offset_offset_possible_outcome_equiv :
  forall env outer inner input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Offset outer (QExpr_Offset inner input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset outer (QExpr_Offset inner input))
      (QExpr_Offset (outer + inner) input).
```

## `query_expr_fetch_fetch_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1882`](../PossibleOutcomeFacts.v#L1882)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_fetch_fetch_possible_outcome_equiv :
  forall env outer inner input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Fetch outer (QExpr_Fetch inner input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch outer (QExpr_Fetch inner input))
      (QExpr_Fetch (Nat.min outer inner) input).
```

## `query_expr_offset_fetch_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1903`](../PossibleOutcomeFacts.v#L1903)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `OFFSET`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_offset_fetch_possible_outcome_equiv :
  forall env offset count input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Offset offset (QExpr_Fetch count input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset offset (QExpr_Fetch count input))
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)).
```

## `query_expr_fetch_offset_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1924`](../PossibleOutcomeFacts.v#L1924)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `OFFSET`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_fetch_offset_possible_outcome_equiv :
  forall env count offset input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Fetch count (QExpr_Offset offset input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch count (QExpr_Offset offset input))
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)).
```

## `query_expr_order_by_order_by_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1945`](../PossibleOutcomeFacts.v#L1945)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_order_by_order_by_possible_outcome_equiv :
  forall env outer_keys inner_keys input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input))
      (QExpr_OrderBy outer_keys input).
```

## `query_expr_possible_equiv_refl`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:1985`](../PossibleOutcomeFacts.v#L1985)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_equiv_refl :
  forall env query,
    query_expr_possible_has_success env query ->
    query_expr_possible_runtime_safe env query ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query query.
```

## `query_expr_possible_equiv_sym`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2001`](../PossibleOutcomeFacts.v#L2001)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_equiv_sym :
  forall env left right,
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env right left.
```

## `query_expr_possible_equiv_trans`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2030`](../PossibleOutcomeFacts.v#L2030)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Composes two SQL verification and runtime outcomes relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_equiv_trans :
  forall env first second third,
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env second third ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first third.
```

## `query_expr_possible_equiv_of_possible_outcome_equiv_safe`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2069`](../PossibleOutcomeFacts.v#L2069)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_equiv_of_possible_outcome_equiv_safe :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    query_expr_possible_runtime_safe env left ->
    query_expr_possible_runtime_safe env right ->
    query_expr_possible_has_success env left ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
```

## `query_expr_fetch_zero_possible_outcome_equiv_safe`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2091`](../PossibleOutcomeFacts.v#L2091)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_fetch_zero_possible_outcome_equiv_safe :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_expr_possible_runtime_safe env left ->
    query_expr_possible_runtime_safe env right ->
    query_expr_possible_has_success env left ->
    query_expr_possible_has_success env right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Fetch 0 left) (QExpr_Fetch 0 right).
```

## `query_expr_order_by_possible_outcome_equiv_of_success_length_le_one`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2138`](../PossibleOutcomeFacts.v#L2138)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Provides the stated reusable upper bound for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_order_by_possible_outcome_equiv_of_success_length_le_one :
  forall env keys input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env input outcome) ->
    (forall rows,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env input (SqlSuccess rows) ->
      (length rows <= 1)%nat) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_OrderBy keys input) input.
```

## `query_expr_possible_outcome_equiv_of_shared_exact_error`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2189`](../PossibleOutcomeFacts.v#L2189)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_outcome_equiv_of_shared_exact_error :
  forall env first second expected,
    query_expr_outputs first = query_expr_outputs second ->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first (SqlError expected) ->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env second (SqlError expected) ->
    (forall rows,
      ~ @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env first (SqlSuccess rows)) ->
    (forall rows,
      ~ @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env second (SqlSuccess rows)) ->
    (forall observed,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env first (SqlError observed) ->
      observed = expected) ->
    (forall observed,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env second (SqlError observed) ->
      observed = expected) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second.
```

## `query_expr_filter_possible_outcome_equiv_congr_stable_total`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2249`](../PossibleOutcomeFacts.v#L2249)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_possible_outcome_equiv_congr_stable_total :
  forall env left_formula right_formula keep left_input right_input,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_input right_input ->
    possible_stable_total_filter_acceptance env left_formula keep ->
    possible_stable_total_filter_acceptance env right_formula keep ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_formula left_input)
      (QExpr_Filter right_formula right_input).
```

## `query_expr_group_possible_outcome_equiv_of_supported_child_outcomes`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2378`](../PossibleOutcomeFacts.v#L2378)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_group_possible_outcome_equiv_of_supported_child_outcomes :
  forall env select_list group_terms having left right
      (supported : list (tuple T) -> list (tuple T) -> Prop),
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group select_list group_terms having left) outcome) ->
    (forall left_rows,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null env right (SqlSuccess right_rows) /\
        supported left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null env left (SqlSuccess left_rows) /\
        supported left_rows right_rows) ->
    (forall error,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlError error) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlError error)) ->
    (forall left_schedule right_schedule left_rows right_rows,
      supported left_rows right_rows ->
      forall outcome,
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env select_list group_terms having
          (rows_bag T left_rows) outcome <->
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env select_list group_terms having
          (rows_bag T right_rows) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
```

## `query_expr_filter_possible_outcome_equiv_of_always_true_uniform`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2535`](../PossibleOutcomeFacts.v#L2535)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_possible_outcome_equiv_of_always_true_uniform :
  forall env formula input,
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env input outcome) ->
    (forall schedule rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env input (SqlSuccess rows) ->
      forall row,
        In row rows ->
        forall outcome,
          @eval_scalar_boolean_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            schedule (env_t T env row) formula outcome <->
          outcome = SqlSuccess (Bool.true (B T))) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Filter formula input) input.
```

## `query_expr_cross_join_union_right_possible_outcome_equiv_safe_uniform`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2568`](../PossibleOutcomeFacts.v#L2568)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_cross_join_union_right_possible_outcome_equiv_safe_uniform :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall schedule left_bag left_bag',
      @query_success_bags T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left left_bag ->
      @query_success_bags T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    (forall schedule,
      @query_expr_runtime_safe T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_CrossJoin left (QExpr_Set Union first second))) ->
    (forall schedule,
      @query_expr_runtime_safe T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Set Union
          (QExpr_CrossJoin left first)
          (QExpr_CrossJoin left second))) ->
    (forall schedule,
      @query_expr_has_success T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_CrossJoin left (QExpr_Set Union first second))) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
```

## `query_program_possible_equiv_nil`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2619`](../PossibleOutcomeFacts.v#L2619)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_program_possible_equiv_nil :
  forall env,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env nil nil.
```

## `query_program_possible_equiv_cons`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2628`](../PossibleOutcomeFacts.v#L2628)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_program_possible_equiv_cons :
  forall env left_query left_program right_query right_program,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (left_query :: left_program) (right_query :: right_program) <->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_query right_query /\
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_program right_program.
```

## `query_program_possible_outcome_equiv_nil`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2644`](../PossibleOutcomeFacts.v#L2644)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_program_possible_outcome_equiv_nil :
  forall env,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env nil nil.
```

## `query_program_possible_outcome_equiv_cons`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2653`](../PossibleOutcomeFacts.v#L2653)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_program_possible_outcome_equiv_cons :
  forall env left_query left_program right_query right_program,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (left_query :: left_program) (right_query :: right_program) <->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_query right_query /\
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_program right_program.
```

## `query_program_possible_equiv_length`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2669`](../PossibleOutcomeFacts.v#L2669)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Relates SQL verification and runtime outcomes to the exact list length or bag cardinality shown below.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Lemma query_program_possible_equiv_length :
  forall env left right,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    length left = length right.
```

## `query_program_possible_outcome_equiv_length`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2683`](../PossibleOutcomeFacts.v#L2683)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Relates SQL verification and runtime outcomes to the exact list length or bag cardinality shown below.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_program_possible_outcome_equiv_length :
  forall env left right,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    length left = length right.
```

## `query_program_possible_equiv_iff_Forall2`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2697`](../PossibleOutcomeFacts.v#L2697)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `equivalence`, `congruence`

```rocq
Theorem query_program_possible_equiv_iff_Forall2 :
  forall env left right,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right <->
    Forall2
      (@query_expr_possible_equiv T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env)
      left right.
```

## `query_program_possible_outcome_equiv_iff_Forall2`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2719`](../PossibleOutcomeFacts.v#L2719)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_program_possible_outcome_equiv_iff_Forall2 :
  forall env left right,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right <->
    Forall2
      (@query_expr_possible_outcome_equiv T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env)
      left right.
```

## `query_rename_uniform_transport_implies_mapped_schema_possible_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2780`](../PossibleOutcomeFacts.v#L2780)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `renaming`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Theorem query_rename_uniform_transport_implies_mapped_schema_possible_outcome_equiv :
  forall environment_relation left_env right_env rho left right,
    environment_relation left_env right_env ->
    query_rename_uniform_transport_under
      environment_relation rho left right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_env left outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_env right outcome) ->
    query_mapped_schema_possible_outcome_equiv
      left_env right_env rho left right.
```

## `query_mapped_schema_possible_outcome_equiv_mapped_schema`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2824`](../PossibleOutcomeFacts.v#L2824)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_mapped_schema_possible_outcome_equiv_mapped_schema :
  forall left_env right_env rho left right,
    query_mapped_schema_possible_outcome_equiv
      left_env right_env rho left right ->
    map rho (query_expr_outputs left) = query_expr_outputs right.
```

## `query_expr_possible_bag_outcome_equiv_success_forward`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2868`](../PossibleOutcomeFacts.v#L2868)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_success_forward :
  forall env left right left_rows,
    possible_bag_outcome_equiv env left right ->
    eval_possible env left (SqlSuccess left_rows) ->
    exists right_rows,
      eval_possible env right (SqlSuccess right_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
```

## `query_expr_possible_bag_outcome_equiv_success_backward`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2895`](../PossibleOutcomeFacts.v#L2895)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_success_backward :
  forall env left right right_rows,
    possible_bag_outcome_equiv env left right ->
    eval_possible env right (SqlSuccess right_rows) ->
    exists left_rows,
      eval_possible env left (SqlSuccess left_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
```

## `query_expr_possible_bag_outcome_equiv_error_iff`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2921`](../PossibleOutcomeFacts.v#L2921)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_error_iff :
  forall env left right error,
    possible_bag_outcome_equiv env left right ->
    (eval_possible env left (SqlError error) <->
     eval_possible env right (SqlError error)).
```

## `query_expr_possible_bag_outcome_equiv_inhabited`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2934`](../PossibleOutcomeFacts.v#L2934)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_inhabited :
  forall env left right,
    possible_bag_outcome_equiv env left right ->
    (exists outcome, eval_possible env left outcome) /\
    (exists outcome, eval_possible env right outcome).
```

## `query_expr_distinct_possible_outcome_equiv_of_possible_bag_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:2966`](../PossibleOutcomeFacts.v#L2966)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `DISTINCT`, `duplicate elimination`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_distinct_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env left right,
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_expr_rank_possible_outcome_equiv_of_possible_bag_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:3036`](../PossibleOutcomeFacts.v#L3036)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `window`, `PARTITION BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_rank_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value right).
```

## `query_expr_order_by_possible_outcome_equiv_of_possible_bag_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:3187`](../PossibleOutcomeFacts.v#L3187)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `ORDER BY`, `ordered observation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_order_by_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env keys left right,
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
```

## `query_expr_offset_possible_outcome_equiv_of_possible_bag_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:3257`](../PossibleOutcomeFacts.v#L3257)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `OFFSET`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_offset_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env offset left right,
    BagClosed T
      (fun rows => eval_possible env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible env right (SqlSuccess rows)) ->
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
```

## `query_expr_fetch_possible_outcome_equiv_of_possible_bag_outcome_equiv`

Source: [`theories/FormalSQL/PossibleOutcomeFacts.v:3277`](../PossibleOutcomeFacts.v#L3277)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`, `ordered`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `FETCH`, `LIMIT`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_fetch_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env count left right,
    BagClosed T
      (fun rows => eval_possible env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible env right (SqlSuccess rows)) ->
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
```

## `tnull_query_success_outcome_is_success_bag`

Source: [`theories/FormalSQL/ProofAgentFacade.v:192`](../ProofAgentFacade.v#L192)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `facade`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_query_success_outcome_is_success_bag :
  forall db env query rows,
    TNullQueryExprOutcome db env query (SqlSuccess rows) ->
    TNullQuerySuccessBag db env query (TNullRowsBag rows).
```

## `tnull_query_expr_outcome_separation_sound`

Source: [`theories/FormalSQL/ProofAgentFacade.v:218`](../ProofAgentFacade.v#L218)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query expr outcome separation sound law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_query_expr_outcome_separation_sound :
  forall db env left right,
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryExprOutcomeEq db env left right.
```

## `tnull_query_expr_outcome_separation_of_left_success_length_difference`

Source: [`theories/FormalSQL/ProofAgentFacade.v:238`](../ProofAgentFacade.v#L238)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Relates SQL verification and runtime outcomes to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:254`](../ProofAgentFacade.v#L254)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Relates SQL verification and runtime outcomes to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:270`](../ProofAgentFacade.v#L270)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query expr outcome separation of right functional observation difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:287`](../ProofAgentFacade.v#L287)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query expr outcome separation of left functional observation difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:309`](../ProofAgentFacade.v#L309)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query expr outcome separation of right functional bag difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `facade`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:331`](../ProofAgentFacade.v#L331)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query expr outcome separation of left functional bag difference law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `facade`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_query_expr_outcome_separation_of_left_functional_bag_difference :
  forall db env left right left_rows right_rows,
    TNullQuerySuccessBagFunctional db env left ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullBagEq (TNullRowsBag left_rows) (TNullRowsBag right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
```

## `condition_true_well_formed`

Source: [`theories/FormalSQL/VerificationConditions.v:210`](../VerificationConditions.v#L210)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:138`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L138)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_refl` for the public result.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_outcome_equiv_refl :
  forall query, query_expr_global_outcome_equiv query query.
```

## `query_expr_global_cardinality_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:144`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L144)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_cardinality_outcome_equiv_refl :
  forall query, query_expr_global_cardinality_outcome_equiv query query.
```

## `query_expr_global_exists_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:150`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L150)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_exists_outcome_equiv_refl :
  forall query, query_expr_global_exists_outcome_equiv query query.
```

## `query_expr_global_typed_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:156`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L156)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_refl` for the public result.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_global_typed_outcome_equiv_refl :
  forall query, query_expr_global_typed_outcome_equiv query query.
```

## `scalar_expr_global_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:211`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L211)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_global_outcome_equiv_refl :
  forall kind (expression : scalar_expr T relname kind),
    scalar_expr_global_outcome_equiv expression expression.
```

## `scalar_expr_global_outcome_equiv_sym`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:218`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L218)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_global_outcome_equiv_sym :
  forall kind (left right : scalar_expr T relname kind),
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv right left.
```

## `scalar_expr_global_group_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:226`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L226)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_global_group_outcome_equiv_refl :
  forall kind (expression : scalar_expr T relname kind),
    scalar_expr_global_group_outcome_equiv expression expression.
```

## `scalar_expr_list_global_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:235`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L235)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_list_global_outcome_equiv_refl :
  forall kind (expressions : list (scalar_expr T relname kind)),
    Forall2 scalar_expr_global_outcome_equiv expressions expressions.
```

## `scalar_expr_list_context_global_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:243`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L243)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_list_context_global_outcome_equiv :
  forall kind prefix
      (left right : scalar_expr T relname kind) suffix,
    scalar_expr_global_outcome_equiv left right ->
    Forall2 scalar_expr_global_outcome_equiv
      (prefix ++ left :: suffix) (prefix ++ right :: suffix).
```

## `scalar_select_list_global_outcome_equiv_outputs`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:257`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L257)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_global_outcome_equiv_outputs :
  forall left right,
    scalar_select_list_global_outcome_equiv left right ->
    scalar_select_outputs left = scalar_select_outputs right.
```

## `scalar_select_list_global_outcome_equiv_values`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:267`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L267)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_global_outcome_equiv_values :
  forall left right,
    scalar_select_list_global_outcome_equiv left right ->
    scalar_value_expr_list_global_outcome_equiv
      (map fst left) (map fst right).
```

## `scalar_select_list_global_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:278`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L278)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_global_outcome_equiv_refl :
  forall select_list,
    scalar_select_list_global_outcome_equiv select_list select_list.
```

## `scalar_select_list_global_outcome_equiv_sym`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:287`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L287)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Reverses a proved SQL verification and runtime outcomes relation.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_list_global_outcome_equiv_sym :
  forall left right,
    scalar_select_list_global_outcome_equiv left right ->
    scalar_select_list_global_outcome_equiv right left.
```

## `scalar_select_context_global_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:703`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L703)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_context_global_outcome_equiv :
  forall context left right,
    scalar_expr_global_outcome_equiv
      (plug_scalar_expr_context
        (scalar_select_context_expression context) left)
      (plug_scalar_expr_context
        (scalar_select_context_expression context) right) ->
    scalar_select_list_global_outcome_equiv
      (plug_scalar_select_context context left)
      (plug_scalar_select_context context right).
```

## `eval_scalar_values_outcome_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:726`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L726)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_values_outcome_global_congr :
  forall left right,
    scalar_value_expr_list_global_outcome_equiv left right ->
    forall env outcome,
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left outcome <->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right outcome.
```

## `eval_scalar_boolean_operands_outcome_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:754`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L754)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_operands_outcome_global_congr :
  forall left right,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    forall env operation outcome,
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule env operation left outcome <->
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule env operation right outcome.
```

## `insert_boolean_operand_global_Forall2`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:790`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L790)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the insert boolean operand global forall2 law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma insert_boolean_operand_global_Forall2 :
  forall sites left_expression right_expression left right,
    scalar_expr_global_outcome_equiv left_expression right_expression ->
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    Forall2 scalar_expr_global_outcome_equiv
      (@insert_boolean_operand T relname boolean_schedule
        sites left_expression left)
      (@insert_boolean_operand T relname boolean_schedule
        sites right_expression right).
```

## `schedule_boolean_operands_aux_global_Forall2`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:813`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L813)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the schedule boolean operands aux global forall2 law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma schedule_boolean_operands_aux_global_Forall2 :
  forall site_rows left right left_ordered right_ordered,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    scalar_boolean_expr_list_global_outcome_equiv
      left_ordered right_ordered ->
    Forall2 scalar_expr_global_outcome_equiv
      (@schedule_boolean_operands_aux T relname boolean_schedule
        site_rows left left_ordered)
      (@schedule_boolean_operands_aux T relname boolean_schedule
        site_rows right right_ordered).
```

## `schedule_boolean_operands_global_Forall2`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:837`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L837)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the schedule boolean operands global forall2 law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma schedule_boolean_operands_global_Forall2 :
  forall site_rows left right,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    Forall2 scalar_expr_global_outcome_equiv
      (@schedule_boolean_operands T relname boolean_schedule site_rows left)
      (@schedule_boolean_operands T relname boolean_schedule site_rows right).
```

## `scalar_expr_call_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:850`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L850)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_call_global_congr :
  forall result_type operator left right,
    scalar_value_expr_list_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Call result_type operator left)
      (SExpr_Call result_type operator right).
```

## `scalar_expr_case_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:873`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L873)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `CASE`, `conditional expression`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_case_global_congr :
  forall result_type left_condition right_condition
      left_then right_then left_else right_else,
    scalar_expr_global_outcome_equiv left_condition right_condition ->
    scalar_expr_global_outcome_equiv left_then right_then ->
    scalar_expr_global_outcome_equiv left_else right_else ->
    scalar_expr_global_outcome_equiv
      (SExpr_Case result_type left_condition left_then left_else)
      (SExpr_Case result_type right_condition right_then right_else).
```

## `scalar_expr_bool_value_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:908`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L908)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_bool_value_global_congr :
  forall result_type embed left right,
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_BoolValue result_type embed left)
      (SExpr_BoolValue result_type embed right).
```

## `scalar_expr_value_bool_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:921`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L921)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_value_bool_global_congr :
  forall decode left right,
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_ValueBool decode left) (SExpr_ValueBool decode right).
```

## `scalar_expr_pred_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:933`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L933)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `predicate`, `Bool3`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_pred_global_congr :
  forall predicate left right,
    scalar_value_expr_list_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Pred predicate left) (SExpr_Pred predicate right).
```

## `scalar_expr_conj_list_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:955`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L955)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_conj_list_global_congr :
  forall site_rows operation left right,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_ConjList site_rows operation left)
      (SExpr_ConjList site_rows operation right).
```

## `scalar_expr_not_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:972`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L972)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_not_global_congr :
  forall left right,
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv (SExpr_Not left) (SExpr_Not right).
```

## `scalar_expr_subquery_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:985`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L985)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_subquery_global_congr :
  forall result_type null_value left right,
    query_expr_global_typed_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Subquery result_type null_value left)
      (SExpr_Subquery result_type null_value right).
```

## `scalar_expr_quant_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1002`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1002)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_quant_global_congr :
  forall quantifier predicate left_arguments right_arguments left right,
    scalar_value_expr_list_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_global_typed_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Quant quantifier predicate left_arguments left)
      (SExpr_Quant quantifier predicate right_arguments right).
```

## `scalar_expr_in_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1040`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1040)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `subquery`, `IN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_in_global_congr :
  forall left_arguments right_arguments left right,
    scalar_value_expr_list_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_global_typed_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_In left_arguments left) (SExpr_In right_arguments right).
```

## `scalar_expr_exists_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1077`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1077)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `subquery`, `EXISTS`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_exists_global_congr :
  forall left right,
    query_expr_global_exists_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Exists left) (SExpr_Exists right).
```

## `eval_project_rows_outcome_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1481`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1481)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_project_rows_outcome_global_congr :
  forall left_select right_select,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    forall env rows outcome,
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_select rows outcome <->
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_select rows outcome.
```

## `query_expr_project_select_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1563`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1563)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_project_select_global_typed_congr :
  forall left_select right_select input,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
```

## `query_expr_filter_expression_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1583`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1583)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_expression_global_typed_congr :
  forall left_expression right_expression input,
    scalar_expr_global_outcome_equiv left_expression right_expression ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter left_expression input)
      (QExpr_Filter right_expression input).
```

## `eval_project_join_sources_global_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1667`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1667)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `projection`, `SELECT list`, `equivalence`, `congruence`

```rocq
Lemma eval_project_join_sources_global_congr_forward :
  forall left_matched right_matched left_left right_left
      left_right right_right,
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env sources outcome,
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_matched left_left left_right sources outcome ->
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_matched right_left right_right sources outcome.
```

## `eval_project_join_sources_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1732`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1732)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `projection`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `join`, `projection`, `SELECT list`, `equivalence`, `congruence`

```rocq
Lemma eval_project_join_sources_global_congr :
  forall left_matched right_matched left_left right_left
      left_right right_right,
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env sources outcome,
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_matched left_left left_right sources outcome <->
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_matched right_left right_right sources outcome.
```

## `query_expr_join_scalar_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1817`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1817)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_join_scalar_global_typed_congr :
  forall kind left_predicate right_predicate
      left_matched right_matched left_left right_left left_right right_right
      left_query right_query,
    scalar_expr_global_outcome_equiv left_predicate right_predicate ->
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Join kind left_predicate left_matched left_left left_right
        left_query right_query)
      (QExpr_Join kind right_predicate right_matched right_left right_right
        left_query right_query).
```

## `scalar_expr_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1861`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1861)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem scalar_expr_context_global_congr :
  forall kind (context : scalar_expr_context kind) replacement replacement',
    query_expr_global_demand_equiv
      (scalar_expr_context_demand context) replacement replacement' ->
    scalar_expr_global_outcome_equiv
      (plug_scalar_expr_context context replacement)
      (plug_scalar_expr_context context replacement').
```

## `first_runtime_error_context_eq`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1913`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1913)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for SQL verification and runtime outcomes.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma first_runtime_error_context_eq :
  forall (A : Type) (observe : A -> option sql_runtime_error)
      prefix left right suffix,
    observe left = observe right ->
    first_runtime_error observe (prefix ++ left :: suffix) =
    first_runtime_error observe (prefix ++ right :: suffix).
```

## `scalar_expr_context_aggregate_runtime_error_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1926`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1926)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem scalar_expr_context_aggregate_runtime_error_congr :
  forall kind (context : scalar_expr_context kind) replacement replacement'
      env,
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_expr_context context replacement) =
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_expr_context context replacement').
```

## `scalar_expr_context_global_group_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1960`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1960)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Corollary scalar_expr_context_global_group_congr :
  forall kind (context : scalar_expr_context kind) replacement replacement',
    query_expr_global_demand_equiv
      (scalar_expr_context_demand context) replacement replacement' ->
    scalar_expr_global_group_outcome_equiv
      (plug_scalar_expr_context context replacement)
      (plug_scalar_expr_context context replacement').
```

## `scalar_select_context_aggregate_runtime_error_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1973`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1973)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `aggregate`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_select_context_aggregate_runtime_error_congr :
  forall context replacement replacement' env,
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_select_context context replacement) =
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_select_context context replacement').
```

## `query_expr_group_scalar_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2146`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2146)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_scalar_global_typed_congr :
  forall left_select right_select group_keys left_having right_having input,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    scalar_expr_global_group_outcome_equiv left_having right_having ->
    (forall current_env,
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group left_select group_keys left_having input)
      (QExpr_Group right_select group_keys right_having input).
```

## `scalar_expr_context_group_key_none`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2190`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2190)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the scalar expr context group key none law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `scalar_expr_context_group_key_none` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scheduled`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`

```rocq
Lemma scalar_expr_context_group_key_none :
  forall (context : scalar_expr_context ScalarResultValue)
      replacement suffix,
    scalar_group_key_terms
      (plug_scalar_expr_context context replacement :: suffix) = None.
```

## `scalar_value_list_context_group_keys_none`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2199`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2199)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the scalar value list context group keys none law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `scalar_value_list_context_group_keys_none` direction for SQL verification and runtime outcomes; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scheduled`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`

```rocq
Lemma scalar_value_list_context_group_keys_none :
  forall context replacement,
    scalar_group_key_terms
      (plug_scalar_value_list_context context replacement) = None.
```

## `query_expr_group_invalid_keys_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2220`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2220)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_invalid_keys_global_typed_congr :
  forall select_list left_keys right_keys having input,
    scalar_group_key_terms left_keys = None ->
    scalar_group_key_terms right_keys = None ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list left_keys having input)
      (QExpr_Group select_list right_keys having input).
```

## `eval_grouping_sets_bag_branch_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2243`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2243)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `grouping sets`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_grouping_sets_bag_branch_congr_forward :
  forall prefix left_select right_select left_keys right_keys suffix,
    (forall env input_bag outcome,
      eval_group_bag env left_select left_keys SExpr_True input_bag outcome ->
      eval_group_bag env right_select right_keys SExpr_True input_bag outcome) ->
    forall env input_bag outcome,
      eval_grouping_sets_bag env
        (prefix ++ (left_select, left_keys) :: suffix) input_bag outcome ->
      eval_grouping_sets_bag env
        (prefix ++ (right_select, right_keys) :: suffix) input_bag outcome.
```

## `eval_grouping_sets_bag_branch_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2271`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2271)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `grouping sets`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_grouping_sets_bag_branch_congr :
  forall prefix left_select right_select left_keys right_keys suffix,
    (forall env input_bag outcome,
      eval_group_bag env left_select left_keys SExpr_True input_bag outcome <->
      eval_group_bag env right_select right_keys SExpr_True input_bag outcome) ->
    forall env input_bag outcome,
      eval_grouping_sets_bag env
        (prefix ++ (left_select, left_keys) :: suffix) input_bag outcome <->
      eval_grouping_sets_bag env
        (prefix ++ (right_select, right_keys) :: suffix) input_bag outcome.
```

## `query_expr_grouping_sets_branch_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2290`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2290)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `grouping sets`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_grouping_sets_branch_global_typed_congr :
  forall prefix left_select right_select left_keys right_keys suffix input,
    query_grouping_sets_outputs
      (prefix ++ (left_select, left_keys) :: suffix) =
    query_grouping_sets_outputs
      (prefix ++ (right_select, right_keys) :: suffix) ->
    (forall env input_bag outcome,
      eval_group_bag env left_select left_keys SExpr_True input_bag outcome <->
      eval_group_bag env right_select right_keys SExpr_True input_bag outcome) ->
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets
        (prefix ++ (left_select, left_keys) :: suffix) input)
      (QExpr_GroupingSets
        (prefix ++ (right_select, right_keys) :: suffix) input).
```

## `query_expr_grouping_sets_select_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2326`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2326)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `grouping sets`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_grouping_sets_select_context_global_congr :
  forall prefix select_context group_keys suffix input replacement replacement',
    query_expr_global_demand_equiv
      (scalar_select_context_demand select_context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets
        (prefix ++
          (plug_scalar_select_context select_context replacement, group_keys) ::
          suffix) input)
      (QExpr_GroupingSets
        (prefix ++
          (plug_scalar_select_context select_context replacement', group_keys) ::
          suffix) input).
```

## `query_expr_grouping_sets_key_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2381`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2381)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `grouping sets`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_grouping_sets_key_context_global_congr :
  forall prefix select_list key_context suffix input replacement replacement',
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets
        (prefix ++
          (select_list,
            plug_scalar_value_list_context key_context replacement) :: suffix)
        input)
      (QExpr_GroupingSets
        (prefix ++
          (select_list,
            plug_scalar_value_list_context key_context replacement') :: suffix)
        input).
```

## `query_expr_group_select_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2407`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2407)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_select_context_global_congr :
  forall select_context group_keys having input replacement replacement',
    query_expr_global_demand_equiv
      (scalar_select_context_demand select_context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group (plug_scalar_select_context select_context replacement)
        group_keys having input)
      (QExpr_Group (plug_scalar_select_context select_context replacement')
        group_keys having input).
```

## `query_expr_group_having_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2430`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2430)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_having_context_global_congr :
  forall select_list group_keys having_context input replacement replacement',
    query_expr_global_demand_equiv
      (scalar_expr_context_demand having_context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list group_keys
        (plug_scalar_expr_context having_context replacement) input)
      (QExpr_Group select_list group_keys
        (plug_scalar_expr_context having_context replacement') input).
```

## `query_expr_group_key_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2449`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2449)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `grouping`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `GROUP BY`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_group_key_context_global_congr :
  forall select_list key_context having input replacement replacement',
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list
        (plug_scalar_value_list_context key_context replacement) having input)
      (QExpr_Group select_list
        (plug_scalar_value_list_context key_context replacement') having input).
```

## `query_expr_context_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2463`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2463)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_context_global_congr :
  forall (context : query_expr_context) replacement replacement',
    query_expr_global_demand_equiv (query_expr_context_demand context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
```

## `query_expr_observation_equiv_of_outcome_rel_equiv_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2511`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2511)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_observation_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_observation_equiv T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env first second.
```

## `query_expr_equiv_of_outcome_rel_equiv_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2536`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2536)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first second.
```

## `query_expr_context_equiv_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2551`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2551)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_context_equiv_safe :
  forall context replacement replacement' env,
    query_expr_global_demand_equiv (query_expr_context_demand context)
      replacement replacement' ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement) ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement') ->
    query_expr_has_success env
      (plug_query_expr_context context replacement) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
```

## `query_bag_closed_equiv_of_success_bags_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2578`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2578)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_possible_bag_closed_outcome_equiv_of_success_bags` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

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
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first)
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env first second.
```

## `query_bag_reset_equiv_of_success_bags_safe`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2627`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2627)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_possible_bag_closed_outcome_equiv_of_success_bags` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_bag_reset_equiv_of_success_bags_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_order_behavior first = BagReset ->
    query_expr_order_behavior second = BagReset ->
    rel_equiv
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first)
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env first second.
```

## `query_distinct_equiv_of_local_success_rel_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2655`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2655)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_distinct_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `DISTINCT`, `duplicate elimination`, `equivalence`, `congruence`

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
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env (QExpr_Distinct left) (QExpr_Distinct right).
```

## `query_distinct_local_list_equiv_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2692`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2692)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_distinct_possible_outcome_equiv_congr` for the public result.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `DISTINCT`, `duplicate elimination`, `equivalence`, `congruence`

```rocq
Theorem query_distinct_local_list_equiv_congr :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env left right ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env (QExpr_Distinct left) (QExpr_Distinct right).
```

## `plug_possible_bag_context_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2766`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2766)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2787`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2787)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2805`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2805)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2819`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2819)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2845`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2845)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2854`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2854)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2866`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2866)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2877`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2877)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2896`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2896)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2910`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2910)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_equiv_possible_bag_context_congr :
  forall env context first second,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first second ->
    possible_bag_query_boundary_equiv
      (query_expr_sort first) (query_expr_sort second)
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env first)))
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env second))).
```

## `query_possible_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2978`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2978)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the query possible bag outcomes law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_possible_bag_outcomes
    (env : Env.env T) (query : query_expr T relname) :
    sql_outcome outcome_bagT -> Prop :=
  @outcome_alpha T (eval_possible_query env query).
```

## `query_expr_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2985`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2985)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Definition query_expr_possible_bag_outcome_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  outcome_relation_equiv (@bag_eq T)
    (query_possible_bag_outcomes env left)
    (query_possible_bag_outcomes env right).
```

## `query_expr_possible_bag_outcome_equiv_intro`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:2992`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L2992)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_intro :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    outcome_relation_equiv (@bag_eq T)
      (query_possible_bag_outcomes env left)
      (query_possible_bag_outcomes env right) ->
    query_expr_possible_bag_outcome_equiv env left right.
```

## `query_expr_possible_bag_outcome_equiv_outputs`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3003`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3003)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_outputs :
  forall env left right,
    query_expr_possible_bag_outcome_equiv env left right ->
    query_expr_outputs left = query_expr_outputs right.
```

## `query_expr_possible_bag_outcome_equiv_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3011`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3011)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_outcomes :
  forall env left right,
    query_expr_possible_bag_outcome_equiv env left right ->
    outcome_relation_equiv (@bag_eq T)
      (query_possible_bag_outcomes env left)
      (query_possible_bag_outcomes env right).
```

## `query_expr_possible_bag_outcome_equiv_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3021`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3021)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_possible_bag_outcome_equiv_iff :
  forall env left right,
    query_expr_possible_bag_outcome_equiv env left right <->
    query_expr_outputs left = query_expr_outputs right /\
    outcome_relation_equiv (@bag_eq T)
      (query_possible_bag_outcomes env left)
      (query_possible_bag_outcomes env right).
```

## `outcome_relation_equiv_implies_outcome_alpha_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3034`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3034)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma outcome_relation_equiv_implies_outcome_alpha_equiv :
  forall (left right : sql_outcome (list outcome_tuple) -> Prop),
    outcome_relation_equiv (@ordered_rows_equiv T) left right ->
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right).
```

## `query_expr_possible_outcome_equiv_implies_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3074`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3074)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Abstracts exact possible ordered-row outcomes to possible bags while preserving output schemas and every runtime-error category.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_outcome_equiv_implies_possible_bag_outcome_equiv :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    query_expr_possible_bag_outcome_equiv env left right.
```

## `query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3089`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3089)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Recovers exact possible ordered-row outcome equivalence from the possible-bag contract when both success relations are BagClosed.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Retain BagClosed for both actual possible-success list relations; one chosen bag representative cannot justify ordered possible outcomes.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_possible_query env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible_query env right (SqlSuccess rows)) ->
    query_expr_possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
```

## `query_expr_possible_outcome_equiv_iff_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3110`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3110)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_possible_outcome_equiv_iff_possible_bag_outcome_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_possible_query env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible_query env right (SqlSuccess rows)) ->
    (@query_expr_possible_outcome_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_expr_possible_bag_outcome_equiv env left right).
```

## `possible_bag_outcome_equiv_refl`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3175`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3175)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Establishes reflexivity for SQL verification and runtime outcomes.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma possible_bag_outcome_equiv_refl :
  forall outcome : sql_outcome outcome_bagT,
    outcome_equiv (@bag_eq T) outcome outcome.
```

## `possible_bag_outcome_relation_equiv_match_left`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3184`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3184)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma possible_bag_outcome_relation_equiv_match_left :
  forall first second outcome,
    outcome_relation_equiv (@bag_eq T) first second ->
    first outcome ->
    exists outcome',
      second outcome' /\ outcome_equiv (@bag_eq T) outcome outcome'.
```

## `possible_bag_outcome_relation_equiv_match_right`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3200`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3200)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma possible_bag_outcome_relation_equiv_match_right :
  forall first second outcome,
    outcome_relation_equiv (@bag_eq T) first second ->
    second outcome ->
    exists outcome',
      first outcome' /\ outcome_equiv (@bag_eq T) outcome' outcome.
```

## `lift_possible_bag_outcome_unary_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3216`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3216)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts possible-bag/outcome equivalence compositionally through an outcome-compatible abstract unary, binary, or nested context.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Supply the displayed outcome-compatibility and well-formedness contracts. They preserve inhabitation and exact runtime-error categories, not only equality of successful bags.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem lift_possible_bag_outcome_unary_congr :
  forall operation first_inputs second_inputs,
    unary_bag_outcome_relation_compatible operation ->
    outcome_relation_equiv (@bag_eq T) first_inputs second_inputs ->
    outcome_relation_equiv (@bag_eq T)
      (lift_possible_bag_outcome_unary operation first_inputs)
      (lift_possible_bag_outcome_unary operation second_inputs).
```

## `lift_possible_bag_outcome_binary_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3274`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3274)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts possible-bag/outcome equivalence compositionally through an outcome-compatible abstract unary, binary, or nested context.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Supply the displayed outcome-compatibility and well-formedness contracts. They preserve inhabitation and exact runtime-error categories, not only equality of successful bags.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem lift_possible_bag_outcome_binary_congr :
  forall operation first_left second_left first_right second_right,
    binary_bag_outcome_relation_compatible operation ->
    outcome_relation_equiv (@bag_eq T) first_left second_left ->
    outcome_relation_equiv (@bag_eq T) first_right second_right ->
    outcome_relation_equiv (@bag_eq T)
      (lift_possible_bag_outcome_binary operation first_left first_right)
      (lift_possible_bag_outcome_binary operation second_left second_right).
```

## `possible_bag_outcome_context_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3410`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3410)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts possible-bag/outcome equivalence compositionally through an outcome-compatible abstract unary, binary, or nested context.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Supply the displayed outcome-compatibility and well-formedness contracts. They preserve inhabitation and exact runtime-error categories, not only equality of successful bags.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem possible_bag_outcome_context_congr :
  forall context first second,
    possible_bag_outcome_context_well_formed context ->
    outcome_relation_equiv (@bag_eq T) first second ->
    outcome_relation_equiv (@bag_eq T)
      (plug_possible_bag_outcome_context context first)
      (plug_possible_bag_outcome_context context second).
```

## `outcome_relation_equiv_rel_equiv_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3438`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3438)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma outcome_relation_equiv_rel_equiv_transport :
  forall first first' second second',
    rel_equiv first first' ->
    rel_equiv second second' ->
    outcome_relation_equiv (@bag_eq T) first' second' ->
    outcome_relation_equiv (@bag_eq T) first second.
```

## `query_expr_possible_bag_outcome_context_boundary_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3468`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3468)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Connects the abstract possible-bag/outcome context layer to actual queries through exact two-sided parent characterizations.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Retain both exact `rel_equiv` parent characterizations, context well-formedness, child possible-bag/outcome equivalence, and exact output-schema equality. Concrete characterizations must account for schedule, correlation, NULL/Bool3, order, multiplicity, and errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_bag_outcome_context_boundary_congr :
  forall env context child_left child_right parent_left parent_right,
    possible_bag_outcome_context_well_formed context ->
    query_expr_possible_bag_outcome_equiv env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    rel_equiv
      (query_possible_bag_outcomes env parent_left)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_left)) ->
    rel_equiv
      (query_possible_bag_outcomes env parent_right)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_right)) ->
    query_expr_possible_bag_outcome_equiv env parent_left parent_right.
```

## `query_expr_possible_bag_outcome_context_boundary_final`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3496`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3496)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Connects the abstract possible-bag/outcome context layer to actual queries through exact two-sided parent characterizations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: Retain both exact `rel_equiv` parent characterizations, context well-formedness, child possible-bag/outcome equivalence, and exact output-schema equality. Concrete characterizations must account for schedule, correlation, NULL/Bool3, order, multiplicity, and errors. The final theorem additionally requires BagClosed for both actual parent success relations.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_possible_bag_outcome_context_boundary_final :
  forall env context child_left child_right parent_left parent_right,
    BagClosed T
      (fun rows => eval_possible_query env parent_left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible_query env parent_right (SqlSuccess rows)) ->
    possible_bag_outcome_context_well_formed context ->
    query_expr_possible_bag_outcome_equiv env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    rel_equiv
      (query_possible_bag_outcomes env parent_left)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_left)) ->
    rel_equiv
      (query_possible_bag_outcomes env parent_right)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_right)) ->
    @query_expr_possible_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env parent_left parent_right.
```

## `query_scheduled_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3562`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3562)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query scheduled bag outcomes law for SQL verification and runtime outcomes, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_scheduled_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (query : query_expr T relname) :
    sql_outcome scheduled_bagT -> Prop :=
  @outcome_alpha T (eval_scheduled_query schedule env query).
```

## `query_possible_bag_outcomes_iff_scheduled`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3570`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3570)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Gives necessary and sufficient conditions for SQL verification and runtime outcomes.

Applicability: Use in either direction to invert or construct a goal about SQL verification and runtime outcomes.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_possible_bag_outcomes_iff_scheduled :
  forall env query outcome,
    @query_possible_bag_outcomes T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env query outcome <->
    exists schedule,
      query_scheduled_bag_outcomes schedule env query outcome.
```

## `query_expr_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3594`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3594)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports the displayed hypotheses and conclusion for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_expr_possible_bag_schedule_transport
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  (forall left_schedule,
    exists right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left)
        (query_scheduled_bag_outcomes right_schedule env right)) /\
  (forall right_schedule,
    exists left_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left)
        (query_scheduled_bag_outcomes right_schedule env right)).
```

## `query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3608`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3608)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes SQL verification and runtime outcomes across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Supply bidirectional per-schedule transport of the complete scheduled bag/error relations and exact output-schema equality. Independent existential outcomes do not establish this contract.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv :
  forall env left right,
    query_expr_possible_bag_schedule_transport env left right ->
    @query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
```

## `query_expr_possible_bag_unary_wrapper_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3692`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3692)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts a matched unary or joint binary child schedule transport through an explicit complete parent bag/error law, returning a schedule-transport contract that remains compositional.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: Retain exact output schemas and prove the complete parent bag/error relation from child relations under the same matched schedule pair. The local law must account for tuple values, multiplicity, Bool3, ordering/group finalization, and runtime errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_possible_bag_unary_wrapper_schedule_transport :
  forall env child_left child_right parent_left parent_right,
    query_expr_possible_bag_schedule_transport
      env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env child_left)
        (query_scheduled_bag_outcomes right_schedule env child_right) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    query_expr_possible_bag_schedule_transport
      env parent_left parent_right.
```

## `query_expr_possible_bag_unary_wrapper_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3721`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3721)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts possible-bag/outcome equivalence compositionally through an outcome-compatible abstract unary, binary, or nested context.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Retain exact output schemas and prove the complete parent bag/error relation from child relations under the same matched schedule pair. The local law must account for tuple values, multiplicity, Bool3, ordering/group finalization, and runtime errors.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_bag_unary_wrapper_congr :
  forall env child_left child_right parent_left parent_right,
    query_expr_possible_bag_schedule_transport
      env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env child_left)
        (query_scheduled_bag_outcomes right_schedule env child_right) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    @query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env parent_left parent_right.
```

## `query_expr_possible_bag_joint_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3748`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3748)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports the displayed hypotheses and conclusion for SQL verification and runtime outcomes.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_expr_possible_bag_joint_schedule_transport
    (env : Env.env T)
    (left_first left_second right_first right_second :
      query_expr T relname) : Prop :=
  query_expr_outputs left_first = query_expr_outputs right_first /\
  query_expr_outputs left_second = query_expr_outputs right_second /\
  (forall left_schedule,
    exists right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) /\
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second)) /\
  (forall right_schedule,
    exists left_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) /\
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second)).
```

## `query_expr_possible_bag_binary_wrapper_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3774`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3774)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts a matched unary or joint binary child schedule transport through an explicit complete parent bag/error law, returning a schedule-transport contract that remains compositional.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL verification and runtime outcomes.

Important premises: Retain exact output schemas and prove the complete parent bag/error relation from child relations under the same matched schedule pair. The local law must account for tuple values, multiplicity, Bool3, ordering/group finalization, and runtime errors. The binary theorem requires one target schedule that relates both child pairs jointly; two marginal schedule transports are insufficient.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_possible_bag_binary_wrapper_schedule_transport :
  forall env left_first left_second right_first right_second
         parent_left parent_right,
    query_expr_possible_bag_joint_schedule_transport env
      left_first left_second right_first right_second ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    query_expr_possible_bag_schedule_transport
      env parent_left parent_right.
```

## `query_expr_possible_bag_binary_wrapper_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3808`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3808)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts possible-bag/outcome equivalence compositionally through an outcome-compatible abstract unary, binary, or nested context.

Applicability: Use to orient, transport, or compose a semantic relation about SQL verification and runtime outcomes.

Important premises: Retain exact output schemas and prove the complete parent bag/error relation from child relations under the same matched schedule pair. The local law must account for tuple values, multiplicity, Bool3, ordering/group finalization, and runtime errors. The binary theorem requires one target schedule that relates both child pairs jointly; two marginal schedule transports are insufficient.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_expr_possible_bag_binary_wrapper_congr :
  forall env left_first left_second right_first right_second
         parent_left parent_right,
    query_expr_possible_bag_joint_schedule_transport env
      left_first left_second right_first right_second ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    @query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env parent_left parent_right.
```

## `lift_possible_bag_outcome_binary_cross_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3963`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3963)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts possible-bag/outcome equivalence compositionally through an outcome-compatible abstract unary, binary, or nested context.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: Supply the displayed outcome-compatibility and well-formedness contracts. They preserve inhabitation and exact runtime-error categories, not only equality of successful bags.

Cross-index: `possible`, `outcome`, `grouping`, `runtime`, `projection`, `filter`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `verification and runtime semantics`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem lift_possible_bag_outcome_binary_cross_congr :
  forall left_operation right_operation
         first_left second_left first_right second_right,
    binary_bag_outcome_relations_cross_compatible
      left_operation right_operation ->
    outcome_relation_equiv (@bag_eq T) first_left second_left ->
    outcome_relation_equiv (@bag_eq T) first_right second_right ->
    outcome_relation_equiv (@bag_eq T)
      (lift_possible_bag_outcome_binary
        left_operation first_left first_right)
      (lift_possible_bag_outcome_binary
        right_operation second_left second_right).
```
