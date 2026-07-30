# Attribute and query renaming transport

Route here for: collision-safe tuple, row, outcome, and compositional query alpha-renaming.

This focused catalog contains 126 declarations routed at declaration granularity from `RenameTransportFacts.v`, `SqlQueryRenameTransport.v`, `SqlRenameFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

The semantics-generic implementation is owned by [`SqlRenameFacts.v`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v) and [`SqlQueryRenameTransport.v`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v). `RenameTransportFacts.v` contains only TNull type/typmod adapters and proof-agent entry points; its query facade accepts a textual `string -> string` name map and cannot change typmods.

## `tnull_attribute_name_renaming_type_preserving`

Source: [`theories/FormalSQL/RenameTransportFacts.v:39`](../RenameTransportFacts.v#L39)

Purpose/direction: Shows that name-only TNull attribute renaming preserves the exact SQL value type, including every textual, decimal, and temporal typmod.

Applicability: Use only with `rename_tnull_attribute_name`, which changes the textual name and leaves the complete SQL type/typmod constructor untouched.

Important premises: No injectivity premise is needed for this one-attribute fact, but the renamer must be the displayed name-only TNull adapter.

Cross-index: `renaming`, `facade`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma tnull_attribute_name_renaming_type_preserving :
  forall rename_name source,
    type_of_attribute TNull
      (rename_tnull_attribute_name rename_name source) =
    type_of_attribute TNull source.
```

## `tnull_attribute_name_renaming_value_conforms`

Source: [`theories/FormalSQL/RenameTransportFacts.v:51`](../RenameTransportFacts.v#L51)

Purpose/direction: Preserves and reflects TNull value conformance under name-only attribute renaming, including NULL payloads and constrained types.

Applicability: Use only with `rename_tnull_attribute_name`, which changes the textual name and leaves the complete SQL type/typmod constructor untouched.

Important premises: No injectivity premise is needed for this one-attribute fact, but the renamer must be the displayed name-only TNull adapter.

Cross-index: `renaming`, `facade`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma tnull_attribute_name_renaming_value_conforms :
  forall rename_name source value,
    value_conforms_attribute
      (rename_tnull_attribute_name rename_name source) value <->
    value_conforms_attribute source value.
```

## `tnull_rows_name_renaming_type_safe`

Source: [`theories/FormalSQL/RenameTransportFacts.v:60`](../RenameTransportFacts.v#L60)

Purpose/direction: Discharges actual successful-row type/typmod safety for every row under the name-only TNull attribute adapter.

Applicability: Use only with `rename_tnull_attribute_name`, which changes the textual name and leaves the complete SQL type/typmod constructor untouched.

Important premises: No injectivity premise is needed for this actual-row type/typmod fact.  Collision reflection remains a separate `rows_rename_collision_safe` obligation.

Cross-index: `renaming`, `facade`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_rows_name_renaming_type_safe :
  forall rename_name rows,
    rows_rename_type_safe
      (rename_tnull_attribute_name rename_name) rows.
```

## `tnull_tuple_conforms_sort_renaming_transport`

Source: [`theories/FormalSQL/RenameTransportFacts.v:69`](../RenameTransportFacts.v#L69)

Purpose/direction: Transports tuple/schema conformance through name-only renaming under injectivity on the source sort, rejecting attribute collisions.

Applicability: Use after proving injectivity on the relevant source sort.  A collision between two represented attributes is deliberately not transportable.

Important premises: Retain tuple conformance and `attribute_rename_injective_on sort`; without the latter, finite-map keys can collide and lose a value.

Cross-index: `renaming`, `facade`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Theorem tnull_tuple_conforms_sort_renaming_transport :
  forall rename_name sort row,
    tuple_conforms_sort sort row ->
    attribute_rename_injective_on sort
      (rename_tnull_attribute_name rename_name) ->
    tuple_conforms_sort
      (Fset.map (A TNull) (A TNull)
        (rename_tnull_attribute_name rename_name) sort)
      (rename_tuple TNull (rename_tnull_attribute_name rename_name) row).
```

## `tnull_rows_renaming_firstn_transport`

Source: [`theories/FormalSQL/RenameTransportFacts.v:117`](../RenameTransportFacts.v#L117)

Purpose/direction: Commutes exact row-wise renaming with the displayed ordered slice, preserving row order and duplicate occurrences.

Applicability: Use for OFFSET/FETCH-style ordered slicing after establishing exact pointwise row renaming; the conclusion is not merely bag equality.

Important premises: Supply the exact `rows_rename_equiv` relation.  It fixes pointwise renamed representatives, list order, length, and duplicate positions.

Cross-index: `renaming`, `facade`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`

```rocq
Lemma tnull_rows_renaming_firstn_transport :
  forall (rename_attribute : attribute TNull -> attribute TNull)
      count left right,
    rows_rename_equiv rename_attribute left right ->
    rows_rename_equiv rename_attribute
      (firstn count left) (firstn count right).
```

## `tnull_rows_renaming_skipn_transport`

Source: [`theories/FormalSQL/RenameTransportFacts.v:127`](../RenameTransportFacts.v#L127)

Purpose/direction: Commutes exact row-wise renaming with the displayed ordered slice, preserving row order and duplicate occurrences.

Applicability: Use for OFFSET/FETCH-style ordered slicing after establishing exact pointwise row renaming; the conclusion is not merely bag equality.

Important premises: Supply the exact `rows_rename_equiv` relation.  It fixes pointwise renamed representatives, list order, length, and duplicate positions.

Cross-index: `renaming`, `facade`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`

```rocq
Lemma tnull_rows_renaming_skipn_transport :
  forall (rename_attribute : attribute TNull -> attribute TNull)
      count left right,
    rows_rename_equiv rename_attribute left right ->
    rows_rename_equiv rename_attribute
      (skipn count left) (skipn count right).
```

## `tnull_query_mapped_schema_outcome_equiv_mapped_schema`

Source: [`theories/FormalSQL/RenameTransportFacts.v:170`](../RenameTransportFacts.v#L170)

Purpose/direction: Extracts the ordered name-only mapped output schema from exact TNull observations; this observational relation is neither full alpha-renaming nor ordinary same-schema equivalence.

Applicability: Use to recover the target schema from mapped-schema outcome equivalence.  It is observational only; certify full alpha-renaming through constructor-local metadata premises, while ordinary equivalence still requires unchanged labels.

Important premises: Supply a textual `string -> string` map and exact mapped-schema outcomes.  The facade applies `rename_tnull_attribute_name`, so typmods cannot change, but this premise alone does not certify predicate/key/subquery metadata.

Cross-index: `renaming`, `facade`, `outcome`, `runtime`, `schema`, `scalar`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `string`, `VARCHAR`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma tnull_query_mapped_schema_outcome_equiv_mapped_schema :
  forall db left_env right_env (rename_name : string -> string) left right,
    tnull_query_mapped_schema_outcome_equiv
      db left_env right_env rename_name left right ->
    map (rename_tnull_attribute_name rename_name)
      (query_expr_outputs left) =
      query_expr_outputs right.
```

## `tnull_query_renaming_context_chain_transport`

Source: [`theories/FormalSQL/RenameTransportFacts.v:204`](../RenameTransportFacts.v#L204)

Purpose/direction: Closes a proved name-only renaming transport under an arbitrary list of paired query contexts, retaining typmods, operator metadata, and outcomes.

Applicability: Use for any finite nesting after certifying every paired context with its constructor-local transport rule.  Supply a textual `string -> string` map; the facade lifts it without permitting a typmod change, while predicates, projections, join/group/sort/window metadata, aliases, and schemas move together.

Important premises: Supply a textual `string -> string` map, `Forall2` compatibility for the complete left/right context lists, and a transport proof for the holes.  The facade preserves typmods and infers no metadata premise from output-only renaming.

Cross-index: `renaming`, `facade`, `grouping`, `projection`, `join`, `bag`, `ordered`, `scalar`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `join`, `GROUP BY`, `projection`, `SELECT list`, `ORDER BY`, `ordered observation`, `window`, `PARTITION BY`, `string`, `VARCHAR`, `bag semantics`, `list/bag bridge`

```rocq
Theorem tnull_query_renaming_context_chain_transport :
  forall db environment_relation (rename_name : string -> string)
      left_contexts right_contexts,
    Forall2
      (tnull_query_rename_context_compatible
        db environment_relation rename_name)
      left_contexts right_contexts ->
    forall left right,
      tnull_query_rename_transport_under
        db environment_relation rename_name left right ->
      tnull_query_rename_transport_under
        db environment_relation rename_name
        (plug_query_rename_contexts left_contexts left)
        (plug_query_rename_contexts right_contexts right).
```

## `query_formula_outcome_rename_compatible_success_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:152`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L152)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_formula_outcome_rename_compatible_success_iff :
  forall environment_relation left right left_env right_env,
    query_formula_outcome_rename_compatible
      environment_relation left right ->
    environment_relation left_env right_env ->
    forall truth,
      (eval_formula left_env left (SqlSuccess truth) <->
       eval_formula right_env right (SqlSuccess truth)).
```

## `query_formula_outcome_rename_compatible_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:172`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L172)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_formula_outcome_rename_compatible_error_iff :
  forall environment_relation left right left_env right_env,
    query_formula_outcome_rename_compatible
      environment_relation left right ->
    environment_relation left_env right_env ->
    forall error,
      (eval_formula left_env left (SqlError error) <->
       eval_formula right_env right (SqlError error)).
```

## `query_rename_transport_under_closed`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:271`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L271)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `query_rename_transport_under_closed` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_rename_transport_under_closed :
  forall rho left right,
    query_rename_transport_under
      (fun left_env right_env => left_env = nil /\ right_env = nil)
      rho left right ->
    query_closed_rename_transport rho left right.
```

## `query_unary_outcome_lift_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:324`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L324)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_unary_outcome_lift_transport :
  forall rho left_child right_child left_local right_local,
    query_outcome_rename_transport rho left_child right_child ->
    (forall left_rows right_rows,
      query_rows_rename rho left_rows right_rows ->
      query_outcome_rename_transport rho
        (left_local left_rows) (right_local right_rows)) ->
    query_outcome_rename_transport rho
      (query_unary_outcome_lift left_child left_local)
      (query_unary_outcome_lift right_child right_local).
```

## `query_binary_outcome_lift_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:366`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L366)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_binary_outcome_lift_error_iff :
  forall left_child right_child local error,
    query_binary_outcome_lift left_child right_child local
      (SqlError error) <->
    left_child (SqlError error) \/
    (exists left_rows,
      left_child (SqlSuccess left_rows) /\
      right_child (SqlError error)) \/
    (exists left_rows right_rows,
      left_child (SqlSuccess left_rows) /\
      right_child (SqlSuccess right_rows) /\
      local left_rows right_rows (SqlError error)).
```

## `query_binary_outcome_lift_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:394`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L394)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_binary_outcome_lift_transport :
  forall rho left_child left_child' right_child right_child'
      left_local right_local,
    query_outcome_rename_transport rho left_child left_child' ->
    query_outcome_rename_transport rho right_child right_child' ->
    (forall left_rows left_rows' right_rows right_rows',
      query_rows_rename rho left_rows left_rows' ->
      query_rows_rename rho right_rows right_rows' ->
      query_outcome_rename_transport rho
        (left_local left_rows right_rows)
        (right_local left_rows' right_rows')) ->
    query_outcome_rename_transport rho
      (query_binary_outcome_lift left_child right_child left_local)
      (query_binary_outcome_lift left_child' right_child' right_local).
```

## `query_outcome_rename_transport_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:472`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L472)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_outcome_rename_transport_congr :
  forall rho left left' right right',
    (forall outcome, left outcome <-> left' outcome) ->
    (forall outcome, right outcome <-> right' outcome) ->
    query_outcome_rename_transport rho left right ->
    query_outcome_rename_transport rho left' right'.
```

## `query_unary_constructor_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:520`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L520)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `query_unary_constructor_rename_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_unary_constructor_rename_transport :
  forall environment_relation rho child child' outer outer'
      left_local right_local,
    query_rename_schema_compatible rho outer outer' ->
    query_rename_transport_under environment_relation rho child child' ->
    query_unary_local_rename_compatible
      environment_relation rho left_local right_local ->
    (forall env outcome,
      eval_query env outer outcome <->
      query_unary_outcome_lift
        (eval_query env child) (left_local env) outcome) ->
    (forall env outcome,
      eval_query env outer' outcome <->
      query_unary_outcome_lift
        (eval_query env child') (right_local env) outcome) ->
    query_rename_transport_under environment_relation rho outer outer'.
```

## `query_binary_constructor_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:551`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L551)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `query_binary_constructor_rename_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_binary_constructor_rename_transport :
  forall environment_relation rho
      left left' right right' outer outer' left_local right_local,
    query_rename_schema_compatible rho outer outer' ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible
      environment_relation rho left_local right_local ->
    (forall env outcome,
      eval_query env outer outcome <->
      query_binary_outcome_lift
        (eval_query env left) (eval_query env right)
        (left_local env) outcome) ->
    (forall env outcome,
      eval_query env outer' outcome <->
      query_binary_outcome_lift
        (eval_query env left') (eval_query env right')
        (right_local env) outcome) ->
    query_rename_transport_under environment_relation rho outer outer'.
```

## `query_rows_bag_rename_rows`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:600`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L600)

Purpose/direction: States the query rows bag rename rows law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_rows_bag_rename_rows :
  forall rho rows,
    bag_eq T (query_rows_bag (rename_rows rho rows))
      (rename_bag rho (query_rows_bag rows)).
```

## `query_rename_bag_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:619`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L619)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_rename_bag_congr :
  forall rho left right,
    bag_eq T left right ->
    bag_eq T (rename_bag rho left) (rename_bag rho right).
```

## `query_same_rows_as_bag_rename_rows`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:649`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L649)

Purpose/direction: Bridges the two displayed representations of collision-safe attribute and query renaming transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_rename_rows :
  forall (rho : attribute T -> attribute T)
      (rows : list tuple) (bag : bagT),
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag (rename_rows rho rows) (rename_bag rho bag).
```

## `query_bag_source_renamed_rows_preimage`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:665`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L665)

Purpose/direction: States the query bag source renamed rows preimage law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_source_renamed_rows_preimage :
  forall (rho : attribute T -> attribute T)
      (bag : bagT) (right_rows : list tuple),
    query_same_rows_as_bag right_rows (rename_bag rho bag) ->
    exists left_rows,
      query_same_rows_as_bag left_rows bag /\
      rows_rename_equiv rho left_rows right_rows.
```

## `query_bag_source_local_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:705`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L705)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_bag_source_local_rename_transport :
  forall rho left_bag right_bag,
    query_bag_source_rename_safe rho left_bag ->
    bag_eq T right_bag (rename_bag rho left_bag) ->
    query_outcome_rename_transport rho
      (query_bag_source_local left_bag)
      (query_bag_source_local right_bag).
```

## `query_source_constructor_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:747`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L747)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `query_source_constructor_rename_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_source_constructor_rename_transport :
  forall environment_relation rho outer outer' left_local right_local,
    query_rename_schema_compatible rho outer outer' ->
    query_outcome_rename_transport rho left_local right_local ->
    (forall env outcome, eval_query env outer outcome <-> left_local outcome) ->
    (forall env outcome, eval_query env outer' outcome <-> right_local outcome) ->
    query_rename_transport_under environment_relation rho outer outer'.
```

## `eval_query_error_source_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:765`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L765)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_error_source_iff :
  forall env outputs error outcome,
    eval_query env (QExpr_Error outputs error) outcome <->
    query_error_source_local error outcome.
```

## `eval_query_values_source_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:775`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L775)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma eval_query_values_source_iff :
  forall env outputs values outcome,
    eval_query env (QExpr_Values outputs values) outcome <->
    query_bag_source_local values outcome.
```

## `eval_query_table_source_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:787`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L787)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma eval_query_table_source_iff :
  forall env outputs table outcome,
    eval_query env (QExpr_Table outputs table) outcome <->
    query_bag_source_local (query_table_bag basesort instance outputs table)
      outcome.
```

## `QExpr_Error_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:802`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L802)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Error`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use after proving the mapped, admissible endpoint-schema contract; the same opaque SQL error is retained exactly.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  No child or local premise is needed; the error value itself must be identical.

Cross-index: `renaming`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem QExpr_Error_rename_transport :
  forall environment_relation rho left_outputs right_outputs error,
    query_rename_schema_compatible rho
      (QExpr_Error left_outputs error) (QExpr_Error right_outputs error) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Error left_outputs error) (QExpr_Error right_outputs error).
```

## `QExpr_Values_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:828`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L828)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Values`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use only when the target VALUES bag is the concrete renamed source bag and every represented source row satisfies collision/type safety.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep `query_bag_source_rename_safe` and exact mapped-bag equality; declared outputs alone do not constrain malformed rows.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem QExpr_Values_rename_transport :
  forall environment_relation rho left_outputs right_outputs
      left_values right_values,
    query_rename_schema_compatible rho
      (QExpr_Values left_outputs left_values)
      (QExpr_Values right_outputs right_values) ->
    query_bag_source_rename_safe rho left_values ->
    bag_eq T right_values (rename_bag rho left_values) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Values left_outputs left_values)
      (QExpr_Values right_outputs right_values).
```

## `QExpr_Table_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:854`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L854)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Table`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use with an explicitly transported table/database bag; changing only the scan output labels is not a table alpha-renaming.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep actual table-bag safety and exact mapped equality between the two database scans.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem QExpr_Table_rename_transport :
  forall environment_relation rho left_outputs right_outputs
      left_table right_table,
    query_rename_schema_compatible rho
      (QExpr_Table left_outputs left_table)
      (QExpr_Table right_outputs right_table) ->
    query_bag_source_rename_safe rho
      (query_table_bag basesort instance left_outputs left_table) ->
    bag_eq T
      (query_table_bag basesort instance right_outputs right_table)
      (rename_bag rho
        (query_table_bag basesort instance left_outputs left_table)) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Table left_outputs left_table)
      (QExpr_Table right_outputs right_table).
```

## `eval_query_set_binary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1070`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1070)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `set operation`

```rocq
Lemma eval_query_set_binary_lift_iff :
  forall env operation left right outcome,
    eval_query env (QExpr_Set operation left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      (query_set_local operation left right) outcome.
```

## `eval_query_natural_join_binary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1092`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1092)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `join`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `join`

```rocq
Lemma eval_query_natural_join_binary_lift_iff :
  forall env left right outcome,
    eval_query env (QExpr_NaturalJoin left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      query_natural_join_local outcome.
```

## `eval_query_cross_join_binary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1114`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1114)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `join`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `join`, `cross product`, `CROSS JOIN`

```rocq
Lemma eval_query_cross_join_binary_lift_iff :
  forall env left right outcome,
    eval_query env (QExpr_CrossJoin left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      query_cross_join_local outcome.
```

## `eval_query_join_binary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1136`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1136)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use for goals whose exact QueryJoin kind selects the stated collision-safe attribute and query renaming transport branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `renaming`, `join`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`

```rocq
Lemma eval_query_join_binary_lift_iff :
  forall env kind predicate matched_select left_select right_select
      left right outcome,
    eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      (query_join_local env kind predicate
        matched_select left_select right_select) outcome.
```

## `QExpr_Set_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1175`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1175)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Set`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use after transporting both children and certifying schema comparison plus the exact UNION/INTERSECT/EXCEPT bag scheduler on actual rows.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep union-support injection, both child transports, and the binary local compatibility premise for actual representatives.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `set operation`

```rocq
Theorem QExpr_Set_rename_transport :
  forall environment_relation rho operation left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    query_rename_schema_compatible rho
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible environment_relation rho
      (fun _ => query_set_local operation left right)
      (fun _ => query_set_local operation left' right') ->
    query_rename_transport_under environment_relation rho
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
```

## `QExpr_NaturalJoin_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1205`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1205)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_NaturalJoin`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use after transporting both children and proving the exact NULL-aware common-label join behavior, including actual cross-row collisions.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep union-support injection, both child transports, and the NULL-aware binary local compatibility premise.

Cross-index: `renaming`, `join`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `join`

```rocq
Theorem QExpr_NaturalJoin_rename_transport :
  forall environment_relation rho left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    query_rename_schema_compatible rho
      (QExpr_NaturalJoin left right) (QExpr_NaturalJoin left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible environment_relation rho
      (fun _ => query_natural_join_local)
      (fun _ => query_natural_join_local) ->
    query_rename_transport_under environment_relation rho
      (QExpr_NaturalJoin left right) (QExpr_NaturalJoin left' right').
```

## `QExpr_CrossJoin_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1233`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1233)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_CrossJoin`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use with disjoint admissible endpoint schemas and an exact local proof for left-biased tuple construction on all reachable row pairs.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep union-support injection, both endpoint disjointness proofs, both child transports, and binary local compatibility.

Cross-index: `renaming`, `join`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `join`, `cross product`, `CROSS JOIN`

```rocq
Theorem QExpr_CrossJoin_rename_transport :
  forall environment_relation rho left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    @query_output_sorts_disjoint T
      (query_expr_sort left) (query_expr_sort right) ->
    @query_output_sorts_disjoint T
      (query_expr_sort left') (query_expr_sort right') ->
    query_rename_schema_compatible rho
      (QExpr_CrossJoin left right) (QExpr_CrossJoin left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible environment_relation rho
      (fun _ => query_cross_join_local)
      (fun _ => query_cross_join_local) ->
    query_rename_transport_under environment_relation rho
      (QExpr_CrossJoin left right) (QExpr_CrossJoin left' right').
```

## `QExpr_Join_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1264`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1264)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Join`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use only when predicate, all kind-dependent projections/aliases, both children, exact Bool3 outcomes, bags, and errors are transported together.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep union-support injection, both child transports, exact predicate outcomes over joined row environments, and full binary local compatibility.

Cross-index: `renaming`, `join`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`

```rocq
Theorem QExpr_Join_rename_transport :
  forall environment_relation rho kind
      left_predicate right_predicate
      left_matched left_left_select left_right_select
      right_matched right_left_select right_right_select
      left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    query_rename_schema_compatible rho
      (QExpr_Join kind left_predicate
        left_matched left_left_select left_right_select left right)
      (QExpr_Join kind right_predicate
        right_matched right_left_select right_right_select left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_formula_outcome_rename_compatible
      (query_join_environment_rename environment_relation rho)
      left_predicate right_predicate ->
    query_binary_local_rename_compatible environment_relation rho
      (fun env => query_join_local env kind left_predicate
        left_matched left_left_select left_right_select)
      (fun env => query_join_local env kind right_predicate
        right_matched right_left_select right_right_select) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Join kind left_predicate
        left_matched left_left_select left_right_select left right)
      (QExpr_Join kind right_predicate
        right_matched right_left_select right_right_select left' right').
```

## `eval_query_project_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1308`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1308)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `projection`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `projection`, `SELECT list`

```rocq
Lemma eval_query_project_unary_lift_iff :
  forall env select_list input outcome,
    eval_query env (QExpr_Project select_list input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_project_local env select_list) outcome.
```

## `eval_query_row_map_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1324`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1324)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `projection`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `projection`, `SELECT list`

```rocq
Lemma eval_query_row_map_unary_lift_iff :
  forall env outputs row_map input outcome,
    eval_query env (QExpr_RowMap outputs row_map input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_row_map_local row_map rows) outcome.
```

## `eval_query_filter_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1340`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1340)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `filter`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `filter`, `WHERE`

```rocq
Lemma eval_query_filter_unary_lift_iff :
  forall env formula input outcome,
    eval_query env (QExpr_Filter formula input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_filter_local env formula) outcome.
```

## `eval_query_group_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1355`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1355)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `grouping`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `GROUP BY`

```rocq
Lemma eval_query_group_unary_lift_iff :
  forall env select_list group_terms having input outcome,
    eval_query env (QExpr_Group select_list group_terms having input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_group_local env select_list group_terms having) outcome.
```

## `eval_query_grouping_sets_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1378`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1378)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`, `grouping`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `grouping sets`, `GROUP BY`

```rocq
Lemma eval_query_grouping_sets_unary_lift_iff :
  forall env grouping_sets input outcome,
    eval_query env (QExpr_GroupingSets grouping_sets input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_grouping_sets_local env grouping_sets) outcome.
```

## `eval_query_rank_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1401`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1401)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `window`, `PARTITION BY`

```rocq
Lemma eval_query_rank_unary_lift_iff :
  forall env partition_keys order_keys rank_attribute rank_value input outcome,
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_rank_local partition_keys order_keys rank_attribute rank_value)
      outcome.
```

## `eval_query_window_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1430`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1430)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `window`, `PARTITION BY`

```rocq
Lemma eval_query_window_unary_lift_iff :
  forall env partition_keys order_keys items input outcome,
    eval_query env (QExpr_Window partition_keys order_keys items input)
      outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_window_local env partition_keys order_keys items) outcome.
```

## `eval_query_distinct_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1462`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1462)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `DISTINCT`, `duplicate elimination`

```rocq
Lemma eval_query_distinct_unary_lift_iff :
  forall env input outcome,
    eval_query env (QExpr_Distinct input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      query_distinct_local outcome.
```

## `eval_query_order_by_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1479`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1479)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `ORDER BY`, `ordered observation`

```rocq
Lemma eval_query_order_by_unary_lift_iff :
  forall env keys input outcome,
    eval_query env (QExpr_OrderBy keys input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_order_by_local keys rows) outcome.
```

## `eval_query_offset_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1496`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1496)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`

```rocq
Lemma eval_query_offset_unary_lift_iff :
  forall env offset input outcome,
    eval_query env (QExpr_Offset offset input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_offset_local offset rows) outcome.
```

## `eval_query_fetch_unary_lift_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1512`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1512)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`

```rocq
Lemma eval_query_fetch_unary_lift_iff :
  forall env count input outcome,
    eval_query env (QExpr_Fetch count input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_fetch_local count rows) outcome.
```

## `outcome_rename_equiv_deterministic_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1544`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1544)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_rename_equiv_deterministic_transport :
  forall rho left right,
    query_deterministic_outcome_rename_equiv rho left right ->
    query_outcome_rename_transport rho
      (fun outcome => outcome = left)
      (fun outcome => outcome = right).
```

## `row_map_rows_outcome_callback_rename_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1580`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1580)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma row_map_rows_outcome_callback_rename_equiv :
  forall rho left_map right_map,
    query_row_map_callback_rename_compatible rho left_map right_map ->
    forall left_rows right_rows,
      rows_rename_equiv rho left_rows right_rows ->
      outcome_rename_equiv rho
        (row_map_rows_outcome left_map left_rows)
        (row_map_rows_outcome right_map right_rows).
```

## `query_row_map_callback_rename_compatible_scheduler`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1629`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1629)

Purpose/direction: States the query row map callback rename compatible scheduler law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_row_map_callback_rename_compatible_scheduler` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_row_map_callback_rename_compatible_scheduler :
  forall rho left_map right_map,
    query_row_map_callback_rename_compatible rho left_map right_map ->
    query_row_map_success_rename_safe rho left_map ->
    query_row_map_scheduler_rename_compatible rho left_map right_map.
```

## `query_row_map_local_rename_compatible_of_scheduler`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1649`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1649)

Purpose/direction: States the query row map local rename compatible of scheduler law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_row_map_local_rename_compatible_of_scheduler` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_row_map_local_rename_compatible_of_scheduler :
  forall environment_relation rho left_map right_map,
    query_row_map_scheduler_rename_compatible rho left_map right_map ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_row_map_local left_map rows)
      (fun _ rows => query_row_map_local right_map rows).
```

## `query_offset_local_rename_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1663`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1663)

Purpose/direction: States the query offset local rename compatible law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_offset_local_rename_compatible` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`

```rocq
Lemma query_offset_local_rename_compatible :
  forall environment_relation rho offset,
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_offset_local offset rows)
      (fun _ rows => query_offset_local offset rows).
```

## `query_fetch_local_rename_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1676`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1676)

Purpose/direction: States the query fetch local rename compatible law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_fetch_local_rename_compatible` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`

```rocq
Lemma query_fetch_local_rename_compatible :
  forall environment_relation rho count,
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_fetch_local count rows)
      (fun _ rows => query_fetch_local count rows).
```

## `QExpr_Project_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1710`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1710)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Project`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use only with a local proof covering every selected expression, input reference, output alias, projection order, and runtime error.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep child transport and the projection-local compatibility premise; output-only alias mapping does not prove input-expression transport.

Cross-index: `renaming`, `projection`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `projection`, `SELECT list`

```rocq
Theorem QExpr_Project_rename_transport :
  forall environment_relation rho left_select right_select input input',
    query_rename_schema_compatible rho
      (QExpr_Project left_select input)
      (QExpr_Project right_select input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_project_local env left_select)
      (fun env => query_project_local env right_select) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Project left_select input)
      (QExpr_Project right_select input').
```

## `QExpr_RowMap_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1736`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1736)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_RowMap`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use with pointwise callback conjugacy plus cross-output collision/type safety for every successful source callback run.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep child transport, pointwise callback compatibility, and successful-output collision/type safety.

Cross-index: `renaming`, `projection`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `projection`, `SELECT list`

```rocq
Theorem QExpr_RowMap_rename_transport :
  forall environment_relation rho left_outputs right_outputs
      left_map right_map input input',
    query_rename_schema_compatible rho
      (QExpr_RowMap left_outputs left_map input)
      (QExpr_RowMap right_outputs right_map input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_row_map_callback_rename_compatible rho left_map right_map ->
    query_row_map_success_rename_safe rho left_map ->
    query_rename_transport_under environment_relation rho
      (QExpr_RowMap left_outputs left_map input)
      (QExpr_RowMap right_outputs right_map input').
```

## `QExpr_Filter_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1766`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1766)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Filter`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use with exact formula outcomes in renamed row environments and the exact ordered filter scheduler; FALSE and UNKNOWN may not be exchanged.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep child transport, exact Bool3/error formula compatibility, and ordered unary local compatibility.

Cross-index: `renaming`, `filter`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `filter`, `WHERE`

```rocq
Theorem QExpr_Filter_rename_transport :
  forall environment_relation rho left_formula right_formula input input',
    query_rename_schema_compatible rho
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_formula_outcome_rename_compatible
      (query_row_environment_rename environment_relation rho)
      left_formula right_formula ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_filter_local env left_formula)
      (fun env => query_filter_local env right_formula) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input').
```

## `QExpr_Group_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1794`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1794)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Group`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use with paired reachable group formation, exact HAVING Bool3/aggregate-error behavior, renamed keys/projection aliases, and the exact bag scheduler.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep child transport, reachable group-formation pairing, exact HAVING plus aggregate-precheck compatibility, and unary local compatibility.

Cross-index: `renaming`, `grouping`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `GROUP BY`

```rocq
Theorem QExpr_Group_rename_transport :
  forall environment_relation rho
      left_select right_select left_terms right_terms
      left_having right_having input input',
    query_rename_schema_compatible rho
      (QExpr_Group left_select left_terms left_having input)
      (QExpr_Group right_select right_terms right_having input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_group_formation_rename_compatible
      environment_relation rho left_terms right_terms ->
    query_group_formula_outcome_rename_compatible
      (query_group_environment_rename
        environment_relation rho left_terms right_terms)
      left_having right_having ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_group_local env left_select left_terms left_having)
      (fun env => query_group_local env right_select right_terms right_having) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Group left_select left_terms left_having input)
      (QExpr_Group right_select right_terms right_having input').
```

## `QExpr_GroupingSets_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1829`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1829)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_GroupingSets`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use only after pairing every grouping-set branch, its projection/group metadata, output schema, bag results, and runtime errors.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep child transport and one exact unary local compatibility proof covering every grouping-set branch.

Cross-index: `renaming`, `grouping`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `grouping sets`, `GROUP BY`

```rocq
Theorem QExpr_GroupingSets_rename_transport :
  forall environment_relation rho left_sets right_sets input input',
    query_rename_schema_compatible rho
      (QExpr_GroupingSets left_sets input)
      (QExpr_GroupingSets right_sets input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_grouping_sets_local env left_sets)
      (fun env => query_grouping_sets_local env right_sets) ->
    query_rename_transport_under environment_relation rho
      (QExpr_GroupingSets left_sets input)
      (QExpr_GroupingSets right_sets input').
```

## `QExpr_Rank_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1855`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1855)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Rank`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use when partition/order keys and the fresh rank output alias are renamed together and the rank callback/error scheduler is preserved.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep both key-list relations, mapped fresh output alias, child transport, and exact rank-local compatibility.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `window`, `PARTITION BY`

```rocq
Theorem QExpr_Rank_rename_transport :
  forall environment_relation rho
      left_partition right_partition left_order right_order
      left_rank right_rank left_value right_value input input',
    query_sort_keys_rename_compatible rho left_partition right_partition ->
    query_sort_keys_rename_compatible rho left_order right_order ->
    right_rank = rho left_rank ->
    attribute_rename_fresh_for (query_expr_sort input) rho left_rank ->
    query_rename_schema_compatible rho
      (QExpr_Rank left_partition left_order left_rank left_value input)
      (QExpr_Rank right_partition right_order right_rank right_value input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ => query_rank_local
        left_partition left_order left_rank left_value)
      (fun _ => query_rank_local
        right_partition right_order right_rank right_value) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Rank left_partition left_order left_rank left_value input)
      (QExpr_Rank right_partition right_order right_rank right_value input').
```

## `QExpr_Window_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1892`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1892)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Window`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use when partition/order keys, every window item and alias, ordered peer behavior, aggregate outcomes, and errors are transported together.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep both key-list relations, mapped item aliases, child transport, and exact window-local compatibility.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `window`, `PARTITION BY`

```rocq
Theorem QExpr_Window_rename_transport :
  forall environment_relation rho
      left_partition right_partition left_order right_order
      left_items right_items input input',
    query_sort_keys_rename_compatible rho left_partition right_partition ->
    query_sort_keys_rename_compatible rho left_order right_order ->
    map rho (map (@qwi_attribute T) left_items) =
      map (@qwi_attribute T) right_items ->
    query_rename_schema_compatible rho
      (QExpr_Window left_partition left_order left_items input)
      (QExpr_Window right_partition right_order right_items input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_window_local env
        left_partition left_order left_items)
      (fun env => query_window_local env
        right_partition right_order right_items) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Window left_partition left_order left_items input)
      (QExpr_Window right_partition right_order right_items input').
```

## `QExpr_Distinct_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1929`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1929)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Distinct`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use only under collision-reflecting child transport and the exact finite-bag duplicate-elimination compatibility premise.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep source-sort injection, child transport, and exact duplicate-elimination local compatibility.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `DISTINCT`, `duplicate elimination`

```rocq
Theorem QExpr_Distinct_rename_transport :
  forall environment_relation rho input input',
    attribute_rename_injective_on (query_expr_sort input) rho ->
    query_rename_schema_compatible rho
      (QExpr_Distinct input) (QExpr_Distinct input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ => query_distinct_local)
      (fun _ => query_distinct_local) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Distinct input) (QExpr_Distinct input').
```

## `QExpr_OrderBy_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1953`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1953)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_OrderBy`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use when each sort-key attribute, direction, NULL placement, comparator, nondeterministic tie order, and exact output order are preserved.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep the complete sort-key relation, child transport, and exact order-producing local compatibility.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `ORDER BY`, `ordered observation`

```rocq
Theorem QExpr_OrderBy_rename_transport :
  forall environment_relation rho left_keys right_keys input input',
    query_sort_keys_rename_compatible rho left_keys right_keys ->
    query_rename_schema_compatible rho
      (QExpr_OrderBy left_keys input) (QExpr_OrderBy right_keys input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_order_by_local left_keys rows)
      (fun _ rows => query_order_by_local right_keys rows) ->
    query_rename_transport_under environment_relation rho
      (QExpr_OrderBy left_keys input) (QExpr_OrderBy right_keys input').
```

## `QExpr_Offset_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1977`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1977)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Offset`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use after transporting the child and mapped endpoint schema; the proved `skipn` law preserves exact positions and multiplicity.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep the child transport; the constructor-local `skipn` compatibility is proved by the library.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`

```rocq
Theorem QExpr_Offset_rename_transport :
  forall environment_relation rho offset input input',
    query_rename_schema_compatible rho
      (QExpr_Offset offset input) (QExpr_Offset offset input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_rename_transport_under environment_relation rho
      (QExpr_Offset offset input) (QExpr_Offset offset input').
```

## `QExpr_Fetch_rename_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:1998`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L1998)

Purpose/direction: Provides the constructor-local renaming transport theorem for `QExpr_Fetch`, preserving mapped schemas and exact successful/error observations under every displayed semantic side condition.

Applicability: Use after transporting the child and mapped endpoint schema; the proved `firstn` law preserves exact positions and multiplicity.

Important premises: The displayed `query_rename_schema_compatible` premise retains ordered mapped outputs, collision/type safety, and admissibility of both endpoints.  Keep the child transport; the constructor-local `firstn` compatibility is proved by the library.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`

```rocq
Theorem QExpr_Fetch_rename_transport :
  forall environment_relation rho count input input',
    query_rename_schema_compatible rho
      (QExpr_Fetch count input) (QExpr_Fetch count input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_rename_transport_under environment_relation rho
      (QExpr_Fetch count input) (QExpr_Fetch count input').
```

## `row_map_rows_output_rename`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2029`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2029)

Purpose/direction: Characterizes the output-boundary RowMap adapter that relabels only successful result tuples and preserves child errors; it is not a full query alpha-renaming theorem.

Applicability: Use only at an output observation boundary.  It does not rename predicates, projection inputs, group/join/sort/window metadata, aliases inside nested operators, or correlated subqueries, so do not cite it as full alpha-renaming.

Important premises: The adapter uses the existing `QExpr_RowMap` and maps successful rows only; retain the exact child evaluation and error category.  No conclusion about attribute-bearing metadata inside the child query follows.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma row_map_rows_output_rename :
  forall rho rows,
    row_map_rows_outcome
      (fun row => SqlSuccess (rename_tuple T rho row)) rows =
    SqlSuccess (rename_rows rho rows).
```

## `query_output_rename_adapter_outputs`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2038`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2038)

Purpose/direction: Characterizes the output-boundary RowMap adapter that relabels only successful result tuples and preserves child errors; it is not a full query alpha-renaming theorem.

Applicability: Use only at an output observation boundary.  It does not rename predicates, projection inputs, group/join/sort/window metadata, aliases inside nested operators, or correlated subqueries, so do not cite it as full alpha-renaming.

Important premises: The adapter uses the existing `QExpr_RowMap` and maps successful rows only; retain the exact child evaluation and error category.  No conclusion about attribute-bearing metadata inside the child query follows.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_output_rename_adapter_outputs :
  forall rho query,
    query_expr_outputs (query_output_rename_adapter rho query) =
    map rho (query_expr_outputs query).
```

## `eval_query_output_rename_adapter_success_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2046`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2046)

Purpose/direction: Characterizes the output-boundary RowMap adapter that relabels only successful result tuples and preserves child errors; it is not a full query alpha-renaming theorem.

Applicability: Use only at an output observation boundary.  It does not rename predicates, projection inputs, group/join/sort/window metadata, aliases inside nested operators, or correlated subqueries, so do not cite it as full alpha-renaming.

Important premises: The adapter uses the existing `QExpr_RowMap` and maps successful rows only; retain the exact child evaluation and error category.  No conclusion about attribute-bearing metadata inside the child query follows.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma eval_query_output_rename_adapter_success_iff :
  forall env rho query output,
    eval_query env (query_output_rename_adapter rho query)
      (SqlSuccess output) <->
    exists input,
      eval_query env query (SqlSuccess input) /\
      output = rename_rows rho input.
```

## `eval_query_output_rename_adapter_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2068`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2068)

Purpose/direction: Characterizes the output-boundary RowMap adapter that relabels only successful result tuples and preserves child errors; it is not a full query alpha-renaming theorem.

Applicability: Use only at an output observation boundary.  It does not rename predicates, projection inputs, group/join/sort/window metadata, aliases inside nested operators, or correlated subqueries, so do not cite it as full alpha-renaming.

Important premises: The adapter uses the existing `QExpr_RowMap` and maps successful rows only; retain the exact child evaluation and error category.  No conclusion about attribute-bearing metadata inside the child query follows.

Cross-index: `renaming`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_output_rename_adapter_error_iff :
  forall env rho query error,
    eval_query env (query_output_rename_adapter rho query)
      (SqlError error) <->
    eval_query env query (SqlError error).
```

## `query_mapped_schema_outcome_equiv_mapped_schema`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2098`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2098)

Purpose/direction: Connects constructor-certified transport to exact mapped-schema observations; this relation alone does not certify renamed operator metadata.

Applicability: Use to package or project exact outcomes under a mapped ordered schema after constructor-local transport has been proved.  Output-only relabeling can also satisfy this observation, so it is not ordinary equivalence or full alpha-renaming.

Important premises: Retain the full mapped-schema and exact success/error relation displayed.  For alpha-renaming, separately derive it from the relevant `QExpr_*_rename_transport` theorems and their metadata, collision, typing, and admissibility premises.

Cross-index: `renaming`, `outcome`, `runtime`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_mapped_schema_outcome_equiv_mapped_schema :
  forall left_env right_env rho left right,
    query_mapped_schema_outcome_equiv
      left_env right_env rho left right ->
    map rho (query_expr_outputs left) = query_expr_outputs right.
```

## `query_rename_transport_under_implies_mapped_schema_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2109`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2109)

Purpose/direction: Connects constructor-certified transport to exact mapped-schema observations; this relation alone does not certify renamed operator metadata.

Applicability: Use to package or project exact outcomes under a mapped ordered schema after constructor-local transport has been proved.  Output-only relabeling can also satisfy this observation, so it is not ordinary equivalence or full alpha-renaming.

Important premises: Retain the full mapped-schema and exact success/error relation displayed.  For alpha-renaming, separately derive it from the relevant `QExpr_*_rename_transport` theorems and their metadata, collision, typing, and admissibility premises.

Cross-index: `renaming`, `outcome`, `runtime`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Theorem query_rename_transport_under_implies_mapped_schema_outcome_equiv :
  forall environment_relation left_env right_env rho left right,
    environment_relation left_env right_env ->
    query_rename_transport_under environment_relation rho left right ->
    (exists outcome, eval_query left_env left outcome) ->
    (exists outcome, eval_query right_env right outcome) ->
    query_mapped_schema_outcome_equiv
      left_env right_env rho left right.
```

## `query_rename_hole_context_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2146`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2146)

Purpose/direction: States the query rename hole context compatible law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_rename_hole_context_compatible` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma query_rename_hole_context_compatible :
  forall environment_relation rho,
    query_rename_context_compatible environment_relation rho
      (@QCtx_Hole T relname) (@QCtx_Hole T relname).
```

## `query_rename_context_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2154`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2154)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `query_rename_context_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Theorem query_rename_context_transport :
  forall environment_relation rho left_context right_context left right,
    query_rename_context_compatible environment_relation rho
      left_context right_context ->
    query_rename_transport_under environment_relation rho left right ->
    query_rename_transport_under environment_relation rho
      (plug_query_expr_context left_context left)
      (plug_query_expr_context right_context right).
```

## `query_rename_context_chain_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v:2179`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v#L2179)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `query_rename_context_chain_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Theorem query_rename_context_chain_transport :
  forall environment_relation rho left_contexts right_contexts,
    Forall2
      (query_rename_context_compatible environment_relation rho)
      left_contexts right_contexts ->
    forall left right,
      query_rename_transport_under environment_relation rho left right ->
      query_rename_transport_under environment_relation rho
        (plug_query_rename_contexts left_contexts left)
        (plug_query_rename_contexts right_contexts right).
```

## `attribute_rename_injective_on_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:78`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L78)

Purpose/direction: Recovers source equality from the declared collision-safe attribute and query renaming transport representation.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_injective_on_identity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_injective_on_identity :
  forall support,
    attribute_rename_injective_on support (fun attribute => attribute).
```

## `attribute_rename_type_preserving_on_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:85`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L85)

Purpose/direction: States the attribute rename type preserving on identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_type_preserving_on_identity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_type_preserving_on_identity :
  forall support,
    attribute_rename_type_preserving_on support (fun attribute => attribute).
```

## `attribute_rename_map_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:92`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L92)

Purpose/direction: States the attribute rename map identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_map_identity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_map_identity :
  forall support,
    Fset.map (A T) (A T) (fun attribute => attribute) support =S= support.
```

## `attribute_rename_map_compose`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:106`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L106)

Purpose/direction: States the attribute rename map compose law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_map_compose` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_map_compose :
  forall rho sigma support,
    Fset.map (A T) (A T) sigma
      (Fset.map (A T) (A T) rho support) =S=
    Fset.map (A T) (A T) (fun attribute => sigma (rho attribute)) support.
```

## `attribute_rename_injective_on_compose`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:129`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L129)

Purpose/direction: Recovers source equality from the declared collision-safe attribute and query renaming transport representation.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_injective_on_compose` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_injective_on_compose :
  forall rho sigma support,
    attribute_rename_injective_on support rho ->
    attribute_rename_injective_on
      (Fset.map (A T) (A T) rho support) sigma ->
    attribute_rename_injective_on support
      (fun attribute => sigma (rho attribute)).
```

## `attribute_rename_type_preserving_on_compose`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:145`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L145)

Purpose/direction: States the attribute rename type preserving on compose law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_type_preserving_on_compose` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_type_preserving_on_compose :
  forall rho sigma support,
    attribute_rename_type_preserving_on support rho ->
    attribute_rename_type_preserving_on
      (Fset.map (A T) (A T) rho support) sigma ->
    attribute_rename_type_preserving_on support
      (fun attribute => sigma (rho attribute)).
```

## `attribute_rename_collision_free_between_of_union`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:160`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L160)

Purpose/direction: States the attribute rename collision free between of union law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_collision_free_between_of_union` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_collision_free_between_of_union :
  forall left right rho,
    attribute_rename_injective_on (left unionS right) rho ->
    attribute_rename_collision_free_between left right rho.
```

## `attribute_rename_fresh_for_of_union_injective`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:173`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L173)

Purpose/direction: Recovers source equality from the declared collision-safe attribute and query renaming transport representation.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_fresh_for_of_union_injective` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_fresh_for_of_union_injective :
  forall support rho fresh,
    ~ fresh inS support ->
    attribute_rename_injective_on
      (support unionS Fset.singleton (A T) fresh) rho ->
    attribute_rename_fresh_for support rho fresh.
```

## `attribute_rename_collision_rejects_injectivity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:199`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L199)

Purpose/direction: States the attribute rename collision rejects injectivity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `attribute_rename_collision_rejects_injectivity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma attribute_rename_collision_rejects_injectivity :
  forall support rho left right,
    left inS support ->
    right inS support ->
    left <> right ->
    rho left = rho right ->
    ~ attribute_rename_injective_on support rho.
```

## `rename_tuple_labels_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:220`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L220)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_labels_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_labels_transport :
  forall rho row,
    labels T (rename_tuple T rho row) =S=
    Fset.map (A T) (A T) rho (labels T row).
```

## `rename_tuple_lookup_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:228`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L228)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_lookup_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_lookup_transport :
  forall rho row,
    attribute_rename_injective_on (labels T row) rho ->
    forall source,
      source inS labels T row ->
      dot T (rename_tuple T rho row) (rho source) = dot T row source.
```

## `rename_tuple_value_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:239`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L239)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_value_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_value_transport :
  forall rho row source,
    attribute_rename_injective_on (labels T row) rho ->
    source inS labels T row ->
    dot T (rename_tuple T rho row) (rho source) = dot T row source.
```

## `rename_tuple_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:248`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L248)

Purpose/direction: States the rename tuple identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_identity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_identity :
  forall row,
    rename_tuple T (fun attribute => attribute) row =t= row.
```

## `rename_tuple_composition`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:272`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L272)

Purpose/direction: States the rename tuple composition law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_composition` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_composition :
  forall rho sigma row,
    attribute_rename_injective_on (labels T row) rho ->
    attribute_rename_injective_on
      (Fset.map (A T) (A T) rho (labels T row)) sigma ->
    rename_tuple T sigma (rename_tuple T rho row) =t=
    rename_tuple T (fun attribute => sigma (rho attribute)) row.
```

## `rename_tuple_equivalence_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:346`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L346)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_equivalence_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_equivalence_transport :
  forall rho left right,
    left =t= right ->
    rename_tuple T rho left =t= rename_tuple T rho right.
```

## `rename_tuple_equivalence_reflection`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:354`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L354)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_equivalence_reflection` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_equivalence_reflection :
  forall rho left right,
    attribute_rename_collision_free_between
      (labels T left) (labels T right) rho ->
    rename_tuple T rho left =t= rename_tuple T rho right ->
    left =t= right.
```

## `rename_tuple_equivalence_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:365`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L365)

Purpose/direction: Gives necessary and sufficient conditions for collision-safe attribute and query renaming transport.

Applicability: Use in either direction to invert or construct a goal about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_tuple_equivalence_iff :
  forall rho left right,
    attribute_rename_collision_free_between
      (labels T left) (labels T right) rho ->
    (left =t= right <->
     rename_tuple T rho left =t= rename_tuple T rho right).
```

## `rename_tuple_well_typed_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:376`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L376)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `rename_tuple_well_typed_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma rename_tuple_well_typed_transport :
  forall rho row,
    attribute_rename_injective_on (labels T row) rho ->
    attribute_rename_type_preserving_on (labels T row) rho ->
    tuple_well_typed row ->
    tuple_well_typed (rename_tuple T rho row).
```

## `rows_rename_equiv_canonical`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:442`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L442)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `equivalence`, `congruence`

```rocq
Lemma rows_rename_equiv_canonical :
  forall rho rows,
    rows_rename_equiv rho rows (rename_rows rho rows).
```

## `rows_rename_equiv_of_canonical_ordered`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:451`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L451)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `equivalence`, `congruence`

```rocq
Lemma rows_rename_equiv_of_canonical_ordered :
  forall rho left right,
    ordered_rows_equiv T (rename_rows rho left) right ->
    rows_rename_equiv rho left right.
```

## `rows_rename_sound_canonical`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:467`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L467)

Purpose/direction: States the rows rename sound canonical law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rows_rename_sound_canonical` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rows_rename_sound_canonical :
  forall rho rows,
    rows_rename_collision_safe rho rows ->
    rows_rename_type_safe rho rows ->
    rows_rename_sound rho rows (rename_rows rho rows).
```

## `rename_rows_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:478`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L478)

Purpose/direction: States the rename rows identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rename_rows_identity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_rows_identity :
  forall rows,
    rows_rename_equiv (fun attribute => attribute) rows rows.
```

## `rows_rename_collision_safe_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:487`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L487)

Purpose/direction: States the rows rename collision safe identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rows_rename_collision_safe_identity :
  forall rows,
    rows_rename_collision_safe
      (fun attribute => attribute) rows.
```

## `rows_rename_type_safe_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:496`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L496)

Purpose/direction: States the rows rename type safe identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rows_rename_type_safe_identity :
  forall rows,
    rows_rename_type_safe (fun attribute => attribute) rows.
```

## `rows_rename_sound_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:503`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L503)

Purpose/direction: States the rows rename sound identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rows_rename_sound_identity` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rows_rename_sound_identity :
  forall rows,
    rows_rename_sound (fun attribute => attribute) rows rows.
```

## `rename_rows_composition`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:514`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L514)

Purpose/direction: States the rename rows composition law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rename_rows_composition` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_rows_composition :
  forall rho sigma rows,
    (forall row,
      In row rows ->
      attribute_rename_injective_on (labels T row) rho) ->
    (forall row,
      In row rows ->
      attribute_rename_injective_on
        (Fset.map (A T) (A T) rho (labels T row)) sigma) ->
    rows_rename_equiv sigma (rename_rows rho rows)
      (rename_rows (fun attribute => sigma (rho attribute)) rows).
```

## `rename_rows_length`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:538`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L538)

Purpose/direction: Relates collision-safe attribute and query renaming transport to the exact list length or bag cardinality shown below.

Applicability: Use when the goal or a hypothesis matches the `rename_rows_length` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rename_rows_length :
  forall rho rows,
    length (rename_rows rho rows) = length rows.
```

## `rows_rename_equiv_length`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:545`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L545)

Purpose/direction: Relates collision-safe attribute and query renaming transport to the exact list length or bag cardinality shown below.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `equivalence`, `congruence`

```rocq
Lemma rows_rename_equiv_length :
  forall rho left right,
    rows_rename_equiv rho left right ->
    length left = length right.
```

## `rename_rows_firstn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:553`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L553)

Purpose/direction: States the rename rows firstn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rename_rows_firstn` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`

```rocq
Lemma rename_rows_firstn :
  forall rho count rows,
    rename_rows rho (firstn count rows) =
    firstn count (rename_rows rho rows).
```

## `rename_rows_skipn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:563`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L563)

Purpose/direction: States the rename rows skipn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rename_rows_skipn` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`

```rocq
Lemma rename_rows_skipn :
  forall rho count rows,
    rename_rows rho (skipn count rows) =
    skipn count (rename_rows rho rows).
```

## `rows_rename_equiv_firstn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:573`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L573)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`, `equivalence`, `congruence`

```rocq
Lemma rows_rename_equiv_firstn :
  forall rho count left right,
    rows_rename_equiv rho left right ->
    rows_rename_equiv rho (firstn count left) (firstn count right).
```

## `rows_rename_equiv_skipn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:587`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L587)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`, `equivalence`, `congruence`

```rocq
Lemma rows_rename_equiv_skipn :
  forall rho count left right,
    rows_rename_equiv rho left right ->
    rows_rename_equiv rho (skipn count left) (skipn count right).
```

## `rows_rename_collision_safe_firstn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:601`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L601)

Purpose/direction: States the rows rename collision safe firstn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `runtime`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rows_rename_collision_safe_firstn :
  forall rho count rows,
    rows_rename_collision_safe rho rows ->
    rows_rename_collision_safe rho (firstn count rows).
```

## `rows_rename_collision_safe_skipn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:616`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L616)

Purpose/direction: States the rows rename collision safe skipn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `runtime`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rows_rename_collision_safe_skipn :
  forall rho count rows,
    rows_rename_collision_safe rho rows ->
    rows_rename_collision_safe rho (skipn count rows).
```

## `rows_rename_type_safe_firstn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:631`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L631)

Purpose/direction: States the rows rename type safe firstn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `runtime`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rows_rename_type_safe_firstn :
  forall rho count rows,
    rows_rename_type_safe rho rows ->
    rows_rename_type_safe rho (firstn count rows).
```

## `rows_rename_type_safe_skipn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:643`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L643)

Purpose/direction: States the rows rename type safe skipn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `runtime`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rows_rename_type_safe_skipn :
  forall rho count rows,
    rows_rename_type_safe rho rows ->
    rows_rename_type_safe rho (skipn count rows).
```

## `rows_rename_sound_firstn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:655`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L655)

Purpose/direction: States the rows rename sound firstn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rows_rename_sound_firstn` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `FETCH`, `LIMIT`

```rocq
Lemma rows_rename_sound_firstn :
  forall rho count left right,
    rows_rename_sound rho left right ->
    rows_rename_sound rho (firstn count left) (firstn count right).
```

## `rows_rename_sound_skipn`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:667`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L667)

Purpose/direction: States the rows rename sound skipn law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rows_rename_sound_skipn` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: `renaming`, `ordered`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `OFFSET`

```rocq
Lemma rows_rename_sound_skipn :
  forall rho count left right,
    rows_rename_sound rho left right ->
    rows_rename_sound rho (skipn count left) (skipn count right).
```

## `rows_rename_sound_reflects_equivalence`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:679`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L679)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use when the goal or a hypothesis matches the `rows_rename_sound_reflects_equivalence` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`

```rocq
Lemma rows_rename_sound_reflects_equivalence :
  forall rho left_rows right_rows left right,
    rows_rename_sound rho left_rows right_rows ->
    Oeset.mem_bool (OTuple T) left left_rows = true ->
    Oeset.mem_bool (OTuple T) right left_rows = true ->
    rename_tuple T rho left =t= rename_tuple T rho right ->
    left =t= right.
```

## `rename_rows_permutation_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:694`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L694)

Purpose/direction: Shows that the declared collision-safe attribute and query renaming transport result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rename_rows_permutation_transport :
  forall rho left right,
    Permutation left right ->
    Permutation (rename_rows rho left) (rename_rows rho right).
```

## `rename_rows_ordered_equiv_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:703`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L703)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `renaming`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `equivalence`, `congruence`

```rocq
Lemma rename_rows_ordered_equiv_transport :
  forall rho left right,
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (rename_rows rho left) (rename_rows rho right).
```

## `rename_rows_multiplicity_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:727`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L727)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`

```rocq
Lemma rename_rows_multiplicity_transport :
  forall rho row rows,
    (forall candidate,
      Oeset.mem_bool (OTuple T) candidate rows = true ->
      attribute_rename_collision_free_between
        (labels T row) (labels T candidate) rho) ->
    Oeset.nb_occ (OTuple T) (rename_tuple T rho row)
      (rename_rows rho rows) =
    Oeset.nb_occ (OTuple T) row rows.
```

## `rows_rename_sound_multiplicity_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:746`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L746)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`

```rocq
Lemma rows_rename_sound_multiplicity_transport :
  forall rho row rows,
    rows_rename_collision_safe rho rows ->
    Oeset.mem_bool (OTuple T) row rows = true ->
    Oeset.nb_occ (OTuple T) (rename_tuple T rho row)
      (rename_rows rho rows) =
    Oeset.nb_occ (OTuple T) row rows.
```

## `rename_bag_multiplicity_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:760`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L760)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `renaming`, `bag`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rename_bag_multiplicity_transport :
  forall rho row bag,
    (forall candidate,
      candidate inBE bag ->
      attribute_rename_collision_free_between
        (labels T row) (labels T candidate) rho) ->
    Febag.nb_occ BTupleT (rename_tuple T rho row) (rename_bag rho bag) =
    Febag.nb_occ BTupleT row bag.
```

## `rename_rows_well_typed_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:782`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L782)

Purpose/direction: Transports the displayed hypotheses and conclusion for collision-safe attribute and query renaming transport.

Applicability: Use when the goal or a hypothesis matches the `rename_rows_well_typed_transport` direction for collision-safe attribute and query renaming transport; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `renaming`, `schema`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `schema conformance`, `typing`

```rocq
Lemma rename_rows_well_typed_transport :
  forall rho rows,
    Forall tuple_well_typed rows ->
    (forall row,
      In row rows ->
      attribute_rename_injective_on (labels T row) rho) ->
    (forall row,
      In row rows ->
      attribute_rename_type_preserving_on (labels T row) rho) ->
    Forall tuple_well_typed (rename_rows rho rows).
```

## `rename_query_outcome_success`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:826`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L826)

Purpose/direction: Inverts or constructs the successful evaluation branch for collision-safe attribute and query renaming transport.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rename_query_outcome_success :
  forall rho rows,
    rename_query_outcome rho (SqlSuccess rows) =
    SqlSuccess (rename_rows rho rows).
```

## `rename_query_outcome_error`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:834`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L834)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for collision-safe attribute and query renaming transport.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rename_query_outcome_error :
  forall rho error,
    rename_query_outcome rho (SqlError error) = SqlError error.
```

## `outcome_rename_equiv_success`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:841`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L841)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_rename_equiv_success :
  forall rho left right,
    outcome_rename_equiv rho (SqlSuccess left) (SqlSuccess right) <->
    rows_rename_equiv rho left right.
```

## `outcome_rename_equiv_error`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:849`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L849)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_rename_equiv_error :
  forall rho left_error right_error,
    outcome_rename_equiv rho (SqlError left_error) (SqlError right_error) <->
    left_error = right_error.
```

## `outcome_rename_equiv_canonical`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:857`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L857)

Purpose/direction: Transports or composes collision-safe attribute and query renaming transport across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma outcome_rename_equiv_canonical :
  forall rho outcome,
    outcome_rename_equiv rho outcome (rename_query_outcome rho outcome).
```

## `rename_query_outcome_identity`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:866`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L866)

Purpose/direction: States the rename query outcome identity law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rename_query_outcome_identity :
  forall outcome,
    outcome_rename_equiv (fun attribute => attribute) outcome outcome.
```

## `rename_query_outcome_composition`

Source: [`vendor/FormalSQL/src/data/sql/SqlRenameFacts.v:875`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v#L875)

Purpose/direction: States the rename query outcome composition law for collision-safe attribute and query renaming transport, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for collision-safe attribute and query renaming transport.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `renaming`, `outcome`, `runtime`

Search aliases: `renaming transport and alpha-renaming`, `rename`, `renaming`, `alias`, `alpha-renaming`, `transport`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma rename_query_outcome_composition :
  forall rho sigma outcome,
    (forall row,
      match outcome with
      | SqlSuccess rows => In row rows
      | SqlError _ => False
      end ->
      attribute_rename_injective_on (labels T row) rho) ->
    (forall row,
      match outcome with
      | SqlSuccess rows => In row rows
      | SqlError _ => False
      end ->
      attribute_rename_injective_on
        (Fset.map (A T) (A T) rho (labels T row)) sigma) ->
    outcome_rename_equiv sigma (rename_query_outcome rho outcome)
      (rename_query_outcome
        (fun attribute => sigma (rho attribute)) outcome).
```
