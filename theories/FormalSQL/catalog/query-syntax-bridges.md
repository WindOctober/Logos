# Query syntax and projection bridges

Route here for: query-level nullable syntax adapters, query-local bindings, tuple projection, attribute lookup.

This focused catalog contains 73 declarations routed at declaration granularity from `QueryBindingSemantics.v`, `QueryTNullSyntax.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `query_local_references_allowed_available_monotone`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:80`](../QueryBindingSemantics.v#L80)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query local references allowed available monotone law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_local_references_allowed_available_monotone` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma query_local_references_allowed_available_monotone :
  forall schemas all_local before after query,
    (forall relation, In relation before -> In relation after) ->
    query_local_references_allowed schemas all_local before query ->
    query_local_references_allowed schemas all_local after query.
```

## `local_query_binding_dependencies_available_monotone`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:111`](../QueryBindingSemantics.v#L111)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the local query binding dependencies available monotone law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `local_query_binding_dependencies_available_monotone` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma local_query_binding_dependencies_available_monotone :
  forall schemas all_local before after bindings,
    (forall relation, In relation before -> In relation after) ->
    local_query_binding_dependencies_well_formed
      schemas all_local before bindings ->
    local_query_binding_dependencies_well_formed
      schemas all_local after bindings.
```

## `declare_local_query_schemas_instance_preserving`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:159`](../QueryBindingSemantics.v#L159)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the declare local query schemas instance preserving law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `declare_local_query_schemas_instance_preserving` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma declare_local_query_schemas_instance_preserving :
  forall db schemas,
    @_instance TNull (declare_local_query_schemas db schemas) =
    @_instance TNull db.
```

## `declare_local_query_schemas_basesort_absent`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:173`](../QueryBindingSemantics.v#L173)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the declare local query schemas basesort absent law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `declare_local_query_schemas_basesort_absent` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma declare_local_query_schemas_basesort_absent :
  forall db schemas relation,
    ~ In relation (local_query_schema_relations schemas) ->
    @_basesort TNull (declare_local_query_schemas db schemas) relation =
    @_basesort TNull db relation.
```

## `set_local_query_binding_rows_relnames_preserving`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:207`](../QueryBindingSemantics.v#L207)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the set local query binding rows relnames preserving law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `set_local_query_binding_rows_relnames_preserving` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma set_local_query_binding_rows_relnames_preserving :
  forall db binding rows,
    @_relnames TNull (set_local_query_binding_rows db binding rows) =
    @_relnames TNull db.
```

## `set_local_query_binding_rows_basesort_preserving`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:215`](../QueryBindingSemantics.v#L215)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the set local query binding rows basesort preserving law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `set_local_query_binding_rows_basesort_preserving` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma set_local_query_binding_rows_basesort_preserving :
  forall db binding rows relation,
    @_basesort TNull (set_local_query_binding_rows db binding rows) relation =
    @_basesort TNull db relation.
```

## `set_local_query_binding_rows_instance_eq`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:225`](../QueryBindingSemantics.v#L225)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the set local query binding rows instance equality law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `set_local_query_binding_rows_instance_eq` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma set_local_query_binding_rows_instance_eq :
  forall db binding rows,
    @_instance TNull (set_local_query_binding_rows db binding rows)
      (local_binding_relation binding) =
    @query_rows_bag TNull rows.
```

## `set_local_query_binding_rows_instance_neq`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:237`](../QueryBindingSemantics.v#L237)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the set local query binding rows instance disequality law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `set_local_query_binding_rows_instance_neq` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma set_local_query_binding_rows_instance_neq :
  forall db binding rows relation,
    relation <> local_binding_relation binding ->
    @_instance TNull (set_local_query_binding_rows db binding rows) relation =
    @_instance TNull db relation.
```

## `set_local_query_binding_rows_table_bag`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:291`](../QueryBindingSemantics.v#L291)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the set local query binding rows table bag law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma set_local_query_binding_rows_table_bag :
  forall db binding rows,
    local_query_binding_reference_well_typed db binding ->
    @query_table_bag TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      (local_binding_outputs binding)
      (local_binding_relation binding) =
    @query_rows_bag TNull rows.
```

## `eval_local_query_binding_reference_values_iff`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:311`](../QueryBindingSemantics.v#L311)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for projection and tuple-syntax bridging.

Applicability: Use in either direction to invert or construct a goal about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma eval_local_query_binding_reference_values_iff :
  forall db binding rows schedule env outcome,
    local_query_binding_reference_well_typed db binding ->
    eval_query_expr_with_schedule
      (set_local_query_binding_rows db binding rows) schedule env
      (local_query_binding_reference binding) outcome <->
    eval_query_expr_with_schedule
      (set_local_query_binding_rows db binding rows) schedule env
      (local_query_binding_values binding rows) outcome.
```

## `eval_local_query_binding_reference_values_exists_iff`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:334`](../QueryBindingSemantics.v#L334)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for projection and tuple-syntax bridging.

Applicability: Use in either direction to invert or construct a goal about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma eval_local_query_binding_reference_values_exists_iff :
  forall db binding rows schedule env outcome,
    local_query_binding_reference_well_typed db binding ->
    @eval_query_exists_outcome TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule env (local_query_binding_reference binding) outcome <->
    @eval_query_exists_outcome TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule env (local_query_binding_values binding rows) outcome.
```

## `local_query_binding_reference_values_global_demand_equiv`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:366`](../QueryBindingSemantics.v#L366)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes projection and tuple-syntax bridging across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NULL`, `UNKNOWN`, `three-valued logic`, `equivalence`, `congruence`

```rocq
Lemma local_query_binding_reference_values_global_demand_equiv :
  forall db binding rows schedule demand,
    local_query_binding_reference_well_typed db binding ->
    @query_expr_global_demand_equiv TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule demand
      (local_query_binding_reference binding)
      (local_query_binding_values binding rows).
```

## `local_query_binding_reference_context_substitution`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:391`](../QueryBindingSemantics.v#L391)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the local query binding reference context substitution law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `query syntax bridge`, `NULL`, `UNKNOWN`, `three-valued logic`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem local_query_binding_reference_context_substitution :
  forall db binding rows schedule
      (context : @query_expr_context TNull relname),
    local_query_binding_reference_well_typed db binding ->
    @query_expr_global_typed_outcome_equiv TNull relname
      (@_basesort TNull (set_local_query_binding_rows db binding rows))
      (@_instance TNull (set_local_query_binding_rows db binding rows))
      unknown3 NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      schedule
      (plug_query_expr_context context
        (local_query_binding_reference binding))
      (plug_query_expr_context context
        (local_query_binding_values binding rows)).
```

## `eval_local_query_bindings_with_schedule_decompose`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:528`](../QueryBindingSemantics.v#L528)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the eval local query bindings with schedule decompose law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`

Search aliases: `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_local_query_bindings_with_schedule_decompose :
  forall schedule env bindings db body outcome,
    eval_local_query_bindings_with_schedule schedule env db bindings
      body outcome <->
    (exists error,
      outcome = SqlError error /\
      local_query_bindings_error_with_schedule schedule env
        db bindings error) \/
    (exists reached,
      local_query_bindings_reachable_with_schedule schedule env
        db bindings reached /\
      eval_query_expr_with_schedule reached schedule env body outcome).
```

## `eval_bound_query_possible_outcome_decompose`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:580`](../QueryBindingSemantics.v#L580)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the eval bound query possible outcome decompose law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Lemma eval_bound_query_possible_outcome_decompose :
  forall db schemas env query outcome,
    eval_bound_query_possible_outcome db schemas env query outcome <->
    (exists schedule error,
      outcome = SqlError error /\
      local_query_bindings_error_with_schedule schedule env
        (declare_local_query_schemas db schemas)
        (bound_query_bindings query) error) \/
    eval_bound_query_body_possible_outcome db schemas env query outcome.
```

## `eval_bound_query_without_bindings_with_schemas`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:634`](../QueryBindingSemantics.v#L634)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the eval bound query without bindings with schemas law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_bound_query_without_bindings_with_schemas` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma eval_bound_query_without_bindings_with_schemas :
  forall db schemas env query outcome,
    eval_bound_query_possible_outcome db schemas env
      (MakeBoundQuery nil query) outcome <->
    eval_inlined_query_possible_outcome db schemas env query outcome.
```

## `bound_query_inline_possible_outcome_contract_sound`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:689`](../QueryBindingSemantics.v#L689)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the bound query inline possible outcome contract sound law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Theorem bound_query_inline_possible_outcome_contract_sound :
  forall db schemas env bound inlined,
    bound_query_inline_possible_outcome_contract
      db schemas env bound inlined ->
    bound_query_possible_outcome_equiv db schemas env
      bound (MakeBoundQuery nil inlined).
```

## `local_query_binding_inline_possible_outcome_contract_sound`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:746`](../QueryBindingSemantics.v#L746)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the local query binding inline possible outcome contract sound law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Corollary local_query_binding_inline_possible_outcome_contract_sound :
  forall db schemas env binding body inlined,
    local_query_binding_inline_possible_outcome_contract
      db schemas env binding body inlined ->
    bound_query_possible_outcome_equiv db schemas env
      (MakeBoundQuery (binding :: nil) body)
      (MakeBoundQuery nil inlined).
```

## `bound_query_body_possible_outcome_lift_refl`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:774`](../QueryBindingSemantics.v#L774)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Establishes reflexivity for projection and tuple-syntax bridging.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma bound_query_body_possible_outcome_lift_refl :
  forall db schemas env query,
    (exists outcome,
      eval_bound_query_body_possible_outcome
        db schemas env query outcome) ->
    bound_query_body_possible_outcome_lift
      db schemas env query query.
```

## `bound_query_body_possible_outcome_lift_sound`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:790`](../QueryBindingSemantics.v#L790)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the bound query body possible outcome lift sound law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Theorem bound_query_body_possible_outcome_lift_sound :
  forall db schemas env left right,
    bound_query_body_possible_outcome_lift
      db schemas env left right ->
    bound_query_possible_outcome_equiv db schemas env left right.
```

## `bound_query_possible_equiv_implies_possible_outcome_equiv`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:871`](../QueryBindingSemantics.v#L871)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes projection and tuple-syntax bridging across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma bound_query_possible_equiv_implies_possible_outcome_equiv :
  forall db schemas env left right,
    bound_query_possible_equiv db schemas env left right ->
    bound_query_possible_outcome_equiv db schemas env left right.
```

## `bound_query_program_inline_possible_outcome_contract_sound`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:930`](../QueryBindingSemantics.v#L930)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the bound query program inline possible outcome contract sound law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Theorem bound_query_program_inline_possible_outcome_contract_sound :
  forall db schemas env bound inlined,
    bound_query_program_inline_possible_outcome_contract
      db schemas env bound inlined ->
    bound_query_program_possible_outcome_equiv
      db schemas env bound (inlined_query_program inlined).
```

## `bound_query_program_body_possible_outcome_lift_sound`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:963`](../QueryBindingSemantics.v#L963)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the bound query program body possible outcome lift sound law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Theorem bound_query_program_body_possible_outcome_lift_sound :
  forall db schemas env left right,
    bound_query_program_body_possible_outcome_lift
      db schemas env left right ->
    bound_query_program_possible_outcome_equiv
      db schemas env left right.
```

## `inlined_query_program_materialization_safe`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:998`](../QueryBindingSemantics.v#L998)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the explicit runtime-safety direction for projection and tuple-syntax bridging.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `runtime`, `schema`

Search aliases: `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Lemma inlined_query_program_materialization_safe :
  forall db schemas env queries,
    bound_query_program_materialization_safe db schemas env
      (inlined_query_program queries).
```

## `bound_query_program_inline_possible_outcome_contract_demand_safe`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1025`](../QueryBindingSemantics.v#L1025)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Establishes the explicit runtime-safety direction for projection and tuple-syntax bridging.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Theorem bound_query_program_inline_possible_outcome_contract_demand_safe :
  forall db schemas env bound inlined,
    bound_query_program_inline_possible_outcome_contract
      db schemas env bound inlined ->
    bound_query_program_materialization_safe db schemas env bound ->
    bound_query_program_demand_safe_outcome_equiv db schemas env
      bound (inlined_query_program inlined).
```

## `bound_query_program_body_possible_outcome_lift_demand_safe`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1043`](../QueryBindingSemantics.v#L1043)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Establishes the explicit runtime-safety direction for projection and tuple-syntax bridging.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`

```rocq
Theorem bound_query_program_body_possible_outcome_lift_demand_safe :
  forall db schemas env left right,
    bound_query_program_body_possible_outcome_lift
      db schemas env left right ->
    bound_query_program_materialization_safe db schemas env left ->
    bound_query_program_materialization_safe db schemas env right ->
    bound_query_program_demand_safe_outcome_equiv
      db schemas env left right.
```

## `bound_query_possible_equiv_runtime_safe`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1058`](../QueryBindingSemantics.v#L1058)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes projection and tuple-syntax bridging across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma bound_query_possible_equiv_runtime_safe :
  forall db schemas env left right,
    bound_query_possible_equiv db schemas env left right ->
    bound_query_runtime_safe db schemas env left /\
    bound_query_runtime_safe db schemas env right.
```

## `bound_query_program_possible_equiv_materialization_safe`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1077`](../QueryBindingSemantics.v#L1077)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes projection and tuple-syntax bridging across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma bound_query_program_possible_equiv_materialization_safe :
  forall db schemas env left right,
    bound_query_program_possible_equiv db schemas env left right ->
    bound_query_program_materialization_safe db schemas env left /\
    bound_query_program_materialization_safe db schemas env right.
```

## `bound_query_program_possible_equiv_implies_possible_outcome_equiv`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1100`](../QueryBindingSemantics.v#L1100)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes projection and tuple-syntax bridging across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma bound_query_program_possible_equiv_implies_possible_outcome_equiv :
  forall db schemas env left right,
    bound_query_program_possible_equiv db schemas env left right ->
    bound_query_program_possible_outcome_equiv db schemas env left right.
```

## `bound_query_program_possible_equiv_implies_demand_safe_outcome_equiv`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1113`](../QueryBindingSemantics.v#L1113)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes projection and tuple-syntax bridging across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `schema`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma bound_query_program_possible_equiv_implies_demand_safe_outcome_equiv :
  forall db schemas env left right,
    bound_query_program_possible_equiv db schemas env left right ->
    bound_query_program_demand_safe_outcome_equiv
      db schemas env left right.
```

## `declare_local_query_schemas_basesort_extensional`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1166`](../QueryBindingSemantics.v#L1166)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the declare local query schemas basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `declare_local_query_schemas_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma declare_local_query_schemas_basesort_extensional :
  forall schemas first second,
    (forall relation,
      @_basesort TNull first relation =S=
      @_basesort TNull second relation) ->
    forall relation,
      @_basesort TNull (declare_local_query_schemas first schemas) relation =S=
      @_basesort TNull (declare_local_query_schemas second schemas) relation.
```

## `bound_query_admissible_database_shape_extensional`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1186`](../QueryBindingSemantics.v#L1186)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the bound query admissible database shape extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `bound_query_admissible_database_shape_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma bound_query_admissible_database_shape_extensional :
  forall schemas first second query,
    @_relnames TNull first = @_relnames TNull second ->
    (forall relation,
      @_basesort TNull first relation =S=
      @_basesort TNull second relation) ->
    bound_query_admissible first schemas query ->
    bound_query_admissible second schemas query.
```

## `bound_query_program_admissible_database_shape_extensional`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1236`](../QueryBindingSemantics.v#L1236)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the bound query program admissible database shape extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `bound_query_program_admissible_database_shape_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma bound_query_program_admissible_database_shape_extensional :
  forall schemas first second program,
    @_relnames TNull first = @_relnames TNull second ->
    (forall relation,
      @_basesort TNull first relation =S=
      @_basesort TNull second relation) ->
    bound_query_program_admissible first schemas program ->
    bound_query_program_admissible second schemas program.
```

## `bound_query_program_admissible_database_schema_transport`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1253`](../QueryBindingSemantics.v#L1253)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports the displayed hypotheses and conclusion for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `bound_query_program_admissible_database_schema_transport` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma bound_query_program_admissible_database_schema_transport :
  forall expected constraints actual schemas program,
    database_conforms_schema expected constraints actual ->
    bound_query_program_admissible expected schemas program ->
    bound_query_program_admissible actual schemas program.
```

## `eval_bound_query_without_bindings`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:1274`](../QueryBindingSemantics.v#L1274)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the eval bound query without bindings law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_bound_query_without_bindings` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`

```rocq
Lemma eval_bound_query_without_bindings :
  forall db env query outcome,
    eval_bound_query_possible_outcome db nil env
      (MakeBoundQuery nil query) outcome <->
    eval_query_expr_outcome_in_env db env query outcome.
```

## `TNullTypeEqb_eq`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:62`](../QueryTNullSyntax.v#L62)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull type eqb equality law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullTypeEqb_eq` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullTypeEqb_eq :
  forall left right,
    TNullTypeEqb left right = true <-> left = right.
```

## `TNullTypeListEqb_eq`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:70`](../QueryTNullSyntax.v#L70)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull type list eqb equality law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullTypeListEqb_eq` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullTypeListEqb_eq :
  forall left right,
    TNullTypeListEqb left right = true <-> left = right.
```

## `TNullRequireArgumentTypes_some_iff`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:90`](../QueryTNullSyntax.v#L90)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for projection and tuple-syntax bridging.

Applicability: Use in either direction to invert or construct a goal about projection and tuple-syntax bridging.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullRequireArgumentTypes_some_iff :
  forall expected actual result_type inferred_type,
    TNullRequireArgumentTypes expected actual result_type =
      Some inferred_type <->
    expected = actual /\ result_type = inferred_type.
```

## `TNullFunTermType_Constant`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:444`](../QueryTNullSyntax.v#L444)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull fun term type constant law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullFunTermType_Constant` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullFunTermType_Constant :
  forall value,
    TNullFunTermType (Constant value) =
      Some (NullValues.type_of_value value).
```

## `TNullFunTermType_Dot`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:452`](../QueryTNullSyntax.v#L452)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull fun term type dot law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullFunTermType_Dot` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullFunTermType_Dot :
  forall attribute,
    TNullFunTermType (Dot attribute) =
      Some (type_of_attribute TNull attribute).
```

## `TNullAggTermType_AExpr`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:460`](../QueryTNullSyntax.v#L460)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull agg term type aexpr law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullAggTermType_AExpr` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullAggTermType_AExpr :
  forall term,
    TNullAggTermType (AExpr term) = TNullFunTermType term.
```

## `TNullAggTermType_AAggregate`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:467`](../QueryTNullSyntax.v#L467)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull agg term type aaggregate law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullAggTermType_AAggregate` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullAggTermType_AAggregate :
  forall function quantifier argument argument_type,
    TNullFunTermType argument = Some argument_type ->
    TNullAggTermType (AAggregate function quantifier argument) =
      if TNullAggregateFunctionArgumentTypeValid function argument_type
      then Some (TNullAggregateFunctionOutputType function) else None.
```

## `TNullAggTermType_ACountStar`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:487`](../QueryTNullSyntax.v#L487)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull agg term type acount star law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullAggTermType_ACountStar` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullAggTermType_ACountStar :
  TNullAggTermType ACountStar = Some type_int64.
```

## `TNullQueryExprAdmissibleWithOutputs_intro`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:559`](../QueryTNullSyntax.v#L559)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull query expr admissible with outputs intro law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `TNullQueryExprAdmissibleWithOutputs_intro` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma TNullQueryExprAdmissibleWithOutputs_intro :
  forall basesort query expected_outputs,
    (@query_expr_admissible TNull relname basesort
      TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
      type_int64 type_bool NullValues.is_null_value query /\
     query_expr_outputs query = expected_outputs) ->
    query_expr_analysis_error_well_placed query ->
    query_expr_boolean_sites_well_formed query ->
    TNullQueryExprAdmissibleWithOutputs basesort query expected_outputs.
```

## `eval_query_expr_row_map_child_error`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:638`](../QueryTNullSyntax.v#L638)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for projection and tuple-syntax bridging.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `possible`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_row_map_child_error :
  forall db env output_attributes row_map input error,
    eval_query_expr_outcome_in_env db env input (SqlError error) ->
    eval_query_expr_outcome_in_env db env
      (RowMapExpr output_attributes row_map input) (SqlError error).
```

## `query_scalar_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1126`](../QueryTNullSyntax.v#L1126)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query scalar expr admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_scalar_expr_admissible_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_scalar_expr_admissible_basesort_extensional :
  (forall query,
    @query_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query ->
    @query_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query) /\
  (forall kind (expression : @scalar_expr T generic_relname kind) phase,
    @scalar_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression ->
    @scalar_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression).
```

## `query_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1188`](../QueryTNullSyntax.v#L1188)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Theorem query_expr_admissible_basesort_extensional :
  forall query,
    @query_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query ->
    @query_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query.
```

## `scalar_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1200`](../QueryTNullSyntax.v#L1200)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the scalar expr admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `scalar_expr_admissible_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Theorem scalar_expr_admissible_basesort_extensional :
  forall kind (expression : @scalar_expr T generic_relname kind) phase,
    @scalar_expr_admissible T generic_relname first_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression ->
    @scalar_expr_admissible T generic_relname second_basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase kind expression.
```

## `query_expr_admissible_of_with_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1235`](../QueryTNullSyntax.v#L1235)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible of with outputs law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_of_with_outputs` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_expr_admissible_of_with_outputs :
  forall query expected_outputs,
    query_expr_admissible_with_outputs query expected_outputs ->
    @query_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null query.
```

## `query_expr_admissible_with_outputs_change`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1245`](../QueryTNullSyntax.v#L1245)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs change law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_change` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_expr_admissible_with_outputs_change :
  forall query first_outputs second_outputs,
    query_expr_admissible_with_outputs query first_outputs ->
    first_outputs = second_outputs ->
    query_expr_admissible_with_outputs query second_outputs.
```

## `query_output_attributes_unique_from_all_diff`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1255`](../QueryTNullSyntax.v#L1255)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for projection and tuple-syntax bridging.

Applicability: Use in either direction to invert or construct a goal about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_output_attributes_unique_from_all_diff :
  forall outputs : list (attribute T),
    ListFacts.all_diff outputs ->
    @query_output_attributes_unique T outputs.
```

## `query_sort_keys_in_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1268`](../QueryTNullSyntax.v#L1268)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query sort keys in outputs law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_sort_keys_in_outputs` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_sort_keys_in_outputs :
  forall (outputs : list (attribute T)) keys,
    Forall (fun key => In (sort_key_attribute key) outputs) keys ->
    query_sort_keys_in_scope (@query_outputs_sort T outputs) keys.
```

## `query_attribute_not_in_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1279`](../QueryTNullSyntax.v#L1279)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query attribute not in outputs law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_attribute_not_in_outputs` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma query_attribute_not_in_outputs :
  forall (outputs : list (attribute T)) attribute,
    ~ In attribute outputs ->
    ~ attribute inS (@query_outputs_sort T outputs).
```

## `query_expr_admissible_with_outputs_error`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1290`](../QueryTNullSyntax.v#L1290)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for projection and tuple-syntax bridging.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_expr_admissible_with_outputs_error :
  forall (outputs : list (attribute T)) error,
    @query_output_attributes_unique T outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Error T generic_relname outputs error) outputs.
```

## `query_expr_admissible_with_outputs_values`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1299`](../QueryTNullSyntax.v#L1299)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs values law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_values` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_expr_admissible_with_outputs_values :
  forall (outputs : list (attribute T)) rows,
    @query_output_attributes_unique T outputs ->
    @query_values_well_sorted T (@query_outputs_sort T outputs) rows ->
    query_expr_admissible_with_outputs
      (@QExpr_Values T generic_relname outputs rows) outputs.
```

## `query_expr_admissible_with_outputs_empty_tuple`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1309`](../QueryTNullSyntax.v#L1309)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for projection and tuple-syntax bridging.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_admissible_with_outputs_empty_tuple :
  query_expr_admissible_with_outputs
    (@QExpr_Values T generic_relname nil
      (Febag.singleton (Fecol.CBag (CTuple T)) (empty_tuple T))) nil.
```

## `query_expr_admissible_with_outputs_table`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1336`](../QueryTNullSyntax.v#L1336)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs table law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_table` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_expr_admissible_with_outputs_table :
  forall (outputs : list (attribute T)) table,
    @query_output_attributes_unique T outputs ->
    @query_outputs_sort T outputs =S= basesort table ->
    query_expr_admissible_with_outputs
      (@QExpr_Table T generic_relname outputs table) outputs.
```

## `query_expr_admissible_with_outputs_set`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1346`](../QueryTNullSyntax.v#L1346)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs set law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_set` direction for SQL bag/set operations; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `set operation`

```rocq
Lemma query_expr_admissible_with_outputs_set :
  forall operation left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    left_outputs = right_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Set T generic_relname operation left right) left_outputs.
```

## `query_expr_admissible_with_outputs_natural_join`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1363`](../QueryTNullSyntax.v#L1363)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs natural join law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_natural_join` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `join`

```rocq
Lemma query_expr_admissible_with_outputs_natural_join :
  forall left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_NaturalJoin T generic_relname left right)
      (@query_natural_join_outputs T left_outputs right_outputs).
```

## `query_expr_admissible_with_outputs_cross_join`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1378`](../QueryTNullSyntax.v#L1378)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs cross join law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_cross_join` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `join`, `cross product`, `CROSS JOIN`

```rocq
Lemma query_expr_admissible_with_outputs_cross_join :
  forall left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    @query_output_sorts_disjoint T
      (@query_outputs_sort T left_outputs)
      (@query_outputs_sort T right_outputs) ->
    query_expr_admissible_with_outputs
      (@QExpr_CrossJoin T generic_relname left right)
      (left_outputs ++ right_outputs).
```

## `query_expr_admissible_with_outputs_join`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1398`](../QueryTNullSyntax.v#L1398)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs join law for outer/semi/anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`

```rocq
Lemma query_expr_admissible_with_outputs_join :
  forall kind predicate matched_select left_select right_select
      left right left_outputs right_outputs,
    @scalar_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null
      ScalarPhaseOn ScalarResultBoolean predicate ->
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    (match kind with
     | QueryJoinInner =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select
     | QueryJoinLeft =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           left_select
     | QueryJoinRight =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           right_select
     | QueryJoinFull =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           left_select /\
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           right_select
     | QueryJoinSemi | QueryJoinAnti =>
         prop_forall
           (fun item =>
             @scalar_expr_admissible T generic_relname basesort
               leaf_has_type call_has_type predicate_has_types
               rank_type boolean_type value_is_null
               ScalarPhaseRowSelect ScalarResultValue (fst item) /\
             scalar_expr_type (fst item) =
               type_of_attribute T (snd item))
           left_select
     end) ->
    query_expr_admissible_with_outputs
      (@QExpr_Join T generic_relname kind predicate
        matched_select left_select right_select left right)
      (match kind with
       | QueryJoinSemi | QueryJoinAnti =>
           scalar_select_outputs left_select
       | _ => scalar_select_outputs matched_select
       end).
```

## `query_expr_admissible_with_outputs_project`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1516`](../QueryTNullSyntax.v#L1516)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs project law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_project` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `projection`, `SELECT list`

```rocq
Lemma query_expr_admissible_with_outputs_project :
  forall select_list input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_select_list_outputs_unique select_list ->
    prop_forall
      (fun item =>
        @scalar_expr_admissible T generic_relname basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null
          ScalarPhaseRowSelect ScalarResultValue (fst item) /\
        scalar_expr_type (fst item) = type_of_attribute T (snd item))
      select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_Project T generic_relname select_list input)
      (scalar_select_outputs select_list).
```

## `query_expr_admissible_with_outputs_row_map`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1536`](../QueryTNullSyntax.v#L1536)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs row map law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_row_map` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `projection`, `SELECT list`

```rocq
Lemma query_expr_admissible_with_outputs_row_map :
  forall (outputs : list (attribute T)) row_map input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T outputs ->
    @query_row_map_well_sorted T (@query_outputs_sort T outputs) row_map ->
    query_expr_admissible_with_outputs
      (@QExpr_RowMap T generic_relname outputs row_map input) outputs.
```

## `query_expr_admissible_with_outputs_filter`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1548`](../QueryTNullSyntax.v#L1548)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs filter law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_filter` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `filter`, `WHERE`

```rocq
Lemma query_expr_admissible_with_outputs_filter :
  forall predicate input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @scalar_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null
      ScalarPhaseWhere ScalarResultBoolean predicate ->
    query_expr_admissible_with_outputs
      (@QExpr_Filter T generic_relname predicate input) input_outputs.
```

## `query_expr_admissible_with_outputs_group`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1564`](../QueryTNullSyntax.v#L1564)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs group law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_group` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `GROUP BY`

```rocq
Lemma query_expr_admissible_with_outputs_group :
  forall select_list group_keys group_terms having input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T (scalar_select_outputs select_list) ->
    prop_forall
      (fun item =>
        @scalar_expr_admissible T generic_relname basesort
          leaf_has_type call_has_type predicate_has_types
          rank_type boolean_type value_is_null
          ScalarPhaseSelect ScalarResultValue (fst item) /\
        scalar_expr_type (fst item) = type_of_attribute T (snd item))
      select_list ->
    @scalar_expr_admissible T generic_relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null
      ScalarPhaseHaving ScalarResultBoolean having ->
    prop_forall
      (@scalar_expr_admissible T generic_relname basesort
        leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type value_is_null
        ScalarPhaseGroupBy ScalarResultValue) group_keys ->
    scalar_group_key_terms group_keys = Some group_terms ->
    query_expr_admissible_with_outputs
      (@QExpr_Group T generic_relname
        select_list group_keys having input)
      (scalar_select_outputs select_list).
```

## `query_expr_admissible_with_outputs_grouping_sets`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1599`](../QueryTNullSyntax.v#L1599)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs grouping sets law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_grouping_sets` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `grouping sets`, `GROUP BY`

```rocq
Lemma query_expr_admissible_with_outputs_grouping_sets :
  forall grouping_sets input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_grouping_sets_well_formed grouping_sets ->
    prop_forall
      (fun grouping_set =>
        prop_forall
          (fun item =>
            @scalar_expr_admissible T generic_relname basesort
              leaf_has_type call_has_type predicate_has_types
              rank_type boolean_type value_is_null
              ScalarPhaseSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item))
          (fst grouping_set) /\
        prop_forall
          (@scalar_expr_admissible T generic_relname basesort
            leaf_has_type call_has_type predicate_has_types
            rank_type boolean_type value_is_null
            ScalarPhaseGroupBy ScalarResultValue)
          (snd grouping_set) /\
        exists group_terms,
          scalar_group_key_terms (snd grouping_set) = Some group_terms)
      grouping_sets ->
    query_expr_admissible_with_outputs
      (@QExpr_GroupingSets T generic_relname grouping_sets input)
      (query_grouping_sets_outputs grouping_sets).
```

## `query_expr_admissible_with_outputs_rank`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1631`](../QueryTNullSyntax.v#L1631)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs rank law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_rank` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `window`, `PARTITION BY`

```rocq
Lemma query_expr_admissible_with_outputs_rank :
  forall partition_keys order_keys rank_attribute embed_rank
      input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    type_of_attribute T rank_attribute = rank_type ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) partition_keys ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) order_keys ->
    ~ rank_attribute inS (@query_outputs_sort T input_outputs) ->
    query_expr_admissible_with_outputs
      (@QExpr_Rank T generic_relname partition_keys order_keys
        rank_attribute embed_rank input)
      (input_outputs ++ rank_attribute :: nil).
```

## `query_expr_admissible_with_outputs_window`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1656`](../QueryTNullSyntax.v#L1656)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs window law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_window` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `window`, `PARTITION BY`

```rocq
Lemma query_expr_admissible_with_outputs_window :
  forall partition_keys order_keys items input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) partition_keys ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) order_keys ->
    Forall
      (fun item =>
        ~ qwi_attribute item inS (@query_outputs_sort T input_outputs))
      items ->
    prop_forall
      (fun item =>
        match item with
        | QueryWindowItem output function =>
            match function with
            | QueryWindowRowNumber _ =>
                type_of_attribute T output = rank_type
            | QueryWindowAggregate term
            | QueryWindowFullPartitionAggregate term =>
                leaf_has_type (type_of_attribute T output) term
            end
        end)
      items ->
    length (map (@qwi_attribute T) items) =
      Fset.cardinal (A T)
        (Fset.mk_set (A T) (map (@qwi_attribute T) items)) ->
    query_expr_admissible_with_outputs
      (@QExpr_Window T generic_relname partition_keys order_keys items input)
      (input_outputs ++ map (@qwi_attribute T) items).
```

## `query_expr_admissible_with_outputs_distinct`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1700`](../QueryTNullSyntax.v#L1700)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs distinct law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_distinct` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `DISTINCT`, `duplicate elimination`

```rocq
Lemma query_expr_admissible_with_outputs_distinct :
  forall input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Distinct T generic_relname input) input_outputs.
```

## `query_expr_admissible_with_outputs_order_by`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1710`](../QueryTNullSyntax.v#L1710)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs order by law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_order_by` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `ORDER BY`, `ordered observation`

```rocq
Lemma query_expr_admissible_with_outputs_order_by :
  forall keys input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope (@query_outputs_sort T input_outputs) keys ->
    query_expr_admissible_with_outputs
      (@QExpr_OrderBy T generic_relname keys input) input_outputs.
```

## `query_expr_admissible_with_outputs_offset`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1724`](../QueryTNullSyntax.v#L1724)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs offset law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_offset` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `OFFSET`

```rocq
Lemma query_expr_admissible_with_outputs_offset :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Offset T generic_relname count input) input_outputs.
```

## `query_expr_admissible_with_outputs_fetch`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1734`](../QueryTNullSyntax.v#L1734)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query expr admissible with outputs fetch law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_fetch` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain exact order whenever the declaration observes it.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `FETCH`, `LIMIT`

```rocq
Lemma query_expr_admissible_with_outputs_fetch :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Fetch T generic_relname count input) input_outputs.
```

## `query_expr_admissible_database_schema_transport`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1748`](../QueryTNullSyntax.v#L1748)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports the displayed hypotheses and conclusion for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_database_schema_transport` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Theorem query_expr_admissible_database_schema_transport :
  forall expected constraints actual query,
    database_conforms_schema expected constraints actual ->
    TNullQueryExprAdmissible (@_basesort TNull expected) query ->
    TNullQueryExprAdmissible (@_basesort TNull actual) query.
```
