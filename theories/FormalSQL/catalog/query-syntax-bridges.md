# Query syntax and projection bridges

Route here for: query-level nullable syntax adapters, query-local bindings, tuple projection, attribute lookup.

This focused catalog contains 55 declarations routed at declaration granularity from `QueryBindingSemantics.v`, `QueryTNullSyntax.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `eval_local_query_bindings_with_schedule_decompose`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:262`](../QueryBindingSemantics.v#L262)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:314`](../QueryBindingSemantics.v#L314)

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

## `bound_query_body_possible_outcome_lift_refl`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:360`](../QueryBindingSemantics.v#L360)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:376`](../QueryBindingSemantics.v#L376)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:457`](../QueryBindingSemantics.v#L457)

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

## `bound_query_program_body_possible_outcome_lift_sound`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:510`](../QueryBindingSemantics.v#L510)

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

## `bound_query_program_body_possible_outcome_lift_demand_safe`

Source: [`theories/FormalSQL/QueryBindingSemantics.v:561`](../QueryBindingSemantics.v#L561)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:576`](../QueryBindingSemantics.v#L576)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:595`](../QueryBindingSemantics.v#L595)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:618`](../QueryBindingSemantics.v#L618)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:631`](../QueryBindingSemantics.v#L631)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:684`](../QueryBindingSemantics.v#L684)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:704`](../QueryBindingSemantics.v#L704)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:754`](../QueryBindingSemantics.v#L754)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:771`](../QueryBindingSemantics.v#L771)

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

Source: [`theories/FormalSQL/QueryBindingSemantics.v:792`](../QueryBindingSemantics.v#L792)

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

## `TNullQueryExprAdmissibleWithOutputs_intro`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:462`](../QueryTNullSyntax.v#L462)

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

## `NumericExpOutputRow_labels`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:617`](../QueryTNullSyntax.v#L617)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric exp output row labels law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpOutputRow_labels` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpOutputRow_labels :
  forall passthrough output_numeric_attribute output_dscale_attribute
         input result dscale,
    labels TNull
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute input result dscale)
    =S=
    Fset.mk_set (A TNull)
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute).
```

## `NumericExpRowAdapter_well_sorted`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:632`](../QueryTNullSyntax.v#L632)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric exp row adapter well sorted law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_well_sorted` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowAdapter_well_sorted :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model,
    @query_row_map_well_sorted TNull
      (Fset.mk_set (A TNull)
        (NumericExpOutputAttributes passthrough
          output_numeric_attribute output_dscale_attribute))
      (NumericExpRowAdapter passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model).
```

## `NumericExpRowMapExpr_admissible`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:656`](../QueryTNullSyntax.v#L656)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric exp row map expr admissible law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowMapExpr_admissible` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowMapExpr_admissible :
  forall basesort passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model input,
    TNullQueryExprAdmissible basesort input ->
    query_expr_contains_analysis_error input = false ->
    @query_output_attributes_unique TNull
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute) ->
    TNullQueryExprAdmissible basesort
      (NumericExpRowMapExpr passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model input).
```

## `NumericExpRowAdapter_null`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:684`](../QueryTNullSyntax.v#L684)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_null` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NULL`, `UNKNOWN`, `three-valued logic`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowAdapter_null :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row,
    dot TNull row avg_value_attribute = NullValues.Value_numeric None ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    SqlSuccess
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute row None None).
```

## `NumericExpRowAdapter_success`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:697`](../QueryTNullSyntax.v#L697)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_success` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowAdapter_success :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale result result_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale =
      NumericExpSuccess result result_dscale ->
    NumericExpSuccessValid result result_dscale = true ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    SqlSuccess
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute row
        (Some result) (Some result_dscale)).
```

## `NumericExpRowAdapter_invalid_success`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:718`](../QueryTNullSyntax.v#L718)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_invalid_success` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowAdapter_invalid_success :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale result result_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale =
      NumericExpSuccess result result_dscale ->
    NumericExpSuccessValid result result_dscale = false ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    @NumericExpRangeError (tuple TNull).
```

## `NumericExpRowAdapter_out_of_range`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:736`](../QueryTNullSyntax.v#L736)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Connects the displayed range/representability premise to projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_out_of_range` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowAdapter_out_of_range :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale = NumericExpValueOutOfRange ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    @NumericExpRangeError (tuple TNull).
```

## `NumericExpSuccessValid_invalid_scale`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:752`](../QueryTNullSyntax.v#L752)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric exp success valid invalid scale law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpSuccessValid_invalid_scale` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma NumericExpSuccessValid_invalid_scale :
  forall result dscale,
    numeric_display_scale_valid_bool dscale = false ->
    NumericExpSuccessValid result dscale = false.
```

## `NumericExpSuccessValid_nonfinite`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:761`](../QueryTNullSyntax.v#L761)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the numeric exp success valid nonfinite law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpSuccessValid_nonfinite` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar`

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpSuccessValid_nonfinite :
  forall dscale,
    NumericExpSuccessValid NumericNegInfinity dscale = false /\
    NumericExpSuccessValid NumericPosInfinity dscale = false /\
    NumericExpSuccessValid NumericNaN dscale = false.
```

## `eval_query_expr_row_map_child_error`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:784`](../QueryTNullSyntax.v#L784)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1272`](../QueryTNullSyntax.v#L1272)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1334`](../QueryTNullSyntax.v#L1334)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1346`](../QueryTNullSyntax.v#L1346)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1381`](../QueryTNullSyntax.v#L1381)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1391`](../QueryTNullSyntax.v#L1391)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1401`](../QueryTNullSyntax.v#L1401)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1414`](../QueryTNullSyntax.v#L1414)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1425`](../QueryTNullSyntax.v#L1425)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1436`](../QueryTNullSyntax.v#L1436)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1445`](../QueryTNullSyntax.v#L1445)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1455`](../QueryTNullSyntax.v#L1455)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1482`](../QueryTNullSyntax.v#L1482)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1492`](../QueryTNullSyntax.v#L1492)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1509`](../QueryTNullSyntax.v#L1509)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1524`](../QueryTNullSyntax.v#L1524)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1544`](../QueryTNullSyntax.v#L1544)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1662`](../QueryTNullSyntax.v#L1662)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1682`](../QueryTNullSyntax.v#L1682)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1694`](../QueryTNullSyntax.v#L1694)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1710`](../QueryTNullSyntax.v#L1710)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1745`](../QueryTNullSyntax.v#L1745)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1777`](../QueryTNullSyntax.v#L1777)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1802`](../QueryTNullSyntax.v#L1802)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1846`](../QueryTNullSyntax.v#L1846)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1856`](../QueryTNullSyntax.v#L1856)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1870`](../QueryTNullSyntax.v#L1870)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1880`](../QueryTNullSyntax.v#L1880)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1894`](../QueryTNullSyntax.v#L1894)

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
