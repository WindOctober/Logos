# Query syntax and projection bridges

Route here for: query-level nullable syntax adapters, tuple projection, attribute lookup.

This focused catalog contains 43 declarations routed at declaration granularity from `QueryTNullSyntax.v`, `TNullSyntax.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `NumericExpOutputRow_labels`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:152`](../QueryTNullSyntax.v#L152)

Purpose/direction: States the numeric exp output row labels law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpOutputRow_labels` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:167`](../QueryTNullSyntax.v#L167)

Purpose/direction: States the numeric exp row adapter well sorted law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_well_sorted` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:191`](../QueryTNullSyntax.v#L191)

Purpose/direction: States the numeric exp row map expr admissible law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowMapExpr_admissible` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpRowMapExpr_admissible :
  forall basesort passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model input,
    @query_expr_admissible TNull relname basesort input ->
    @query_output_attributes_unique TNull
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute) ->
    @query_expr_admissible TNull relname basesort
      (NumericExpRowMapExpr passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model input).
```

## `NumericExpRowAdapter_null`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:209`](../QueryTNullSyntax.v#L209)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_null` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:222`](../QueryTNullSyntax.v#L222)

Purpose/direction: Inverts or constructs the successful evaluation branch for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_success` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:243`](../QueryTNullSyntax.v#L243)

Purpose/direction: Inverts or constructs the successful evaluation branch for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_invalid_success` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:261`](../QueryTNullSyntax.v#L261)

Purpose/direction: Connects the displayed range/representability premise to projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `NumericExpRowAdapter_out_of_range` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scalar` (rank 52)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:277`](../QueryTNullSyntax.v#L277)

Purpose/direction: States the numeric exp success valid invalid scale law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpSuccessValid_invalid_scale` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every typmod/precision/scale and representability condition.

Cross-index: `scalar` (rank 52)

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`, `typmod`, `precision/scale`

```rocq
Lemma NumericExpSuccessValid_invalid_scale :
  forall result dscale,
    numeric_display_scale_valid_bool dscale = false ->
    NumericExpSuccessValid result dscale = false.
```

## `NumericExpSuccessValid_nonfinite`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:286`](../QueryTNullSyntax.v#L286)

Purpose/direction: States the numeric exp success valid nonfinite law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `NumericExpSuccessValid_nonfinite` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `scalar` (rank 52)

Search aliases: `query syntax bridge`, `NUMERIC`, `DECIMAL`

```rocq
Lemma NumericExpSuccessValid_nonfinite :
  forall dscale,
    NumericExpSuccessValid NumericNegInfinity dscale = false /\
    NumericExpSuccessValid NumericPosInfinity dscale = false /\
    NumericExpSuccessValid NumericNaN dscale = false.
```

## `eval_query_expr_row_map_child_error`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:309`](../QueryTNullSyntax.v#L309)

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for projection and tuple-syntax bridging.

Applicability: Use at the successful-outcome/runtime-error boundary for projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime` (rank 52)

Search aliases: `query syntax bridge`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_query_expr_row_map_child_error :
  forall db env output_attributes row_map input error,
    eval_query_expr_outcome_in_env db env input (SqlError error) ->
    eval_query_expr_outcome_in_env db env
      (RowMapExpr output_attributes row_map input) (SqlError error).
```

## `query_formula_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:424`](../QueryTNullSyntax.v#L424)

Purpose/direction: States the query formula expr admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_formula_expr_admissible_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_formula_expr_admissible_basesort_extensional :
  (forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query) /\
  (forall formula,
    @formula_expr_admissible T generic_relname first_basesort formula ->
    @formula_expr_admissible T generic_relname second_basesort formula).
```

## `query_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:447`](../QueryTNullSyntax.v#L447)

Purpose/direction: States the query expr admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Theorem query_expr_admissible_basesort_extensional :
  forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query.
```

## `formula_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:455`](../QueryTNullSyntax.v#L455)

Purpose/direction: States the formula expr admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_expr_admissible_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Theorem formula_expr_admissible_basesort_extensional :
  forall formula,
    @formula_expr_admissible T generic_relname first_basesort formula ->
    @formula_expr_admissible T generic_relname second_basesort formula.
```

## `query_expr_admissible_with_outputs_change`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:480`](../QueryTNullSyntax.v#L480)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:491`](../QueryTNullSyntax.v#L491)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:504`](../QueryTNullSyntax.v#L504)

Purpose/direction: States the query sort keys in outputs law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_sort_keys_in_outputs` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_sort_keys_in_outputs :
  forall (outputs : list (attribute T)) keys,
    Forall
      (fun key => In (sort_key_attribute key) outputs)
      keys ->
    query_sort_keys_in_scope (@query_outputs_sort T outputs) keys.
```

## `query_attribute_not_in_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:517`](../QueryTNullSyntax.v#L517)

Purpose/direction: States the query attribute not in outputs law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_attribute_not_in_outputs` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 52)

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Lemma query_attribute_not_in_outputs :
  forall (outputs : list (attribute T)) attribute,
    ~ In attribute outputs ->
    ~ attribute inS (@query_outputs_sort T outputs).
```

## `query_expr_admissible_with_outputs_error`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:528`](../QueryTNullSyntax.v#L528)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:537`](../QueryTNullSyntax.v#L537)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:550`](../QueryTNullSyntax.v#L550)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:577`](../QueryTNullSyntax.v#L577)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:587`](../QueryTNullSyntax.v#L587)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:604`](../QueryTNullSyntax.v#L604)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:619`](../QueryTNullSyntax.v#L619)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:639`](../QueryTNullSyntax.v#L639)

Purpose/direction: States the query expr admissible with outputs join law for outer/semi/anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`

```rocq
Lemma query_expr_admissible_with_outputs_join :
  forall kind predicate matched_select left_select right_select
      left right left_outputs right_outputs,
    @formula_expr_admissible T generic_relname basesort predicate ->
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    query_expr_admissible_with_outputs
      (@QExpr_Join T generic_relname kind predicate
        matched_select left_select right_select left right)
      (match kind with
       | QueryJoinSemi | QueryJoinAnti => select_list_outputs left_select
       | _ => select_list_outputs matched_select
       end).
```

## `query_expr_admissible_with_outputs_project`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:665`](../QueryTNullSyntax.v#L665)

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
    query_expr_admissible_with_outputs
      (@QExpr_Project T generic_relname select_list input)
      (select_list_outputs select_list).
```

## `query_expr_admissible_with_outputs_row_map`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:677`](../QueryTNullSyntax.v#L677)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:689`](../QueryTNullSyntax.v#L689)

Purpose/direction: States the query expr admissible with outputs filter law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_filter` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `filter`, `WHERE`

```rocq
Lemma query_expr_admissible_with_outputs_filter :
  forall predicate input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @formula_expr_admissible T generic_relname basesort predicate ->
    query_expr_admissible_with_outputs
      (@QExpr_Filter T generic_relname predicate input) input_outputs.
```

## `query_expr_admissible_with_outputs_group`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:703`](../QueryTNullSyntax.v#L703)

Purpose/direction: States the query expr admissible with outputs group law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_group` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `GROUP BY`

```rocq
Lemma query_expr_admissible_with_outputs_group :
  forall select_list group_terms having input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @formula_expr_admissible T generic_relname basesort having ->
    query_select_list_outputs_unique select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_Group T generic_relname
        select_list group_terms having input)
      (select_list_outputs select_list).
```

## `query_expr_admissible_with_outputs_grouping_sets`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:718`](../QueryTNullSyntax.v#L718)

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
    query_expr_admissible_with_outputs
      (@QExpr_GroupingSets T generic_relname grouping_sets input)
      (query_grouping_sets_outputs grouping_sets).
```

## `query_expr_admissible_with_outputs_rank`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:730`](../QueryTNullSyntax.v#L730)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:754`](../QueryTNullSyntax.v#L754)

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
    length (map (@qwi_attribute T) items) =
      Fset.cardinal (A T)
        (Fset.mk_set (A T) (map (@qwi_attribute T) items)) ->
    query_expr_admissible_with_outputs
      (@QExpr_Window T generic_relname partition_keys order_keys items input)
      (input_outputs ++ map (@qwi_attribute T) items).
```

## `query_expr_admissible_with_outputs_distinct`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:783`](../QueryTNullSyntax.v#L783)

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

## `query_expr_admissible_with_outputs_unordered`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:793`](../QueryTNullSyntax.v#L793)

Purpose/direction: States the query expr admissible with outputs unordered law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_unordered` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_expr_admissible_with_outputs_unordered :
  forall input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Unordered T generic_relname input) input_outputs.
```

## `query_expr_admissible_with_outputs_order_by`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:803`](../QueryTNullSyntax.v#L803)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:817`](../QueryTNullSyntax.v#L817)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:827`](../QueryTNullSyntax.v#L827)

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

## `formula_expr_not_admissible`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:837`](../QueryTNullSyntax.v#L837)

Purpose/direction: States the formula expr not admissible law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_expr_not_admissible` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma formula_expr_not_admissible :
  forall formula,
    @formula_expr_admissible T generic_relname basesort formula ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Not T generic_relname formula).
```

## `formula_expr_quant_admissible_from_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:848`](../QueryTNullSyntax.v#L848)

Purpose/direction: States the formula expr quant admissible from outputs law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_expr_quant_admissible_from_outputs` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma formula_expr_quant_admissible_from_outputs :
  forall quantifier predicate arguments subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    length arguments = 1%nat ->
    length expected_outputs = 1%nat ->
    (length arguments + length expected_outputs)%nat =
      predicate_arity T predicate ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Quant T generic_relname
        quantifier predicate arguments subquery).
```

## `formula_expr_in_admissible_from_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:865`](../QueryTNullSyntax.v#L865)

Purpose/direction: States the formula expr in admissible from outputs law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_expr_in_admissible_from_outputs` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `subquery`, `IN`

```rocq
Lemma formula_expr_in_admissible_from_outputs :
  forall (select_items : list (@select T)) subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    query_in_positionally_aligned
      (@_Select_List T select_items) expected_outputs ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_In T generic_relname select_items subquery).
```

## `formula_expr_exists_admissible_from_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:886`](../QueryTNullSyntax.v#L886)

Purpose/direction: States the formula expr exists admissible from outputs law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `formula_expr_exists_admissible_from_outputs` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `subquery`, `EXISTS`

```rocq
Lemma formula_expr_exists_admissible_from_outputs :
  forall subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Exists T generic_relname subquery).
```

## `query_expr_admissible_database_schema_transport`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:900`](../QueryTNullSyntax.v#L900)

Purpose/direction: Transports the displayed hypotheses and conclusion for projection and tuple-syntax bridging.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_database_schema_transport` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `schema conformance`, `typing`

```rocq
Theorem query_expr_admissible_database_schema_transport :
  forall expected constraints actual query,
    database_conforms_schema expected constraints actual ->
    @query_expr_admissible TNull relname (@_basesort TNull expected) query ->
    @query_expr_admissible TNull relname (@_basesort TNull actual) query.
```

## `direct_projection_preserves_attr`

Source: [`theories/FormalSQL/TNullSyntax.v:85`](../TNullSyntax.v#L85)

Purpose/direction: Shows that the indicated operator preserves the displayed projection and tuple-syntax bridging property.

Applicability: Use when the goal or a hypothesis matches the `direct_projection_preserves_attr` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 52)

Search aliases: `query syntax bridge`, `projection`, `SELECT list`

```rocq
Lemma direct_projection_preserves_attr :
  forall env select_list attribute,
    select_list_directly_selects_attr select_list attribute ->
    select_list_has_unique_outputs select_list ->
    projection_preserves_attr env select_list attribute.
```
