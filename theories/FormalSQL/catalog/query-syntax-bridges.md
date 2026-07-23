# Query syntax and projection bridges

Route here for: query-level nullable syntax adapters, tuple projection, attribute lookup.

This focused catalog contains 62 declarations routed at declaration granularity from `PiFacts.v`, `QueryTNullSyntax.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `pi_sort`

Source: [`theories/FormalSQL/PiFacts.v:21`](../PiFacts.v#L21)

Purpose/direction: States the pi sort law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `pi_sort` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `projection` (rank 52)

Search aliases: `query syntax bridge`, `projection`, `SELECT list`

```rocq
Lemma pi_sort :
  forall db s q,
    @sort TNull relname (@_basesort TNull db) (Pi s q) =S= select_list_sort s.
```

## `pi_output_tuple_has_select_list_sort`

Source: [`theories/FormalSQL/PiFacts.v:37`](../PiFacts.v#L37)

Purpose/direction: States the pi output tuple has select list sort law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `pi_output_tuple_has_select_list_sort` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 52)

Search aliases: `query syntax bridge`, `projection`, `SELECT list`

```rocq
Lemma pi_output_tuple_has_select_list_sort :
  forall db s q t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s q) ->
    labels TNull t =S= select_list_sort s.
```

## `common_pi_output_tuple_implies_same_select_list_sort`

Source: [`theories/FormalSQL/PiFacts.v:63`](../PiFacts.v#L63)

Purpose/direction: Establishes commutativity for the declared projection and tuple-syntax bridging operator.

Applicability: Use when the goal or a hypothesis matches the `common_pi_output_tuple_implies_same_select_list_sort` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 52)

Search aliases: `query syntax bridge`, `projection`, `SELECT list`

```rocq
Lemma common_pi_output_tuple_implies_same_select_list_sort :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    t inBE eval_query_in_state db (Pi s2 q2) ->
    select_list_sort s1 =S= select_list_sort s2.
```

## `pi_sort_mismatch_not_equiv_with_witness`

Source: [`theories/FormalSQL/PiFacts.v:77`](../PiFacts.v#L77)

Purpose/direction: Derives query non-equivalence from the displayed projection/sort mismatch witness.

Applicability: Use to close a non-equivalence goal after supplying the exact error or mismatch witness required by `pi_sort_mismatch_not_equiv_with_witness`; it does not assume equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the displayed runtime-error or mismatch witness; equivalence is the negated conclusion, not a premise.

Cross-index: `projection` (rank 52)

Search aliases: `query syntax bridge`, `projection`, `SELECT list`, `non-equivalence`, `mismatch witness`

```rocq
Lemma pi_sort_mismatch_not_equiv_with_witness :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    (select_list_sort s1 =S= select_list_sort s2 -> False) ->
    ~ query_equiv db (Pi s1 q1) (Pi s2 q2).
```

## `nonempty_pi_equiv_iff_sort_and_occ`

Source: [`theories/FormalSQL/PiFacts.v:102`](../PiFacts.v#L102)

Purpose/direction: Gives necessary and sufficient conditions for projection and tuple-syntax bridging.

Applicability: Use in either direction to invert or construct a goal about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `projection` (rank 52), `bag` (rank 52)

Search aliases: `query syntax bridge`, `projection`, `SELECT list`, `multiplicity`, `equivalence`, `congruence`

```rocq
Lemma nonempty_pi_equiv_iff_sort_and_occ :
  forall db s1 q1 s2 q2,
    well_sorted_database db ->
    query_nonempty db (Pi s1 q1) ->
    query_equiv db (Pi s1 q1) (Pi s2 q2) <->
      query_succeeds db (Pi s1 q1) /\
      query_succeeds db (Pi s2 q2) /\
      select_list_sort s1 =S= select_list_sort s2 /\
      forall t, query_occ db (Pi s1 q1) t = query_occ db (Pi s2 q2) t.
```

## `NumericExpOutputRow_labels`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:151`](../QueryTNullSyntax.v#L151)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:166`](../QueryTNullSyntax.v#L166)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:190`](../QueryTNullSyntax.v#L190)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:208`](../QueryTNullSyntax.v#L208)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:221`](../QueryTNullSyntax.v#L221)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:242`](../QueryTNullSyntax.v#L242)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:260`](../QueryTNullSyntax.v#L260)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:276`](../QueryTNullSyntax.v#L276)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:285`](../QueryTNullSyntax.v#L285)

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

## `query_sort_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:418`](../QueryTNullSyntax.v#L418)

Purpose/direction: States the query sort basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_sort_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_sort_basesort_extensional :
  forall query,
    @sort T generic_relname first_basesort query =S=
    @sort T generic_relname second_basesort query.
```

## `query_output_sorts_disjoint_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:434`](../QueryTNullSyntax.v#L434)

Purpose/direction: States the query output sorts disjoint basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_output_sorts_disjoint_basesort_extensional` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_output_sorts_disjoint_basesort_extensional :
  forall left_first right_first left_second right_second,
    left_first =S= left_second ->
    right_first =S= right_second ->
    @query_output_sorts_disjoint T left_first right_first ->
    @query_output_sorts_disjoint T left_second right_second.
```

## `bag_query_formula_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:457`](../QueryTNullSyntax.v#L457)

Purpose/direction: States the bag query formula admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_formula_admissible_basesort_extensional :
  (forall query,
    @bag_query_admissible T generic_relname first_basesort query ->
    @bag_query_admissible T generic_relname second_basesort query) /\
  (forall formula,
    @bag_formula_admissible T generic_relname first_basesort formula ->
    @bag_formula_admissible T generic_relname second_basesort formula).
```

## `bag_query_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:518`](../QueryTNullSyntax.v#L518)

Purpose/direction: States the bag query admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_basesort_extensional :
  forall query,
    @bag_query_admissible T generic_relname first_basesort query ->
    @bag_query_admissible T generic_relname second_basesort query.
```

## `bag_formula_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:526`](../QueryTNullSyntax.v#L526)

Purpose/direction: States the bag formula admissible basesort extensional law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_formula_admissible_basesort_extensional :
  forall formula,
    @bag_formula_admissible T generic_relname first_basesort formula ->
    @bag_formula_admissible T generic_relname second_basesort formula.
```

## `query_formula_expr_admissible_basesort_extensional`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:542`](../QueryTNullSyntax.v#L542)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:561`](../QueryTNullSyntax.v#L561)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:569`](../QueryTNullSyntax.v#L569)

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

## `query_sort_equal_symmetry`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:593`](../QueryTNullSyntax.v#L593)

Purpose/direction: States the query sort equal symmetry law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_sort_equal_symmetry` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_sort_equal_symmetry :
  forall left right : Fset.set (A T), left =S= right -> right =S= left.
```

## `query_sort_equal_transitivity`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:601`](../QueryTNullSyntax.v#L601)

Purpose/direction: States the query sort equal transitivity law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_sort_equal_transitivity` direction for projection and tuple-syntax bridging; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`

```rocq
Lemma query_sort_equal_transitivity :
  forall first second third : Fset.set (A T),
    first =S= second -> second =S= third -> first =S= third.
```

## `bag_query_admissible_with_sort_empty_tuple`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:610`](../QueryTNullSyntax.v#L610)

Purpose/direction: States the exact empty-input or empty-result law for projection and tuple-syntax bridging.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_empty_tuple :
  bag_query_admissible_with_sort
    (@Q_Empty_Tuple T generic_relname) (Fset.empty (A T)).
```

## `bag_query_admissible_with_sort_empty_relation`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:617`](../QueryTNullSyntax.v#L617)

Purpose/direction: States the exact empty-input or empty-result law for projection and tuple-syntax bridging.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_empty_relation :
  forall expected_sort,
    bag_query_admissible_with_sort
      (@Q_Empty_Relation T generic_relname expected_sort) expected_sort.
```

## `bag_query_admissible_with_sort_table`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:625`](../QueryTNullSyntax.v#L625)

Purpose/direction: States the bag query admissible with sort table law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_table :
  forall table expected_sort,
    basesort table =S= expected_sort ->
    bag_query_admissible_with_sort
      (@Q_Table T generic_relname table) expected_sort.
```

## `bag_query_admissible_with_sort_set`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:635`](../QueryTNullSyntax.v#L635)

Purpose/direction: States the bag query admissible with sort set law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_set :
  forall operation left right left_sort right_sort,
    bag_query_admissible_with_sort left left_sort ->
    bag_query_admissible_with_sort right right_sort ->
    left_sort =S= right_sort ->
    bag_query_admissible_with_sort
      (@Q_Set T generic_relname operation left right) left_sort.
```

## `bag_query_admissible_with_sort_cross_join`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:653`](../QueryTNullSyntax.v#L653)

Purpose/direction: States the bag query admissible with sort cross join law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_cross_join :
  forall left right left_sort right_sort,
    bag_query_admissible_with_sort left left_sort ->
    bag_query_admissible_with_sort right right_sort ->
    @query_output_sorts_disjoint T left_sort right_sort ->
    bag_query_admissible_with_sort
      (@Q_CrossJoin T generic_relname left right)
      (Fset.union (A T) left_sort right_sort).
```

## `bag_query_admissible_with_sort_project`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:676`](../QueryTNullSyntax.v#L676)

Purpose/direction: States the bag query admissible with sort project law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_project :
  forall select_list input input_sort,
    bag_query_admissible_with_sort input input_sort ->
    query_select_list_outputs_unique select_list ->
    bag_query_admissible_with_sort
      (@Q_Pi T generic_relname select_list input)
      (select_list_sort select_list).
```

## `bag_query_admissible_with_sort_filter`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:688`](../QueryTNullSyntax.v#L688)

Purpose/direction: States the bag query admissible with sort filter law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_filter :
  forall formula input input_sort,
    @bag_formula_admissible T generic_relname basesort formula ->
    bag_query_admissible_with_sort input input_sort ->
    bag_query_admissible_with_sort
      (@Q_Sigma T generic_relname formula input) input_sort.
```

## `bag_query_admissible_with_sort_aggregate`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:699`](../QueryTNullSyntax.v#L699)

Purpose/direction: States the bag query admissible with sort aggregate law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `GROUP BY`, `aggregate`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_query_admissible_with_sort_aggregate :
  forall select_list group_terms having input input_sort,
    group_terms <> nil ->
    @bag_formula_admissible T generic_relname basesort having ->
    bag_query_admissible_with_sort input input_sort ->
    query_select_list_outputs_unique select_list ->
    bag_query_admissible_with_sort
      (@Q_Gamma T generic_relname select_list group_terms having input)
      (select_list_sort select_list).
```

## `bag_formula_in_admissible_from_sort`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:714`](../QueryTNullSyntax.v#L714)

Purpose/direction: States the bag formula in admissible from sort law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_formula_in_admissible_from_sort :
  forall (select_items : list (@select T)) subquery expected_sort,
    bag_query_admissible_with_sort subquery expected_sort ->
    length select_items = 1%nat ->
    length (Fset.elements (A T) expected_sort) = 1%nat ->
    query_in_positionally_aligned (@_Select_List T select_items)
      (Fset.elements (A T) expected_sort) ->
    @bag_formula_admissible T generic_relname basesort
      (@Sql_In T (@query T generic_relname) select_items subquery).
```

## `bag_formula_exists_admissible_from_sort`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:731`](../QueryTNullSyntax.v#L731)

Purpose/direction: States the bag formula exists admissible from sort law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `subquery`, `EXISTS`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_formula_exists_admissible_from_sort :
  forall subquery expected_sort,
    bag_query_admissible_with_sort subquery expected_sort ->
    @bag_formula_admissible T generic_relname basesort
      (@Sql_Exists T (@query T generic_relname) subquery).
```

## `query_expr_bag_admissible_from_sort`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:741`](../QueryTNullSyntax.v#L741)

Purpose/direction: States the query expr bag admissible from sort law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_bag_admissible_from_sort :
  forall (outputs : list (attribute T))
      (query : @query T generic_relname) (expected_sort : Fset.set (A T)),
    @query_output_attributes_unique T outputs ->
    bag_query_admissible_with_sort query expected_sort ->
    @query_outputs_sort T outputs =S= expected_sort ->
    @query_expr_admissible T generic_relname basesort
      (QExpr_Bag outputs query).
```

## `query_expr_admissible_with_outputs_change`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:774`](../QueryTNullSyntax.v#L774)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:785`](../QueryTNullSyntax.v#L785)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:798`](../QueryTNullSyntax.v#L798)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:811`](../QueryTNullSyntax.v#L811)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:822`](../QueryTNullSyntax.v#L822)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:831`](../QueryTNullSyntax.v#L831)

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

## `query_expr_admissible_with_outputs_bag`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:841`](../QueryTNullSyntax.v#L841)

Purpose/direction: States the query expr admissible with outputs bag law for projection and tuple-syntax bridging, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about projection and tuple-syntax bridging.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_admissible_with_outputs_bag :
  forall (outputs : list (attribute T)) query expected_sort,
    @query_output_attributes_unique T outputs ->
    @bag_query_admissible_with_sort T generic_relname basesort
      query expected_sort ->
    @query_outputs_sort T outputs =S= expected_sort ->
    query_expr_admissible_with_outputs
      (@QExpr_Bag T generic_relname outputs query) outputs.
```

## `query_expr_admissible_with_outputs_set`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:858`](../QueryTNullSyntax.v#L858)

Purpose/direction: States the query expr admissible with outputs set law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_expr_admissible_with_outputs_set` direction for SQL bag/set operations; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `query syntax bridge`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:875`](../QueryTNullSyntax.v#L875)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:890`](../QueryTNullSyntax.v#L890)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:910`](../QueryTNullSyntax.v#L910)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:936`](../QueryTNullSyntax.v#L936)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:948`](../QueryTNullSyntax.v#L948)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:960`](../QueryTNullSyntax.v#L960)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:974`](../QueryTNullSyntax.v#L974)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:989`](../QueryTNullSyntax.v#L989)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1001`](../QueryTNullSyntax.v#L1001)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1025`](../QueryTNullSyntax.v#L1025)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1054`](../QueryTNullSyntax.v#L1054)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1064`](../QueryTNullSyntax.v#L1064)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1078`](../QueryTNullSyntax.v#L1078)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1088`](../QueryTNullSyntax.v#L1088)

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

## `formula_expr_quant_admissible_from_outputs`

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1098`](../QueryTNullSyntax.v#L1098)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1115`](../QueryTNullSyntax.v#L1115)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1136`](../QueryTNullSyntax.v#L1136)

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

Source: [`theories/FormalSQL/QueryTNullSyntax.v:1150`](../QueryTNullSyntax.v#L1150)

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
