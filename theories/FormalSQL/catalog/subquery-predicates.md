# Predicate subqueries and correlation

Route here for: EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/scalar-expression goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality.

This focused catalog contains 93 declarations routed at declaration granularity from `CorrelatedMembershipFacts.v`, `MembershipCompositionFacts.v`, `SubqueryFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `interp_direct_attribute_in_env_t_absent`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:23`](../CorrelatedMembershipFacts.v#L23)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that an attribute absent from the current row of an environment extension is resolved from the retained outer environment.

Applicability: Use when the goal or a hypothesis matches the `interp_direct_attribute_in_env_t_absent` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `schema`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `schema conformance`, `typing`, `correlation`, `environment shadowing`, `attribute lookup`

```rocq
Lemma interp_direct_attribute_in_env_t_absent :
  forall (T : Tuple.Rcd) env row attribute,
    (attribute inS? labels T row) = false ->
    interp_aggterm T (env_t T env row)
      (@A_Expr T (@F_Dot T attribute)) =
    interp_aggterm T env (@A_Expr T (@F_Dot T attribute)).
```

## `correlated_inner_guard_relation_of_outer_match`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:40`](../CorrelatedMembershipFacts.v#L40)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports one reached outer-to-inner semantic match to the reversed correlated guard while retaining row presence, shadowing, and symmetry premises.

Applicability: Use when the goal or a hypothesis matches the `correlated_inner_guard_relation_of_outer_match` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `inner guard`, `outer match`, `semantic tuple equality`

```rocq
Theorem correlated_inner_guard_relation_of_outer_match :
  forall (T : Tuple.Rcd) (relation : value T -> value T -> Prop)
      base_env outer_row inner_row outer_attribute inner_attribute,
    (forall left right, relation left right -> relation right left) ->
    relation
      (dot T outer_row outer_attribute)
      (dot T inner_row inner_attribute) ->
    inner_attribute inS labels T inner_row ->
    (outer_attribute inS? labels T inner_row) = false ->
    outer_attribute inS labels T outer_row ->
    relation
      (interp_aggterm T
        (env_t T (env_t T base_env outer_row) inner_row)
        (@A_Expr T (@F_Dot T inner_attribute)))
      (interp_aggterm T
        (env_t T (env_t T base_env outer_row) inner_row)
        (@A_Expr T (@F_Dot T outer_attribute))).
```

## `NoDupA_bidirectionally_related_members_eq`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:73`](../CorrelatedMembershipFacts.v#L73)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies two represented occurrences only after NoDupA and both directions of the caller-supplied semantic relation are proved.

Applicability: Use when the goal or a hypothesis matches the `NoDupA_bidirectionally_related_members_eq` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `semantic support`, `duplicate elimination`, `NoDupA`

```rocq
Lemma NoDupA_bidirectionally_related_members_eq :
  forall (A : Type) (relation : A -> A -> Prop) values left right,
    NoDupA relation values ->
    In left values ->
    In right values ->
    relation left right ->
    relation right left ->
    left = right.
```

## `key_unique_self_filter_existsb_exact`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:100`](../CorrelatedMembershipFacts.v#L100)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Computes filtered self-membership from an actual semantic self witness and occurrence-sensitive key uniqueness; the primary-key form also exposes NOT NULL.

Applicability: Use when the goal or a hypothesis matches the `key_unique_self_filter_existsb_exact` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `schema`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `integrity constraint`, `key`, `unique key`, `self membership`, `semantic tuple equality`

```rocq
Theorem key_unique_self_filter_existsb_exact :
  forall (Row Key : Type) (key_relation : Key -> Key -> Prop)
      (key_of : Row -> Key) rows (keep matches : Row -> bool) outer,
    NoDupA key_relation (map key_of rows) ->
    In outer rows ->
    matches outer = true ->
    (forall candidate,
      In candidate rows ->
      matches candidate = true ->
      key_relation (key_of outer) (key_of candidate)) ->
    (forall candidate,
      In candidate rows ->
      key_relation (key_of outer) (key_of candidate) ->
      key_relation (key_of candidate) (key_of outer)) ->
    existsb matches (filter keep rows) = keep outer.
```

## `primary_key_self_filter_existsb_exact`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:146`](../CorrelatedMembershipFacts.v#L146)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Computes filtered self-membership from an actual semantic self witness and occurrence-sensitive key uniqueness; the primary-key form also exposes NOT NULL.

Applicability: Use when the goal or a hypothesis matches the `primary_key_self_filter_existsb_exact` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `schema`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `schema conformance`, `typing`, `integrity constraint`, `key`, `primary key`, `self membership`, `NOT NULL`

```rocq
Theorem primary_key_self_filter_existsb_exact :
  forall key rows (keep matches : tuple TNull -> bool) outer,
    primary_key_conforms key rows ->
    In outer rows ->
    matches outer = true ->
    (forall candidate,
      In candidate rows ->
      matches candidate = true ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate) ->
      sql_key_equal_true
        (SchemaConstraints.project_row key candidate)
        (SchemaConstraints.project_row key outer)) ->
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (SchemaConstraints.project_row key outer) /\
    existsb matches (filter keep rows) = keep outer.
```

## `tnull_in_rows_unknown_iff`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:26`](../MembershipCompositionFacts.v#L26)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes TNull IN UNKNOWN as at least one UNKNOWN candidate comparison and no TRUE candidate, over the canonical bag representative.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `IN`, `semantic tuple equality`, `duplicates`

```rocq
Lemma tnull_in_rows_unknown_iff :
  forall values (subquery : query_expr TNull relname) rows,
    @in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery rows = unknown3 <->
    Exists
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = unknown3)
      (@query_canonical_rows TNull rows) /\
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row <> true3)
      (@query_canonical_rows TNull rows).
```

## `tnull_in_rows_semantic_cases`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:46`](../MembershipCompositionFacts.v#L46)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Partitions TNull IN into empty/FALSE, TRUE-match, UNKNOWN-without-match, and nonempty-all-FALSE cases without replacing SQL tuple comparison by Rocq equality.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `IN`, `empty input`, `TRUE FALSE UNKNOWN`, `duplicates`

```rocq
Theorem tnull_in_rows_semantic_cases :
  forall values (subquery : query_expr TNull relname) rows,
    ((@query_canonical_rows TNull rows = nil) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = false3) \/
    ((exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = true3) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = true3) \/
    ((Exists
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row <> true3)
        (@query_canonical_rows TNull rows)) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = unknown3) \/
    ((@query_canonical_rows TNull rows <> nil) /\
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = false3)
        (@query_canonical_rows TNull rows) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = false3).
```

## `tnull_not_in_rows_acceptance_iff_all_false`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:106`](../MembershipCompositionFacts.v#L106)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes TNull NOT IN acceptance by all candidate comparisons being FALSE, equivalently by absence of both a TRUE match and an UNKNOWN comparison.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `NOT IN`, `all comparisons FALSE`, `empty input`

```rocq
Theorem tnull_not_in_rows_acceptance_iff_all_false :
  forall values (subquery : query_expr TNull relname) rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
          values subquery rows)) = true <->
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = false3)
      (@query_canonical_rows TNull rows).
```

## `tnull_not_in_rows_acceptance_iff_no_true_or_unknown`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:128`](../MembershipCompositionFacts.v#L128)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes TNull NOT IN acceptance by all candidate comparisons being FALSE, equivalently by absence of both a TRUE match and an UNKNOWN comparison.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `NOT IN`, `anti existence`, `NULL marker`

```rocq
Theorem tnull_not_in_rows_acceptance_iff_no_true_or_unknown :
  forall values (subquery : query_expr TNull relname) rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
          values subquery rows)) = true <->
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery row = true3) /\
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery row = unknown3).
```

## `query_distinct_rows_support_rel`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:218`](../MembershipCompositionFacts.v#L218)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates every legal DISTINCT output representative bidirectionally to the input's semantic row support without preserving duplicate counts.

Applicability: Use only for duplicate-insensitive support or IN TRUE-acceptance.  DISTINCT changes row multiplicity and may not be erased for COUNT, bags, exact ordered results, or full FALSE/UNKNOWN truth without additional premises.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `DISTINCT`, `duplicate elimination`, `bag semantics`, `list/bag bridge`, `semantic support`, `duplicates`, `IN`

```rocq
Theorem query_distinct_rows_support_rel :
  forall input output,
    query_same_rows_as_bag output
      (query_distinct_bag (query_rows_bag input)) ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      output input.
```

## `in_rows_acceptance_distinct`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:264`](../MembershipCompositionFacts.v#L264)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows SQL IN TRUE-acceptance is unchanged by DISTINCT candidate elimination while leaving the underlying row multiplicities distinct.

Applicability: Use only for duplicate-insensitive support or IN TRUE-acceptance.  DISTINCT changes row multiplicity and may not be erased for COUNT, bags, exact ordered results, or full FALSE/UNKNOWN truth without additional premises.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `DISTINCT`, `duplicate elimination`, `filter acceptance`, `duplicate-insensitive`

```rocq
Theorem in_rows_acceptance_distinct :
  forall values (subquery : query_expr T relname) input output,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) input ->
    query_same_rows_as_bag output
      (query_distinct_bag (query_rows_bag input)) ->
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null
        values subquery output) =
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null
        values subquery input).
```

## `tnull_scalar_expr_not_in_accepts_exact_of_all_false`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:328`](../MembershipCompositionFacts.v#L328)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts the displayed TNull NOT IN semantic case to exact scalar-expression acceptance at one correlated environment, retaining argument and child error premises.

Applicability: Use at one fixed correlated environment after proving argument safety, child-success inhabitation, the displayed case for every legal child success, and exclusion of every child error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `correlation`, `exact acceptance`, `runtime error`

```rocq
Theorem tnull_scalar_expr_not_in_accepts_exact_of_all_false :
  forall env arguments subquery,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = false3)
        (@query_canonical_rows TNull rows)) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery)) true.
```

## `tnull_scalar_expr_not_in_rejects_exact_of_true_match`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:374`](../MembershipCompositionFacts.v#L374)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts the displayed TNull NOT IN semantic case to exact scalar-expression acceptance at one correlated environment, retaining argument and child error premises.

Applicability: Use at one fixed correlated environment after proving argument safety, child-success inhabitation, the displayed case for every legal child success, and exclusion of every child error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `TRUE match`, `exact rejection`, `runtime error`

```rocq
Theorem tnull_scalar_expr_not_in_rejects_exact_of_true_match :
  forall env arguments subquery,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = true3) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery)) false.
```

## `tnull_scalar_expr_not_in_rejects_exact_of_unknown_without_match`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:410`](../MembershipCompositionFacts.v#L410)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts the displayed TNull NOT IN semantic case to exact scalar-expression acceptance at one correlated environment, retaining argument and child error premises.

Applicability: Use at one fixed correlated environment after proving argument safety, child-success inhabitation, the displayed case for every legal child success, and exclusion of every child error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `UNKNOWN without match`, `exact rejection`, `runtime error`

```rocq
Theorem tnull_scalar_expr_not_in_rejects_exact_of_unknown_without_match :
  forall env arguments subquery,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      Exists
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row <> true3)
        (@query_canonical_rows TNull rows)) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery)) false.
```

## `interp_exists_quant_not_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:20`](../SubqueryFacts.v#L20)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma interp_exists_quant_not_true_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    Bool.existsb Bool3 interpretation values <> true3 <->
    Forall (fun value => interpretation value <> true3) values.
```

## `interp_forall_quant_not_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:37`](../SubqueryFacts.v#L37)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma interp_forall_quant_not_false_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    Bool.forallb Bool3 interpretation values <> false3 <->
    Forall (fun value => interpretation value <> false3) values.
```

## `interp_exists_quant_unknown_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:55`](../SubqueryFacts.v#L55)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma interp_exists_quant_unknown_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    interp_quant Bool3 Exists_F interpretation values = unknown3 <->
    Exists (fun value => interpretation value = unknown3) values /\
    Forall (fun value => interpretation value <> true3) values.
```

## `interp_forall_quant_unknown_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:92`](../SubqueryFacts.v#L92)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma interp_forall_quant_unknown_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    interp_quant Bool3 Forall_F interpretation values = unknown3 <->
    Exists (fun value => interpretation value = unknown3) values /\
    Forall (fun value => interpretation value <> false3) values.
```

## `interp_quant_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:129`](../SubqueryFacts.v#L129)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `interp_quant_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

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

Source: [`theories/FormalSQL/SubqueryFacts.v:149`](../SubqueryFacts.v#L149)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `rows_empty_decision_rel_permut` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma rows_empty_decision_rel_permut :
  forall (A B : Type) (R : A -> B -> Prop) left right,
    _permut R left right ->
    rows_empty_decision left = rows_empty_decision right.
```

## `rows_empty_decision_oeset_permut`

Source: [`theories/FormalSQL/SubqueryFacts.v:161`](../SubqueryFacts.v#L161)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `rows_empty_decision_oeset_permut` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Corollary rows_empty_decision_oeset_permut :
  forall (A : Type) (order : Oeset.Rcd A) left right,
    Oeset.permut order left right ->
    rows_empty_decision left = rows_empty_decision right.
```

## `existsb_rel_permut`

Source: [`theories/FormalSQL/SubqueryFacts.v:175`](../SubqueryFacts.v#L175)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the existsb rel permut law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `existsb_rel_permut` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

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

## `existsb_support_rel`

Source: [`theories/FormalSQL/SubqueryFacts.v:201`](../SubqueryFacts.v#L201)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that a Boolean existence observation is invariant under bidirectional relational support when the tested predicates agree on related representatives; multiplicity is intentionally ignored.

Applicability: Use only for a Boolean existence consumer after proving bidirectional support and predicate properness.  It does not preserve counts, list order, evaluation effects, or a three-valued predicate result.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `bag semantics`, `list/bag bridge`, `support`, `duplicate-insensitive existence`

```rocq
Lemma existsb_support_rel :
  forall (A B : Type) (R : A -> B -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      left_predicate left_value = right_predicate right_value) ->
    list_support_rel R left right ->
    existsb left_predicate left = existsb right_predicate right.
```

## `scalar_expr_truth_exact_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:303`](../SubqueryFacts.v#L303)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Projects an inhabited, unique exact Bool3 success with no reachable runtime error to its SQL TRUE-acceptance bit.

Applicability: Use only with the displayed exact-truth contract: it includes one successful observation, uniqueness of the full Bool3 truth, and exclusion of every runtime error at the same environment.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `exact Bool3 truth`, `UNKNOWN`, `runtime error`

```rocq
Lemma scalar_expr_truth_exact_acceptance_exact :
  forall env formula expected,
    scalar_expr_truth_exact_at env formula expected ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env formula
      (Bool.is_true (B T) expected).
```

## `scalar_expr_not_truth_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:322`](../SubqueryFacts.v#L322)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports an inhabited, error-free exact Bool3 observation through SQL NOT; in particular, UNKNOWN remains UNKNOWN.

Applicability: Use only with the displayed exact-truth contract: it includes one successful observation, uniqueness of the full Bool3 truth, and exclusion of every runtime error at the same environment.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `SQL NOT`, `exact Bool3 truth`, `UNKNOWN`

```rocq
Theorem scalar_expr_not_truth_exact :
  forall env formula expected,
    scalar_expr_truth_exact_at env formula expected ->
    scalar_expr_truth_exact_at env (SExpr_Not formula)
      (Bool.negb (B T) expected).
```

## `scalar_expr_not_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:339`](../SubqueryFacts.v#L339)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Derives exact acceptance for SQL NOT from the stronger exact-truth contract, without complementing a FALSE/UNKNOWN acceptance bit.

Applicability: Use only with the displayed exact-truth contract: it includes one successful observation, uniqueness of the full Bool3 truth, and exclusion of every runtime error at the same environment.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `SQL NOT`, `UNKNOWN`, `filter acceptance`

```rocq
Corollary scalar_expr_not_acceptance_exact :
  forall env formula expected,
    scalar_expr_truth_exact_at env formula expected ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Not formula)
      (Bool.is_true (B T) (Bool.negb (B T) expected)).
```

## `eval_scalar_boolean_operands_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:376`](../SubqueryFacts.v#L376)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_operands_env_congr :
  forall left_env right_env operation expressions,
    Forall
      (scalar_expr_env_outcome_equiv left_env right_env) expressions ->
    forall outcome,
      eval_scalar_operands left_env operation expressions outcome <->
      eval_scalar_operands right_env operation expressions outcome.
```

## `scalar_expr_conj_list_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:413`](../SubqueryFacts.v#L413)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_conj_list_env_congr :
  forall left_env right_env site_rows operation expressions,
    Forall
      (scalar_expr_env_outcome_equiv left_env right_env) expressions ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_ConjList site_rows operation expressions).
```

## `scalar_expr_not_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:444`](../SubqueryFacts.v#L444)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_not_env_congr :
  forall left_env right_env formula,
    scalar_expr_env_outcome_equiv left_env right_env formula ->
    scalar_expr_env_outcome_equiv left_env right_env (SExpr_Not formula).
```

## `scalar_expr_pred_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:457`](../SubqueryFacts.v#L457)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_pred_env_congr_safe :
  forall left_env right_env predicate arguments,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_Pred predicate arguments).
```

## `query_expr_table_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:477`](../SubqueryFacts.v#L477)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_expr_table_env_congr :
  forall left_env right_env attributes relation,
    query_expr_env_outcome_equiv left_env right_env
      (@QExpr_Table T relname attributes relation).
```

## `query_expr_cross_join_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:486`](../SubqueryFacts.v#L486)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `join`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `join`, `cross product`, `CROSS JOIN`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_env_congr :
  forall left_env right_env left right,
    query_expr_env_outcome_equiv left_env right_env left ->
    query_expr_env_outcome_equiv left_env right_env right ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_CrossJoin left right).
```

## `eval_filter_rows_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:537`](../SubqueryFacts.v#L537)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `filter`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_env_congr :
  forall left_env right_env formula,
    (forall row,
      scalar_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    forall rows outcome,
      eval_filter_rows left_env formula rows outcome <->
      eval_filter_rows right_env formula rows outcome.
```

## `query_expr_filter_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:560`](../SubqueryFacts.v#L560)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `filter`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_env_congr :
  forall left_env right_env formula input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      scalar_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Filter formula input).
```

## `quantified_rows_truth_congr_of_bag_eq`

Source: [`theories/FormalSQL/SubqueryFacts.v:615`](../SubqueryFacts.v#L615)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem quantified_rows_truth_congr_of_bag_eq :
  forall which_quantifier which_predicate values subquery left right
      (property : tuple T -> Prop),
    @bag_eq T (query_rows_bag left) (query_rows_bag right) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      (property first <-> property second)) ->
    Forall property (query_canonical_rows left) ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      property left_row ->
      quantified_row_truth which_predicate values subquery left_row =
      quantified_row_truth which_predicate values subquery right_row) ->
    quantified_rows_truth which_quantifier which_predicate values
      subquery left =
    quantified_rows_truth which_quantifier which_predicate values
      subquery right.
```

## `query_row_has_outputs_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:677`](../SubqueryFacts.v#L677)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_row_has_outputs_congr :
  forall outputs left right,
    Oeset.compare (OTuple T) left right = Eq ->
    query_row_has_outputs outputs left ->
    query_row_has_outputs outputs right.
```

## `query_row_output_values_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:690`](../SubqueryFacts.v#L690)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_row_output_values_congr :
  forall outputs left right,
    query_row_has_outputs outputs left ->
    Oeset.compare (OTuple T) left right = Eq ->
    @query_row_output_values T outputs left =
    @query_row_output_values T outputs right.
```

## `in_row_truth_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:708`](../SubqueryFacts.v#L708)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma in_row_truth_congr :
  forall values subquery left right,
    query_row_has_outputs (query_expr_outputs subquery) left ->
    Oeset.compare (OTuple T) left right = Eq ->
    in_row_truth values subquery left = in_row_truth values subquery right.
```

## `relational_permut_Forall_backward`

Source: [`theories/FormalSQL/SubqueryFacts.v:720`](../SubqueryFacts.v#L720)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the relational permut forall backward law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `relational_permut_Forall_backward` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma relational_permut_Forall_backward :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop) (Q : B -> Prop)
      left right,
    (forall left_value right_value,
      R left_value right_value -> Q right_value -> P left_value) ->
    _permut R left right ->
    Forall Q right ->
    Forall P left.
```

## `query_canonical_rows_has_outputs`

Source: [`theories/FormalSQL/SubqueryFacts.v:748`](../SubqueryFacts.v#L748)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query canonical rows has outputs law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_canonical_rows_has_outputs` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma query_canonical_rows_has_outputs :
  forall outputs rows,
    Forall (query_row_has_outputs outputs) rows ->
    Forall (query_row_has_outputs outputs) (query_canonical_rows rows).
```

## `existsb_rel_permut_with_left_property`

Source: [`theories/FormalSQL/SubqueryFacts.v:773`](../SubqueryFacts.v#L773)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the existsb rel permut with left property law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `existsb_rel_permut_with_left_property` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma existsb_rel_permut_with_left_property :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      P left_value ->
      left_predicate left_value = right_predicate right_value) ->
    _permut R left right ->
    Forall P left ->
    existsb left_predicate left = existsb right_predicate right.
```

## `existsb_support_rel_with_left_property`

Source: [`theories/FormalSQL/SubqueryFacts.v:800`](../SubqueryFacts.v#L800)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the existsb support rel with left property law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `existsb_support_rel_with_left_property` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `bag semantics`, `list/bag bridge`

```rocq
Lemma existsb_support_rel_with_left_property :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      P left_value ->
      left_predicate left_value = right_predicate right_value) ->
    list_support_rel R left right ->
    Forall P left ->
    existsb left_predicate left = existsb right_predicate right.
```

## `in_rows_acceptance_existsb`

Source: [`theories/FormalSQL/SubqueryFacts.v:841`](../SubqueryFacts.v#L841)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Reduces only the TRUE-acceptance observation of SQL IN over a row bag to an ordinary Boolean existence test, retaining the underlying FALSE/UNKNOWN distinction.

Applicability: Use after proving the per-candidate `Bool.is_true` decision.  The conclusion is suitable for WHERE or semijoin filtering only; it is not equality of the complete SQL Bool3 result.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `join`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_acceptance_existsb :
  forall values subquery rows (accept : tuple T -> bool),
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) rows ->
    (forall row,
      Bool.is_true (B T) (in_row_truth values subquery row) = accept row) ->
    Bool.is_true (B T) (in_rows_truth values subquery rows) =
    existsb accept rows.
```

## `in_rows_acceptance_support_rel`

Source: [`theories/FormalSQL/SubqueryFacts.v:898`](../SubqueryFacts.v#L898)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports only SQL IN TRUE-acceptance across duplicate-insensitive support correspondence under FormalSQL semantic tuple equality.

Applicability: Use only at an IN TRUE-acceptance boundary after candidate-query success/error behavior has been handled separately.  Do not use it to prove full Bool3 equality, NOT IN, multiplicity, or ordered outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `bag semantics`, `list/bag bridge`, `semantic tuple equality`, `duplicate-insensitive support`

```rocq
Theorem in_rows_acceptance_support_rel :
  forall values subquery left right,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) left ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) right ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    Bool.is_true (B T) (in_rows_truth values subquery left) =
    Bool.is_true (B T) (in_rows_truth values subquery right).
```

## `in_rows_acceptance_append`

Source: [`theories/FormalSQL/SubqueryFacts.v:940`](../SubqueryFacts.v#L940)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Distributes SQL IN TRUE-acceptance over appended candidate lists as Boolean OR without equating the underlying FALSE and UNKNOWN truths.

Applicability: Use only at an IN TRUE-acceptance boundary after candidate-query success/error behavior has been handled separately.  Do not use it to prove full Bool3 equality, NOT IN, multiplicity, or ordered outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `UNION`, `filter acceptance`

```rocq
Theorem in_rows_acceptance_append :
  forall values subquery left right,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) left ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) right ->
    Bool.is_true (B T)
      (in_rows_truth values subquery (left ++ right)) =
    Datatypes.orb
      (Bool.is_true (B T) (in_rows_truth values subquery left))
      (Bool.is_true (B T) (in_rows_truth values subquery right)).
```

## `query_same_rows_as_bag_empty_decision`

Source: [`theories/FormalSQL/SubqueryFacts.v:973`](../SubqueryFacts.v#L973)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_empty_decision :
  forall first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    rows_empty_decision first = rows_empty_decision second.
```

## `quantified_rows_exists_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:996`](../SubqueryFacts.v#L996)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_exists_true_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Exists_F which_predicate values subquery rows =
      Bool.true (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth which_predicate values subquery row =
          Bool.true (B T).
```

## `quantified_rows_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1009`](../SubqueryFacts.v#L1009)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_exists_false_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Exists_F which_predicate values subquery rows =
      Bool.false (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth which_predicate values subquery row =
          Bool.false (B T).
```

## `quantified_rows_forall_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1022`](../SubqueryFacts.v#L1022)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_forall_true_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Forall_F which_predicate values subquery rows =
      Bool.true (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth which_predicate values subquery row =
          Bool.true (B T).
```

## `quantified_rows_forall_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1035`](../SubqueryFacts.v#L1035)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_forall_false_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Forall_F which_predicate values subquery rows =
      Bool.false (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth which_predicate values subquery row =
          Bool.false (B T).
```

## `in_rows_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1048`](../SubqueryFacts.v#L1048)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_true_iff : forall values subquery rows,
  in_rows_truth values subquery rows = Bool.true (B T) <->
  exists row,
    In row (query_canonical_rows rows) /\
    in_row_truth values subquery row = Bool.true (B T).
```

## `in_rows_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1058`](../SubqueryFacts.v#L1058)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_false_iff : forall values subquery rows,
  in_rows_truth values subquery rows = Bool.false (B T) <->
  forall row,
    In row (query_canonical_rows rows) ->
    in_row_truth values subquery row = Bool.false (B T).
```

## `query_canonical_rows_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1068`](../SubqueryFacts.v#L1068)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `query_canonical_rows_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma query_canonical_rows_empty :
  @query_canonical_rows T [] = [].
```

## `eval_scalar_value_subquery_outcome_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1078`](../SubqueryFacts.v#L1078)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `outcome`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_scalar_value_subquery_outcome_iff :
  forall env result_type null_value subquery outcome,
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery) outcome <->
    value_is_null null_value = true /\
    exists query_outcome,
      eval_query env subquery query_outcome /\
      @scalar_subquery_value_outcome T null_value
        (query_expr_outputs subquery) query_outcome = outcome.
```

## `eval_scalar_value_subquery_child_error`

Source: [`theories/FormalSQL/SubqueryFacts.v:1100`](../SubqueryFacts.v#L1100)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Exposes the modeled SQL error condition or propagation direction for predicate-subquery evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_scalar_value_subquery_child_error :
  forall env result_type null_value subquery error,
    value_is_null null_value = true ->
    eval_query env subquery (SqlError error) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery) (SqlError error).
```

## `eval_scalar_value_subquery_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1114`](../SubqueryFacts.v#L1114)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_scalar_value_subquery_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`

```rocq
Lemma eval_scalar_value_subquery_empty :
  forall env result_type null_value subquery,
    value_is_null null_value = true ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery)
      (SqlSuccess null_value).
```

## `eval_scalar_value_subquery_singleton`

Source: [`theories/FormalSQL/SubqueryFacts.v:1129`](../SubqueryFacts.v#L1129)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the eval scalar value subquery singleton law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `eval_scalar_value_subquery_singleton` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`

```rocq
Lemma eval_scalar_value_subquery_singleton :
  forall env result_type null_value subquery output row,
    query_expr_outputs subquery = [output] ->
    value_is_null null_value = true ->
    eval_query env subquery (SqlSuccess [row]) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery)
      (SqlSuccess (dot T row output)).
```

## `eval_scalar_value_subquery_cardinality_violation`

Source: [`theories/FormalSQL/SubqueryFacts.v:1147`](../SubqueryFacts.v#L1147)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates predicate-subquery evaluation to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_scalar_value_subquery_cardinality_violation :
  forall env result_type null_value subquery first second rest,
    value_is_null null_value = true ->
    eval_query env subquery (SqlSuccess (first :: second :: rest)) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery)
      (SqlError CardinalityViolation).
```

## `eval_scalar_boolean_quant_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1163`](../SubqueryFacts.v#L1163)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for scalar-subquery quantified-comparison evaluation.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `scalar subquery`, `SINGLE_VALUE`, `CardinalityViolation`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_scalar_boolean_quant_error_iff :
  forall env which_quantifier which_predicate arguments subquery error,
    eval_scalar_boolean env
      (SExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlError error) <->
    eval_scalar_values env arguments (SqlError error) \/
    exists values,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlError error).
```

## `eval_scalar_boolean_quant_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1182`](../SubqueryFacts.v#L1182)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for scalar-subquery quantified-comparison evaluation.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `scalar subquery`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_scalar_boolean_quant_success_iff :
  forall env which_quantifier which_predicate arguments subquery truth,
    eval_scalar_boolean env
      (SExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlSuccess truth) <->
    exists values rows,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = quantified_rows_truth which_quantifier which_predicate
        values subquery rows.
```

## `scalar_expr_quant_acceptance_exact_of_fixed_truth`

Source: [`theories/FormalSQL/SubqueryFacts.v:1205`](../SubqueryFacts.v#L1205)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the scalar expr quant acceptance exact of fixed truth law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem scalar_expr_quant_acceptance_exact_of_fixed_truth :
  forall env quantifier predicate arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      quantified_rows_truth quantifier predicate values
        subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Quant quantifier predicate arguments subquery)
      (Bool.is_true (B T) fixed_truth).
```

## `eval_scalar_boolean_quant_forall_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1248`](../SubqueryFacts.v#L1248)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_scalar_boolean_quant_forall_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_scalar_boolean_quant_forall_empty :
  forall env which_predicate arguments subquery values,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_boolean env
      (SExpr_Quant Forall_F which_predicate arguments subquery)
      (SqlSuccess (Bool.true (B T))).
```

## `eval_scalar_boolean_quant_exists_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1263`](../SubqueryFacts.v#L1263)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_scalar_boolean_quant_exists_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_scalar_boolean_quant_exists_empty :
  forall env which_predicate arguments subquery values,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_boolean env
      (SExpr_Quant Exists_F which_predicate arguments subquery)
      (SqlSuccess (Bool.false (B T))).
```

## `eval_scalar_boolean_in_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1278`](../SubqueryFacts.v#L1278)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_scalar_boolean_in_error_iff :
  forall env arguments subquery error,
    eval_scalar_boolean env (SExpr_In arguments subquery) (SqlError error) <->
    eval_scalar_values env arguments (SqlError error) \/
    exists values,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlError error).
```

## `eval_scalar_boolean_in_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1295`](../SubqueryFacts.v#L1295)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma eval_scalar_boolean_in_success_iff :
  forall env arguments subquery truth,
    eval_scalar_boolean env (SExpr_In arguments subquery) (SqlSuccess truth) <->
    exists values rows,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = in_rows_truth values subquery rows.
```

## `eval_scalar_boolean_in_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1310`](../SubqueryFacts.v#L1310)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_scalar_boolean_in_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma eval_scalar_boolean_in_empty :
  forall env arguments subquery values,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_boolean env (SExpr_In arguments subquery)
      (SqlSuccess (Bool.false (B T))).
```

## `scalar_expr_in_truth_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1328`](../SubqueryFacts.v#L1328)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Builds exact tuple-valued IN truth from runtime-safe arguments, an inhabited child, fixed Bool3 truth across every child success, and no errors.

Applicability: Use after proving argument safety, child-success inhabitation, one fixed full Bool3 IN truth across all legal child observations, and absence of child errors; an acceptance bit alone cannot justify NOT IN.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `exact Bool3 truth`, `UNKNOWN`

```rocq
Theorem scalar_expr_in_truth_exact :
  forall env arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth values subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_truth_exact_at env (SExpr_In arguments subquery) fixed_truth.
```

## `scalar_expr_in_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1367`](../SubqueryFacts.v#L1367)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Builds exact tuple-valued IN acceptance from pointwise SQL equality decisions while retaining empty inputs, duplicates, UNKNOWN, and errors.

Applicability: Use at a filter/join acceptance boundary with the pointwise tuple-IN decision and every displayed child/no-error premise; FALSE and UNKNOWN may share rejection but remain distinct semantic truths.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `UNKNOWN`, `filter acceptance`

```rocq
Theorem scalar_expr_in_acceptance_exact :
  forall env arguments subquery
      (accept : list (value T) -> tuple T -> bool) accepted,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs (query_expr_outputs subquery)) rows) ->
    (forall values,
      eval_scalar_values env arguments (SqlSuccess values) ->
      forall row,
        Bool.is_true (B T) (in_row_truth values subquery row) =
        accept values row) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      existsb (accept values) rows = accepted) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_In arguments subquery) accepted.
```

## `scalar_expr_not_in_acceptance_exact_of_fixed_truth`

Source: [`theories/FormalSQL/SubqueryFacts.v:1428`](../SubqueryFacts.v#L1428)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Builds NOT IN acceptance only from fixed exact IN truth, applying SQL negation before TRUE projection so UNKNOWN is never accepted.

Applicability: Use after proving argument safety, child-success inhabitation, one fixed full Bool3 IN truth across all legal child observations, and absence of child errors; an acceptance bit alone cannot justify NOT IN.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `exact Bool3 truth`, `UNKNOWN`, `runtime error`

```rocq
Theorem scalar_expr_not_in_acceptance_exact_of_fixed_truth :
  forall env arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth values subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery))
      (Bool.is_true (B T) (Bool.negb (B T) fixed_truth)).
```

## `eval_scalar_boolean_exists_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1451`](../SubqueryFacts.v#L1451)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_scalar_boolean_exists_error_iff : forall env subquery error,
  eval_scalar_boolean env (SExpr_Exists subquery) (SqlError error) <->
  eval_exists env subquery (SqlError error).
```

## `eval_scalar_boolean_exists_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1460`](../SubqueryFacts.v#L1460)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_scalar_boolean_exists_success_iff : forall env subquery truth,
  eval_scalar_boolean env (SExpr_Exists subquery) (SqlSuccess truth) <->
  eval_exists env subquery (SqlSuccess truth).
```

## `eval_scalar_boolean_exists_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1472`](../SubqueryFacts.v#L1472)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    forall outcome,
      eval_scalar_boolean left_env (SExpr_Exists subquery) outcome <->
      eval_scalar_boolean right_env (SExpr_Exists subquery) outcome.
```

## `scalar_expr_exists_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1488`](../SubqueryFacts.v#L1488)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_Exists subquery).
```

## `eval_scalar_boolean_quant_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1504`](../SubqueryFacts.v#L1504)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_quant_env_congr_safe :
  forall left_env right_env which_quantifier which_predicate
      arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_scalar_boolean left_env
        (SExpr_Quant which_quantifier which_predicate arguments subquery)
        outcome <->
      eval_scalar_boolean right_env
        (SExpr_Quant which_quantifier which_predicate arguments subquery)
        outcome.
```

## `scalar_expr_quant_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1544`](../SubqueryFacts.v#L1544)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_quant_env_congr_safe :
  forall left_env right_env which_quantifier which_predicate
      arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    query_expr_env_outcome_equiv left_env right_env subquery ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_Quant which_quantifier which_predicate arguments subquery).
```

## `eval_scalar_boolean_in_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1562`](../SubqueryFacts.v#L1562)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_in_env_congr_safe :
  forall left_env right_env arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_scalar_boolean left_env (SExpr_In arguments subquery) outcome <->
      eval_scalar_boolean right_env (SExpr_In arguments subquery) outcome.
```

## `scalar_expr_in_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1595`](../SubqueryFacts.v#L1595)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma scalar_expr_in_env_congr_safe :
  forall left_env right_env arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    query_expr_env_outcome_equiv left_env right_env subquery ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_In arguments subquery).
```

## `eval_scalar_boolean_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1608`](../SubqueryFacts.v#L1608)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_scalar_boolean_exists_false_iff : forall env subquery,
  eval_scalar_boolean env (SExpr_Exists subquery)
    (SqlSuccess (Bool.false (B T))) <->
  eval_exists env subquery (SqlSuccess (Bool.false (B T))).
```

## `eval_scalar_boolean_exists_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1618`](../SubqueryFacts.v#L1618)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_scalar_boolean_exists_true_iff : forall env subquery,
  eval_scalar_boolean env (SExpr_Exists subquery)
    (SqlSuccess (Bool.true (B T))) <->
  eval_exists env subquery (SqlSuccess (Bool.true (B T))).
```

## `exists_truth_from_empty_negation_acceptance`

Source: [`theories/FormalSQL/SubqueryFacts.v:1643`](../SubqueryFacts.v#L1643)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `exists_truth_from_empty_negation_acceptance` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma exists_truth_from_empty_negation_acceptance :
  forall empty,
    Bool.is_true (B T)
      (Bool.negb (B T) (exists_truth_from_empty empty)) = empty.
```

## `scalar_expr_exists_truth_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1657`](../SubqueryFacts.v#L1657)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Builds the exact two-valued EXISTS truth from inhabited child outcomes that all agree on emptiness and from exclusion of every child error.

Applicability: Use at one fixed, possibly correlated environment after proving a child success, agreement of every child success on emptiness, and exclusion of every child runtime error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`, `exact Bool3 truth`, `empty input`

```rocq
Theorem scalar_expr_exists_truth_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_expr_truth_exact_at env (SExpr_Exists subquery)
      (exists_truth_from_empty empty).
```

## `scalar_expr_not_exists_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1683`](../SubqueryFacts.v#L1683)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes NOT EXISTS acceptance as child emptiness while preserving the fixed correlated environment and excluding every child runtime error.

Applicability: Use at one fixed, possibly correlated environment after proving a child success, agreement of every child success on emptiness, and exclusion of every child runtime error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT EXISTS`, `empty input`, `runtime error`

```rocq
Theorem scalar_expr_not_exists_acceptance_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Not (SExpr_Exists subquery)) empty.
```

## `scalar_expr_exists_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1708`](../SubqueryFacts.v#L1708)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Builds an exact EXISTS acceptance contract from inhabited child successes that agree on emptiness and from explicit absence of errors.

Applicability: Use at one fixed, possibly correlated environment after providing a child success, agreement of every child success on emptiness, and absence of every child SQL error.

Important premises: Retain child-success inhabitation, universal agreement on `rows_empty_decision`, the fixed environment, and exclusion of every error.

Cross-index: `runtime`, `filter`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem scalar_expr_exists_acceptance_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Exists subquery) (Datatypes.negb empty).
```

## `eval_scalar_boolean_quant_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1733`](../SubqueryFacts.v#L1733)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes scalar-subquery quantified-comparison evaluation across the declared equivalence.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: every explicit antecedent (`->`) in the declaration is required; this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `scalar subquery`, `subquery`, `quantified predicate`, `ANY/ALL`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_quant_subquery_congr :
  forall env which_quantifier which_predicate arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_scalar_boolean env
        (SExpr_Quant which_quantifier which_predicate arguments left) outcome <->
      eval_scalar_boolean env
        (SExpr_Quant which_quantifier which_predicate arguments right) outcome.
```

## `eval_scalar_boolean_in_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1760`](../SubqueryFacts.v#L1760)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `IN`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_in_subquery_congr :
  forall env arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_scalar_boolean env (SExpr_In arguments left) outcome <->
      eval_scalar_boolean env (SExpr_In arguments right) outcome.
```

## `eval_scalar_boolean_exists_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1785`](../SubqueryFacts.v#L1785)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_exists_subquery_congr :
  forall env left right,
    (forall outcome,
      eval_exists env left outcome <-> eval_exists env right outcome) ->
    forall outcome,
      eval_scalar_boolean env (SExpr_Exists left) outcome <->
      eval_scalar_boolean env (SExpr_Exists right) outcome.
```

## `scalar_expr_quant_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1813`](../SubqueryFacts.v#L1813)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma scalar_expr_quant_admissible_iff :
  forall phase which_quantifier which_predicate arguments subquery,
    @scalar_expr_admissible T relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase ScalarResultBoolean
      (SExpr_Quant which_quantifier which_predicate arguments subquery) <->
    scalar_phase_allows_subquery phase = true /\
    prop_forall
      (@scalar_expr_admissible T relname basesort
        leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type value_is_null phase ScalarResultValue)
      arguments /\
    @query_expr_admissible T relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null subquery /\
    arguments <> nil /\
    length arguments = length (query_expr_outputs subquery) /\
    length arguments + length (query_expr_outputs subquery) =
      predicate_arity T which_predicate /\
    predicate_has_types which_predicate
      (map scalar_expr_type arguments ++
       map (type_of_attribute T) (query_expr_outputs subquery)).
```

## `scalar_expr_in_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1839`](../SubqueryFacts.v#L1839)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma scalar_expr_in_admissible_iff : forall phase arguments subquery,
  @scalar_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null phase ScalarResultBoolean
    (SExpr_In arguments subquery) <->
  scalar_phase_allows_subquery phase = true /\
  prop_forall
    (@scalar_expr_admissible T relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase ScalarResultValue)
    arguments /\
  @query_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null subquery /\
  scalar_expr_in_positionally_aligned arguments
    (query_expr_outputs subquery).
```

## `scalar_expr_exists_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1859`](../SubqueryFacts.v#L1859)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma scalar_expr_exists_admissible_iff : forall phase subquery,
  @scalar_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null phase ScalarResultBoolean
    (SExpr_Exists subquery) <->
  scalar_phase_allows_subquery phase = true /\
  @query_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null subquery.
```

## `scalar_expr_subquery_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1872`](../SubqueryFacts.v#L1872)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma scalar_expr_subquery_admissible_iff :
  forall phase result_type null_value subquery,
  @scalar_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null phase ScalarResultValue
    (SExpr_Subquery result_type null_value subquery) <->
  scalar_phase_allows_subquery phase = true /\
  @query_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null subquery /\
  value_is_null null_value = true /\
  type_of_value T null_value = result_type /\
  match query_expr_outputs subquery with
  | output :: nil => type_of_attribute T output = result_type
  | _ => False
  end.
```

## `eval_scalar_value_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1894`](../SubqueryFacts.v#L1894)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_value_context_correlated_congr :
  forall (context : @scalar_expr_context T relname ScalarResultValue)
      left right outer_env outer_row outcome,
    @query_expr_global_demand_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (scalar_expr_context_demand context) left right ->
    eval_scalar_value (env_t T outer_env outer_row)
      (plug_scalar_expr_context context left) outcome <->
    eval_scalar_value (env_t T outer_env outer_row)
      (plug_scalar_expr_context context right) outcome.
```

## `eval_scalar_boolean_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1912`](../SubqueryFacts.v#L1912)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_scalar_boolean_context_correlated_congr :
  forall (context : @scalar_expr_context T relname ScalarResultBoolean)
      left right outer_env outer_row outcome,
    @query_expr_global_demand_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (scalar_expr_context_demand context) left right ->
    eval_scalar_boolean (env_t T outer_env outer_row)
      (plug_scalar_expr_context context left) outcome <->
    eval_scalar_boolean (env_t T outer_env outer_row)
      (plug_scalar_expr_context context right) outcome.
```

## `eval_query_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1930`](../SubqueryFacts.v#L1930)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `equivalence`, `congruence`

```rocq
Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_demand_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (query_expr_context_demand context) left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
```
