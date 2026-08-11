# Predicate subqueries and correlation

Route here for: EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/scalar-expression goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality.

This focused catalog contains 109 declarations routed at declaration granularity from `CorrelatedMembershipFacts.v`, `MembershipCompositionFacts.v`, `MembershipJoinCompositionFacts.v`, `SubqueryFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

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

## `in_rows_acceptance_distinct`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:173`](../MembershipCompositionFacts.v#L173)

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

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:237`](../MembershipCompositionFacts.v#L237)

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

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:283`](../MembershipCompositionFacts.v#L283)

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

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:319`](../MembershipCompositionFacts.v#L319)

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

## `query_join_row_has_match_map`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:26`](../MembershipJoinCompositionFacts.v#L26)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query join row has match map law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_join_row_has_match_map` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `join`, `scalar`

Search aliases: `predicate subquery semantics`, `join`, `subquery`

```rocq
Lemma query_join_row_has_match_map :
  forall (matches : tuple T -> tuple T -> bool) left right_rows,
    query_join_row_has_match (map (matches left) right_rows) =
    existsb (matches left) right_rows.
```

## `query_join_source_rows_left_map`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:36`](../MembershipJoinCompositionFacts.v#L36)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query join source rows left map law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `query_join_source_rows_left_map` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `join`, `scalar`

Search aliases: `predicate subquery semantics`, `join`, `subquery`

```rocq
Lemma query_join_source_rows_left_map :
  forall rows : list (tuple T),
    map (@query_join_source_row T) (map (@JoinSourceLeft T) rows) = rows.
```

## `query_join_semi_sources_boolean_matrix`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:47`](../MembershipJoinCompositionFacts.v#L47)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query join semi sources boolean matrix law for semi-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated semi-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `join`, `scalar`

Search aliases: `predicate subquery semantics`, `semi join`, `EXISTS`, `join`, `subquery`

```rocq
Lemma query_join_semi_sources_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) left_rows right_rows,
    query_join_sources T QueryJoinSemi left_rows right_rows
      (map (fun left => map (matches left) right_rows) left_rows) =
    map (@JoinSourceLeft T)
      (filter (fun left => existsb (matches left) right_rows) left_rows).
```

## `query_join_anti_sources_boolean_matrix`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:77`](../MembershipJoinCompositionFacts.v#L77)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query join anti sources boolean matrix law for anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `join`, `scalar`

Search aliases: `predicate subquery semantics`, `anti join`, `NOT EXISTS`, `join`, `subquery`

```rocq
Lemma query_join_anti_sources_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) left_rows right_rows,
    query_join_sources T QueryJoinAnti left_rows right_rows
      (map (fun left => map (matches left) right_rows) left_rows) =
    map (@JoinSourceLeft T)
      (filter
        (fun left => negb (existsb (matches left) right_rows)) left_rows).
```

## `eval_filter_rows_correlated_semijoin_sources_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:155`](../MembershipJoinCompositionFacts.v#L155)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the eval filter rows correlated semijoin sources exact law for semi-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated semi-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `join`, `scalar`

Search aliases: `predicate subquery semantics`, `semi join`, `EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`

```rocq
Theorem eval_filter_rows_correlated_semijoin_sources_exact :
  forall env formula left_rows right_rows matches outcome,
    correlated_filter_join_acceptance_exact_at
      env formula right_rows matches (fun matched => matched) left_rows ->
    eval_filter_rows env formula left_rows outcome <->
    outcome =
      SqlSuccess
        (map (@query_join_source_row T)
          (query_join_sources T QueryJoinSemi left_rows right_rows
            (map (fun left => map (matches left) right_rows) left_rows))).
```

## `eval_filter_rows_correlated_antijoin_sources_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:180`](../MembershipJoinCompositionFacts.v#L180)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the eval filter rows correlated antijoin sources exact law for anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `join`, `scalar`

Search aliases: `predicate subquery semantics`, `anti join`, `NOT EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`

```rocq
Theorem eval_filter_rows_correlated_antijoin_sources_exact :
  forall env formula left_rows right_rows matches outcome,
    correlated_filter_join_acceptance_exact_at
      env formula right_rows matches negb left_rows ->
    eval_filter_rows env formula left_rows outcome <->
    outcome =
      SqlSuccess
        (map (@query_join_source_row T)
          (query_join_sources T QueryJoinAnti left_rows right_rows
            (map (fun left => map (matches left) right_rows) left_rows))).
```

## `scalar_expr_correlated_in_semijoin_acceptance_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:246`](../MembershipJoinCompositionFacts.v#L246)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the scalar expr correlated in semijoin acceptance exact law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `correlated`, `correlation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem scalar_expr_correlated_in_semijoin_acceptance_exact :
  forall env arguments subquery
      (right_rows : list (tuple T)) (matches : tuple T -> bool),
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs (query_expr_outputs subquery)) rows) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      existsb
        (fun row => Bool.is_true (B T)
          (@in_row_truth T relname unknown value_is_null
            values subquery row)) rows =
      existsb matches right_rows) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_exact env (SExpr_In arguments subquery)
      (existsb matches right_rows).
```

## `scalar_expr_correlated_exists_semijoin_acceptance_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:287`](../MembershipJoinCompositionFacts.v#L287)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the scalar expr correlated exists semijoin acceptance exact law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `correlated`, `correlation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem scalar_expr_correlated_exists_semijoin_acceptance_exact :
  forall env subquery
      (right_rows : list (tuple T)) (matches : tuple T -> bool),
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      Bool.is_true (B T) truth = existsb matches right_rows) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_exact env (SExpr_Exists subquery) (existsb matches right_rows).
```

## `scalar_expr_correlated_not_exists_antijoin_acceptance_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:314`](../MembershipJoinCompositionFacts.v#L314)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the scalar expr correlated not exists antijoin acceptance exact law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `correlated`, `correlation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem scalar_expr_correlated_not_exists_antijoin_acceptance_exact :
  forall env subquery
      (right_rows : list (tuple T)) (matches : tuple T -> bool),
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty (negb (existsb matches right_rows))) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_exact env (SExpr_Not (SExpr_Exists subquery))
      (negb (existsb matches right_rows)).
```

## `tnull_scalar_expr_correlated_not_in_antijoin_acceptance_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:360`](../MembershipJoinCompositionFacts.v#L360)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull scalar expr correlated not in antijoin acceptance exact law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `correlated`, `correlation`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem tnull_scalar_expr_correlated_not_in_antijoin_acceptance_exact :
  forall env arguments subquery
      (right_rows : list (tuple TNull))
      (matches : tuple TNull -> bool),
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      if existsb matches right_rows
      then exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = true3
      else Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = false3)
        (@query_canonical_rows TNull rows)) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery))
      (negb (existsb matches right_rows)).
```

## `query_expr_correlated_filter_join_relation_transport`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:424`](../MembershipJoinCompositionFacts.v#L424)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports the displayed hypotheses and conclusion for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `outcome`, `runtime`, `filter`, `join`, `scalar`

Search aliases: `predicate subquery semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem query_expr_correlated_filter_join_relation_transport :
  forall schedule env source_formula input kind target_predicate
      matched_select left_select right_select right row_rel,
    (exists right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows)) ->
    (forall error,
      ~ @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env right (SqlError error)) ->
    (forall left_rows right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows) ->
      outcome_relation_transport (Forall2 row_rel)
        (@eval_filter_rows_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env source_formula left_rows)
        (@query_join_rows_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env kind target_predicate matched_select left_select
          right_select left_rows right_rows)) ->
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter source_formula input))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Join kind target_predicate
          matched_select left_select right_select input right)).
```

## `query_expr_correlated_filter_join_possible_outcome_related`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:539`](../MembershipJoinCompositionFacts.v#L539)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the query expr correlated filter join possible outcome related law for outer/semi/anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `join`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `predicate subquery semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem query_expr_correlated_filter_join_possible_outcome_related :
  forall env source_formula input kind target_predicate
      matched_select left_select right_select right row_rel,
    correlated_filter_join_possible_outcome_contract env source_formula kind
      target_predicate matched_select left_select right_select right row_rel ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_related T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (Forall2 row_rel)
      (QExpr_Filter source_formula input)
      (QExpr_Join kind target_predicate
        matched_select left_select right_select input right).
```

## `query_expr_correlated_filter_join_possible_outcome_equiv`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:570`](../MembershipJoinCompositionFacts.v#L570)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `join`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `predicate subquery semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Corollary query_expr_correlated_filter_join_possible_outcome_equiv :
  forall env source_formula input kind target_predicate
      matched_select left_select right_select right,
    query_expr_outputs (QExpr_Filter source_formula input) =
      query_expr_outputs
        (QExpr_Join kind target_predicate
          matched_select left_select right_select input right) ->
    correlated_filter_join_possible_outcome_contract env source_formula kind
      target_predicate matched_select left_select right_select right
      (fun left right => Oeset.compare (OTuple T) left right = Eq) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter source_formula input)
      (QExpr_Join kind target_predicate
        matched_select left_select right_select input right).
```

## `query_expr_correlated_filter_semijoin_possible_outcome_related`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:601`](../MembershipJoinCompositionFacts.v#L601)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the query expr correlated filter semijoin possible outcome related law for outer/semi/anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `join`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `predicate subquery semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Corollary query_expr_correlated_filter_semijoin_possible_outcome_related :
  forall env source_formula input target_predicate
      matched_select left_select right_select right row_rel,
    correlated_filter_join_possible_outcome_contract env source_formula
      QueryJoinSemi target_predicate matched_select left_select right_select
      right row_rel ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_related T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (Forall2 row_rel)
      (QExpr_Filter source_formula input)
      (QExpr_Join QueryJoinSemi target_predicate
        matched_select left_select right_select input right).
```

## `query_expr_correlated_filter_antijoin_possible_outcome_related`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:622`](../MembershipJoinCompositionFacts.v#L622)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the query expr correlated filter antijoin possible outcome related law for outer/semi/anti-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `join`, `scalar`

Search aliases: `possible outcome`, `all Boolean schedules`, `predicate subquery semantics`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `subquery`, `correlated`, `correlation`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Corollary query_expr_correlated_filter_antijoin_possible_outcome_related :
  forall env source_formula input target_predicate
      matched_select left_select right_select right row_rel,
    correlated_filter_join_possible_outcome_contract env source_formula
      QueryJoinAnti target_predicate matched_select left_select right_select
      right row_rel ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_related T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (Forall2 row_rel)
      (QExpr_Filter source_formula input)
      (QExpr_Join QueryJoinAnti target_predicate
        matched_select left_select right_select input right).
```

## `interp_exists_quant_not_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:21`](../SubqueryFacts.v#L21)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:38`](../SubqueryFacts.v#L38)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:56`](../SubqueryFacts.v#L56)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:93`](../SubqueryFacts.v#L93)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:130`](../SubqueryFacts.v#L130)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:150`](../SubqueryFacts.v#L150)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:162`](../SubqueryFacts.v#L162)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:176`](../SubqueryFacts.v#L176)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:202`](../SubqueryFacts.v#L202)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:304`](../SubqueryFacts.v#L304)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:323`](../SubqueryFacts.v#L323)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:340`](../SubqueryFacts.v#L340)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:377`](../SubqueryFacts.v#L377)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:414`](../SubqueryFacts.v#L414)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:445`](../SubqueryFacts.v#L445)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:458`](../SubqueryFacts.v#L458)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:478`](../SubqueryFacts.v#L478)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:487`](../SubqueryFacts.v#L487)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:538`](../SubqueryFacts.v#L538)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:561`](../SubqueryFacts.v#L561)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:616`](../SubqueryFacts.v#L616)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:678`](../SubqueryFacts.v#L678)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:691`](../SubqueryFacts.v#L691)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:709`](../SubqueryFacts.v#L709)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:721`](../SubqueryFacts.v#L721)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:749`](../SubqueryFacts.v#L749)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:774`](../SubqueryFacts.v#L774)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:801`](../SubqueryFacts.v#L801)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:842`](../SubqueryFacts.v#L842)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:899`](../SubqueryFacts.v#L899)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:941`](../SubqueryFacts.v#L941)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:974`](../SubqueryFacts.v#L974)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:997`](../SubqueryFacts.v#L997)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1010`](../SubqueryFacts.v#L1010)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1023`](../SubqueryFacts.v#L1023)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1036`](../SubqueryFacts.v#L1036)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1049`](../SubqueryFacts.v#L1049)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1059`](../SubqueryFacts.v#L1059)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1069`](../SubqueryFacts.v#L1069)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1079`](../SubqueryFacts.v#L1079)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1101`](../SubqueryFacts.v#L1101)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1115`](../SubqueryFacts.v#L1115)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1130`](../SubqueryFacts.v#L1130)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1148`](../SubqueryFacts.v#L1148)

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

## `scalar_subquery_value_outcome_safe_of_length_le_one`

Source: [`theories/FormalSQL/SubqueryFacts.v:1167`](../SubqueryFacts.v#L1167)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for predicate-subquery evaluation.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_subquery_value_outcome_safe_of_length_le_one :
  forall null_value outputs rows,
    (List.length rows <= 1)%nat ->
    forall error,
      @scalar_subquery_value_outcome T null_value outputs
        (SqlSuccess rows) <> SqlError error.
```

## `scalar_subquery_runtime_safe_of_cardinality`

Source: [`theories/FormalSQL/SubqueryFacts.v:1184`](../SubqueryFacts.v#L1184)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates predicate-subquery evaluation to the exact list length or bag cardinality shown below.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scheduled`, `runtime`, `scalar`

Search aliases: `fixed Boolean schedule`, `foundation`, `predicate subquery semantics`, `subquery`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem scalar_subquery_runtime_safe_of_cardinality :
  forall env result_type null_value subquery,
    value_is_null null_value = true ->
    @query_success_length_le T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env subquery 1 ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    forall error,
      ~ eval_scalar_value env
          (SExpr_Subquery result_type null_value subquery) (SqlError error).
```

## `eval_scalar_boolean_quant_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1207`](../SubqueryFacts.v#L1207)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1226`](../SubqueryFacts.v#L1226)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1249`](../SubqueryFacts.v#L1249)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1292`](../SubqueryFacts.v#L1292)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1307`](../SubqueryFacts.v#L1307)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1322`](../SubqueryFacts.v#L1322)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1339`](../SubqueryFacts.v#L1339)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1354`](../SubqueryFacts.v#L1354)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1372`](../SubqueryFacts.v#L1372)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1411`](../SubqueryFacts.v#L1411)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1472`](../SubqueryFacts.v#L1472)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1495`](../SubqueryFacts.v#L1495)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1504`](../SubqueryFacts.v#L1504)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1516`](../SubqueryFacts.v#L1516)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1532`](../SubqueryFacts.v#L1532)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1548`](../SubqueryFacts.v#L1548)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1588`](../SubqueryFacts.v#L1588)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1606`](../SubqueryFacts.v#L1606)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1639`](../SubqueryFacts.v#L1639)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1652`](../SubqueryFacts.v#L1652)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1662`](../SubqueryFacts.v#L1662)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1687`](../SubqueryFacts.v#L1687)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1701`](../SubqueryFacts.v#L1701)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1727`](../SubqueryFacts.v#L1727)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1752`](../SubqueryFacts.v#L1752)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1777`](../SubqueryFacts.v#L1777)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1804`](../SubqueryFacts.v#L1804)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1829`](../SubqueryFacts.v#L1829)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1857`](../SubqueryFacts.v#L1857)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1883`](../SubqueryFacts.v#L1883)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1903`](../SubqueryFacts.v#L1903)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1916`](../SubqueryFacts.v#L1916)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1938`](../SubqueryFacts.v#L1938)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1956`](../SubqueryFacts.v#L1956)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:1974`](../SubqueryFacts.v#L1974)

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
