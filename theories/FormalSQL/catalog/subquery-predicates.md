# Predicate subqueries and correlation

Route here for: EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality.

This focused catalog contains 86 declarations routed at declaration granularity from `CorrelatedMembershipFacts.v`, `MembershipCompositionFacts.v`, `MembershipJoinCompositionFacts.v`, `SubqueryFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `interp_direct_attribute_in_env_t_absent`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:23`](../CorrelatedMembershipFacts.v#L23)

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

Purpose/direction: Computes filtered self-membership from an actual semantic self witness and occurrence-sensitive key uniqueness; the primary-key form also exposes NOT NULL.

Applicability: Use when the goal or a hypothesis matches the `primary_key_self_filter_existsb_exact` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `schema`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `integrity constraint`, `key`, `primary key`, `self membership`, `NOT NULL`

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
        (project_row key outer) (project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate) ->
      sql_key_equal_true
        (project_row key candidate) (project_row key outer)) ->
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (project_row key outer) /\
    existsb matches (filter keep rows) = keep outer.
```

## `tnull_primary_key_self_in_rows_acceptance_exact`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:192`](../CorrelatedMembershipFacts.v#L192)

Purpose/direction: Establishes TNull primary-key self-IN TRUE-acceptance from an actual tuple-comparison witness, key reflection, and the complete projected NOT NULL fact.

Applicability: Use when the goal or a hypothesis matches the `tnull_primary_key_self_in_rows_acceptance_exact` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `schema`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `integrity constraint`, `key`, `primary key`, `IN`, `self membership`

```rocq
Theorem tnull_primary_key_self_in_rows_acceptance_exact :
  forall key rows (keep : tuple TNull -> bool) outer env select_items
      (project_candidate : tuple TNull -> tuple TNull),
    primary_key_conforms key rows ->
    In outer rows ->
    Bool.is_true Bool3
      (@in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items (project_candidate outer)) = true ->
    (forall candidate,
      In candidate rows ->
      Bool.is_true Bool3
        (@in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items (project_candidate candidate)) = true ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate) ->
      sql_key_equal_true
        (project_row key candidate) (project_row key outer)) ->
    Bool.is_true Bool3
      (@in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items
        (map project_candidate (filter keep rows))) = keep outer /\
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (project_row key outer).
```

## `tnull_primary_key_self_in_rows_true`

Source: [`theories/FormalSQL/CorrelatedMembershipFacts.v:257`](../CorrelatedMembershipFacts.v#L257)

Purpose/direction: Establishes TNull primary-key self-IN TRUE-acceptance from an actual tuple-comparison witness, key reflection, and the complete projected NOT NULL fact.

Applicability: Use when the goal or a hypothesis matches the `tnull_primary_key_self_in_rows_true` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `schema`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `integrity constraint`, `key`, `primary key`, `IN`, `exact TRUE`, `correlation`

```rocq
Corollary tnull_primary_key_self_in_rows_true :
  forall key rows (keep : tuple TNull -> bool) outer env select_items
      (project_candidate : tuple TNull -> tuple TNull),
    primary_key_conforms key rows ->
    In outer rows ->
    keep outer = true ->
    Bool.is_true Bool3
      (@in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items (project_candidate outer)) = true ->
    (forall candidate,
      In candidate rows ->
      Bool.is_true Bool3
        (@in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items (project_candidate candidate)) = true ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate) ->
      sql_key_equal_true
        (project_row key candidate) (project_row key outer)) ->
    Bool.is_true Bool3
      (@in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items
        (map project_candidate (filter keep rows))) = true /\
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (project_row key outer).
```

## `tnull_in_rows_unknown_iff`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:24`](../MembershipCompositionFacts.v#L24)

Purpose/direction: Characterizes TNull IN UNKNOWN as at least one UNKNOWN candidate comparison and no TRUE candidate, over the canonical bag representative.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `IN`, `semantic tuple equality`, `duplicates`

```rocq
Lemma tnull_in_rows_unknown_iff :
  forall env select_items rows,
    @in_rows_truth TNull unknown3 NullValues.is_null_value
      env select_items rows = unknown3 <->
    Exists
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = unknown3)
      (@query_canonical_rows TNull rows) /\
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row <> true3)
      (@query_canonical_rows TNull rows).
```

## `tnull_in_rows_semantic_cases`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:44`](../MembershipCompositionFacts.v#L44)

Purpose/direction: Partitions TNull IN into empty/FALSE, TRUE-match, UNKNOWN-without-match, and nonempty-all-FALSE cases without replacing SQL tuple comparison by Rocq equality.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `IN`, `empty input`, `TRUE FALSE UNKNOWN`, `duplicates`

```rocq
Theorem tnull_in_rows_semantic_cases :
  forall env select_items rows,
    ((@query_canonical_rows TNull rows = nil) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = false3) \/
    ((exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = true3) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = true3) \/
    ((Exists
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row <> true3)
        (@query_canonical_rows TNull rows)) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = unknown3) \/
    ((@query_canonical_rows TNull rows <> nil) /\
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = false3)
        (@query_canonical_rows TNull rows) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = false3).
```

## `tnull_not_in_rows_acceptance_iff_all_false`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:103`](../MembershipCompositionFacts.v#L103)

Purpose/direction: Characterizes TNull NOT IN acceptance by all candidate comparisons being FALSE, equivalently by absence of both a TRUE match and an UNKNOWN comparison.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `NOT IN`, `all comparisons FALSE`, `empty input`

```rocq
Theorem tnull_not_in_rows_acceptance_iff_all_false :
  forall env select_items rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull unknown3 NullValues.is_null_value
          env select_items rows)) = true <->
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = false3)
      (@query_canonical_rows TNull rows).
```

## `tnull_not_in_rows_acceptance_iff_no_true_or_unknown`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:125`](../MembershipCompositionFacts.v#L125)

Purpose/direction: Characterizes TNull NOT IN acceptance by all candidate comparisons being FALSE, equivalently by absence of both a TRUE match and an UNKNOWN comparison.

Applicability: Use at the TNull row-truth boundary over query_canonical_rows.  Empty inputs and duplicate candidates remain represented, and UNKNOWN must not be collapsed into FALSE when reasoning about NOT IN.

Important premises: preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `NULL`, `UNKNOWN`, `three-valued logic`, `NOT IN`, `anti existence`, `NULL marker`

```rocq
Theorem tnull_not_in_rows_acceptance_iff_no_true_or_unknown :
  forall env select_items rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull unknown3 NullValues.is_null_value
          env select_items rows)) = true <->
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items row = true3) /\
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items row = unknown3).
```

## `query_distinct_rows_support_rel`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:230`](../MembershipCompositionFacts.v#L230)

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

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:276`](../MembershipCompositionFacts.v#L276)

Purpose/direction: Shows SQL IN TRUE-acceptance is unchanged by DISTINCT candidate elimination while leaving the underlying row multiplicities distinct.

Applicability: Use only for duplicate-insensitive support or IN TRUE-acceptance.  DISTINCT changes row multiplicity and may not be erased for COUNT, bags, exact ordered results, or full FALSE/UNKNOWN truth without additional premises.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `DISTINCT`, `duplicate elimination`, `filter acceptance`, `duplicate-insensitive`

```rocq
Theorem in_rows_acceptance_distinct :
  forall env select_items input output,
    query_same_rows_as_bag output
      (query_distinct_bag (query_rows_bag input)) ->
    Bool.is_true (B T)
      (@in_rows_truth T unknown value_is_null env select_items output) =
    Bool.is_true (B T)
      (@in_rows_truth T unknown value_is_null env select_items input).
```

## `formula_in_union_all_acceptance_exact`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:290`](../MembershipCompositionFacts.v#L290)

Purpose/direction: Builds exact correlated IN acceptance over UNION ALL as the Boolean OR of fixed branch decisions while retaining duplicate candidates and requiring both branch error relations to be empty.

Applicability: Use only for UNION ALL at one fixed correlated environment after proving schema compatibility, argument safety, inhabited branch successes, fixed per-branch TRUE-acceptance decisions, and absence of both branch errors.  It is not a full Bool3 or UNION DISTINCT distribution theorem.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `set operation`, `UNION`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `UNION ALL`, `correlation`, `filter acceptance`, `runtime error`

```rocq
Theorem formula_in_union_all_acceptance_exact :
  forall env select_items left right (accept : tuple T -> bool)
      left_accepted right_accepted,
    query_expr_sort left =S= query_expr_sort right ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env left (SqlSuccess rows)) ->
    (exists rows, eval_query env right (SqlSuccess rows)) ->
    (forall row,
      Bool.is_true (B T)
        (@in_row_truth T unknown value_is_null env select_items row) =
      accept row) ->
    (forall rows,
      eval_query env left (SqlSuccess rows) ->
      existsb accept rows = left_accepted) ->
    (forall rows,
      eval_query env right (SqlSuccess rows) ->
      existsb accept rows = right_accepted) ->
    (forall error, ~ eval_query env left (SqlError error)) ->
    (forall error, ~ eval_query env right (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_In select_items (QExpr_Set Union left right))
      (orb left_accepted right_accepted).
```

## `tnull_formula_not_in_accepts_exact_of_all_false`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:412`](../MembershipCompositionFacts.v#L412)

Purpose/direction: Lifts the displayed TNull NOT IN semantic case to exact formula acceptance at one correlated environment, retaining argument and child error premises.

Applicability: Use at one fixed correlated environment after proving argument safety, child-success inhabitation, the displayed case for every legal child success, and exclusion of every child error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `correlation`, `exact acceptance`, `runtime error`

```rocq
Theorem tnull_formula_not_in_accepts_exact_of_all_false :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error TNull
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = false3)
        (@query_canonical_rows TNull rows)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value env
      (FExpr_Not (FExpr_In select_items subquery)) true.
```

## `tnull_formula_not_in_rejects_exact_of_true_match`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:454`](../MembershipCompositionFacts.v#L454)

Purpose/direction: Lifts the displayed TNull NOT IN semantic case to exact formula acceptance at one correlated environment, retaining argument and child error premises.

Applicability: Use at one fixed correlated environment after proving argument safety, child-success inhabitation, the displayed case for every legal child success, and exclusion of every child error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `TRUE match`, `exact rejection`, `runtime error`

```rocq
Theorem tnull_formula_not_in_rejects_exact_of_true_match :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error TNull
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = true3) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value env
      (FExpr_Not (FExpr_In select_items subquery)) false.
```

## `tnull_formula_not_in_rejects_exact_of_unknown_without_match`

Source: [`theories/FormalSQL/MembershipCompositionFacts.v:486`](../MembershipCompositionFacts.v#L486)

Purpose/direction: Lifts the displayed TNull NOT IN semantic case to exact formula acceptance at one correlated environment, retaining argument and child error premises.

Applicability: Use at one fixed correlated environment after proving argument safety, child-success inhabitation, the displayed case for every legal child success, and exclusion of every child error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the stated SQL NULL/Bool3 hypotheses; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `NULL`, `UNKNOWN`, `three-valued logic`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `UNKNOWN without match`, `exact rejection`, `runtime error`

```rocq
Theorem tnull_formula_not_in_rejects_exact_of_unknown_without_match :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error TNull
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Exists
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row <> true3)
        (@query_canonical_rows TNull rows)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value env
      (FExpr_Not (FExpr_In select_items subquery)) false.
```

## `formula_in_distinct_acceptance_exact_of_inner`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:48`](../MembershipJoinCompositionFacts.v#L48)

Purpose/direction: Lifts an exact correlated IN acceptance contract through DISTINCT without claiming equality of the complete FALSE/UNKNOWN Bool3 result.

Applicability: Use when the goal or a hypothesis matches the `formula_in_distinct_acceptance_exact_of_inner` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `DISTINCT`, `duplicate elimination`, `correlation`, `runtime error`

```rocq
Theorem formula_in_distinct_acceptance_exact_of_inner :
  forall env select_items input accepted,
    formula_exact env (FExpr_In select_items input) accepted ->
    formula_exact env
      (FExpr_In select_items (QExpr_Distinct input)) accepted.
```

## `query_expr_project_filter_runtime_safe_exact`

Source: [`theories/FormalSQL/MembershipJoinCompositionFacts.v:122`](../MembershipJoinCompositionFacts.v#L122)

Purpose/direction: Composes child, filter-formula, and reached-projection safety into exact runtime safety for a Project over Filter without inferring safety from bags.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `projection`, `filter`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `evaluation reachability`

```rocq
Theorem query_expr_project_filter_runtime_safe_exact :
  forall env select_list formula input (keep : tuple T -> bool),
    (forall row,
      formula_exact (env_t T env row) formula (keep row)) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    @query_expr_runtime_safe T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env input ->
    @query_expr_runtime_safe T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Project select_list (QExpr_Filter formula input)).
```

## `interp_exists_quant_not_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:23`](../SubqueryFacts.v#L23)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:40`](../SubqueryFacts.v#L40)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:58`](../SubqueryFacts.v#L58)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:95`](../SubqueryFacts.v#L95)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:132`](../SubqueryFacts.v#L132)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:152`](../SubqueryFacts.v#L152)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:164`](../SubqueryFacts.v#L164)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:178`](../SubqueryFacts.v#L178)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:204`](../SubqueryFacts.v#L204)

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

## `formula_truth_exact_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:288`](../SubqueryFacts.v#L288)

Purpose/direction: Projects an inhabited, unique exact Bool3 success with no reachable runtime error to its SQL TRUE-acceptance bit.

Applicability: Use only with the displayed exact-truth contract: it includes one successful observation, uniqueness of the full Bool3 truth, and exclusion of every runtime error at the same environment.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `exact Bool3 truth`, `UNKNOWN`, `runtime error`

```rocq
Lemma formula_truth_exact_acceptance_exact :
  forall env formula expected,
    formula_truth_exact_at env formula expected ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env formula
      (Bool.is_true (B T) expected).
```

## `formula_not_truth_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:307`](../SubqueryFacts.v#L307)

Purpose/direction: Transports an inhabited, error-free exact Bool3 observation through SQL NOT; in particular, UNKNOWN remains UNKNOWN.

Applicability: Use only with the displayed exact-truth contract: it includes one successful observation, uniqueness of the full Bool3 truth, and exclusion of every runtime error at the same environment.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `SQL NOT`, `exact Bool3 truth`, `UNKNOWN`

```rocq
Theorem formula_not_truth_exact :
  forall env formula expected,
    formula_truth_exact_at env formula expected ->
    formula_truth_exact_at env (FExpr_Not formula)
      (Bool.negb (B T) expected).
```

## `formula_not_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:324`](../SubqueryFacts.v#L324)

Purpose/direction: Derives exact acceptance for SQL NOT from the stronger exact-truth contract, without complementing a FALSE/UNKNOWN acceptance bit.

Applicability: Use only with the displayed exact-truth contract: it includes one successful observation, uniqueness of the full Bool3 truth, and exclusion of every runtime error at the same environment.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `SQL NOT`, `UNKNOWN`, `filter acceptance`

```rocq
Corollary formula_not_acceptance_exact :
  forall env formula expected,
    formula_truth_exact_at env formula expected ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env (FExpr_Not formula)
      (Bool.is_true (B T) (Bool.negb (B T) expected)).
```

## `formula_expr_conj_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:353`](../SubqueryFacts.v#L353)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_conj_env_congr :
  forall left_env right_env operation left right,
    formula_expr_env_outcome_equiv left_env right_env left ->
    formula_expr_env_outcome_equiv left_env right_env right ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Conj operation left right).
```

## `formula_expr_not_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:402`](../SubqueryFacts.v#L402)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_not_env_congr :
  forall left_env right_env formula,
    formula_expr_env_outcome_equiv left_env right_env formula ->
    formula_expr_env_outcome_equiv left_env right_env (FExpr_Not formula).
```

## `formula_expr_pred_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:415`](../SubqueryFacts.v#L415)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_pred_env_congr_safe :
  forall left_env right_env predicate arguments,
    Env.equiv_env T left_env right_env ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      arguments = None ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      arguments = None ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Pred predicate arguments).
```

## `query_expr_table_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:457`](../SubqueryFacts.v#L457)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_expr_table_env_congr :
  forall left_env right_env attributes relation,
    query_expr_env_outcome_equiv left_env right_env
      (@QExpr_Table T relname attributes relation).
```

## `query_expr_cross_join_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:466`](../SubqueryFacts.v#L466)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `join`, `scalar`

Search aliases: `predicate subquery semantics`, `join`, `cross product`, `CROSS JOIN`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_env_congr :
  forall left_env right_env left right,
    query_expr_env_outcome_equiv left_env right_env left ->
    query_expr_env_outcome_equiv left_env right_env right ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_CrossJoin left right).
```

## `eval_filter_rows_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:517`](../SubqueryFacts.v#L517)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `filter`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_env_congr :
  forall left_env right_env formula,
    (forall row,
      formula_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    forall rows outcome,
      eval_filter_rows left_env formula rows outcome <->
      eval_filter_rows right_env formula rows outcome.
```

## `query_expr_filter_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:540`](../SubqueryFacts.v#L540)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `filter`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_env_congr :
  forall left_env right_env formula input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      formula_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Filter formula input).
```

## `project_rows_outcome_env_congr_safe_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:579`](../SubqueryFacts.v#L579)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma project_rows_outcome_env_congr_safe_exact :
  forall left_env right_env select_list rows,
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T left_env row) select_list = None) ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T right_env row) select_list = None) ->
    (forall row,
      Projection.projection T (Env.env_t T left_env row)
        (@Select_List T select_list) =
      Projection.projection T (Env.env_t T right_env row)
        (@Select_List T select_list)) ->
    project_rows left_env select_list rows =
    project_rows right_env select_list rows.
```

## `query_expr_project_env_congr_safe_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:605`](../SubqueryFacts.v#L605)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `projection`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_project_env_congr_safe_exact :
  forall left_env right_env select_list input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T left_env row) select_list = None) ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T right_env row) select_list = None) ->
    (forall row,
      Projection.projection T (Env.env_t T left_env row)
        (@Select_List T select_list) =
      Projection.projection T (Env.env_t T right_env row)
        (@Select_List T select_list)) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Project select_list input).
```

## `quantified_rows_truth_congr_of_bag_eq`

Source: [`theories/FormalSQL/SubqueryFacts.v:668`](../SubqueryFacts.v#L668)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem quantified_rows_truth_congr_of_bag_eq :
  forall env which_quantifier which_predicate arguments subquery left right
      (property : tuple T -> Prop),
    @bag_eq T (query_rows_bag left) (query_rows_bag right) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      (property first <-> property second)) ->
    Forall property (query_canonical_rows left) ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      property left_row ->
      quantified_row_truth env which_predicate arguments subquery left_row =
      quantified_row_truth env which_predicate arguments subquery right_row) ->
    quantified_rows_truth env which_quantifier which_predicate arguments
      subquery left =
    quantified_rows_truth env which_quantifier which_predicate arguments
      subquery right.
```

## `query_tuple_equal_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:727`](../SubqueryFacts.v#L727)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma query_tuple_equal_congr :
  forall left left' right right',
    Oeset.compare (OTuple T) left left' = Eq ->
    Oeset.compare (OTuple T) right right' = Eq ->
    @query_tuple_equal T unknown value_is_null left right =
    @query_tuple_equal T unknown value_is_null left' right'.
```

## `in_row_truth_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:794`](../SubqueryFacts.v#L794)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `equivalence`, `congruence`

```rocq
Lemma in_row_truth_env_congr :
  forall left_env right_env select_items row,
    Env.equiv_env T left_env right_env ->
    in_row_truth left_env select_items row =
    in_row_truth right_env select_items row.
```

## `in_rows_truth_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:807`](../SubqueryFacts.v#L807)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `equivalence`, `congruence`

```rocq
Lemma in_rows_truth_env_congr :
  forall left_env right_env select_items rows,
    Env.equiv_env T left_env right_env ->
    in_rows_truth left_env select_items rows =
    in_rows_truth right_env select_items rows.
```

## `in_rows_acceptance_existsb`

Source: [`theories/FormalSQL/SubqueryFacts.v:828`](../SubqueryFacts.v#L828)

Purpose/direction: Reduces only the TRUE-acceptance observation of SQL IN over a row bag to an ordinary Boolean existence test, retaining the underlying FALSE/UNKNOWN distinction.

Applicability: Use after proving the per-candidate `Bool.is_true` decision.  The conclusion is suitable for WHERE or semijoin filtering only; it is not equality of the complete SQL Bool3 result.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `filter`, `join`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_acceptance_existsb :
  forall env select_items rows (accept : tuple T -> bool),
    (forall row,
      Bool.is_true (B T) (in_row_truth env select_items row) = accept row) ->
    Bool.is_true (B T) (in_rows_truth env select_items rows) =
    existsb accept rows.
```

## `in_rows_acceptance_support_rel`

Source: [`theories/FormalSQL/SubqueryFacts.v:884`](../SubqueryFacts.v#L884)

Purpose/direction: Transports only SQL IN TRUE-acceptance across duplicate-insensitive support correspondence under FormalSQL semantic tuple equality.

Applicability: Use only at an IN TRUE-acceptance boundary after candidate-query success/error behavior has been handled separately.  Do not use it to prove full Bool3 equality, NOT IN, multiplicity, or ordered outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `bag`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `bag semantics`, `list/bag bridge`, `semantic tuple equality`, `duplicate-insensitive support`

```rocq
Theorem in_rows_acceptance_support_rel :
  forall env select_items left right,
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    Bool.is_true (B T) (in_rows_truth env select_items left) =
    Bool.is_true (B T) (in_rows_truth env select_items right).
```

## `in_rows_acceptance_append`

Source: [`theories/FormalSQL/SubqueryFacts.v:920`](../SubqueryFacts.v#L920)

Purpose/direction: Distributes SQL IN TRUE-acceptance over appended candidate lists as Boolean OR without equating the underlying FALSE and UNKNOWN truths.

Applicability: Use only at an IN TRUE-acceptance boundary after candidate-query success/error behavior has been handled separately.  Do not use it to prove full Bool3 equality, NOT IN, multiplicity, or ordered outcomes.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `UNION`, `filter acceptance`

```rocq
Theorem in_rows_acceptance_append :
  forall env select_items left right,
    Bool.is_true (B T)
      (in_rows_truth env select_items (left ++ right)) =
    Datatypes.orb
      (Bool.is_true (B T) (in_rows_truth env select_items left))
      (Bool.is_true (B T) (in_rows_truth env select_items right)).
```

## `query_same_rows_as_bag_empty_decision`

Source: [`theories/FormalSQL/SubqueryFacts.v:942`](../SubqueryFacts.v#L942)

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

Source: [`theories/FormalSQL/SubqueryFacts.v:965`](../SubqueryFacts.v#L965)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_exists_true_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Exists_F which_predicate arguments subquery rows =
      Bool.true (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.true (B T).
```

## `quantified_rows_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:978`](../SubqueryFacts.v#L978)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_exists_false_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Exists_F which_predicate arguments subquery rows =
      Bool.false (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.false (B T).
```

## `quantified_rows_forall_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:991`](../SubqueryFacts.v#L991)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_forall_true_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Forall_F which_predicate arguments subquery rows =
      Bool.true (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.true (B T).
```

## `quantified_rows_forall_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1004`](../SubqueryFacts.v#L1004)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma quantified_rows_forall_false_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Forall_F which_predicate arguments subquery rows =
      Bool.false (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.false (B T).
```

## `in_rows_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1017`](../SubqueryFacts.v#L1017)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_true_iff : forall env select_items rows,
  in_rows_truth env select_items rows = Bool.true (B T) <->
  exists row,
    In row (query_canonical_rows rows) /\
    in_row_truth env select_items row = Bool.true (B T).
```

## `in_rows_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1027`](../SubqueryFacts.v#L1027)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma in_rows_false_iff : forall env select_items rows,
  in_rows_truth env select_items rows = Bool.false (B T) <->
  forall row,
    In row (query_canonical_rows rows) ->
    in_row_truth env select_items row = Bool.false (B T).
```

## `query_canonical_rows_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1037`](../SubqueryFacts.v#L1037)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `query_canonical_rows_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`

```rocq
Lemma query_canonical_rows_empty :
  @query_canonical_rows T [] = [].
```

## `eval_formula_quant_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1044`](../SubqueryFacts.v#L1044)

Purpose/direction: Gives necessary and sufficient conditions for scalar-subquery quantified-comparison evaluation.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `scalar subquery`, `SINGLE_VALUE`, `CardinalityViolation`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_formula_quant_error_iff :
  forall env which_quantifier which_predicate arguments subquery error,
    eval_formula env
      (FExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlError error) <->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = Some error \/
    (first_runtime_error
       (@eval_aggterm_runtime_error T
         symbol_runtime_error aggregate_runtime_error env)
       arguments = None /\
     eval_query env subquery (SqlError error)).
```

## `eval_formula_quant_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1068`](../SubqueryFacts.v#L1068)

Purpose/direction: Gives necessary and sufficient conditions for scalar-subquery quantified-comparison evaluation.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `scalar subquery`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_formula_quant_success_iff :
  forall env which_quantifier which_predicate arguments subquery truth,
    eval_formula env
      (FExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlSuccess truth) <->
    exists rows,
      first_runtime_error
        (@eval_aggterm_runtime_error T
          symbol_runtime_error aggregate_runtime_error env)
        arguments = None /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = quantified_rows_truth env which_quantifier which_predicate
        arguments subquery rows.
```

## `formula_quant_acceptance_exact_of_fixed_truth`

Source: [`theories/FormalSQL/SubqueryFacts.v:1094`](../SubqueryFacts.v#L1094)

Purpose/direction: States the formula quant acceptance exact of fixed truth law for predicate-subquery evaluation, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem formula_quant_acceptance_exact_of_fixed_truth :
  forall env quantifier predicate arguments subquery fixed_truth,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env) arguments = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      quantified_rows_truth env quantifier predicate arguments
        subquery rows = fixed_truth) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Quant quantifier predicate arguments subquery)
      (Bool.is_true (B T) fixed_truth).
```

## `eval_formula_quant_forall_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1132`](../SubqueryFacts.v#L1132)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_quant_forall_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_formula_quant_forall_empty :
  forall env which_predicate arguments subquery,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env
      (FExpr_Quant Forall_F which_predicate arguments subquery)
      (SqlSuccess (Bool.true (B T))).
```

## `eval_formula_quant_exists_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1151`](../SubqueryFacts.v#L1151)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_quant_exists_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma eval_formula_quant_exists_empty :
  forall env which_predicate arguments subquery,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env
      (FExpr_Quant Exists_F which_predicate arguments subquery)
      (SqlSuccess (Bool.false (B T))).
```

## `eval_formula_in_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1170`](../SubqueryFacts.v#L1170)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_formula_in_error_iff :
  forall env select_items subquery error,
    eval_formula env (FExpr_In select_items subquery) (SqlError error) <->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = Some error \/
    (first_runtime_error
       (@eval_select_runtime_error T
         symbol_runtime_error aggregate_runtime_error env)
       select_items = None /\
     eval_query env subquery (SqlError error)).
```

## `eval_formula_in_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1192`](../SubqueryFacts.v#L1192)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma eval_formula_in_success_iff :
  forall env select_items subquery truth,
    eval_formula env (FExpr_In select_items subquery) (SqlSuccess truth) <->
    exists rows,
      first_runtime_error
        (@eval_select_runtime_error T
          symbol_runtime_error aggregate_runtime_error env)
        select_items = None /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = in_rows_truth env select_items rows.
```

## `eval_formula_in_empty`

Source: [`theories/FormalSQL/SubqueryFacts.v:1210`](../SubqueryFacts.v#L1210)

Purpose/direction: States the exact empty-input or empty-result law for predicate-subquery evaluation.

Applicability: Use when the goal or a hypothesis matches the `eval_formula_in_empty` direction for predicate-subquery evaluation; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma eval_formula_in_empty :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env (FExpr_In select_items subquery)
      (SqlSuccess (Bool.false (B T))).
```

## `formula_in_truth_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1232`](../SubqueryFacts.v#L1232)

Purpose/direction: Builds exact tuple-valued IN truth from runtime-safe arguments, an inhabited child, fixed Bool3 truth across every child success, and no errors.

Applicability: Use after proving argument safety, child-success inhabitation, one fixed full Bool3 IN truth across all legal child observations, and absence of child errors; an acceptance bit alone cannot justify NOT IN.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `exact Bool3 truth`, `UNKNOWN`

```rocq
Theorem formula_in_truth_exact :
  forall env select_items subquery fixed_truth,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth env select_items rows = fixed_truth) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_truth_exact_at env (FExpr_In select_items subquery) fixed_truth.
```

## `formula_in_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1268`](../SubqueryFacts.v#L1268)

Purpose/direction: Builds exact tuple-valued IN acceptance from pointwise SQL equality decisions while retaining empty inputs, duplicates, UNKNOWN, and errors.

Applicability: Use at a filter/join acceptance boundary with the pointwise tuple-IN decision and every displayed child/no-error premise; FALSE and UNKNOWN may share rejection but remain distinct semantic truths.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `UNKNOWN`, `filter acceptance`

```rocq
Theorem formula_in_acceptance_exact :
  forall env select_items subquery (accept : tuple T -> bool) accepted,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall row,
      Bool.is_true (B T) (in_row_truth env select_items row) = accept row) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      existsb accept rows = accepted) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_In select_items subquery) accepted.
```

## `formula_not_in_acceptance_exact_of_fixed_truth`

Source: [`theories/FormalSQL/SubqueryFacts.v:1314`](../SubqueryFacts.v#L1314)

Purpose/direction: Builds NOT IN acceptance only from fixed exact IN truth, applying SQL negation before TRUE projection so UNKNOWN is never accepted.

Applicability: Use after proving argument safety, child-success inhabitation, one fixed full Bool3 IN truth across all legal child observations, and absence of child errors; an acceptance bit alone cannot justify NOT IN.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT IN`, `exact Bool3 truth`, `UNKNOWN`, `runtime error`

```rocq
Theorem formula_not_in_acceptance_exact_of_fixed_truth :
  forall env select_items subquery fixed_truth,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth env select_items rows = fixed_truth) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Not (FExpr_In select_items subquery))
      (Bool.is_true (B T) (Bool.negb (B T) fixed_truth)).
```

## `eval_formula_exists_error_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1337`](../SubqueryFacts.v#L1337)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_formula_exists_error_iff : forall env subquery error,
  eval_formula env (FExpr_Exists subquery) (SqlError error) <->
  eval_exists env subquery (SqlError error).
```

## `eval_formula_exists_success_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1346`](../SubqueryFacts.v#L1346)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_formula_exists_success_iff : forall env subquery truth,
  eval_formula env (FExpr_Exists subquery) (SqlSuccess truth) <->
  (truth = Bool.false (B T) /\
    eval_exists env subquery (SqlSuccess (Bool.false (B T)))) \/
  (truth = Bool.true (B T) /\
    eval_exists env subquery (SqlSuccess (Bool.true (B T)))).
```

## `eval_formula_exists_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1365`](../SubqueryFacts.v#L1365)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    forall outcome,
      eval_formula left_env (FExpr_Exists subquery) outcome <->
      eval_formula right_env (FExpr_Exists subquery) outcome.
```

## `formula_expr_exists_env_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1393`](../SubqueryFacts.v#L1393)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Exists subquery).
```

## `eval_formula_in_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1409`](../SubqueryFacts.v#L1409)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_in_env_congr_safe :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    forall outcome,
      eval_formula left_env (FExpr_In select_items subquery) outcome <->
      eval_formula right_env (FExpr_In select_items subquery) outcome.
```

## `formula_expr_in_env_congr_safe`

Source: [`theories/FormalSQL/SubqueryFacts.v:1460`](../SubqueryFacts.v#L1460)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma formula_expr_in_env_congr_safe :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    query_expr_env_outcome_equiv left_env right_env subquery ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_In select_items subquery).
```

## `eval_formula_exists_false_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1480`](../SubqueryFacts.v#L1480)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_formula_exists_false_iff : forall env subquery,
  eval_formula env (FExpr_Exists subquery)
    (SqlSuccess (Bool.false (B T))) <->
  eval_exists env subquery (SqlSuccess (Bool.false (B T))).
```

## `eval_formula_exists_true_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1494`](../SubqueryFacts.v#L1494)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma eval_formula_exists_true_iff : forall env subquery,
  eval_formula env (FExpr_Exists subquery)
    (SqlSuccess (Bool.true (B T))) <->
  eval_exists env subquery (SqlSuccess (Bool.true (B T))).
```

## `exists_truth_from_empty_negation_acceptance`

Source: [`theories/FormalSQL/SubqueryFacts.v:1522`](../SubqueryFacts.v#L1522)

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

## `formula_exists_truth_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1536`](../SubqueryFacts.v#L1536)

Purpose/direction: Builds the exact two-valued EXISTS truth from inhabited child outcomes that all agree on emptiness and from exclusion of every child error.

Applicability: Use at one fixed, possibly correlated environment after proving a child success, agreement of every child success on emptiness, and exclusion of every child runtime error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`, `exact Bool3 truth`, `empty input`

```rocq
Theorem formula_exists_truth_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    formula_truth_exact_at env (FExpr_Exists subquery)
      (exists_truth_from_empty empty).
```

## `formula_not_exists_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1565`](../SubqueryFacts.v#L1565)

Purpose/direction: Characterizes NOT EXISTS acceptance as child emptiness while preserving the fixed correlated environment and excluding every child runtime error.

Applicability: Use at one fixed, possibly correlated environment after proving a child success, agreement of every child success on emptiness, and exclusion of every child runtime error.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `runtime outcome`, `runtime safety`, `error propagation`, `NOT EXISTS`, `empty input`, `runtime error`

```rocq
Theorem formula_not_exists_acceptance_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Not (FExpr_Exists subquery)) empty.
```

## `formula_exists_acceptance_exact`

Source: [`theories/FormalSQL/SubqueryFacts.v:1590`](../SubqueryFacts.v#L1590)

Purpose/direction: Builds an exact EXISTS acceptance contract from inhabited child successes that agree on emptiness and from explicit absence of errors.

Applicability: Use at one fixed, possibly correlated environment after providing a child success, agreement of every child success on emptiness, and absence of every child SQL error.

Important premises: Retain child-success inhabitation, universal agreement on `rows_empty_decision`, the fixed environment, and exclusion of every error.

Cross-index: `runtime`, `filter`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Theorem formula_exists_acceptance_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Exists subquery) (Datatypes.negb empty).
```

## `eval_formula_quant_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1615`](../SubqueryFacts.v#L1615)

Purpose/direction: Transports or composes scalar-subquery quantified-comparison evaluation across the declared equivalence.

Applicability: Use after the restricted scalar-subquery child has been lowered, to invert/transport the surrounding quantified comparison without changing its SQL NULL or error outcome.

Important premises: every explicit antecedent (`->`) in the declaration is required; this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `scalar subquery`, `subquery`, `quantified predicate`, `ANY/ALL`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_quant_subquery_congr :
  forall env which_quantifier which_predicate arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env
        (FExpr_Quant which_quantifier which_predicate arguments left) outcome <->
      eval_formula env
        (FExpr_Quant which_quantifier which_predicate arguments right) outcome.
```

## `eval_formula_in_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1642`](../SubqueryFacts.v#L1642)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `IN`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_in_subquery_congr :
  forall env select_items left right,
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env (FExpr_In select_items left) outcome <->
      eval_formula env (FExpr_In select_items right) outcome.
```

## `eval_formula_exists_subquery_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1664`](../SubqueryFacts.v#L1664)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_exists_subquery_congr :
  forall env left right,
    (forall outcome,
      eval_exists env left outcome <-> eval_exists env right outcome) ->
    forall outcome,
      eval_formula env (FExpr_Exists left) outcome <->
      eval_formula env (FExpr_Exists right) outcome.
```

## `formula_expr_quant_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1688`](../SubqueryFacts.v#L1688)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `quantified predicate`, `ANY/ALL`

```rocq
Lemma formula_expr_quant_admissible_iff :
  forall which_quantifier which_predicate arguments subquery,
    @formula_expr_admissible T relname basesort
      (FExpr_Quant which_quantifier which_predicate arguments subquery) <->
    @query_expr_admissible T relname basesort subquery /\
    prop_forall (aggterm_phase_admissible ScalarPhaseHaving) arguments /\
    length arguments = 1%nat /\
    length (query_expr_outputs subquery) = 1%nat /\
    (length arguments + length (query_expr_outputs subquery))%nat =
      predicate_arity T which_predicate.
```

## `formula_expr_in_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1702`](../SubqueryFacts.v#L1702)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `IN`

```rocq
Lemma formula_expr_in_admissible_iff : forall select_items subquery,
  @formula_expr_admissible T relname basesort
    (FExpr_In select_items subquery) <->
  @query_expr_admissible T relname basesort subquery /\
  select_list_phase_admissible ScalarPhaseHaving
    (_Select_List select_items) /\
  select_list_sort (_Select_List select_items) =S= query_expr_sort subquery /\
  query_in_positionally_aligned (_Select_List select_items)
    (query_expr_outputs subquery).
```

## `formula_expr_exists_admissible_iff`

Source: [`theories/FormalSQL/SubqueryFacts.v:1715`](../SubqueryFacts.v#L1715)

Purpose/direction: Gives necessary and sufficient conditions for predicate-subquery evaluation.

Applicability: Use in either direction to invert or construct a goal about predicate-subquery evaluation.

Important premises: preserve the displayed environment/correlation and SQL three-valued result.

Cross-index: primary card only

Search aliases: `predicate subquery semantics`, `subquery`, `EXISTS`

```rocq
Lemma formula_expr_exists_admissible_iff : forall subquery,
  @formula_expr_admissible T relname basesort (FExpr_Exists subquery) <->
  @query_expr_admissible T relname basesort subquery.
```

## `eval_formula_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1722`](../SubqueryFacts.v#L1722)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_formula_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context left) outcome <->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context right) outcome.
```

## `eval_query_context_correlated_congr`

Source: [`theories/FormalSQL/SubqueryFacts.v:1738`](../SubqueryFacts.v#L1738)

Purpose/direction: Transports or composes predicate-subquery evaluation across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about predicate-subquery evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; preserve the displayed environment/correlation and SQL three-valued result; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `scalar`

Search aliases: `predicate subquery semantics`, `subquery`, `correlated`, `correlation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
```
