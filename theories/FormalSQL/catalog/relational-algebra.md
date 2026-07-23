# Bags, occurrences, projection, and relational algebra

Route here for: bag/list abstraction, multiplicity, filter/project/join/set operators.

This focused catalog contains 115 declarations routed at declaration granularity from `OccFacts.v`, `OrderedQueryFacts.v`, `ProofAgentFacade.v`, `RelationalAlgebraFacts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `query_equiv_iff_occ`

Source: [`theories/FormalSQL/OccFacts.v:20`](../OccFacts.v#L20)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `equivalence`, `congruence`

```rocq
Lemma query_equiv_iff_occ :
  forall db q1 q2,
    query_equiv db q1 q2 <->
    query_succeeds db q1 /\
    query_succeeds db q2 /\
    forall t, query_occ db q1 t = query_occ db q2 t.
```

## `pi_congr`

Source: [`theories/FormalSQL/OccFacts.v:40`](../OccFacts.v#L40)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `projection` (rank 36)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `equivalence`, `congruence`

```rocq
Lemma pi_congr :
  forall db s q1 q2,
    query_equiv db q1 q2 ->
    query_succeeds db (Pi s q1) ->
    query_succeeds db (Pi s q2) ->
    query_equiv db (Pi s q1) (Pi s q2).
```

## `sigma_congr`

Source: [`theories/FormalSQL/OccFacts.v:79`](../OccFacts.v#L79)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `filter` (rank 30)

Search aliases: `relational algebra`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma sigma_congr :
  forall db f q1 q2,
    query_equiv db q1 q2 ->
    query_succeeds db (Sigma f q1) ->
    query_succeeds db (Sigma f q2) ->
    query_equiv db (Sigma f q1) (Sigma f q2).
```

## `pi_eval_bag_congr`

Source: [`theories/FormalSQL/OccFacts.v:115`](../OccFacts.v#L115)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `projection` (rank 26), `bag` (rank 24)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma pi_eval_bag_congr :
  forall db env select_list left right,
    eval_query_in_env db env left =BE= eval_query_in_env db env right ->
    eval_query_in_env db env (Pi select_list left) =BE=
    eval_query_in_env db env (Pi select_list right).
```

## `sigma_eval_bag_congr`

Source: [`theories/FormalSQL/OccFacts.v:138`](../OccFacts.v#L138)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `filter` (rank 24), `bag` (rank 24)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma sigma_eval_bag_congr :
  forall db env formula left right,
    eval_query_in_env db env left =BE= eval_query_in_env db env right ->
    eval_query_in_env db env (Sigma formula left) =BE=
    eval_query_in_env db env (Sigma formula right).
```

## `gamma_eval_bag_congr`

Source: [`theories/FormalSQL/OccFacts.v:160`](../OccFacts.v#L160)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 24)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma gamma_eval_bag_congr :
  forall db env select_list group_terms having left right,
    eval_query_in_env db env left =BE= eval_query_in_env db env right ->
    eval_query_in_env db env
      (Gamma select_list group_terms having left) =BE=
    eval_query_in_env db env
      (Gamma select_list group_terms having right).
```

## `query_satisfies_of_equiv`

Source: [`theories/FormalSQL/OccFacts.v:211`](../OccFacts.v#L211)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma query_satisfies_of_equiv :
  forall db q1 q2 f,
    query_equiv db q1 q2 ->
    query_satisfies db q1 f ->
    query_satisfies db q2 f.
```

## `eval_query_expr_project_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:503`](../OrderedQueryFacts.v#L503)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `projection` (rank 36)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma eval_query_expr_project_success_iff :
  forall env select_list input output,
    eval_query env (QExpr_Project select_list input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list input_rows = SqlSuccess output.
```

## `eval_query_expr_filter_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:538`](../OrderedQueryFacts.v#L538)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `filter` (rank 28)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_query_expr_filter_success_iff :
  forall env formula input output,
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlSuccess output).
```

## `eval_filter_rows_always_true_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1699`](../OrderedQueryFacts.v#L1699)

Purpose/direction: Characterizes successful filtering when every reached formula evaluation succeeds with SQL TRUE.

Applicability: Use only after proving every reached predicate outcome is exactly `SqlSuccess true3`; errors and UNKNOWN are not covered.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter` (rank 26)

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_filter_rows_always_true_iff :
  forall env formula rows,
    (forall row,
      In row rows ->
      forall outcome,
        @eval_formula_expr_outcome T relname basesort instance unknown
          contains_nulls symbol_runtime_error aggregate_runtime_error
          value_is_null (env_t T env row) formula outcome <->
        outcome = SqlSuccess (Bool.true (B T))) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null env formula rows outcome <->
      outcome = SqlSuccess rows.
```

## `relational_permutation_map_inv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1805`](../OrderedQueryFacts.v#L1805)

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma relational_permutation_map_inv :
  forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) output input,
    _permut R output (map f input) ->
    exists reordered,
      Permutation input reordered /\
      Forall2 R output (map f reordered).
```

## `projected_rows_same_as_mapped_bag`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1915`](../OrderedQueryFacts.v#L1915)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma projected_rows_same_as_mapped_bag :
  forall env select_list rows bag,
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        bag).
```

## `mapped_bag_rows_have_projection_preimage`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1947`](../OrderedQueryFacts.v#L1947)

Purpose/direction: States the mapped bag rows have projection preimage law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 36), `bag` (rank 36)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma mapped_bag_rows_have_projection_preimage :
  forall env select_list bag output,
    query_same_rows_as_bag output
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        bag) ->
    exists input_rows,
      query_same_rows_as_bag input_rows bag /\
      ordered_rows_equiv T output
        (map
          (fun row =>
            projection T (env_t T env row) (@Select_List T select_list))
          input_rows).
```

## `tnull_direct_projection_preserves_attribute`

Source: [`theories/FormalSQL/ProofAgentFacade.v:213`](../ProofAgentFacade.v#L213)

Purpose/direction: Shows that the indicated operator preserves the displayed relational algebra property.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_preserves_attribute` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `facade` (rank 16), `projection` (rank 16), `schema` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `schema conformance`, `typing`

```rocq
Lemma tnull_direct_projection_preserves_attribute :
  forall (env : TNullEnvironment) (select : TNullSelectList)
      (attribute : TNullAttribute) (row : TNullRow),
    select_list_directly_selects_attr select attribute ->
    select_list_has_unique_outputs select ->
    attribute inS TNullRowLabels row ->
    TNullRowValue (TNullProjectRow env select row) attribute =
    TNullRowValue row attribute.
```

## `tnull_direct_projection_row_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:231`](../ProofAgentFacade.v#L231)

Purpose/direction: States the tnull direct projection row equality law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_row_eq` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_row_eq :
  forall (env : TNullEnvironment) (select : TNullSelectList)
      (row : TNullRow),
    select_list_has_unique_outputs select ->
    (forall attribute,
      attribute inS TNullRowLabels row ->
      select_list_directly_selects_attr select attribute) ->
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select row))
      (TNullRowLabels row) ->
    TNullRowEq (TNullProjectRow env select row) row.
```

## `tnull_row_permut_implies_rows_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:261`](../ProofAgentFacade.v#L261)

Purpose/direction: States the tnull row permut implies rows bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 6)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_row_permut_implies_rows_bag_eq :
  forall left right,
    TNullRowPermut left right ->
    TNullBagEq (TNullRowsBag left) (TNullRowsBag right).
```

## `tnull_double_projection_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:274`](../ProofAgentFacade.v#L274)

Purpose/direction: States the tnull double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 6)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_double_projection_bag_eq :
  forall env outer_left inner_left outer_right inner_right bag,
    (forall row,
      TNullRowEq
        (TNullProjectRow env outer_left
          (TNullProjectRow env inner_left row))
        (TNullProjectRow env outer_right
          (TNullProjectRow env inner_right row))) ->
    TNullBagEq
      (TNullBagMap
        (fun row => TNullProjectRow env outer_left row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner_left row) bag))
      (TNullBagMap
        (fun row => TNullProjectRow env outer_right row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner_right row) bag)).
```

## `tnull_double_projection_query_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:300`](../ProofAgentFacade.v#L300)

Purpose/direction: States the tnull double projection query bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 4), `projection` (rank 4), `bag` (rank 2)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_double_projection_query_bag_eq :
  forall (db : TNullDatabase) (env : TNullEnvironment)
      (outer_left inner_left outer_right inner_right : TNullSelectList)
      (input : TNullQuery),
    (forall row,
      TNullRowEq
        (TNullProjectRow env outer_left
          (TNullProjectRow env inner_left row))
        (TNullProjectRow env outer_right
          (TNullProjectRow env inner_right row))) ->
    TNullBagEq
      (eval_query_in_env db env
        (Pi outer_left (Pi inner_left input)))
      (eval_query_in_env db env
        (Pi outer_right (Pi inner_right input))).
```

## `tnull_map_theta_join_total_functional`

Source: [`theories/FormalSQL/ProofAgentFacade.v:341`](../ProofAgentFacade.v#L341)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_theta_join_total_functional :
  forall (B : Type)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> B) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (TNullThetaJoinRows join accept left right) =
    map emit left.
```

## `tnull_map_left_join_total_functional`

Source: [`theories/FormalSQL/ProofAgentFacade.v:364`](../ProofAgentFacade.v#L364)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_left_join_total_functional` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_left_join_total_functional :
  forall (B : Type)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> B) (pad : TNullRow -> TNullRow)
      left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left -> project (pad left_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (TNullLeftJoinRows join accept pad left right) =
    map emit left.
```

## `tnull_map_theta_join_total_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:394`](../ProofAgentFacade.v#L394)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional_permut` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_theta_join_total_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit left).
```

## `tnull_map_left_join_total_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:449`](../ProofAgentFacade.v#L449)

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_left_join_total_functional_permut` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 10), `join` (rank 2)

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_left_join_total_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (pad : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      TNullRowEq (project (pad left_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullLeftJoinRows join accept pad left right))
      (map emit left).
```

## `tnull_row_eq_of_labels_and_values`

Source: [`theories/FormalSQL/ProofAgentFacade.v:654`](../ProofAgentFacade.v#L654)

Purpose/direction: States the tnull row equality of labels and values law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_row_eq_of_labels_and_values` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`

```rocq
Lemma tnull_row_eq_of_labels_and_values :
  forall left right,
    TNullAttributeSetEq (TNullRowLabels left) (TNullRowLabels right) ->
    (forall attribute,
      attribute inS TNullRowLabels left ->
      TNullRowValue left attribute = TNullRowValue right attribute) ->
    TNullRowEq left right.
```

## `tnull_direct_projection_row_eq_on_expected_labels`

Source: [`theories/FormalSQL/ProofAgentFacade.v:671`](../ProofAgentFacade.v#L671)

Purpose/direction: States the tnull direct projection row equality on expected labels law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_row_eq_on_expected_labels` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade` (rank 14), `projection` (rank 8)

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_row_eq_on_expected_labels :
  forall env select expected row,
    select_list_has_unique_outputs select ->
    (forall attribute,
      attribute inS expected ->
      select_list_directly_selects_attr select attribute) ->
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select row)) expected ->
    TNullAttributeSetEq (TNullRowLabels row) expected ->
    TNullRowEq (TNullProjectRow env select row) row.
```

## `tnull_bag_map_ext`

Source: [`theories/FormalSQL/ProofAgentFacade.v:697`](../ProofAgentFacade.v#L697)

Purpose/direction: States the tnull bag map ext law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_bag_map_ext :
  forall left_map right_map bag,
    (forall row,
      In row (Febag.elements TNullRowBagRecord bag) ->
      TNullRowEq (left_map row) (right_map row)) ->
    TNullBagEq
      (TNullBagMap left_map bag)
      (TNullBagMap right_map bag).
```

## `tnull_bag_map_identity`

Source: [`theories/FormalSQL/ProofAgentFacade.v:714`](../ProofAgentFacade.v#L714)

Purpose/direction: States the tnull bag map identity law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_bag_map_identity :
  forall bag,
    TNullBagEq (TNullBagMap (fun row => row) bag) bag.
```

## `tnull_projection_bag_map_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:727`](../ProofAgentFacade.v#L727)

Purpose/direction: States the tnull projection bag map compose law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 16)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_projection_bag_map_compose :
  forall env outer inner bag,
    TNullBagEq
      (TNullBagMap
        (fun row => TNullProjectRow env outer row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner row) bag))
      (TNullBagMap
        (fun row =>
          TNullProjectRow env outer (TNullProjectRow env inner row)) bag).
```

## `tnull_single_double_projection_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:771`](../ProofAgentFacade.v#L771)

Purpose/direction: States the tnull single double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 16), `projection` (rank 16), `bag` (rank 6)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_single_double_projection_bag_eq :
  forall env single outer inner bag,
    (forall row,
      In row (Febag.elements TNullRowBagRecord bag) ->
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row))) ->
    TNullBagEq
      (TNullBagMap (fun row => TNullProjectRow env single row) bag)
      (TNullBagMap
        (fun row => TNullProjectRow env outer row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner row) bag)).
```

## `tnull_single_double_projection_query_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:792`](../ProofAgentFacade.v#L792)

Purpose/direction: States the tnull single double projection query bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 4), `projection` (rank 4), `bag` (rank 2)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_single_double_projection_query_bag_eq :
  forall db env single outer inner input,
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row))) ->
    TNullBagEq
      (eval_query_in_env db env (Pi single input))
      (eval_query_in_env db env (Pi outer (Pi inner input))).
```

## `tnull_direct_projection_query_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:834`](../ProofAgentFacade.v#L834)

Purpose/direction: States the tnull direct projection query bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 4), `projection` (rank 4), `bag` (rank 2)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_direct_projection_query_bag_eq :
  forall db env select input,
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullRowEq (TNullProjectRow env select row) row) ->
    TNullBagEq
      (eval_query_in_env db env (Pi select input))
      (eval_query_in_env db env input).
```

## `tnull_direct_table_projection_query_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:858`](../ProofAgentFacade.v#L858)

Purpose/direction: States the tnull direct table projection query bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade` (rank 3), `projection` (rank 1), `bag` (rank 1)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary tnull_direct_table_projection_query_bag_eq :
  forall db env relation select,
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord (@_instance TNull db relation)) ->
      TNullRowEq (TNullProjectRow env select row) row) ->
    TNullBagEq
      (eval_query_in_env db env
        (Pi select (@Q_Table TNull relname relation)))
      (eval_query_in_env db env (@Q_Table TNull relname relation)).
```

## `tnull_cross_join_eval_bag_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:876`](../ProofAgentFacade.v#L876)

Purpose/direction: Lifts bag equality through the displayed TNull relational operator under its explicit evaluation premises.

Applicability: Use to transport an already proved child bag equality through this operator; retain every displayed evaluator premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 12), `join` (rank 4), `bag` (rank 4)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma tnull_cross_join_eval_bag_congr :
  forall db env left left' right right',
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env left') ->
    TNullBagEq
      (eval_query_in_env db env right)
      (eval_query_in_env db env right') ->
    TNullBagEq
      (eval_query_in_env db env (CrossJoin left right))
      (eval_query_in_env db env (CrossJoin left' right')).
```

## `tnull_pi_eval_bag_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:899`](../ProofAgentFacade.v#L899)

Purpose/direction: Lifts bag equality through the displayed TNull relational operator under its explicit evaluation premises.

Applicability: Use to transport an already proved child bag equality through this operator; retain every displayed evaluator premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 12), `projection` (rank 6), `bag` (rank 4)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma tnull_pi_eval_bag_congr :
  forall db env select left right,
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env right) ->
    TNullBagEq
      (eval_query_in_env db env (Pi select left))
      (eval_query_in_env db env (Pi select right)).
```

## `tnull_sigma_eval_bag_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:912`](../ProofAgentFacade.v#L912)

Purpose/direction: Lifts bag equality through the displayed TNull relational operator under its explicit evaluation premises.

Applicability: Use to transport an already proved child bag equality through this operator; retain every displayed evaluator premise.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `facade` (rank 12), `filter` (rank 4), `bag` (rank 4)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma tnull_sigma_eval_bag_congr :
  forall db env formula left right,
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env right) ->
    TNullBagEq
      (eval_query_in_env db env (Sigma formula left))
      (eval_query_in_env db env (Sigma formula right)).
```

## `interp_direct_attribute_in_env_t`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:18`](../RelationalAlgebraFacts.v#L18)

Purpose/direction: States the interp direct attribute in env t law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_direct_attribute_in_env_t` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 52)

Search aliases: `relational algebra`, `schema conformance`, `typing`

```rocq
Lemma interp_direct_attribute_in_env_t :
  forall (T : Tuple.Rcd) env row attribute,
    attribute inS labels T row ->
    interp_aggterm T (env_t T env row)
      (@A_Expr T (@F_Dot T attribute)) =
    dot T row attribute.
```

## `rel_equiv_refl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:33`](../RelationalAlgebraFacts.v#L33)

Purpose/direction: Establishes reflexivity for relational algebra.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_refl :
  forall (A : Type) (relation : A -> Prop),
    rel_equiv relation relation.
```

## `rel_equiv_sym`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:40`](../RelationalAlgebraFacts.v#L40)

Purpose/direction: Reverses a proved relational algebra relation.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_sym :
  forall (A : Type) (left right : A -> Prop),
    rel_equiv left right -> rel_equiv right left.
```

## `rel_equiv_trans`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:49`](../RelationalAlgebraFacts.v#L49)

Purpose/direction: Composes two relational algebra relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_trans :
  forall (A : Type) (first second third : A -> Prop),
    rel_equiv first second ->
    rel_equiv second third ->
    rel_equiv first third.
```

## `rel_incl_refl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:63`](../RelationalAlgebraFacts.v#L63)

Purpose/direction: Establishes reflexivity for relational algebra.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_incl_refl :
  forall (A : Type) (relation : A -> Prop),
    rel_incl relation relation.
```

## `rel_incl_trans`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:70`](../RelationalAlgebraFacts.v#L70)

Purpose/direction: Composes two relational algebra relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_incl_trans :
  forall (A : Type) (first second third : A -> Prop),
    rel_incl first second ->
    rel_incl second third ->
    rel_incl first third.
```

## `rel_equiv_iff_mutual_incl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:80`](../RelationalAlgebraFacts.v#L80)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma rel_equiv_iff_mutual_incl :
  forall (A : Type) (left right : A -> Prop),
    rel_equiv left right <->
    rel_incl left right /\ rel_incl right left.
```

## `alpha_rel_incl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:94`](../RelationalAlgebraFacts.v#L94)

Purpose/direction: States the alpha rel incl law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `alpha_rel_incl` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`

```rocq
Lemma alpha_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_incl left right ->
    rel_incl (alpha T left) (alpha T right).
```

## `gamma_rel_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:104`](../RelationalAlgebraFacts.v#L104)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: primary card only

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma gamma_rel_equiv :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T -> Prop),
    rel_equiv left right ->
    rel_equiv (gamma T left) (gamma T right).
```

## `gamma_rel_incl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:115`](../RelationalAlgebraFacts.v#L115)

Purpose/direction: States the gamma rel incl law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `gamma_rel_incl` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`

```rocq
Lemma gamma_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T -> Prop),
    rel_incl left right ->
    rel_incl (gamma T left) (gamma T right).
```

## `permutation_closure_rel_incl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:126`](../RelationalAlgebraFacts.v#L126)

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma permutation_closure_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_incl left right ->
    rel_incl
      (permutation_closure T left)
      (permutation_closure T right).
```

## `permutation_closure_rel_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:139`](../RelationalAlgebraFacts.v#L139)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma permutation_closure_rel_equiv :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    rel_equiv
      (permutation_closure T left)
      (permutation_closure T right).
```

## `permutation_closure_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:155`](../RelationalAlgebraFacts.v#L155)

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma permutation_closure_idempotent :
  forall (T : Tuple.Rcd) (observations : list (tuple T) -> Prop),
    rel_equiv
      (permutation_closure T (permutation_closure T observations))
      (permutation_closure T observations).
```

## `permutation_closure_least_bag_closed`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:167`](../RelationalAlgebraFacts.v#L167)

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 28)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma permutation_closure_least_bag_closed :
  forall (T : Tuple.Rcd)
         (observations target : list (tuple T) -> Prop),
    rel_incl observations target ->
    BagClosed T target ->
    rel_incl (permutation_closure T observations) target.
```

## `bag_closed_rel_equiv_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:181`](../RelationalAlgebraFacts.v#L181)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_closed_rel_equiv_transport :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    BagClosed T left ->
    BagClosed T right.
```

## `bag_closed_intersection`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:196`](../RelationalAlgebraFacts.v#L196)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_intersection :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows /\ right rows).
```

## `bag_closed_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:212`](../RelationalAlgebraFacts.v#L212)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_union :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows \/ right rows).
```

## `bag_closed_complement`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:230`](../RelationalAlgebraFacts.v#L230)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_complement :
  forall (T : Tuple.Rcd) (predicate : list (tuple T) -> Prop),
    BagClosed T predicate ->
    BagClosed T (fun rows => ~ predicate rows).
```

## `bag_closed_exists`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:242`](../RelationalAlgebraFacts.v#L242)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_exists :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => exists index, family index rows).
```

## `bag_closed_forall`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:257`](../RelationalAlgebraFacts.v#L257)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_forall :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => forall index, family index rows).
```

## `ordered_rows_equiv_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:273`](../RelationalAlgebraFacts.v#L273)

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `cardinality` (rank 44)

Search aliases: `relational algebra`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_length :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    length left = length right.
```

## `ordered_rows_equiv_occ`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:283`](../RelationalAlgebraFacts.v#L283)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_occ :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    forall row,
      Oeset.nb_occ (OTuple T) row left =
      Oeset.nb_occ (OTuple T) row right.
```

## `rows_bag_occ`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:295`](../RelationalAlgebraFacts.v#L295)

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_occ :
  forall (T : Tuple.Rcd) (rows : list (tuple T)) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T rows) =
    Oeset.nb_occ (OTuple T) row rows.
```

## `bag_eq_iff_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:305`](../RelationalAlgebraFacts.v#L305)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 26)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_eq_iff_occurrences :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right <->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right.
```

## `bag_eq_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:318`](../RelationalAlgebraFacts.v#L318)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 26), `cardinality` (rank 52)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_eq_cardinal :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
    Febag.cardinal (Fecol.CBag (CTuple T)) right.
```

## `rows_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:330`](../RelationalAlgebraFacts.v#L330)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T)),
    Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T rows) =
    N.of_nat (length rows).
```

## `query_same_rows_as_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:340`](../RelationalAlgebraFacts.v#L340)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag rows bag ->
    Febag.cardinal (Fecol.CBag (CTuple T)) bag =
    N.of_nat (length rows).
```

## `query_same_rows_as_bag_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:354`](../RelationalAlgebraFacts.v#L354)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36), `cardinality` (rank 44)

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_length :
  forall (T : Tuple.Rcd) (first second : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag first bag ->
    query_same_rows_as_bag second bag ->
    length first = length second.
```

## `query_same_rows_as_bag_iff_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:368`](../RelationalAlgebraFacts.v#L368)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_iff_occurrences :
  forall (T : Tuple.Rcd) (rows : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag rows bag <->
    forall row,
      Oeset.nb_occ (OTuple T) row rows =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
```

## `query_same_rows_as_bag_filter`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:387`](../RelationalAlgebraFacts.v#L387)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter` (rank 28), `bag` (rank 36)

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_filter :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool) rows bag,
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    @query_same_rows_as_bag T rows bag ->
    @query_same_rows_as_bag T (filter keep rows)
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag).
```

## `query_same_rows_as_filtered_bag_preimage`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:414`](../RelationalAlgebraFacts.v#L414)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_filtered_bag_preimage :
  forall (T : Tuple.Rcd) rows bag (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    @query_same_rows_as_bag T rows
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag) ->
    exists input_rows,
      @query_same_rows_as_bag T input_rows bag /\
      filter keep input_rows = rows.
```

## `double_projection_bag_eq`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:487`](../RelationalAlgebraFacts.v#L487)

Purpose/direction: States the double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 36), `bag` (rank 26)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma double_projection_bag_eq :
  forall (T : Tuple.Rcd) (env : Env.env T)
      (outer_left inner_left outer_right inner_right : _select_list T)
      (bag : SqlQuerySemantics.bagT T),
    (forall row,
      Oeset.compare (OTuple T)
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_left)))
          (@Select_List T outer_left))
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_right)))
          (@Select_List T outer_right)) = Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row => projection T (env_t T env row) (@Select_List T outer_left))
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          (fun row => projection T (env_t T env row) (@Select_List T inner_left))
          bag))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row => projection T (env_t T env row) (@Select_List T outer_right))
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          (fun row => projection T (env_t T env row) (@Select_List T inner_right))
          bag)).
```

## `double_projection_query_bag_eq`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:582`](../RelationalAlgebraFacts.v#L582)

Purpose/direction: States the double projection query bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection` (rank 23), `bag` (rank 21)

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary double_projection_query_bag_eq :
  forall (T : Tuple.Rcd) (relname : Type)
      (basesort : relname -> Fset.set (A T))
      (instance : relname -> Febag.bag (Fecol.CBag (CTuple T)))
      unknown contains_nulls env
      (outer_left inner_left outer_right inner_right : _select_list T)
      (input : query T relname),
    (forall row,
      Oeset.compare (OTuple T)
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_left)))
          (@Select_List T outer_left))
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_right)))
          (@Select_List T outer_right)) = Eq) ->
    bag_eq T
      (@eval_query T relname basesort instance unknown contains_nulls env
        (@Q_Pi T relname outer_left (@Q_Pi T relname inner_left input)))
      (@eval_query T relname basesort instance unknown contains_nulls env
        (@Q_Pi T relname outer_right (@Q_Pi T relname inner_right input))).
```

## `oeset_nb_occ_of_NoDupA`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:616`](../RelationalAlgebraFacts.v#L616)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`

```rocq
Lemma oeset_nb_occ_of_NoDupA :
  forall (A : Type) (ordered : Oeset.Rcd A) values,
    SetoidList.NoDupA
      (fun left right => Oeset.compare ordered left right = Eq) values ->
    forall value,
      Oeset.nb_occ ordered value values =
      if Oeset.mem_bool ordered value values then 1%N else 0%N.
```

## `oeset_NoDupA_same_support_same_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:652`](../RelationalAlgebraFacts.v#L652)

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`

```rocq
Lemma oeset_NoDupA_same_support_same_occurrences :
  forall (A : Type) (ordered : Oeset.Rcd A) left right,
    SetoidList.NoDupA
      (fun first second => Oeset.compare ordered first second = Eq) left ->
    SetoidList.NoDupA
      (fun first second => Oeset.compare ordered first second = Eq) right ->
    (forall value,
      Oeset.mem_bool ordered value left =
      Oeset.mem_bool ordered value right) ->
    forall value,
      Oeset.nb_occ ordered value left = Oeset.nb_occ ordered value right.
```

## `alpha_membership_iff_occurrence_representative`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:670`](../RelationalAlgebraFacts.v#L670)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma alpha_membership_iff_occurrence_representative :
  forall (T : Tuple.Rcd) (observations : list (tuple T) -> Prop)
         (bag : SqlBagAbstraction.bagT T),
    alpha T observations bag <->
    exists rows,
      observations rows /\
      forall row,
        Oeset.nb_occ (OTuple T) row rows =
        Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
```

## `query_set_union_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:703`](../RelationalAlgebraFacts.v#L703)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
```

## `query_set_union_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:716`](../RelationalAlgebraFacts.v#L716)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_union_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:729`](../RelationalAlgebraFacts.v#L729)

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Union left right)
             (query_set_bag Union right left).
```

## `query_set_union_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:740`](../RelationalAlgebraFacts.v#L740)

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Union (query_set_bag Union first second) third)
      (query_set_bag Union first (query_set_bag Union second third)).
```

## `query_set_union_max_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:752`](../RelationalAlgebraFacts.v#L752)

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag UnionMax left right)
             (query_set_bag UnionMax right left).
```

## `query_set_union_max_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:763`](../RelationalAlgebraFacts.v#L763)

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (query_set_bag UnionMax first second) third)
      (query_set_bag UnionMax first
        (query_set_bag UnionMax second third)).
```

## `query_set_union_max_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:777`](../RelationalAlgebraFacts.v#L777)

Purpose/direction: Establishes idempotence for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag UnionMax bag bag) bag.
```

## `query_set_union_max_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:787`](../RelationalAlgebraFacts.v#L787)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
```

## `query_set_union_max_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:800`](../RelationalAlgebraFacts.v#L800)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_inter_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:813`](../RelationalAlgebraFacts.v#L813)

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Inter left right)
             (query_set_bag Inter right left).
```

## `query_set_inter_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:824`](../RelationalAlgebraFacts.v#L824)

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Inter
        (query_set_bag Inter first second) third)
      (query_set_bag Inter first
        (query_set_bag Inter second third)).
```

## `query_set_inter_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:838`](../RelationalAlgebraFacts.v#L838)

Purpose/direction: Establishes idempotence for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag Inter bag bag) bag.
```

## `query_set_inter_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:848`](../RelationalAlgebraFacts.v#L848)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_inter_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:861`](../RelationalAlgebraFacts.v#L861)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_union_max_inter_absorb`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:874`](../RelationalAlgebraFacts.v#L874)

Purpose/direction: Establishes the displayed absorption law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_inter_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag UnionMax left (query_set_bag Inter left right))
      left.
```

## `query_set_inter_union_max_absorb`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:886`](../RelationalAlgebraFacts.v#L886)

Purpose/direction: Establishes the displayed absorption law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_union_max_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Inter left (query_set_bag UnionMax left right))
      left.
```

## `query_set_diff_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:898`](../RelationalAlgebraFacts.v#L898)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_diff_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:911`](../RelationalAlgebraFacts.v#L911)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_diff_self_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:924`](../RelationalAlgebraFacts.v#L924)

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_self_empty :
  forall bag : bagT,
    bag_eq T (query_set_bag Diff bag bag)
             (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_diff_union_cancel_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:935`](../RelationalAlgebraFacts.v#L935)

Purpose/direction: Establishes the displayed cancellation direction for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_union_cancel_right :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) right)
      left.
```

## `query_set_diff_union_cancel_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:947`](../RelationalAlgebraFacts.v#L947)

Purpose/direction: Establishes the displayed cancellation direction for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_union_cancel_left :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) left)
      right.
```

## `query_cross_join_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:959`](../RelationalAlgebraFacts.v#L959)

Purpose/direction: States the exact empty-input or empty-result law for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 24), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_cross_join_empty :
  forall bag : bagT,
    bag_eq T
      (query_cross_join_bag
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))) /\
    bag_eq T
      (query_cross_join_bag bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_natural_join_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:985`](../RelationalAlgebraFacts.v#L985)

Purpose/direction: States the exact empty-input or empty-result law for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 26), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_natural_join_empty :
  forall (value_is_null : value T -> bool) (bag : bagT),
    bag_eq T
      (query_natural_join_bag value_is_null
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))) /\
    bag_eq T
      (query_natural_join_bag value_is_null bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_distinct_bag_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1012`](../RelationalAlgebraFacts.v#L1012)

Purpose/direction: States the exact empty-input or empty-result law for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_empty :
  bag_eq T
    (query_distinct_bag (Febag.empty (Fecol.CBag (CTuple T))))
    (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_distinct_bag_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1030`](../RelationalAlgebraFacts.v#L1030)

Purpose/direction: Establishes idempotence for the declared bag multiplicity operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_idempotent :
  forall bag : bagT,
    bag_eq T (query_distinct_bag (query_distinct_bag bag))
             (query_distinct_bag bag).
```

## `query_cross_join_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1048`](../RelationalAlgebraFacts.v#L1048)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 24), `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_cross_join_bag_cardinal :
  forall left right : bagT,
    Febag.cardinal (Fecol.CBag (CTuple T))
      (query_cross_join_bag left right) =
    (Febag.cardinal (Fecol.CBag (CTuple T)) left *
     Febag.cardinal (Fecol.CBag (CTuple T)) right)%N.
```

## `query_natural_join_bag_cardinal_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1082`](../RelationalAlgebraFacts.v#L1082)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join` (rank 26), `bag` (rank 36), `cardinality` (rank 52)

Search aliases: `relational algebra`, `join`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_natural_join_bag_cardinal_le :
  forall (value_is_null : value T -> bool) (left right : bagT),
    (Febag.cardinal (Fecol.CBag (CTuple T))
       (query_natural_join_bag value_is_null left right) <=
     Febag.cardinal (Fecol.CBag (CTuple T)) left *
     Febag.cardinal (Fecol.CBag (CTuple T)) right)%N.
```

## `query_join_matched_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1131`](../RelationalAlgebraFacts.v#L1131)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma query_join_matched_sources_length_le :
  forall (left : tuple T) rights flags,
    length (query_join_matched_sources T left rights flags) <= length rights.
```

## `query_join_left_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1140`](../RelationalAlgebraFacts.v#L1140)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Lemma query_join_left_sources_length_le :
  forall kind lefts rights matrix,
    length (query_join_left_sources T kind lefts rights matrix) <=
    match kind with
    | QueryJoinInner | QueryJoinRight => length lefts * length rights
    | QueryJoinLeft | QueryJoinFull =>
        length lefts * Nat.max 1 (length rights)
    | QueryJoinSemi | QueryJoinAnti => length lefts
    end.
```

## `query_join_unmatched_right_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1171`](../RelationalAlgebraFacts.v#L1171)

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma query_join_unmatched_right_sources_length_le :
  forall index rights matrix,
    length
      (query_join_unmatched_right_sources_from T index rights matrix) <=
    length rights.
```

## `query_join_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1183`](../RelationalAlgebraFacts.v#L1183)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 26), `cardinality` (rank 40)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Lemma query_join_sources_length_le :
  forall kind lefts rights matrix,
    length (query_join_sources T kind lefts rights matrix) <=
    match kind with
    | QueryJoinInner => length lefts * length rights
    | QueryJoinLeft => length lefts * Nat.max 1 (length rights)
    | QueryJoinRight => length lefts * length rights + length rights
    | QueryJoinFull =>
        length lefts * Nat.max 1 (length rights) + length rights
    | QueryJoinSemi | QueryJoinAnti => length lefts
    end.
```

## `eval_join_row_conditions_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1230`](../RelationalAlgebraFacts.v#L1230)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 26), `cardinality` (rank 44)

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma eval_join_row_conditions_success_length :
  forall env predicate left rights flags,
    @eval_join_row_conditions_outcome T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate left rights (SqlSuccess flags) ->
    length flags = length rights.
```

## `eval_join_conditions_success_dimensions`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1244`](../RelationalAlgebraFacts.v#L1244)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when the goal or a hypothesis matches the `eval_join_conditions_success_dimensions` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join` (rank 26)

Search aliases: `relational algebra`, `join`

```rocq
Lemma eval_join_conditions_success_dimensions :
  forall env predicate lefts rights matrix,
    @eval_join_conditions_outcome T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate lefts rights (SqlSuccess matrix) ->
    length matrix = length lefts /\
    Forall (fun flags => length flags = length rights) matrix.
```

## `project_join_sources_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1267`](../RelationalAlgebraFacts.v#L1267)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection` (rank 36), `join` (rank 26), `cardinality` (rank 44)

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma project_join_sources_success_length :
  forall env matched_select left_select right_select sources output,
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env matched_select left_select right_select
      sources = SqlSuccess output ->
    length output = length sources.
```

## `eval_join_bag_success_cardinal_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1287`](../RelationalAlgebraFacts.v#L1287)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join` (rank 24), `bag` (rank 34), `cardinality` (rank 50)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_join_bag_success_cardinal_le :
  forall env kind predicate matched_select left_select right_select
         left_bag right_bag output_bag,
    @eval_join_bag_outcome T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null env kind
      predicate matched_select left_select right_select left_bag right_bag
      (SqlSuccess output_bag) ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) output_bag <=
     match kind with
     | QueryJoinInner =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinLeft =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         N.max 1 (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag)
     | QueryJoinRight =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag +
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinFull =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         N.max 1 (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag) +
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinSemi | QueryJoinAnti =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag
     end)%N.
```

## `query_grouping_sets_actual_success_bags_congr`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1357`](../RelationalAlgebraFacts.v#L1357)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping` (rank 40), `bag` (rank 36)

Search aliases: `relational algebra`, `grouping sets`, `GROUP BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_grouping_sets_actual_success_bags_congr :
  forall env grouping_sets left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_GroupingSets grouping_sets left))
      (success_bags env (QExpr_GroupingSets grouping_sets right)).
```

## `query_expr_equiv_implies_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1383`](../RelationalAlgebraFacts.v#L1383)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_implies_success_bags :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_set_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1396`](../RelationalAlgebraFacts.v#L1396)

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_set_success_bags_congr_of_query_expr_equiv :
  forall env operation left left' right right',
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_Set operation left right))
      (success_bags env (QExpr_Set operation left' right')).
```

## `query_natural_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1420`](../RelationalAlgebraFacts.v#L1420)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 26), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_natural_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_NaturalJoin left right))
      (success_bags env (QExpr_NaturalJoin left' right')).
```

## `query_cross_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1438`](../RelationalAlgebraFacts.v#L1438)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 24), `bag` (rank 36)

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_cross_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_CrossJoin left right))
      (success_bags env (QExpr_CrossJoin left' right')).
```

## `query_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1456`](../RelationalAlgebraFacts.v#L1456)

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `join` (rank 26), `bag` (rank 36)

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_join_success_bags_congr_of_query_expr_equiv :
  forall env kind predicate matched_select left_select right_select
         left left' right right',
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left' right')).
```

## `qexpr_bag_equiv_iff_safe_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1480`](../RelationalAlgebraFacts.v#L1480)

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `bag` (rank 26)

Search aliases: `relational algebra`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma qexpr_bag_equiv_iff_safe_occurrences :
  forall env outputs left right,
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (QExpr_Bag outputs left) (QExpr_Bag outputs right) <->
    bag_query_runtime_error basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env left = None /\
    bag_query_runtime_error basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env right = None /\
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (@eval_query T relname basesort instance unknown contains_nulls env left) =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (@eval_query T relname basesort instance unknown contains_nulls env right).
```

## `bag_query_equiv_refl_safe`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1516`](../RelationalAlgebraFacts.v#L1516)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `runtime` (rank 52), `bag` (rank 36)

Search aliases: `relational algebra`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_query_equiv_refl_safe :
  forall env query,
    bag_query_runtime_error basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query query.
```

## `bag_query_equiv_sym`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1528`](../RelationalAlgebraFacts.v#L1528)

Purpose/direction: Reverses a proved bag multiplicity relation.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_query_equiv_sym :
  forall env left right,
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env left right ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env right left.
```

## `bag_query_equiv_trans`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1542`](../RelationalAlgebraFacts.v#L1542)

Purpose/direction: Composes two bag multiplicity relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag` (rank 36)

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_query_equiv_trans :
  forall env first second third,
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env first second ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env second third ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env first third.
```
