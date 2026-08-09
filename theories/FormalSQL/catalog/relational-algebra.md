# Bags, occurrences, projection, and relational algebra

Route here for: bag/list abstraction, multiplicity, filter/project/join/set operators.

This focused catalog contains 279 declarations routed at declaration granularity from `FilterFkEliminationFacts.v`, `GroupedFilterOutcomeFacts.v`, `NumericRegroupFacts.v`, `OrderedQueryFacts.v`, `OuterJoinFilterFacts.v`, `ProofAgentFacade.v`, `RelationalAlgebraFacts.v`, `SemijoinCompositionFacts.v`, `SqlQueryContexts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `join_matched_rows_filter_inputs_exact`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:45`](../FilterFkEliminationFacts.v#L45)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Factors stable total Boolean join acceptance into input guards and a residual predicate while preserving the exact output list and duplicate occurrences.

Applicability: Use when the goal or a hypothesis matches the `join_matched_rows_filter_inputs_exact` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`, `join`

Search aliases: `relational algebra`, `join`, `filter`, `WHERE`, `inner join`, `filter movement`, `multiplicity`, `total predicate`

```rocq
Theorem join_matched_rows_filter_inputs_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (source accept : A -> B -> bool)
      (left_guard : A -> bool) (right_guard : B -> bool) left right,
    (forall left_row right_row,
      source left_row right_row =
      andb (left_guard left_row)
        (andb (right_guard right_row) (accept left_row right_row))) ->
    join_matched_rows join source left right =
    join_matched_rows join accept
      (filter left_guard left) (filter right_guard right).
```

## `inner_filter_to_input_filters_exact`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:108`](../FilterFkEliminationFacts.v#L108)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Factors stable total Boolean join acceptance into input guards and a residual predicate while preserving the exact output list and duplicate occurrences.

Applicability: Use when the goal or a hypothesis matches the `inner_filter_to_input_filters_exact` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `inner join`, `filter pushdown`, `exact list`, `properness`

```rocq
Theorem inner_filter_to_input_filters_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) (post : C -> bool)
      (left_guard : A -> bool) (right_guard : B -> bool) left right,
    (forall left_row right_row,
      andb (accept left_row right_row) (post (join left_row right_row)) =
      andb (left_guard left_row)
        (andb (right_guard right_row) (accept left_row right_row))) ->
    filter post (join_matched_rows join accept left right) =
    join_matched_rows join accept
      (filter left_guard left) (filter right_guard right).
```

## `join_left_guard_reached_iff_of_witness`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:141`](../FilterFkEliminationFacts.v#L141)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates prefilter and post-join guard reachability only under the displayed match witness; the self form supplies both directions for a reflexive match.

Applicability: Use in either direction to invert or construct a goal about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `left guard`, `reachability`, `self witness`

```rocq
Theorem join_left_guard_reached_iff_of_witness :
  forall (A B : Type) (accept : A -> B -> bool) left right,
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    forall left_row,
      join_left_guard_reached accept left right left_row <->
      In left_row left.
```

## `join_right_guard_reached_iff_of_witness`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:156`](../FilterFkEliminationFacts.v#L156)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates prefilter and post-join guard reachability only under the displayed match witness; the self form supplies both directions for a reflexive match.

Applicability: Use in either direction to invert or construct a goal about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `right guard`, `reachability`, `self witness`

```rocq
Theorem join_right_guard_reached_iff_of_witness :
  forall (A B : Type) (accept : A -> B -> bool) left right,
    (forall right_row,
      In right_row right ->
      exists left_row,
        In left_row left /\ accept left_row right_row = true) ->
    forall right_row,
      join_right_guard_reached accept left right right_row <->
      In right_row right.
```

## `join_self_guard_reachability_exact`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:173`](../FilterFkEliminationFacts.v#L173)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates prefilter and post-join guard reachability only under the displayed match witness; the self form supplies both directions for a reflexive match.

Applicability: Use when the goal or a hypothesis matches the `join_self_guard_reachability_exact` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `self join`, `filter movement`, `evaluation reachability`

```rocq
Theorem join_self_guard_reachability_exact :
  forall (A : Type) (accept : A -> A -> bool) rows,
    (forall row, In row rows -> accept row row = true) ->
    (forall row,
      join_left_guard_reached accept rows rows row <-> In row rows) /\
    (forall row,
      join_right_guard_reached accept rows rows row <-> In row rows).
```

## `join_matched_rows_member_of_accepted_cell`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:191`](../FilterFkEliminationFacts.v#L191)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that one accepted pair contributes its emitted occurrence to the concrete matched-row scheduler without dropping duplicates.

Applicability: Use when the goal or a hypothesis matches the `join_matched_rows_member_of_accepted_cell` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `accepted cell`, `reached occurrence`, `multiplicity`

```rocq
Lemma join_matched_rows_member_of_accepted_cell :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) left right left_row right_row,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    In (join left_row right_row)
      (join_matched_rows join accept left right).
```

## `query_filter_success_bags_of_stable_total_acceptance`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:247`](../FilterFkEliminationFacts.v#L247)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes successful filter bags by one stable total acceptance callback only after exact per-row Boolean-expression success and no-error are supplied.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `stable total acceptance`, `success bag`, `non volatility`

```rocq
Theorem query_filter_success_bags_of_stable_total_acceptance :
  forall env formula input keep,
    stable_total_filter_acceptance env formula keep ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule env
        (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          query_success_bags basesort instance unknown symbol_runtime_error
            aggregate_runtime_error value_is_null boolean_schedule env
            input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
```

## `query_filter_error_iff_of_stable_total_acceptance`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:269`](../FilterFkEliminationFacts.v#L269)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes filter errors under the same stable total acceptance contract, retaining child errors and exact reached predicate error categories.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `stable total acceptance`, `runtime error`, `reachability`

```rocq
Theorem query_filter_error_iff_of_stable_total_acceptance :
  forall env formula input keep,
    stable_total_filter_acceptance env formula keep ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
```

## `eval_filter_rows_uniform_error_of_reached_member`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:318`](../FilterFkEliminationFacts.v#L318)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Constructs the sequential FILTER error from one reached bad occurrence when every reached row succeeds or exposes that same category.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `reached occurrence`, `exact error category`, `evaluation order`

```rocq
Theorem eval_filter_rows_uniform_error_of_reached_member :
  forall env formula rows bad error,
    In bad rows ->
    eval_scalar_boolean (env_t T env bad) formula (SqlError error) ->
    (forall row,
      In row rows ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula rows (SqlError error).
```

## `eval_filter_rows_error_category_of_reached_categories`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:378`](../FilterFkEliminationFacts.v#L378)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that any FILTER error has the fixed category shared by every reached predicate-error observation.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `error category`, `reached rows`, `evaluation order`

```rocq
Theorem eval_filter_rows_error_category_of_reached_categories :
  forall env formula rows expected error,
    (forall row,
      In row rows ->
      forall observed,
        eval_scalar_boolean (env_t T env row) formula (SqlError observed) ->
        observed = expected) ->
    eval_filter_rows env formula rows (SqlError error) ->
    error = expected.
```

## `eval_filter_rows_success_excludes_reached_exact_error`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:397`](../FilterFkEliminationFacts.v#L397)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Excludes every successful FILTER traversal when one reached occurrence has no successful predicate observation.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `success exclusion`, `reached error`, `evaluation order`

```rocq
Theorem eval_filter_rows_success_excludes_reached_exact_error :
  forall env formula rows bad,
    In bad rows ->
    (forall truth,
      ~ eval_scalar_boolean (env_t T env bad) formula (SqlSuccess truth)) ->
    forall output,
      ~ eval_filter_rows env formula rows (SqlSuccess output).
```

## `eval_filter_rows_reached_uniform_error_exact`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:426`](../FilterFkEliminationFacts.v#L426)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Packages FILTER error existence, success exclusion, and uniqueness of the exact runtime category from explicit reached-row premises.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `exact error only`, `reached occurrence`

```rocq
Theorem eval_filter_rows_reached_uniform_error_exact :
  forall env formula rows bad expected,
    In bad rows ->
    eval_scalar_boolean (env_t T env bad) formula (SqlError expected) ->
    (forall row,
      In row rows ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError expected)) ->
    (forall truth,
      ~ eval_scalar_boolean (env_t T env bad) formula (SqlSuccess truth)) ->
    (forall row,
      In row rows ->
      forall observed,
        eval_scalar_boolean (env_t T env row) formula (SqlError observed) ->
        observed = expected) ->
    eval_filter_rows env formula rows (SqlError expected) /\
    (forall output,
      ~ eval_filter_rows env formula rows (SqlSuccess output)) /\
    (forall observed,
      eval_filter_rows env formula rows (SqlError observed) ->
      observed = expected).
```

## `eval_filter_rows_uniform_error_of_join_witness`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:465`](../FilterFkEliminationFacts.v#L465)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Constructs the FILTER error derivation from a concrete accepted join cell; the self form retains the explicit accepted diagonal witness.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`, `join`

Search aliases: `relational algebra`, `join`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `witness reachability`, `exact error category`

```rocq
Theorem eval_filter_rows_uniform_error_of_join_witness :
  forall (A B : Type) env formula
      (join : A -> B -> tuple T) (accept : A -> B -> bool)
      left right left_row right_row error,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    eval_scalar_boolean (env_t T env (join left_row right_row)) formula
      (SqlError error) ->
    (forall row,
      In row (join_matched_rows join accept left right) ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula
      (join_matched_rows join accept left right) (SqlError error).
```

## `eval_filter_rows_uniform_error_of_self_match`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:491`](../FilterFkEliminationFacts.v#L491)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Constructs the FILTER error derivation from a concrete accepted join cell; the self form retains the explicit accepted diagonal witness.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `self join`, `self witness`, `exact error category`

```rocq
Corollary eval_filter_rows_uniform_error_of_self_match :
  forall (A : Type) env formula
      (join : A -> A -> tuple T) (accept : A -> A -> bool)
      rows bad error,
    In bad rows ->
    accept bad bad = true ->
    eval_scalar_boolean (env_t T env (join bad bad)) formula (SqlError error) ->
    (forall row,
      In row (join_matched_rows join accept rows rows) ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula
      (join_matched_rows join accept rows rows) (SqlError error).
```

## `nonnull_foreign_key_direct_accept_has_middle`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:520`](../FilterFkEliminationFacts.v#L520)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts a conforming non-NULL foreign key to an explicit referenced middle witness, or derives rejection when no such middle row exists.

Applicability: Use when the goal or a hypothesis matches the `nonnull_foreign_key_direct_accept_has_middle` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `relational algebra`, `integrity constraint`, `key`, `foreign key`, `NOT NULL`, `middle elimination`, `existence`

```rocq
Theorem nonnull_foreign_key_direct_accept_has_middle :
  forall db raw_foreigns referenced_relation
      source_attributes referenced_attributes
      (project_source project_foreign project_referenced :
        tuple TNull -> tuple TNull)
      (middle_accept direct_accept :
        tuple TNull -> tuple TNull -> bool)
      source foreign,
    rows_attributes_not_null source_attributes raw_foreigns ->
    foreign_key_conforms db raw_foreigns
      (ForeignKeyConstraint source_attributes referenced_relation
        referenced_attributes) ->
    In foreign raw_foreigns ->
    direct_accept (project_source source) (project_foreign foreign) = true ->
    (forall referenced,
      In referenced (instance_rows db referenced_relation) ->
      foreign_key_key_equal_true source_attributes referenced_attributes
        foreign referenced ->
      direct_accept (project_source source) (project_foreign foreign) = true ->
      middle_accept (project_source source)
        (project_referenced referenced) = true) ->
    exists referenced,
      In referenced (instance_rows db referenced_relation) /\
      foreign_key_key_equal_true source_attributes referenced_attributes
        foreign referenced /\
      middle_accept (project_source source)
        (project_referenced referenced) = true.
```

## `nonnull_foreign_key_no_middle_rejects_direct`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:568`](../FilterFkEliminationFacts.v#L568)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts a conforming non-NULL foreign key to an explicit referenced middle witness, or derives rejection when no such middle row exists.

Applicability: Use when the goal or a hypothesis matches the `nonnull_foreign_key_no_middle_rejects_direct` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `relational algebra`, `integrity constraint`, `key`, `foreign key`, `NOT NULL`, `null rejection`, `middle elimination`

```rocq
Corollary nonnull_foreign_key_no_middle_rejects_direct :
  forall db raw_foreigns referenced_relation
      source_attributes referenced_attributes
      (project_source project_foreign project_referenced :
        tuple TNull -> tuple TNull)
      (middle_accept direct_accept :
        tuple TNull -> tuple TNull -> bool)
      source foreign,
    rows_attributes_not_null source_attributes raw_foreigns ->
    foreign_key_conforms db raw_foreigns
      (ForeignKeyConstraint source_attributes referenced_relation
        referenced_attributes) ->
    In foreign raw_foreigns ->
    (forall referenced,
      In referenced (instance_rows db referenced_relation) ->
      middle_accept (project_source source)
        (project_referenced referenced) = false) ->
    (forall referenced,
      In referenced (instance_rows db referenced_relation) ->
      foreign_key_key_equal_true source_attributes referenced_attributes
        foreign referenced ->
      direct_accept (project_source source) (project_foreign foreign) = true ->
      middle_accept (project_source source)
        (project_referenced referenced) = true) ->
    direct_accept (project_source source) (project_foreign foreign) = false.
```

## `join_matched_rows_empty_of_rejection`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:615`](../FilterFkEliminationFacts.v#L615)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Eliminates exactly the displayed rejected matched or NULL-padded branch without moving SQL evaluations or changing duplicate multiplicity.

Applicability: Use when the goal or a hypothesis matches the `join_matched_rows_empty_of_rejection` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `null rejection`, `empty branch`, `multiplicity`

```rocq
Lemma join_matched_rows_empty_of_rejection :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) left right,
    (forall left_row right_row,
      In left_row left -> In right_row right ->
      accept left_row right_row = false) ->
    join_matched_rows join accept left right = nil.
```

## `middle_padding_downstream_empty`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:642`](../FilterFkEliminationFacts.v#L642)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Eliminates exactly the displayed rejected matched or NULL-padded branch without moving SQL evaluations or changing duplicate multiplicity.

Applicability: Use when the goal or a hypothesis matches the `middle_padding_downstream_empty` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`, `left join`, `NULL padding`, `null rejection`, `middle elimination`

```rocq
Theorem middle_padding_downstream_empty :
  forall (A B D M O : Type)
      (pad : A -> M) (middle_accept : A -> B -> bool)
      (emit : M -> D -> O) (downstream_accept : M -> D -> bool)
      source_rows middle_rows downstream_rows,
    (forall source downstream,
      In source source_rows -> In downstream downstream_rows ->
      downstream_accept (pad source) downstream = false) ->
    join_matched_rows emit downstream_accept
      (join_unmatched_left_rows pad middle_accept
        source_rows middle_rows)
      downstream_rows = nil.
```

## `filtered_payload_erasure_permut`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:669`](../FilterFkEliminationFacts.v#L669)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports one filtered occurrence block across explicit predicate agreement and a payload relation while preserving multiplicity.

Applicability: Use when the goal or a hypothesis matches the `filtered_payload_erasure_permut` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`, `filter`, `payload erasure`, `multiplicity`, `semantic relation`

```rocq
Theorem filtered_payload_erasure_permut :
  forall (M A D O1 O2 : Type) (R : O1 -> O2 -> Prop)
      (emit_left : M -> D -> O1) (emit_right : A -> D -> O2)
      (accept_left : M -> D -> bool) (accept_right : A -> D -> bool)
      middle source downstream_rows,
    (forall downstream,
      In downstream downstream_rows ->
      accept_left middle downstream = accept_right source downstream) ->
    (forall downstream,
      In downstream downstream_rows ->
      accept_left middle downstream = true ->
      R (emit_left middle downstream) (emit_right source downstream)) ->
    _permut R
      (map (emit_left middle)
        (filter (accept_left middle) downstream_rows))
      (map (emit_right source)
        (filter (accept_right source) downstream_rows)).
```

## `query_expr_outcome_equiv_of_shared_exact_error`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:742`](../FilterFkEliminationFacts.v#L742)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_possible_outcome_equiv_of_shared_exact_error` for the public result.

Purpose/direction: Lifts two error-only query relations exposing the same unique category to exact outcome equivalence after successful outcomes are excluded.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`, `exact error only`, `error category`, `success exclusion`

```rocq
Theorem query_expr_outcome_equiv_of_shared_exact_error :
  forall env first second expected,
    query_expr_outputs first = query_expr_outputs second ->
    eval_query env first (SqlError expected) ->
    eval_query env second (SqlError expected) ->
    (forall rows, ~ eval_query env first (SqlSuccess rows)) ->
    (forall rows, ~ eval_query env second (SqlSuccess rows)) ->
    (forall observed,
      eval_query env first (SqlError observed) -> observed = expected) ->
    (forall observed,
      eval_query env second (SqlError observed) -> observed = expected) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env first second.
```

## `scalar_expr_pred_acceptance_exact_safe`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:589`](../GroupedFilterOutcomeFacts.v#L589)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Builds an exact SQL TRUE-acceptance contract for an interpreted scalar predicate from explicit argument runtime safety.

Applicability: Use for `SExpr_Pred` only after proving its authoritative `first_runtime_error` classifier is `None`; the decision is `Bool.is_true`, not an equality between SQL FALSE and UNKNOWN.

Important premises: The displayed `first_runtime_error ... arguments = None` premise is mandatory; retain the authoritative predicate interpreter and use `Bool.is_true` only for filter acceptance.

Cross-index: `runtime`, `filter`, `scalar`

Search aliases: `relational algebra`, `filter`, `WHERE`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma scalar_expr_pred_acceptance_exact_safe :
  forall env predicate arguments values,
    scalar_value_list_exact_at env arguments values ->
    scalar_expr_acceptance_exact_at env (SExpr_Pred predicate arguments)
      (Bool.is_true (B T) (interp_predicate T predicate values)).
```

## `eval_filter_rows_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:998`](../GroupedFilterOutcomeFacts.v#L998)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes row-filter outcomes exactly as successful `List.filter` under per-row exact-acceptance/no-error contracts.

Applicability: Use after proving `scalar_expr_acceptance_exact_at` for every input occurrence; the result preserves list order and duplicates and the premise excludes predicate errors.

Important premises: Supply the displayed per-row `scalar_expr_acceptance_exact_at` contract, including its successful observation and no-error components; do not replace `List.filter` by a set abstraction.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Theorem eval_filter_rows_acceptance_exact :
  forall env formula rows keep,
    (forall row,
      In row rows ->
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    forall outcome,
      eval_filter_rows env formula rows outcome <->
      outcome = SqlSuccess (List.filter keep rows).
```

## `filter_scalar_observation_equiv_at_sym`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1117`](../GroupedFilterOutcomeFacts.v#L1117)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Reverses a proved relational algebra relation.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma filter_scalar_observation_equiv_at_sym :
  forall left_env left_formula right_env right_formula,
    filter_scalar_observation_equiv_at
      left_env left_formula right_env right_formula ->
    filter_scalar_observation_equiv_at
      right_env right_formula left_env left_formula.
```

## `eval_filter_rows_ordered_outcome_congr_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1155`](../GroupedFilterOutcomeFacts.v#L1155)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_ordered_outcome_congr_forward :
  forall left_env left_formula left_rows left_outcome,
    eval_filter_rows left_env left_formula left_rows left_outcome ->
    forall right_env right_formula right_rows,
      ordered_rows_equiv T left_rows right_rows ->
      (forall left_row right_row,
        Oeset.compare (OTuple T) left_row right_row = Eq ->
        filter_scalar_observation_equiv_at
          (env_t T left_env left_row) left_formula
          (env_t T right_env right_row) right_formula) ->
      exists right_outcome,
        eval_filter_rows right_env right_formula right_rows right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
```

## `eval_filter_rows_ordered_outcome_congr`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1242`](../GroupedFilterOutcomeFacts.v#L1242)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem eval_filter_rows_ordered_outcome_congr :
  forall left_env left_formula left_rows
      right_env right_formula right_rows,
    ordered_rows_equiv T left_rows right_rows ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_scalar_observation_equiv_at
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    (exists left_outcome,
      eval_filter_rows left_env left_formula left_rows left_outcome) ->
    outcome_relation_equiv (ordered_rows_equiv T)
      (eval_filter_rows left_env left_formula left_rows)
      (eval_filter_rows right_env right_formula right_rows).
```

## `query_expr_filter_outcome_congr_extensional_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1315`](../GroupedFilterOutcomeFacts.v#L1315)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_outcome_congr_extensional_forward :
  forall env left_formula right_formula left_input right_input,
    @query_expr_outcome_observation_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_scalar_observation_equiv_at
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    forall left_outcome,
      eval_query env (QExpr_Filter left_formula left_input) left_outcome ->
      exists right_outcome,
        eval_query env (QExpr_Filter right_formula right_input) right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
```

## `query_expr_filter_outcome_congr_extensional`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1386`](../GroupedFilterOutcomeFacts.v#L1386)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_filter_possible_outcome_equiv_congr_stable_total` for the public result.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_outcome_congr_extensional :
  forall env left_formula right_formula left_input right_input,
    query_outcome_equiv env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_scalar_observation_equiv_at
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    (exists left_outcome,
      eval_query env (QExpr_Filter left_formula left_input) left_outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_formula left_input)
      (QExpr_Filter right_formula right_input).
```

## `query_set_union_occurrence_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1073`](../NumericRegroupFacts.v#L1073)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_occurrence_exact : forall left right row,
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row
    (query_set_bag Union left right) =
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right)%N.
```

## `query_bag_duplicate_free_of_rows_NoDupA`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1087`](../NumericRegroupFacts.v#L1087)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_duplicate_free_of_rows_NoDupA : forall rows,
  NoDupA
    (fun first second => Oeset.compare (OTuple T) first second = Eq)
    rows ->
  query_bag_duplicate_free (rows_bag T rows).
```

## `query_bag_duplicate_free_transport`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1102`](../NumericRegroupFacts.v#L1102)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports the displayed hypotheses and conclusion for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_duplicate_free_transport : forall left right,
  bag_eq T left right ->
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right.
```

## `query_bags_disjoint_sym`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1169`](../NumericRegroupFacts.v#L1169)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Reverses a proved bag multiplicity relation.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_bags_disjoint_sym : forall left right,
  query_bags_disjoint left right -> query_bags_disjoint right left.
```

## `query_set_union_duplicate_free`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1176`](../NumericRegroupFacts.v#L1176)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query set union duplicate free law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_duplicate_free : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  query_bag_duplicate_free (query_set_bag Union left right).
```

## `query_set_union_disjoint_right`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1195`](../NumericRegroupFacts.v#L1195)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query set union disjoint right law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_disjoint_right : forall first second third,
  query_bags_disjoint first third ->
  query_bags_disjoint second third ->
  query_bags_disjoint (query_set_bag Union first second) third.
```

## `query_distinct_bag_inert`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1213`](../NumericRegroupFacts.v#L1213)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query distinct bag inert law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_inert : forall bag,
  query_bag_duplicate_free bag ->
  bag_eq T (query_distinct_bag bag) bag.
```

## `query_distinct_bag_occurrence_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1238`](../NumericRegroupFacts.v#L1238)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_occurrence_exact : forall bag row,
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row
    (query_distinct_bag bag) =
  if Febag.mem (SqlQuerySemantics.BTupleT T) row bag then 1%N else 0%N.
```

## `query_duplicate_free_support_bag_eq`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1261`](../NumericRegroupFacts.v#L1261)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query duplicate free support bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_duplicate_free_support_bag_eq :
  forall left right : bagT,
    query_bag_duplicate_free left ->
    query_bag_duplicate_free right ->
    (forall row,
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left = 0%N <->
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right = 0%N) ->
    bag_eq T left right.
```

## `query_distinct_union_inert`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1293`](../NumericRegroupFacts.v#L1293)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query distinct union inert law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_distinct_union_inert : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  bag_eq T
    (query_distinct_bag (query_set_bag Union left right))
    (query_set_bag Union left right).
```

## `query_bag_filter_occurrence_exact`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1312`](../NumericRegroupFacts.v#L1312)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_occurrence_exact :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool)
      (bag : Febag.bag (SqlQuerySemantics.BTupleT T)),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (Febag.filter (Fecol.CBag (CTuple T)) keep bag) =
      if keep row
      then Febag.nb_occ (Fecol.CBag (CTuple T)) row bag
      else 0%N.
```

## `query_bag_filter_duplicate_free`

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1335`](../NumericRegroupFacts.v#L1335)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query bag filter duplicate free law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_duplicate_free :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool)
      (bag : Febag.bag (SqlQuerySemantics.BTupleT T)),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    query_bag_duplicate_free bag ->
    query_bag_duplicate_free
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag).
```

## `query_bag_reset_success_permutation_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:574`](../OrderedQueryFacts.v#L574)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes concrete-row permutation closure for successful observations at any constructor classified as a bag reset.

Applicability: Use when `query_expr_order_behavior query = BagReset` computes or is proved directly.  The conclusion concerns successful row lists only; prove SQL errors separately.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_bag_reset_success_permutation_closed :
  forall env query,
    query_expr_order_behavior query = BagReset ->
    ConcretePermutationClosed T
      (fun rows => eval_query env query (SqlSuccess rows)).
```

## `query_project_preserves_success_permutation_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:585`](../OrderedQueryFacts.v#L585)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports concrete-row permutation closure of successful observations through pointwise projection.

Applicability: Use with `ConcretePermutationClosed` for the child, not merely `BagClosed`.  It reorders the same concrete row representatives and makes no claim about error outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_project_preserves_success_permutation_closed :
  forall env select_list input,
    ConcretePermutationClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    ConcretePermutationClosed T
      (fun rows =>
        eval_query env (QExpr_Project select_list input) (SqlSuccess rows)).
```

## `query_row_map_preserves_success_permutation_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:598`](../OrderedQueryFacts.v#L598)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports concrete-row permutation closure of successful observations through pointwise row mapping.

Applicability: Use with `ConcretePermutationClosed` for the child, not merely `BagClosed`.  It reorders the same concrete row representatives and makes no claim about error outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_row_map_preserves_success_permutation_closed :
  forall env output_attributes row_map input,
    ConcretePermutationClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    ConcretePermutationClosed T
      (fun rows =>
        eval_query env (QExpr_RowMap output_attributes row_map input)
          (SqlSuccess rows)).
```

## `query_filter_preserves_success_permutation_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:612`](../OrderedQueryFacts.v#L612)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports concrete-row permutation closure of successful observations through pointwise filtering.

Applicability: Use with `ConcretePermutationClosed` for the child, not merely `BagClosed`.  It reorders the same concrete row representatives and makes no claim about error outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_filter_preserves_success_permutation_closed :
  forall env formula input,
    ConcretePermutationClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    ConcretePermutationClosed T
      (fun rows =>
        eval_query env (QExpr_Filter formula input) (SqlSuccess rows)).
```

## `query_structural_successes_bag_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:627`](../OrderedQueryFacts.v#L627)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Turns the syntax-directed reset/Project/Filter/RowMap certificate into observation-level BagClosed for successful rows.

Applicability: Try first on a Project/Filter/RowMap stack above a bag reset; the Boolean premise usually closes by reflexivity.  It intentionally does not cross OrderBy, Offset, or Fetch, and errors remain separate.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_structural_successes_bag_closed :
  forall env query,
    query_expr_permutation_closure_certified query = true ->
    BagClosed T
      (fun rows => eval_query env query (SqlSuccess rows)).
```

## `query_expr_cross_join_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:718`](../OrderedQueryFacts.v#L718)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when the goal or a hypothesis matches the `query_expr_cross_join_has_success` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`

```rocq
Lemma query_expr_cross_join_has_success :
  forall env left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_CrossJoin left right).
```

## `query_expr_join_has_success_of_acceptance_projection_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:738`](../OrderedQueryFacts.v#L738)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `projection`, `join`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `projection`, `SELECT list`

```rocq
Lemma query_expr_join_has_success_of_acceptance_projection_exact :
  forall env kind predicate matched_select left_select right_select
      left right (accepted : tuple T -> tuple T -> bool)
      (emit : query_join_source T -> tuple T),
    query_has_success env left ->
    query_has_success env right ->
    (forall left_row right_row,
      @join_condition_acceptance_exact_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env predicate left_row right_row
        (accepted left_row right_row)) ->
    (forall source,
      @join_source_projection_exact_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env matched_select left_select right_select source
        (emit source)) ->
    query_has_success env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right).
```

## `eval_query_expr_project_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1265`](../OrderedQueryFacts.v#L1265)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scheduled`, `projection`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma eval_query_expr_project_success_length :
  forall env select_list input output,
    eval_query env (QExpr_Project select_list input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows.
```

## `eval_query_expr_table_success_cardinal`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1286`](../OrderedQueryFacts.v#L1286)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `bag`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_query_expr_table_success_cardinal :
  forall env outputs table rows,
    @query_outputs_sort T outputs =S= basesort table ->
    eval_query env (QExpr_Table outputs table) (SqlSuccess rows) ->
    Febag.cardinal (Fecol.CBag (CTuple T)) (instance table) =
      N.of_nat (length rows).
```

## `eval_query_expr_filter_success_Forall_accepted`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1322`](../OrderedQueryFacts.v#L1322)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `eval_query_expr_filter_success_Forall_accepted` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scheduled`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_query_expr_filter_success_Forall_accepted :
  forall env formula input output (property : tuple T -> Prop),
    (forall input_rows row truth,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      @eval_scalar_boolean_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule (env_t T env row) formula
        (SqlSuccess truth) ->
      Bool.is_true (B T) truth = true ->
      property row) ->
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) ->
    Forall property output.
```

## `query_expr_project_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1346`](../OrderedQueryFacts.v#L1346)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_project_success_Forall` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma query_expr_project_success_Forall :
  forall env select_list input
      (input_property output_property : tuple T -> Prop),
    query_success_Forall env input input_property ->
    (forall input_row output_row,
      input_property input_row ->
      @project_row_success T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list input_row output_row ->
      output_property output_row) ->
    query_success_Forall env
      (QExpr_Project select_list input) output_property.
```

## `query_expr_filter_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1383`](../OrderedQueryFacts.v#L1383)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_filter_success_Forall` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma query_expr_filter_success_Forall :
  forall env formula input (property : tuple T -> Prop),
    query_success_Forall env input property ->
    query_success_Forall env (QExpr_Filter formula input) property.
```

## `query_expr_union_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1399`](../OrderedQueryFacts.v#L1399)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_union_success_Forall :
  forall env left right (property : tuple T -> Prop),
    query_expr_sort left =S= query_expr_sort right ->
    tuple_property_semantic_invariant property ->
    query_success_Forall env left property ->
    query_success_Forall env right property ->
    query_success_Forall env (QExpr_Set Union left right) property.
```

## `query_expr_cross_join_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1436`](../OrderedQueryFacts.v#L1436)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_cross_join_success_Forall :
  forall env left right (property : tuple T -> Prop),
    tuple_property_semantic_invariant property ->
    (forall left_rows right_rows,
      eval_query env left (SqlSuccess left_rows) ->
      eval_query env right (SqlSuccess right_rows) ->
      Forall property
        (Febag.elements (Fecol.CBag (CTuple T))
          (query_cross_join_bag
            (rows_bag T left_rows) (rows_bag T right_rows)))) ->
    query_success_Forall env (QExpr_CrossJoin left right) property.
```

## `query_filter_success_bags_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1538`](../OrderedQueryFacts.v#L1538)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_filter_success_bags_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    rel_equiv
      (success_bags env (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
```

## `query_expr_filter_has_success_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1748`](../OrderedQueryFacts.v#L1748)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_filter_has_success_exact` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma query_expr_filter_has_success_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    query_has_success env input ->
    query_has_success env (QExpr_Filter formula input).
```

## `query_filter_success_bags_functional_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1823`](../OrderedQueryFacts.v#L1823)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_filter_success_bags_functional_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Filter formula input) first ->
      success_bags env (QExpr_Filter formula input) second ->
      bag_eq T first second.
```

## `query_expr_filter_bag_closed_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1895`](../OrderedQueryFacts.v#L1895)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_filter_bag_closed_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) formula (keep row)) ->
    BagClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_Filter formula input) (SqlSuccess rows)).
```

## `query_success_length_le_cross_join`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2471`](../OrderedQueryFacts.v#L2471)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `cardinality`

```rocq
Theorem query_success_length_le_cross_join :
  forall env left right left_bound right_bound,
    query_length_le env left left_bound ->
    query_length_le env right right_bound ->
    query_length_le env (QExpr_CrossJoin left right)
      (left_bound * right_bound).
```

## `query_success_length_le_natural_join`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2498`](../OrderedQueryFacts.v#L2498)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Theorem query_success_length_le_natural_join :
  forall env left right left_bound right_bound,
    query_length_le env left left_bound ->
    query_length_le env right right_bound ->
    query_length_le env (QExpr_NaturalJoin left right)
      (left_bound * right_bound).
```

## `eval_query_expr_join_success_length_le`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2545`](../OrderedQueryFacts.v#L2545)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `scheduled`, `join`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Theorem eval_query_expr_join_success_length_le :
  forall env kind predicate matched_select left_select right_select
      left right output left_bound right_bound,
    eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlSuccess output) ->
    (forall rows,
      eval_query env left (SqlSuccess rows) ->
      length rows <= left_bound) ->
    (forall rows,
      eval_query env right (SqlSuccess rows) ->
      length rows <= right_bound) ->
    length output <=
      query_join_length_upper_bound kind left_bound right_bound.
```

## `query_success_length_le_join`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2602`](../OrderedQueryFacts.v#L2602)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Corollary query_success_length_le_join :
  forall env kind predicate matched_select left_select right_select
      left right left_bound right_bound,
    query_length_le env left left_bound ->
    query_length_le env right right_bound ->
    query_length_le env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right)
      (query_join_length_upper_bound kind left_bound right_bound).
```

## `eval_query_expr_right_join_single_left_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2622`](../OrderedQueryFacts.v#L2622)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Relates outer/semi/anti-join semantics to the exact list length or bag cardinality shown below.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `scheduled`, `join`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Theorem eval_query_expr_right_join_single_left_success_length :
  forall env predicate matched_select left_select right_select
      left right output,
    eval_query env
      (QExpr_Join QueryJoinRight predicate
        matched_select left_select right_select left right)
      (SqlSuccess output) ->
    (forall rows,
      eval_query env left (SqlSuccess rows) ->
      length rows = 1%nat) ->
    exists right_rows,
      eval_query env right (SqlSuccess right_rows) /\
      length output = length right_rows.
```

## `query_success_length_le_right_join_single_left`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2662`](../OrderedQueryFacts.v#L2662)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `scheduled`, `join`, `cardinality`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

```rocq
Corollary query_success_length_le_right_join_single_left :
  forall env predicate matched_select left_select right_select
      left right bound,
    (forall rows,
      eval_query env left (SqlSuccess rows) ->
      length rows = 1%nat) ->
    query_length_le env right bound ->
    query_length_le env
      (QExpr_Join QueryJoinRight predicate
        matched_select left_select right_select left right) bound.
```

## `eval_filter_rows_always_true_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3547`](../OrderedQueryFacts.v#L3547)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_filter_possible_outcome_equiv_of_always_true_uniform` for the public result.

Purpose/direction: Characterizes successful filtering when every reached predicate evaluation succeeds with SQL TRUE.

Applicability: Use only after proving every reached predicate outcome is exactly `SqlSuccess true3`; errors and UNKNOWN are not covered.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `scheduled`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_filter_rows_always_true_iff :
  forall env formula rows,
    (forall row,
      In row rows ->
      forall outcome,
        @eval_scalar_boolean_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null boolean_schedule (env_t T env row) formula outcome <->
        outcome = SqlSuccess (Bool.true (B T))) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule env formula rows outcome <->
      outcome = SqlSuccess rows.
```

## `relational_permutation_map_inv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3650`](../OrderedQueryFacts.v#L3650)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma relational_permutation_map_inv :
  forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) output input,
    _permut R output (map f input) ->
    exists reordered,
      Permutation input reordered /\
      Forall2 R output (map f reordered).
```

## `eval_project_rows_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3712`](../OrderedQueryFacts.v#L3712)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `eval_project_rows_has_success` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma eval_project_rows_has_success :
  forall env select_list rows,
    (forall row,
      In row rows ->
      scalar_select_values_has_success_at
        (env_t T env row) select_list) ->
    exists output,
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list rows (SqlSuccess output).
```

## `query_row_map_success_bags_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3875`](../OrderedQueryFacts.v#L3875)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_row_map_success_bags_total :
  forall env outputs row_map mapping input,
    row_map_total_as row_map mapping ->
    row_mapping_semantic_proper mapping ->
    rel_equiv
      (success_bags env (QExpr_RowMap outputs row_map input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T (query_row_map_bag mapping input_bag) output).
```

## `query_row_map_success_bags_functional_of_contract`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4005`](../OrderedQueryFacts.v#L4005)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_row_map_success_bags_functional_of_contract :
  forall env outputs row_map input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    row_map_success_bag_contract row_map ->
    forall first second,
      success_bags env (QExpr_RowMap outputs row_map input) first ->
      success_bags env (QExpr_RowMap outputs row_map input) second ->
      bag_eq T first second.
```

## `query_values_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4086`](../OrderedQueryFacts.v#L4086)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_values_success_bags :
  forall env outputs values,
    rel_equiv
      (success_bags env (QExpr_Values outputs values))
      (fun output => bag_eq T values output).
```

## `query_table_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4104`](../OrderedQueryFacts.v#L4104)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_table_success_bags :
  forall env outputs table,
    rel_equiv
      (success_bags env (QExpr_Table outputs table))
      (fun output =>
        bag_eq T
          (@query_table_bag T relname basesort instance outputs table)
          output).
```

## `query_table_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4175`](../OrderedQueryFacts.v#L4175)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows that a base table has one possible successful bag modulo bag equality.

Applicability: Use as the generic base case for possible-bag functionality of a table.

Important premises: Supply two possible successful bags for the same environment, outputs, and table.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_table_success_bags_functional :
  forall env outputs table first second,
    success_bags env (QExpr_Table outputs table) first ->
    success_bags env (QExpr_Table outputs table) second ->
    bag_eq T first second.
```

## `query_set_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4266`](../OrderedQueryFacts.v#L4266)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_set_success_bags_functional :
  forall env operation left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Set operation left right) first ->
      success_bags env (QExpr_Set operation left right) second ->
      bag_eq T first second.
```

## `query_cross_join_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4306`](../OrderedQueryFacts.v#L4306)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_cross_join_success_bags_functional :
  forall env left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_CrossJoin left right) first ->
      success_bags env (QExpr_CrossJoin left right) second ->
      bag_eq T first second.
```

## `query_natural_join_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4347`](../OrderedQueryFacts.v#L4347)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_natural_join_success_bags_functional :
  forall env left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_NaturalJoin left right) first ->
      success_bags env (QExpr_NaturalJoin left right) second ->
      bag_eq T first second.
```

## `query_expr_permutation_closure_certified_possible_bag_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4498`](../OrderedQueryFacts.v#L4498)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Shows that the declared bag multiplicity result is invariant under input permutation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_expr_permutation_closure_certified_possible_bag_closed :
  forall env query,
    query_expr_permutation_closure_certified query = true ->
    BagClosed T (fun rows =>
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env query (SqlSuccess rows)).
```

## `rows_key_aligned_filter`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5318`](../OrderedQueryFacts.v#L5318)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports heterogeneous relational order-key alignment through the displayed positional or total deterministic list consumer.

Applicability: Use only with a semantic key relation.  Filter decisions must be key-determined and maps total/deterministic; this interface does not equate peer payload order, bags, volatile expressions, or SQL errors.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `ordered alignment`, `filter observation`, `peer ties`

```rocq
Theorem rows_key_aligned_filter :
  forall (A B LeftKey RightKey : Type)
      (key_rel : LeftKey -> RightKey -> Prop)
      (left_key : A -> LeftKey) (right_key : B -> RightKey)
      (left_keep : LeftKey -> bool) (right_keep : RightKey -> bool),
    (forall left_value right_value,
      key_rel left_value right_value ->
      left_keep left_value = right_keep right_value) ->
    forall left right,
      rows_key_aligned key_rel left_key right_key left right ->
      rows_key_aligned key_rel left_key right_key
        (filter (fun row => left_keep (left_key row)) left)
        (filter (fun row => right_keep (right_key row)) right).
```

## `left_right_outer_scheduler_swap_Permutation`

Source: [`theories/FormalSQL/OuterJoinFilterFacts.v:169`](../OuterJoinFilterFacts.v#L169)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Shows exact occurrence permutation between LEFT and operand-swapped RIGHT outer schedulers after transposing both match decisions and matched-row emission.

Applicability: Use only after the target condition is the exact transpose and the matched and padded projections agree through one common emitter.  SQL condition/projection errors and semantic tuple equality remain separate.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `left join`, `right join`, `transpose`

```rocq
Theorem left_right_outer_scheduler_swap_Permutation :
  forall (A B C : Type) (join : A -> B -> C) (pad_left : A -> C)
      (accept : A -> B -> bool) left right,
    Permutation
      (left_outer_scheduler_rows join pad_left accept left right)
      (right_outer_scheduler_rows
        (fun right_row left_row => join left_row right_row)
        pad_left
        (fun right_row left_row => accept left_row right_row)
        right left).
```

## `full_outer_filter_to_left_outer_exact`

Source: [`theories/FormalSQL/OuterJoinFilterFacts.v:276`](../OuterJoinFilterFacts.v#L276)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Rewrites a null-rejecting filter over the three FULL-join scheduler branches to a LEFT join over the filtered left input, preserving duplicate occurrences exactly.

Applicability: Use only after matched and left-padded rows are proved to inherit one left guard and every right-padded row is rejected.  At SQL level also prove predicate totality, non-volatility, properness, and exact error equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `full join`, `left join`, `null rejection`, `multiplicity`

```rocq
Theorem full_outer_filter_to_left_outer_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (pad_left : A -> C) (pad_right : B -> C)
      (accept : A -> B -> bool) (guard_left : A -> bool)
      (guard_output : C -> bool) left right,
    (forall left_row right_row,
      guard_output (join left_row right_row) = guard_left left_row) ->
    (forall left_row,
      guard_output (pad_left left_row) = guard_left left_row) ->
    (forall right_row,
      guard_output (pad_right right_row) = false) ->
    filter guard_output
      (full_outer_scheduler_rows
        join pad_left pad_right accept left right) =
    left_outer_scheduler_rows join pad_left accept
      (filter guard_left left) right.
```

## `left_outer_null_reject_to_inner_exact`

Source: [`theories/FormalSQL/OuterJoinFilterFacts.v:310`](../OuterJoinFilterFacts.v#L310)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Removes exactly the NULL-padded branch of a LEFT outer scheduler under an explicit rejecting consumer, retaining matched-row filtering and duplicate occurrences.

Applicability: Use only when every padded-left row is rejected.  Moving the retained matched-row filter or claiming SQL outcome equivalence additionally requires totality, properness, non-volatility, and exact error premises.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `scalar`

Search aliases: `relational algebra`, `NULL`, `UNKNOWN`, `three-valued logic`, `left join`, `inner join`, `null rejection`, `multiplicity`

```rocq
Theorem left_outer_null_reject_to_inner_exact :
  forall (A B C : Type) (join : A -> B -> C) (pad_left : A -> C)
      (accept : A -> B -> bool) (guard_output : C -> bool) left right,
    (forall left_row, guard_output (pad_left left_row) = false) ->
    filter guard_output
      (left_outer_scheduler_rows join pad_left accept left right) =
    filter guard_output (join_matched_rows join accept left right).
```

## `tnull_row_eq_refl`

Source: [`theories/FormalSQL/ProofAgentFacade.v:58`](../ProofAgentFacade.v#L58)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes reflexivity for relational algebra.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: supply the declared equivalence/properness relation.

Cross-index: `facade`

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_refl :
  forall row, TNullRowEq row row.
```

## `tnull_row_eq_sym`

Source: [`theories/FormalSQL/ProofAgentFacade.v:65`](../ProofAgentFacade.v#L65)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Reverses a proved relational algebra relation.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `facade`

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_sym :
  forall left right,
    TNullRowEq left right ->
    TNullRowEq right left.
```

## `tnull_row_eq_trans`

Source: [`theories/FormalSQL/ProofAgentFacade.v:74`](../ProofAgentFacade.v#L74)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Composes two relational algebra relations through an intermediate result.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `facade`

Search aliases: `relational algebra`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_trans :
  forall first second third,
    TNullRowEq first second ->
    TNullRowEq second third ->
    TNullRowEq first third.
```

## `tnull_row_permut_implies_rows_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:98`](../ProofAgentFacade.v#L98)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull row permut implies rows bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_row_permut_implies_rows_bag_eq :
  forall left right,
    TNullRowPermut left right ->
    TNullBagEq (TNullRowsBag left) (TNullRowsBag right).
```

## `tnull_query_program_head_separation_sound`

Source: [`theories/FormalSQL/ProofAgentFacade.v:363`](../ProofAgentFacade.v#L363)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query program head separation sound law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_program_head_separation_sound` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`

```rocq
Lemma tnull_query_program_head_separation_sound :
  forall db env left right left_tail right_tail,
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryProgramOutcomeEq db env
        (left :: left_tail) (right :: right_tail).
```

## `tnull_query_program_prefix_separation_sound`

Source: [`theories/FormalSQL/ProofAgentFacade.v:379`](../ProofAgentFacade.v#L379)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: States the tnull query program prefix separation sound law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_program_prefix_separation_sound` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `possible`, `facade`, `outcome`, `runtime`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`

```rocq
Lemma tnull_query_program_prefix_separation_sound :
  forall db env left_prefix right_prefix left right left_tail right_tail,
    length left_prefix = length right_prefix ->
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryProgramOutcomeEq db env
        (left_prefix ++ left :: left_tail)
        (right_prefix ++ right :: right_tail).
```

## `tnull_map_theta_join_total_functional`

Source: [`theories/FormalSQL/ProofAgentFacade.v:428`](../ProofAgentFacade.v#L428)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `join`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:451`](../ProofAgentFacade.v#L451)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_left_join_total_functional` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `join`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:481`](../ProofAgentFacade.v#L481)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional_permut` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `join`

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

## `tnull_map_theta_join_total_functional_permut_accepted`

Source: [`theories/FormalSQL/ProofAgentFacade.v:538`](../ProofAgentFacade.v#L538)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_total_functional_permut_accepted` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `join`

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_map_theta_join_total_functional_permut_accepted :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
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

## `tnull_map_theta_join_functional_permut_filter_exists`

Source: [`theories/FormalSQL/ProofAgentFacade.v:604`](../ProofAgentFacade.v#L604)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull map theta join functional permut filter exists law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_theta_join_functional_permut_filter_exists` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `filter`, `join`

Search aliases: `relational algebra`, `join`, `filter`, `WHERE`

```rocq
Lemma tnull_map_theta_join_functional_permut_filter_exists :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit
        (filter
          (fun left_row => existsb (accept left_row) right) left)).
```

## `tnull_map_left_join_total_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:630`](../ProofAgentFacade.v#L630)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes totality of the indicated join semantics operation under the shown premises.

Applicability: Use when the goal or a hypothesis matches the `tnull_map_left_join_total_functional_permut` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `join`

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

## `tnull_map_left_join_functional_permut`

Source: [`theories/FormalSQL/ProofAgentFacade.v:664`](../ProofAgentFacade.v#L664)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Identifies a projected at-most-one LEFT JOIN with the mapped left input up to semantic permutation, retaining unmatched and duplicate left occurrences without a total-match premise.

Applicability: Use when each left occurrence has zero or one accepted right occurrence and matched and padded rows project to the same direct left result; semantic permutation preserves duplicate left rows.

Important premises: Retain both matched and padded projection equalities and the per-left at-most-one bound.  No foreign-key totality premise is required; the conclusion is occurrence-preserving permutation.

Cross-index: `facade`, `join`

Search aliases: `relational algebra`, `functional LEFT JOIN`, `at-most-one match`, `nullable unmatched key`, `left multiplicity`, `join`

```rocq
Lemma tnull_map_left_join_functional_permut :
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
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullLeftJoinRows join accept pad left right))
      (map emit left).
```

## `tnull_row_eq_of_labels_and_values`

Source: [`theories/FormalSQL/ProofAgentFacade.v:689`](../ProofAgentFacade.v#L689)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull row equality of labels and values law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_row_eq_of_labels_and_values` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`

Search aliases: `relational algebra`

```rocq
Lemma tnull_row_eq_of_labels_and_values :
  forall left right,
    TNullAttributeSetEq (TNullRowLabels left) (TNullRowLabels right) ->
    (forall attribute,
      attribute inS TNullRowLabels left ->
      TNullRowValue left attribute = TNullRowValue right attribute) ->
    TNullRowEq left right.
```

## `tnull_theta_join_by_witness`

Source: [`theories/FormalSQL/ProofAgentFacade.v:754`](../ProofAgentFacade.v#L754)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the tnull theta join by witness law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_theta_join_by_witness` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `join`

Search aliases: `relational algebra`, `join`

```rocq
Lemma tnull_theta_join_by_witness :
  forall (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (left right : list TNullRow) (witness : bool),
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (witness = true ->
      forall left_row,
        In left_row left ->
        exists right_row,
          In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (length (filter (accept left_row) right) <= 1)%nat) ->
    (witness = false ->
      forall left_row right_row,
        In left_row left ->
        In right_row right ->
        accept left_row right_row = false) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (if witness then map emit left else nil).
```

## `tnull_total_functional_theta_project_nodup`

Source: [`theories/FormalSQL/ProofAgentFacade.v:815`](../ProofAgentFacade.v#L815)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`

```rocq
Lemma tnull_total_functional_theta_project_nodup :
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
    NoDupA TNullRowEq (map emit left) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
```

## `tnull_total_functional_theta_project_nodup_accepted`

Source: [`theories/FormalSQL/ProofAgentFacade.v:850`](../ProofAgentFacade.v#L850)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`

```rocq
Lemma tnull_total_functional_theta_project_nodup_accepted :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    NoDupA TNullRowEq (map emit left) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
```

## `tnull_functional_theta_project_nodup_of_key_reflection`

Source: [`theories/FormalSQL/ProofAgentFacade.v:890`](../ProofAgentFacade.v#L890)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`

```rocq
Lemma tnull_functional_theta_project_nodup_of_key_reflection :
  forall (Key : Type) (key_relation : Key -> Key -> Prop)
      (key : TNullRow -> Key)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project : TNullRow -> TNullRow) left right,
    NoDupA key_relation (map key left) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (forall left_first left_second right_first right_second,
      In left_first left -> In left_second left ->
      In right_first right -> In right_second right ->
      accept left_first right_first = true ->
      accept left_second right_second = true ->
      TNullRowEq
        (project (join left_first right_first))
        (project (join left_second right_second)) ->
      key_relation (key left_first) (key left_second)) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
```

## `tnull_nodup_occ_le_one`

Source: [`theories/FormalSQL/ProofAgentFacade.v:936`](../ProofAgentFacade.v#L936)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `bag`

Search aliases: `relational algebra`, `multiplicity`

```rocq
Lemma tnull_nodup_occ_le_one :
  forall rows,
    NoDupA TNullRowEq rows ->
    forall row,
      (Oeset.nb_occ TNullRowOrder row rows <= 1)%N.
```

## `list_flat_map_permut_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:68`](../RelationalAlgebraFacts.v#L68)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the list flat map permut rel law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `list_flat_map_permut_rel` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`

```rocq
Lemma list_flat_map_permut_rel :
  forall A B C D
      (R : A -> B -> Prop) (S : C -> D -> Prop)
      (left_block : A -> list C) (right_block : B -> list D)
      left right,
    _permut R left right ->
    (forall left_value right_value,
      In left_value left ->
      In right_value right ->
      R left_value right_value ->
      _permut S
        (left_block left_value)
        (right_block right_value)) ->
    _permut S
      (flat_map left_block left)
      (flat_map right_block right).
```

## `theta_filter_map_permut_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:131`](../RelationalAlgebraFacts.v#L131)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the theta filter map permut rel law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `theta_filter_map_permut_rel` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma theta_filter_map_permut_rel :
  forall A B C D E F
      (outer_rel : A -> B -> Prop)
      (inner_rel : C -> D -> Prop)
      (output_rel : E -> F -> Prop)
      (left_accept : A -> C -> bool)
      (right_accept : B -> D -> bool)
      (left_emit : A -> C -> E)
      (right_emit : B -> D -> F)
      left_outer right_outer left_inner right_inner,
    _permut outer_rel left_outer right_outer ->
    _permut inner_rel left_inner right_inner ->
    (forall left_row right_row left_value right_value,
      In left_row left_outer ->
      In right_row right_outer ->
      In left_value left_inner ->
      In right_value right_inner ->
      outer_rel left_row right_row ->
      inner_rel left_value right_value ->
      left_accept left_row left_value =
        right_accept right_row right_value) ->
    (forall left_row right_row left_value right_value,
      In left_row left_outer ->
      In right_row right_outer ->
      In left_value left_inner ->
      In right_value right_inner ->
      outer_rel left_row right_row ->
      inner_rel left_value right_value ->
      output_rel
        (left_emit left_row left_value)
        (right_emit right_row right_value)) ->
    _permut output_rel
      (flat_map
        (fun left_row =>
          map (left_emit left_row)
            (filter (left_accept left_row) left_inner))
        left_outer)
      (flat_map
        (fun right_row =>
          map (right_emit right_row)
            (filter (right_accept right_row) right_inner))
        right_outer).
```

## `interp_direct_attribute_in_env_t`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:209`](../RelationalAlgebraFacts.v#L209)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the interp direct attribute in env t law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `interp_direct_attribute_in_env_t` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema`

Search aliases: `relational algebra`, `schema conformance`, `typing`

```rocq
Lemma interp_direct_attribute_in_env_t :
  forall (T : Tuple.Rcd) env row attribute,
    attribute inS labels T row ->
    interp_aggterm T (env_t T env row)
      (@A_Expr T (@F_Dot T attribute)) =
    dot T row attribute.
```

## `list_support_rel_compose`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:238`](../RelationalAlgebraFacts.v#L238)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_compose :
  forall A B C (R : A -> B -> Prop) (S : B -> C -> Prop)
      (U : A -> C -> Prop) left middle right,
    list_support_rel R left middle ->
    list_support_rel S middle right ->
    (forall x y z, R x y -> S y z -> U x z) ->
    list_support_rel U left right.
```

## `list_support_rel_map_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:264`](../RelationalAlgebraFacts.v#L264)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_map_transport :
  forall A B C D (R : A -> B -> Prop) (S : C -> D -> Prop)
      (left_map : A -> C) (right_map : B -> D) left right,
    list_support_rel R left right ->
    (forall x y, R x y -> S (left_map x) (right_map y)) ->
    list_support_rel S (map left_map left) (map right_map right).
```

## `list_support_rel_filter_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:294`](../RelationalAlgebraFacts.v#L294)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional relational support through two total filters whose decisions agree only on actually related representatives.

Applicability: Use after proving support and decision properness on the support relation.  It ignores multiplicity and does not model volatile or runtime-error-producing SQL predicate evaluation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `bag semantics`, `list/bag bridge`, `support`, `properness`, `reachable representatives`

```rocq
Lemma list_support_rel_filter_transport :
  forall A B (R : A -> B -> Prop)
      (left_keep : A -> bool) (right_keep : B -> bool) left right,
    list_support_rel R left right ->
    (forall left_row right_row,
      R left_row right_row ->
      left_keep left_row = right_keep right_row) ->
    list_support_rel R
      (filter left_keep left) (filter right_keep right).
```

## `list_support_rel_map_iff`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:330`](../RelationalAlgebraFacts.v#L330)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_map_iff :
  forall A B C D (R : B -> D -> Prop)
      (left_map : A -> B) (right_map : C -> D) left right,
    list_support_rel R (map left_map left) (map right_map right) <->
    list_support_rel
      (fun x y => R (left_map x) (right_map y)) left right.
```

## `list_support_rel_unmap_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:358`](../RelationalAlgebraFacts.v#L358)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_unmap_left :
  forall A B C (R : B -> C -> Prop) (mapping : A -> B) left right,
    list_support_rel R (map mapping left) right ->
    list_support_rel (fun x y => R (mapping x) y) left right.
```

## `list_support_rel_map_left_with_witness`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:378`](../RelationalAlgebraFacts.v#L378)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional row support through the displayed relation; it does not preserve duplicate multiplicity by itself.

Applicability: Use to connect row-existence witnesses across relational stages; do not treat the conclusion as bag equality or multiplicity preservation.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`

```rocq
Lemma list_support_rel_map_left_with_witness :
  forall A B C (R : A -> C -> Prop) (mapping : A -> B) left right,
    list_support_rel R left right ->
    list_support_rel
      (fun mapped output =>
        exists original, mapped = mapping original /\ R original output)
      (map mapping left) right.
```

## `all_diff_map_key_NoDupA`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:403`](../RelationalAlgebraFacts.v#L403)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `all_diff_map_key_NoDupA` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: primary card only

Search aliases: `relational algebra`

```rocq
Lemma all_diff_map_key_NoDupA :
  forall (A B : Type) (key : A -> B) rows,
    ListFacts.all_diff (map key rows) ->
    SetoidList.NoDupA
      (fun left right => key left = key right) rows.
```

## `rel_equiv_refl`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:423`](../RelationalAlgebraFacts.v#L423)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:430`](../RelationalAlgebraFacts.v#L430)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:439`](../RelationalAlgebraFacts.v#L439)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:453`](../RelationalAlgebraFacts.v#L453)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:460`](../RelationalAlgebraFacts.v#L460)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:470`](../RelationalAlgebraFacts.v#L470)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:484`](../RelationalAlgebraFacts.v#L484)

Interface layer: General reusable foundation; no SQL interface layer is implied.

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

## `bag_closed_rel_equiv_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:494`](../RelationalAlgebraFacts.v#L494)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_closed_rel_equiv_transport :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    BagClosed T left ->
    BagClosed T right.
```

## `bag_closed_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:507`](../RelationalAlgebraFacts.v#L507)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_union :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows \/ right rows).
```

## `bag_closed_exists`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:523`](../RelationalAlgebraFacts.v#L523)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_closed_exists :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => exists index, family index rows).
```

## `ordered_rows_equiv_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:538`](../RelationalAlgebraFacts.v#L538)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `cardinality`

Search aliases: `relational algebra`, `cardinality`, `equivalence`, `congruence`

```rocq
Lemma ordered_rows_equiv_length :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    length left = length right.
```

## `ordered_rows_equiv_occ`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:548`](../RelationalAlgebraFacts.v#L548)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:560`](../RelationalAlgebraFacts.v#L560)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_occ :
  forall (T : Tuple.Rcd) (rows : list (tuple T)) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T rows) =
    Oeset.nb_occ (OTuple T) row rows.
```

## `bag_eq_iff_occurrences`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:570`](../RelationalAlgebraFacts.v#L570)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:583`](../RelationalAlgebraFacts.v#L583)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_eq_cardinal :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
    Febag.cardinal (Fecol.CBag (CTuple T)) right.
```

## `bag_occurrences_disjoint_of_boolean_separator`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:600`](../RelationalAlgebraFacts.v#L600)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates membership or occurrence evidence to bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma bag_occurrences_disjoint_of_boolean_separator :
  forall (T : Tuple.Rcd)
      (left right : SqlBagAbstraction.bagT T)
      (separate : tuple T -> bool),
    (forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left <> 0%N ->
      separate row = false) ->
    (forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right <> 0%N ->
      separate row = true) ->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left = 0%N \/
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right = 0%N.
```

## `bag_filter_congr_on_support`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:640`](../RelationalAlgebraFacts.v#L640)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports finite-bag filtering across bag-equal inputs when two predicates agree on semantic tuple occurrences in the left support.

Applicability: Use when an environment-dependent row predicate has been proved equal to another predicate only on represented input rows; input bags need be semantically bag-equal, not Leibniz-equal.

Important premises: Retain input `bag_eq`, positive left multiplicity, semantic tuple equality, and cross-predicate agreement; no equality is required outside the represented left support.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma bag_filter_congr_on_support :
  forall (T : Tuple.Rcd)
      (left_keep right_keep : tuple T -> bool)
      (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    (forall left_row right_row,
      (Febag.nb_occ (Fecol.CBag (CTuple T)) left_row left >= 1)%N ->
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      left_keep left_row = right_keep right_row) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) left_keep left)
      (Febag.filter (Fecol.CBag (CTuple T)) right_keep right).
```

## `rows_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:658`](../RelationalAlgebraFacts.v#L658)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T)),
    Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T rows) =
    N.of_nat (length rows).
```

## `query_same_rows_as_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:668`](../RelationalAlgebraFacts.v#L668)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:682`](../RelationalAlgebraFacts.v#L682)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:696`](../RelationalAlgebraFacts.v#L696)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

## `query_same_rows_as_bag_semantic_permut_elements`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:748`](../RelationalAlgebraFacts.v#L748)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_semantic_permut_elements :
  forall (T : Tuple.Rcd) rows bag,
    @query_same_rows_as_bag T rows bag ->
    _permut
      (fun left right => Oeset.compare (OTuple T) left right = Eq)
      rows (Febag.elements (Fecol.CBag (CTuple T)) bag).
```

## `query_same_rows_as_bag_Forall_transport`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:768`](../RelationalAlgebraFacts.v#L768)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports the displayed hypotheses and conclusion for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_Forall_transport :
  forall (T : Tuple.Rcd) (property : tuple T -> Prop) first second bag,
    tuple_property_semantic_invariant property ->
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    Forall property first ->
    Forall property second.
```

## `query_same_rows_as_bag_filter`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:798`](../RelationalAlgebraFacts.v#L798)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

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

## `query_canonical_rows_same_as_bag`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:824`](../RelationalAlgebraFacts.v#L824)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_canonical_rows_same_as_bag :
  forall (T : Tuple.Rcd) rows bag,
    @query_same_rows_as_bag T rows bag ->
    @query_same_rows_as_bag T (@query_canonical_rows T rows) bag.
```

## `query_canonical_rows_length_between`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:838`](../RelationalAlgebraFacts.v#L838)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality`

Search aliases: `relational algebra`, `cardinality`

```rocq
Lemma query_canonical_rows_length_between :
  forall (T : Tuple.Rcd) first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    List.length (@query_canonical_rows T first) =
    List.length (@query_canonical_rows T second).
```

## `query_canonical_rows_filter_permut`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:854`](../RelationalAlgebraFacts.v#L854)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query canonical rows filter permut law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_canonical_rows_filter_permut :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool) left right original,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    @query_same_rows_as_bag T left (rows_bag T original) ->
    @query_same_rows_as_bag T right
      (rows_bag T (List.filter keep original)) ->
    Oeset.permut (OTuple T)
      (List.filter keep (@query_canonical_rows T left))
      (@query_canonical_rows T right).
```

## `query_same_rows_as_filtered_bag_preimage`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:918`](../RelationalAlgebraFacts.v#L918)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

## `oeset_nb_occ_of_NoDupA`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:991`](../RelationalAlgebraFacts.v#L991)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1027`](../RelationalAlgebraFacts.v#L1027)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for relational algebra.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

## `rows_bag_eq_of_nodup_support_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1049`](../RelationalAlgebraFacts.v#L1049)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed duplicate-freedom property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma rows_bag_eq_of_nodup_support_rel :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    SetoidList.NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left ->
    SetoidList.NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      right ->
    bag_eq T (rows_bag T left) (rows_bag T right).
```

## `alpha_membership_iff_occurrence_representative`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1101`](../RelationalAlgebraFacts.v#L1101)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for bag multiplicity.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1134`](../RelationalAlgebraFacts.v#L1134)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
```

## `query_set_union_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1147`](../RelationalAlgebraFacts.v#L1147)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_union_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1160`](../RelationalAlgebraFacts.v#L1160)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Union left right)
             (query_set_bag Union right left).
```

## `query_set_union_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1171`](../RelationalAlgebraFacts.v#L1171)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Union (query_set_bag Union first second) third)
      (query_set_bag Union first (query_set_bag Union second third)).
```

## `query_set_union_max_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1183`](../RelationalAlgebraFacts.v#L1183)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag UnionMax left right)
             (query_set_bag UnionMax right left).
```

## `query_set_union_max_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1194`](../RelationalAlgebraFacts.v#L1194)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1208`](../RelationalAlgebraFacts.v#L1208)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag UnionMax bag bag) bag.
```

## `query_set_union_max_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1218`](../RelationalAlgebraFacts.v#L1218)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
```

## `query_set_union_max_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1231`](../RelationalAlgebraFacts.v#L1231)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_inter_comm`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1244`](../RelationalAlgebraFacts.v#L1244)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes commutativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Inter left right)
             (query_set_bag Inter right left).
```

## `query_set_inter_assoc`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1255`](../RelationalAlgebraFacts.v#L1255)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes associativity for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1269`](../RelationalAlgebraFacts.v#L1269)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared SQL bag/set operations operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag Inter bag bag) bag.
```

## `query_set_inter_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1279`](../RelationalAlgebraFacts.v#L1279)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_inter_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1292`](../RelationalAlgebraFacts.v#L1292)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_union_max_inter_absorb`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1305`](../RelationalAlgebraFacts.v#L1305)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed absorption law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_union_max_inter_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag UnionMax left (query_set_bag Inter left right))
      left.
```

## `query_set_inter_union_max_absorb`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1317`](../RelationalAlgebraFacts.v#L1317)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed absorption law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `INTERSECT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_inter_union_max_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Inter left (query_set_bag UnionMax left right))
      left.
```

## `query_set_diff_empty_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1329`](../RelationalAlgebraFacts.v#L1329)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_diff_empty_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1342`](../RelationalAlgebraFacts.v#L1342)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
```

## `query_set_diff_self_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1355`](../RelationalAlgebraFacts.v#L1355)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_self_empty :
  forall bag : bagT,
    bag_eq T (query_set_bag Diff bag bag)
             (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_set_diff_union_cancel_right`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1366`](../RelationalAlgebraFacts.v#L1366)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed cancellation direction for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_union_cancel_right :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) right)
      left.
```

## `query_set_diff_union_cancel_left`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1378`](../RelationalAlgebraFacts.v#L1378)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes the displayed cancellation direction for SQL bag/set operations.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `EXCEPT`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_set_diff_union_cancel_left :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) left)
      right.
```

## `query_cross_join_empty`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1390`](../RelationalAlgebraFacts.v#L1390)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1416`](../RelationalAlgebraFacts.v#L1416)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1443`](../RelationalAlgebraFacts.v#L1443)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the exact empty-input or empty-result law for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_empty :
  bag_eq T
    (query_distinct_bag (Febag.empty (Fecol.CBag (CTuple T))))
    (Febag.empty (Fecol.CBag (CTuple T))).
```

## `query_distinct_bag_idempotent`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1461`](../RelationalAlgebraFacts.v#L1461)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Establishes idempotence for the declared bag multiplicity operator.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `DISTINCT`, `duplicate elimination`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_distinct_bag_idempotent :
  forall bag : bagT,
    bag_eq T (query_distinct_bag (query_distinct_bag bag))
             (query_distinct_bag bag).
```

## `query_cross_join_bag_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1479`](../RelationalAlgebraFacts.v#L1479)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`, `cardinality`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1513`](../RelationalAlgebraFacts.v#L1513)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`, `cardinality`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1562`](../RelationalAlgebraFacts.v#L1562)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma query_join_matched_sources_length_le :
  forall (left : tuple T) rights flags,
    length (query_join_matched_sources T left rights flags) <= length rights.
```

## `query_join_left_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1571`](../RelationalAlgebraFacts.v#L1571)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1602`](../RelationalAlgebraFacts.v#L1602)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for join cardinality.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma query_join_unmatched_right_sources_length_le :
  forall index rights matrix,
    length
      (query_join_unmatched_right_sources_from T index rights matrix) <=
    length rights.
```

## `query_join_sources_length_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1614`](../RelationalAlgebraFacts.v#L1614)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

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

## `query_join_full_sources_member_iff`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1872`](../RelationalAlgebraFacts.v#L1872)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Gives necessary and sufficient conditions for outer-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `join`

```rocq
Theorem query_join_full_sources_member_iff :
  forall (matches : tuple T -> tuple T -> bool) lefts rights output,
    In output
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun left => map (matches left) rights) lefts)) <->
    (exists left right,
      In left lefts /\
      In right rights /\
      matches left right = true /\
      JoinSourceMatched T (join_tuple T left right) = output) \/
    (exists left,
      In left lefts /\
      (forall right, In right rights -> matches left right = false) /\
      JoinSourceLeft T left = output) \/
    (exists right,
      In right rights /\
      (forall left, In left lefts -> matches left right = false) /\
      JoinSourceRight T right = output).
```

## `query_join_sources_member_iff`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2180`](../RelationalAlgebraFacts.v#L2180)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes scheduler-source membership for every native join kind, keeping matched, unmatched-left, unmatched-right, semi, and anti reachability distinct.

Applicability: Use on a concrete scheduler source list and inspect the constructor-specific disjunct.  Semi and anti emit left sources for opposite reachability decisions; outer unmatched branches are not symmetric aliases.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `join`

Search aliases: `relational algebra`, `join`, `inner join`, `outer join`, `semi join`, `anti join`, `scheduler`

```rocq
Theorem query_join_sources_member_iff :
  forall kind (matches : tuple T -> tuple T -> bool) lefts rights output,
    In output
      (query_join_sources T kind lefts rights
        (map (fun left => map (matches left) rights) lefts)) <->
    query_join_source_supported kind matches lefts rights output.
```

## `query_join_sources_support_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2543`](../RelationalAlgebraFacts.v#L2543)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Transports bidirectional source support across all six native join constructors under exact match-decision correspondence.

Applicability: Use after proving bidirectional input support and exact Boolean match correspondence.  The projected form also requires both source inputs to be reached before applying an emitter; prove bags, order, and errors separately.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `bag semantics`, `list/bag bridge`, `support`, `matched and unmatched branches`

```rocq
Theorem query_join_sources_support_rel :
  forall kind (left_rel right_rel : tuple T -> tuple T -> Prop)
      (left_match right_match : tuple T -> tuple T -> bool)
      left_rows left_rows' right_rows right_rows',
    list_support_rel left_rel left_rows left_rows' ->
    list_support_rel right_rel right_rows right_rows' ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      left_match left right = right_match left' right') ->
    list_support_rel (query_join_kind_source_rel kind left_rel right_rel)
      (query_join_sources T kind left_rows right_rows
        (map (fun left => map (left_match left) right_rows) left_rows))
      (query_join_sources T kind left_rows' right_rows'
        (map (fun left => map (right_match left) right_rows') left_rows')).
```

## `query_join_sources_projected_support_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2612`](../RelationalAlgebraFacts.v#L2612)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts all-kind join-source support through reached-only emitters, without claiming multiplicity, ordering, or runtime-error equivalence.

Applicability: Use after proving bidirectional input support and exact Boolean match correspondence.  The projected form also requires both source inputs to be reached before applying an emitter; prove bags, order, and errors separately.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `bag semantics`, `list/bag bridge`, `projection`, `reached source`, `support`

```rocq
Theorem query_join_sources_projected_support_rel :
  forall kind (left_rel right_rel output_rel : tuple T -> tuple T -> Prop)
      (left_match right_match : tuple T -> tuple T -> bool)
      (left_emit right_emit : query_join_source T -> tuple T)
      left_rows left_rows' right_rows right_rows',
    list_support_rel left_rel left_rows left_rows' ->
    list_support_rel right_rel right_rows right_rows' ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      left_match left right = right_match left' right') ->
    (forall first second,
      query_join_source_supported kind
        left_match left_rows right_rows first ->
      query_join_source_supported kind
        right_match left_rows' right_rows' second ->
      query_join_kind_source_rel kind left_rel right_rel first second ->
      output_rel (left_emit first) (right_emit second)) ->
    list_support_rel output_rel
      (map left_emit
        (query_join_sources T kind left_rows right_rows
          (map (fun left => map (left_match left) right_rows) left_rows)))
      (map right_emit
        (query_join_sources T kind left_rows' right_rows'
          (map
            (fun left => map (right_match left) right_rows') left_rows'))).
```

## `query_join_full_projected_support_rel`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2674`](../RelationalAlgebraFacts.v#L2674)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query join full projected support rel law for outer-join semantics, in the exact direction displayed by the declaration.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `join`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_join_full_projected_support_rel :
  forall (left_rel right_rel output_rel : tuple T -> tuple T -> Prop)
      (left_match right_match : tuple T -> tuple T -> bool)
      (left_emit right_emit : query_join_source T -> tuple T)
      left_rows left_rows' right_rows right_rows',
    list_support_rel left_rel left_rows left_rows' ->
    list_support_rel right_rel right_rows right_rows' ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      left_match left right = right_match left' right') ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      output_rel
        (left_emit
          (JoinSourceMatched T (join_tuple T left right)))
        (right_emit
          (JoinSourceMatched T (join_tuple T left' right')))) ->
    (forall left left',
      left_rel left left' ->
      output_rel
        (left_emit (JoinSourceLeft T left))
        (right_emit (JoinSourceLeft T left'))) ->
    (forall right right',
      right_rel right right' ->
      output_rel
        (left_emit (JoinSourceRight T right))
        (right_emit (JoinSourceRight T right'))) ->
    list_support_rel output_rel
      (map left_emit
        (query_join_sources T QueryJoinFull left_rows right_rows
          (map (fun left => map (left_match left) right_rows) left_rows)))
      (map right_emit
        (query_join_sources T QueryJoinFull left_rows' right_rows'
          (map
            (fun left => map (right_match left) right_rows') left_rows'))).
```

## `query_bag_filter_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2837`](../RelationalAlgebraFacts.v#L2837)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_union :
  forall (keep : tuple T -> bool) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) keep
        (query_set_bag Union left right))
      (query_set_bag Union
        (Febag.filter (Fecol.CBag (CTuple T)) keep left)
        (Febag.filter (Fecol.CBag (CTuple T)) keep right)).
```

## `query_bag_map_union`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2860`](../RelationalAlgebraFacts.v#L2860)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_map_union :
  forall (mapping : tuple T -> tuple T) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping (query_set_bag Union left right))
      (query_set_bag Union
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping left)
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping right)).
```

## `query_bag_map_congr`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2902`](../RelationalAlgebraFacts.v#L2902)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_bag_map_congr :
  forall (mapping : tuple T -> tuple T) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    bag_eq T left right ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping left)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping right).
```

## `query_bag_filter_commute`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2927`](../RelationalAlgebraFacts.v#L2927)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_commute :
  forall (first second : tuple T -> bool) (bag : bagT),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      first left = first right) ->
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      second left = second right) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) first
        (Febag.filter (Fecol.CBag (CTuple T)) second bag))
      (Febag.filter (Fecol.CBag (CTuple T)) second
        (Febag.filter (Fecol.CBag (CTuple T)) first bag)).
```

## `query_bag_filter_map_fusion`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2954`](../RelationalAlgebraFacts.v#L2954)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Exposes the named multiplicity-preserving finite-bag filter/map homomorphism under semantic predicate or row-map properness.

Applicability: Use below the query evaluator after proving every displayed predicate/map respects semantic tuple equality; these laws preserve multiplicity but do not discharge expression runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_bag_filter_map_fusion :
  forall (keep : tuple T -> bool) (mapping : tuple T -> tuple T) (bag : bagT),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      Oeset.compare (OTuple T) (mapping left) (mapping right) = Eq) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) keep
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping bag))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping
        (Febag.filter (Fecol.CBag (CTuple T))
          (fun row => keep (mapping row)) bag)).
```

## `query_bag_map_pairwise_equiv_of_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2990`](../RelationalAlgebraFacts.v#L2990)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Equates two mapped bags of equal cardinality when every reached left mapped row is semantically equal to every reached right one.

Applicability: Use for constant-observation projections after equal bag cardinality and pairwise equality on actual representatives are established.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`, `cardinality`

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_bag_map_pairwise_equiv_of_cardinal :
  forall (left_map right_map : tuple T -> tuple T) (left right : bagT),
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
      Febag.cardinal (Fecol.CBag (CTuple T)) right ->
    (forall left_row right_row,
      In left_row (Febag.elements (Fecol.CBag (CTuple T)) left) ->
      In right_row (Febag.elements (Fecol.CBag (CTuple T)) right) ->
      Oeset.compare (OTuple T) (left_map left_row) (right_map right_row) =
        Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        left_map left)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        right_map right).
```

## `query_cross_join_bag_singleton_right_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3042`](../RelationalAlgebraFacts.v#L3042)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Normalizes a CROSS JOIN with one right bag occurrence to the corresponding multiplicity-preserving row map of the left bag.

Applicability: Use only for a semantic singleton bag on the right; lift to a query outcome separately so child and projection errors remain observable.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_cross_join_bag_singleton_right_map :
  forall (left : bagT) right_row,
    bag_eq T
      (query_cross_join_bag left
        (Febag.singleton (Fecol.CBag (CTuple T)) right_row))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun left_row => join_tuple T left_row right_row) left).
```

## `eval_join_row_conditions_acceptance_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3219`](../RelationalAlgebraFacts.v#L3219)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Characterizes one left row's complete join-condition evaluation as the successful Boolean acceptance map over right rows.

Applicability: Use after establishing the exact acceptance contract for every right row that occurs in the displayed list; order and duplicates are retained by `map`.

Important premises: Supply `join_condition_acceptance_exact_at` for every right-row occurrence; the conclusion retains list order and duplicate flags.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_join_row_conditions_acceptance_exact :
  forall env predicate left rights (accepted : tuple T -> bool),
    (forall right,
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted right)) ->
    forall outcome,
      @eval_join_row_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env predicate left rights outcome <->
      outcome = SqlSuccess (map accepted rights).
```

## `eval_join_conditions_acceptance_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3272`](../RelationalAlgebraFacts.v#L3272)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts pairwise exact join acceptance to the complete row-major successful condition matrix, excluding condition errors.

Applicability: Use after establishing exact acceptance for every reached left/right pair; the conclusion is the literal row-major matrix, not a bag.

Important premises: Supply `join_condition_acceptance_exact_at` for every reached pair from both input lists; the resulting matrix remains row-major.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_join_conditions_acceptance_exact :
  forall env predicate lefts rights
      (accepted : tuple T -> tuple T -> bool),
    (forall left right,
      In left lefts ->
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)) ->
    forall outcome,
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env predicate lefts rights outcome <->
      outcome =
        SqlSuccess
          (map (fun left => map (accepted left) rights) lefts).
```

## `eval_project_join_sources_exact_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3363`](../RelationalAlgebraFacts.v#L3363)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Lifts exact projection of every reached matched or padded join source to one ordered successful map over the source list.

Applicability: Use after proving exact successful projection only for sources in the reached source list; matched and both NULL-padded source forms must remain covered.

Important premises: Supply exact successful projection for every source occurring in the source list; do not omit matched, left-padded, or right-padded constructors that can be reached.

Cross-index: `outcome`, `runtime`, `projection`, `join`

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_project_join_sources_exact_map :
  forall env matched_select left_select right_select sources
      (emit : query_join_source T -> tuple T),
    (forall source,
      In source sources ->
      join_source_projection_exact_at env
        matched_select left_select right_select source (emit source)) ->
    forall outcome,
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env matched_select left_select right_select
        sources outcome <->
      outcome = SqlSuccess (map emit sources).
```

## `eval_join_bag_safe_of_acceptance_projection_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3419`](../RelationalAlgebraFacts.v#L3419)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Combines total exact pair acceptance with exact matched/padded projection to construct a successful join bag and rule out every local join error for any modeled join kind.

Applicability: Use to discharge local join success and no-error obligations after providing total pairwise acceptance and total source-projection contracts; child-query errors are outside this bag-local theorem.

Important premises: Both universal contracts are mandatory: exact acceptance for every left/right pair and exact successful projection for every possible join source.  The conclusion is bag-local and does not establish child-query safety.

Cross-index: `outcome`, `runtime`, `projection`, `join`, `bag`

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_join_bag_safe_of_acceptance_projection_exact :
  forall env kind predicate matched_select left_select right_select
      (accepted : tuple T -> tuple T -> bool)
      (emit : query_join_source T -> tuple T)
      left_bag right_bag,
    (forall left right,
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)) ->
    (forall source,
      join_source_projection_exact_at env
        matched_select left_select right_select source (emit source)) ->
    (exists output_bag,
      @eval_join_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env kind predicate matched_select left_select right_select
        left_bag right_bag (SqlSuccess output_bag)) /\
    (forall error,
      ~ @eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule env kind predicate matched_select left_select right_select
          left_bag right_bag (SqlError error)).
```

## `eval_join_row_conditions_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3502`](../RelationalAlgebraFacts.v#L3502)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma eval_join_row_conditions_success_length :
  forall env predicate left rights flags,
    @eval_join_row_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env predicate left rights
      (SqlSuccess flags) ->
    length flags = length rights.
```

## `eval_join_conditions_success_dimensions`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3516`](../RelationalAlgebraFacts.v#L3516)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when the goal or a hypothesis matches the `eval_join_conditions_success_dimensions` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`

```rocq
Lemma eval_join_conditions_success_dimensions :
  forall env predicate lefts rights matrix,
    @eval_join_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env predicate lefts rights
      (SqlSuccess matrix) ->
    length matrix = length lefts /\
    Forall (fun flags => length flags = length rights) matrix.
```

## `query_join_right_single_left_sources_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3576`](../RelationalAlgebraFacts.v#L3576)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates outer-join semantics to the exact list length or bag cardinality shown below.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `join`, `cardinality`

```rocq
Lemma query_join_right_single_left_sources_length :
  forall (left : tuple T) rights flags,
    length flags = length rights ->
    length
      (query_join_sources T QueryJoinRight (left :: nil) rights
        (flags :: nil)) =
    length rights.
```

## `query_same_rows_as_bag_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3789`](../RelationalAlgebraFacts.v#L3789)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_same_rows_as_bag_map :
  forall (mapping : tuple T -> tuple T) rows bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map mapping rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping bag).
```

## `query_join_left_functional_projection_bag_on_representatives`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3824`](../RelationalAlgebraFacts.v#L3824)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: States the query join left functional projection bag on representatives law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `join`, `bag`

Search aliases: `relational algebra`, `functional LEFT JOIN`, `at-most-one match`, `nullable unmatched key`, `left multiplicity`, `join`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_join_left_functional_projection_bag_on_representatives :
  forall env predicate matched_select left_select right_select
      (project emit : tuple T -> tuple T) left_bag right_bag joined_bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (project first) (project second) = Eq) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    (forall left_rows right_rows matrix,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env predicate left_rows right_rows
        (SqlSuccess matrix) ->
      Forall
        (fun flags =>
          (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
        matrix) ->
    (forall left_rows right_rows left right values,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      In left left_rows ->
      In right right_rows ->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule (env_t T env (join_tuple T left right))
        (map fst matched_select) (SqlSuccess values) ->
      Oeset.compare (OTuple T)
        (project (project_row matched_select values)) (emit left) = Eq) ->
    (forall left_rows left values,
      query_same_rows_as_bag left_rows left_bag ->
      In left left_rows ->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule (env_t T env left)
        (map fst left_select) (SqlSuccess values) ->
      Oeset.compare (OTuple T)
        (project (project_row left_select values)) (emit left) = Eq) ->
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env QueryJoinLeft predicate matched_select left_select
      right_select
      left_bag right_bag (SqlSuccess joined_bag) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        project joined_bag)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        emit left_bag).
```

## `project_join_sources_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3935`](../RelationalAlgebraFacts.v#L3935)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma project_join_sources_success_length :
  forall env matched_select left_select right_select sources output,
    @eval_project_join_sources_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env matched_select left_select right_select sources
      (SqlSuccess output) ->
    length output = length sources.
```

## `eval_join_bag_success_cardinal_le`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3964`](../RelationalAlgebraFacts.v#L3964)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `bag`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_join_bag_success_cardinal_le :
  forall env kind predicate matched_select left_select right_select
         left_bag right_bag output_bag,
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env kind
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

## `eval_join_bag_right_single_left_success_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4044`](../RelationalAlgebraFacts.v#L4044)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates outer-join semantics to the exact list length or bag cardinality shown below.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `bag`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `join`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem eval_join_bag_right_single_left_success_cardinal :
  forall env predicate matched_select left_select right_select
         left_bag right_bag output_bag,
    Febag.cardinal (Fecol.CBag (CTuple T)) left_bag = 1%N ->
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env
      QueryJoinRight predicate matched_select left_select right_select
      left_bag right_bag (SqlSuccess output_bag) ->
    Febag.cardinal (Fecol.CBag (CTuple T)) output_bag =
      Febag.cardinal (Fecol.CBag (CTuple T)) right_bag.
```

## `query_grouping_sets_actual_success_bags_congr`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4093`](../RelationalAlgebraFacts.v#L4093)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `grouping`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `grouping sets`, `GROUP BY`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_grouping_sets_actual_success_bags_congr :
  forall env grouping_sets left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_GroupingSets grouping_sets left))
      (success_bags env (QExpr_GroupingSets grouping_sets right)).
```

## `query_expr_equiv_implies_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4122`](../RelationalAlgebraFacts.v#L4122)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_implies_success_bags :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_expr_outcome_equiv_implies_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4139`](../RelationalAlgebraFacts.v#L4139)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Projects fixed-environment error-preserving ordered equivalence to equality of possible successful bags, including the error-only case.

Applicability: Use to forget successful row order at one environment; the theorem deliberately drops error observations, so retain a separate error proof when rebuilding parent outcome equivalence.

Important premises: Supply the exact fixed-environment child outcome equivalence; this conclusion preserves successful multiplicity but intentionally does not carry the error relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_implies_success_bags :
  forall env left right,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_set_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4152`](../RelationalAlgebraFacts.v#L4152)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_set_success_bags_congr_of_query_expr_equiv :
  forall env operation left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env right right' ->
    rel_equiv
      (success_bags env (QExpr_Set operation left right))
      (success_bags env (QExpr_Set operation left' right')).
```

## `query_natural_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4176`](../RelationalAlgebraFacts.v#L4176)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_natural_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env right right' ->
    rel_equiv
      (success_bags env (QExpr_NaturalJoin left right))
      (success_bags env (QExpr_NaturalJoin left' right')).
```

## `query_cross_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4194`](../RelationalAlgebraFacts.v#L4194)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_cross_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env right right' ->
    rel_equiv
      (success_bags env (QExpr_CrossJoin left right))
      (success_bags env (QExpr_CrossJoin left' right')).
```

## `query_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4212`](../RelationalAlgebraFacts.v#L4212)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_join_success_bags_congr_of_query_expr_equiv :
  forall env kind predicate matched_select left_select right_select
         left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env right right' ->
    rel_equiv
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left' right')).
```

## `query_cross_join_union_right_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4239`](../RelationalAlgebraFacts.v#L4239)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Distributes CROSS JOIN over right-hand UNION ALL at the possible-bag layer while preserving duplicate multiplicity.

Applicability: Use for right-hand UNION ALL distribution only after proving both displayed sort equalities and possible-bag functionality of the duplicated left child.

Important premises: Both set-operation sort equalities and pairwise possible-bag functionality of the duplicated left child are mandatory; UNION is multiplicity-preserving UNION ALL here.

Cross-index: `scheduled`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_cross_join_union_right_success_bags :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    rel_equiv
      (success_bags env
        (QExpr_CrossJoin left (QExpr_Set Union first second)))
      (success_bags env
        (QExpr_Set Union
          (QExpr_CrossJoin left first)
          (QExpr_CrossJoin left second))).
```

## `query_expr_join_no_error_of_acceptance_projection_exact`

Source: [`theories/FormalSQL/SemijoinCompositionFacts.v:41`](../SemijoinCompositionFacts.v#L41)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Rules out every native join error after both children are error-free and every reached condition and matched/padded projection has one exact success.

Applicability: Use only after proving both children error-free, exact condition acceptance for every row pair, and exact successful projection for every potentially reached join source.  This proves safety, not bag or outcome equivalence.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `runtime`, `projection`, `join`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `exact acceptance`, `projection safety`, `runtime error`

```rocq
Theorem query_expr_join_no_error_of_acceptance_projection_exact :
  forall env kind predicate matched_select left_select right_select
      left right (accepted : tuple T -> tuple T -> bool)
      (emit : query_join_source T -> tuple T),
    (forall error, ~ eval_query env left (SqlError error)) ->
    (forall error, ~ eval_query env right (SqlError error)) ->
    (forall left_row right_row,
      @join_condition_acceptance_exact_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env predicate left_row right_row
        (accepted left_row right_row)) ->
    (forall source,
      @join_source_projection_exact_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env matched_select left_select right_select source
        (emit source)) ->
    forall error,
      ~ eval_query env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error).
```

## `partial_semijoin_projection_support_rel`

Source: [`theories/FormalSQL/SemijoinCompositionFacts.v:101`](../SemijoinCompositionFacts.v#L101)

Interface layer: General reusable foundation; no SQL interface layer is implied.

Purpose/direction: Relates the support of surviving semijoin rows to the support of projected matching join cells without assuming a functional match; repeated right matches remain present on the join side.

Applicability: Use only at a support or duplicate-elimination boundary after relating every accepted projected join cell to its surviving left row.  It intentionally does not preserve multiplicity, order, SQL Bool3 evaluation, or runtime errors.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `bag semantics`, `list/bag bridge`, `semijoin`, `join projection`, `support`, `DISTINCT`, `duplicates`

```rocq
Theorem partial_semijoin_projection_support_rel :
  forall (LeftView RightView : Type)
      (R : LeftView -> RightView -> Prop)
      (join : Row -> Row -> Row) (accept : Row -> Row -> bool)
      (emit : Row -> LeftView) (project : Row -> RightView)
      left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      R (emit left_row) (project (join left_row right_row))) ->
    list_support_rel R
      (map emit
        (filter (fun left_row => existsb (accept left_row) right) left))
      (map project (partial_semijoin_rows join accept left right)).
```

## `query_expr_set_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1096`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1096)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_set_global_typed_congr :
  forall operation first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Set operation first second) (QExpr_Set operation first' second').
```

## `query_expr_natural_join_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1139`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1139)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_natural_join_global_typed_congr :
  forall first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_NaturalJoin first second) (QExpr_NaturalJoin first' second').
```

## `query_expr_cross_join_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1169`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1169)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_global_typed_congr :
  forall first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_CrossJoin first second) (QExpr_CrossJoin first' second').
```

## `query_expr_join_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1199`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1199)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_join_global_typed_congr :
  forall kind predicate matched_select left_select right_select
         left left' right right',
    query_expr_global_typed_outcome_equiv left left' ->
    query_expr_global_typed_outcome_equiv right right' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Join kind predicate matched_select left_select right_select
        left right)
      (QExpr_Join kind predicate matched_select left_select right_select
        left' right').
```

## `query_expr_project_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1242`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1242)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_project_global_typed_congr :
  forall select_list first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Project select_list first) (QExpr_Project select_list second).
```

## `query_expr_row_map_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1261`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1261)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_row_map_global_typed_congr :
  forall output_attributes row_map first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_RowMap output_attributes row_map first)
      (QExpr_RowMap output_attributes row_map second).
```

## `query_expr_filter_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1277`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1277)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate. Use `query_expr_context_possible_outcome_equiv` for the public result.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`, `schema`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_global_typed_congr :
  forall expression input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter expression input) (QExpr_Filter expression input').
```

## `eval_filter_rows_expression_global_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1525`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1525)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_expression_global_congr_forward :
  forall left right,
    scalar_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left rows outcome ->
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right rows outcome.
```

## `eval_filter_rows_expression_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1546`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1546)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_expression_global_congr :
  forall left right,
    scalar_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left rows outcome <->
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right rows outcome.
```

## `eval_join_row_conditions_expression_global_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1603`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1603)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_row_conditions_expression_global_congr_forward :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_row right_rows outcome,
      eval_join_row_conditions env first left_row right_rows outcome ->
      eval_join_row_conditions env second left_row right_rows outcome.
```

## `eval_join_row_conditions_expression_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1620`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1620)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_row_conditions_expression_global_congr :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_row right_rows outcome,
      eval_join_row_conditions env first left_row right_rows outcome <->
      eval_join_row_conditions env second left_row right_rows outcome.
```

## `eval_join_conditions_expression_global_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1634`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1634)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_conditions_expression_global_congr_forward :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome ->
      eval_join_conditions env second left_rows right_rows outcome.
```

## `eval_join_conditions_expression_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1653`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1653)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_conditions_expression_global_congr :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome <->
      eval_join_conditions env second left_rows right_rows outcome.
```

## `eval_join_bag_scalar_global_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1756`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1756)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_join_bag_scalar_global_congr_forward :
  forall left_predicate right_predicate
      left_matched right_matched left_left right_left left_right right_right,
    scalar_expr_global_outcome_equiv left_predicate right_predicate ->
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env kind left_bag right_bag outcome,
      eval_join_bag env kind left_predicate
        left_matched left_left left_right left_bag right_bag outcome ->
      eval_join_bag env kind right_predicate
        right_matched right_left right_right left_bag right_bag outcome.
```

## `eval_join_bag_scalar_global_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1792`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1792)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_join_bag_scalar_global_congr :
  forall left_predicate right_predicate
      left_matched right_matched left_left right_left left_right right_right,
    scalar_expr_global_outcome_equiv left_predicate right_predicate ->
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env kind left_bag right_bag outcome,
      eval_join_bag env kind left_predicate
        left_matched left_left left_right left_bag right_bag outcome <->
      eval_join_bag env kind right_predicate
        right_matched right_left right_right left_bag right_bag outcome.
```

## `query_binary_bag_outcome_operation`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3870`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3870)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query binary bag outcome operation law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_binary_bag_outcome_operation : Type :=
  constructor_bagT -> constructor_bagT ->
  sql_outcome constructor_bagT -> Prop.
```

## `query_success_only_binary_bag_operation`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3876`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3876)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_success_only_binary_bag_operation
    (operation : binary_bag_relation T) :
    query_binary_bag_outcome_operation :=
  fun left_bag right_bag outcome =>
    match outcome with
    | SqlSuccess output_bag => operation left_bag right_bag output_bag
    | SqlError _ => False
    end.
```

## `query_eager_left_binary_outcome_relation`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3885`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3885)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query eager left binary outcome relation law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Definition query_eager_left_binary_outcome_relation
    (operation : query_binary_bag_outcome_operation) :
    binary_bag_outcome_relation T :=
  fun left_outcome right_outcome output =>
    match left_outcome with
    | SqlError error => output = SqlError error
    | SqlSuccess left_bag =>
        match right_outcome with
        | SqlError error => output = SqlError error
        | SqlSuccess right_bag => operation left_bag right_bag output
        end
    end.
```

## `query_binary_bag_outcome_operation_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3899`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3899)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query binary bag outcome operation extensional law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_binary_bag_outcome_operation_extensional
    (operation : query_binary_bag_outcome_operation) : Prop :=
  forall left_bag left_bag' right_bag right_bag' output output',
    bag_eq T left_bag left_bag' ->
    bag_eq T right_bag right_bag' ->
    outcome_equiv (@bag_eq T) output output' ->
    (operation left_bag right_bag output <->
     operation left_bag' right_bag' output').
```

## `query_binary_bag_outcome_operations_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3911`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3911)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query binary bag outcome operations compatible law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_binary_bag_outcome_operations_compatible
    (left_operation right_operation :
      query_binary_bag_outcome_operation) : Prop :=
  forall left_bag left_bag' right_bag right_bag',
    bag_eq T left_bag left_bag' ->
    bag_eq T right_bag right_bag' ->
    outcome_relation_equiv (@bag_eq T)
      (left_operation left_bag right_bag)
      (right_operation left_bag' right_bag').
```

## `binary_bag_outcome_relations_cross_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3921`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3921)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the binary bag outcome relations cross compatible law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition binary_bag_outcome_relations_cross_compatible
    (left_operation right_operation : binary_bag_outcome_relation T) : Prop :=
  forall left_input left_input' right_input right_input',
    outcome_equiv (@bag_eq T) left_input left_input' ->
    outcome_equiv (@bag_eq T) right_input right_input' ->
    outcome_relation_equiv (@bag_eq T)
      (left_operation left_input right_input)
      (right_operation left_input' right_input').
```

## `query_error_singleton_outcome_relation_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3930`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3930)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_error_singleton_outcome_relation_equiv :
  forall error,
    outcome_relation_equiv (@bag_eq T)
      (fun outcome : sql_outcome constructor_bagT =>
        outcome = SqlError error)
      (fun outcome : sql_outcome constructor_bagT =>
        outcome = SqlError error).
```

## `query_eager_left_binary_outcome_relation_cross_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:3944`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L3944)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query eager left binary outcome relation cross compatible law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_eager_left_binary_outcome_relation_cross_compatible :
  forall left_operation right_operation,
    query_binary_bag_outcome_operations_compatible
      left_operation right_operation ->
    binary_bag_outcome_relations_cross_compatible
      (query_eager_left_binary_outcome_relation left_operation)
      (query_eager_left_binary_outcome_relation right_operation).
```

## `query_scheduled_binary_parent_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4060`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4060)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Builds the generic eager-left scheduled parent characterization from exact success/error inversion laws and an extensional local operation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: Supply exact two-sided success and error inversion laws, an extensional operator-local outcome relation, and an inhabited right-child scheduled relation for eager-left errors.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_scheduled_binary_parent_bag_outcomes_characterization :
  forall schedule env parent left right operation,
    (forall output,
      eval_scheduled_query schedule env parent (SqlSuccess output) <->
      exists left_rows, exists right_rows, exists output_bag,
        eval_scheduled_query schedule env left (SqlSuccess left_rows) /\
        eval_scheduled_query schedule env right (SqlSuccess right_rows) /\
        operation (rows_bag T left_rows) (rows_bag T right_rows)
          (SqlSuccess output_bag) /\
        query_same_rows_as_bag output output_bag) ->
    (forall error,
      eval_scheduled_query schedule env parent (SqlError error) <->
      eval_scheduled_query schedule env left (SqlError error) \/
      exists left_rows,
        eval_scheduled_query schedule env left (SqlSuccess left_rows) /\
        (eval_scheduled_query schedule env right (SqlError error) \/
         exists right_rows,
           eval_scheduled_query schedule env right (SqlSuccess right_rows) /\
           operation (rows_bag T left_rows) (rows_bag T right_rows)
             (SqlError error))) ->
    query_binary_bag_outcome_operation_extensional operation ->
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env parent)
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation operation)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
```

## `query_success_only_binary_bag_operation_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4245`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4245)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_success_only_binary_bag_operation_extensional :
  forall relation,
    binary_bag_relation_extensional relation ->
    query_binary_bag_outcome_operation_extensional
      (@query_success_only_binary_bag_operation T relation).
```

## `query_success_only_binary_bag_operations_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4258`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4258)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma query_success_only_binary_bag_operations_compatible :
  forall relation,
    binary_bag_relation_extensional relation ->
    (forall left_bag right_bag,
      exists output_bag, relation left_bag right_bag output_bag) ->
    query_binary_bag_outcome_operations_compatible
      (@query_success_only_binary_bag_operation T relation)
      (@query_success_only_binary_bag_operation T relation).
```

## `query_set_outcome_operations_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4291`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4291)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query set outcome operations compatible law for SQL bag/set operations, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_set_outcome_operations_compatible :
  forall operation left left' right right',
    query_expr_sort left =S= query_expr_sort left' ->
    query_expr_sort right =S= query_expr_sort right' ->
    query_binary_bag_outcome_operations_compatible
      (query_set_outcome_operation operation left right)
      (query_set_outcome_operation operation left' right').
```

## `query_natural_join_outcome_operations_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4341`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4341)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query natural join outcome operations compatible law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_natural_join_outcome_operations_compatible :
  query_binary_bag_outcome_operations_compatible
    query_natural_join_outcome_operation
    query_natural_join_outcome_operation.
```

## `query_cross_join_outcome_operations_compatible`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4354`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4354)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query cross join outcome operations compatible law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_cross_join_outcome_operations_compatible :
  query_binary_bag_outcome_operations_compatible
    query_cross_join_outcome_operation
    query_cross_join_outcome_operation.
```

## `query_join_outcome_operation_extensional`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4369`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4369)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: States the query join outcome operation extensional law for join semantics, in the exact direction displayed by the declaration.

Applicability: Use at the successful-outcome/runtime-error boundary for join semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma query_join_outcome_operation_extensional :
  forall schedule env kind predicate matched_select left_select right_select,
    query_binary_bag_outcome_operation_extensional
      (query_join_outcome_operation schedule env kind predicate
        matched_select left_select right_select).
```

## `eval_adapter_query_set_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4415`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4415)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for SQL bag/set operations.

Applicability: Use in either direction to invert or construct a goal about SQL bag/set operations.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `set operation`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_adapter_query_set_error_iff :
  forall schedule env operation left right error,
    eval_adapter_query schedule env (QExpr_Set operation left right)
      (SqlError error) <->
    eval_adapter_query schedule env left (SqlError error) \/
    exists left_rows,
      eval_adapter_query schedule env left (SqlSuccess left_rows) /\
      eval_adapter_query schedule env right (SqlError error).
```

## `eval_adapter_query_natural_join_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4431`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4431)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for join semantics.

Applicability: Use in either direction to invert or construct a goal about join semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_adapter_query_natural_join_error_iff :
  forall schedule env left right error,
    eval_adapter_query schedule env (QExpr_NaturalJoin left right)
      (SqlError error) <->
    eval_adapter_query schedule env left (SqlError error) \/
    exists left_rows,
      eval_adapter_query schedule env left (SqlSuccess left_rows) /\
      eval_adapter_query schedule env right (SqlError error).
```

## `eval_adapter_query_cross_join_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4447`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4447)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for join semantics.

Applicability: Use in either direction to invert or construct a goal about join semantics.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_adapter_query_cross_join_error_iff :
  forall schedule env left right error,
    eval_adapter_query schedule env (QExpr_CrossJoin left right)
      (SqlError error) <->
    eval_adapter_query schedule env left (SqlError error) \/
    exists left_rows,
      eval_adapter_query schedule env left (SqlSuccess left_rows) /\
      eval_adapter_query schedule env right (SqlError error).
```

## `query_set_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4463`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4463)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled binary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: Retain the fixed schedule, exact eager-left success/error behavior, operator extensionality, and inhabitation of the actual right-child scheduled outcome relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_set_scheduled_bag_outcomes_characterization :
  forall schedule env operation left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env (QExpr_Set operation left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          (query_set_outcome_operation operation left right))
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
```

## `query_natural_join_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4524`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4524)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled binary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: Retain the fixed schedule, exact eager-left success/error behavior, operator extensionality, and inhabitation of the actual right-child scheduled outcome relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_natural_join_scheduled_bag_outcomes_characterization :
  forall schedule env left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env (QExpr_NaturalJoin left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          query_natural_join_outcome_operation)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
```

## `query_cross_join_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4586`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4586)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled binary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: Retain the fixed schedule, exact eager-left success/error behavior, operator extensionality, and inhabitation of the actual right-child scheduled outcome relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_cross_join_scheduled_bag_outcomes_characterization :
  forall schedule env left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env (QExpr_CrossJoin left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          query_cross_join_outcome_operation)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
```

## `query_join_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4648`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4648)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled binary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: Retain the fixed schedule, exact eager-left success/error behavior, operator extensionality, and inhabitation of the actual right-child scheduled outcome relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_join_scheduled_bag_outcomes_characterization :
  forall schedule env kind predicate matched_select left_select right_select
         left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          (query_join_outcome_operation schedule env kind predicate
            matched_select left_select right_select))
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
```

## `query_set_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4681`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4681)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports both child bag/error relations under one matched schedule pair through the complete scheduled binary constructor semantics.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: Supply complete bag/error equivalence for both children under the same matched schedule pair; neither errors nor multiplicity may be projected away. SET also retains both child sort equalities.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_set_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env operation
         left_first left_second right_first right_second,
    query_expr_sort left_first =S= query_expr_sort right_first ->
    query_expr_sort left_second =S= query_expr_sort right_second ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_Set operation left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_Set operation right_first right_second)).
```

## `query_natural_join_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4723`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4723)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports both child bag/error relations under one matched schedule pair through the complete scheduled binary constructor semantics.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: Supply complete bag/error equivalence for both children under the same matched schedule pair; neither errors nor multiplicity may be projected away.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_natural_join_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
         left_first left_second right_first right_second,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_NaturalJoin left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_NaturalJoin right_first right_second)).
```

## `query_cross_join_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4762`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4762)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports both child bag/error relations under one matched schedule pair through the complete scheduled binary constructor semantics.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: Supply complete bag/error equivalence for both children under the same matched schedule pair; neither errors nor multiplicity may be projected away.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_cross_join_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
         left_first left_second right_first right_second,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_CrossJoin left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_CrossJoin right_first right_second)).
```

## `query_join_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4801`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4801)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports both child bag/error relations under one matched schedule pair through the complete scheduled binary constructor semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: Supply complete bag/error equivalence for both children under the same matched schedule pair; neither errors nor multiplicity may be projected away. JOIN also retains cross-schedule compatibility of the exact local join outcome operations.

Cross-index: `scheduled`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_join_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env kind predicate
         matched_select left_select right_select
         left_first left_second right_first right_second,
    query_binary_bag_outcome_operations_compatible
      (query_join_outcome_operation left_schedule env kind predicate
        matched_select left_select right_select)
      (query_join_outcome_operation right_schedule env kind predicate
        matched_select left_select right_select) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          right_first right_second)).
```

## `query_expr_set_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4856`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4856)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about SQL bag/set operations.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_set_possible_bag_schedule_transport :
  forall env operation left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Set operation left_first left_second)
      (QExpr_Set operation right_first right_second).
```

## `query_expr_set_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4881`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4881)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient.

Cross-index: `possible`, `outcome`, `runtime`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_set_possible_bag_outcome_equiv :
  forall env operation left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Set operation left_first left_second)
      (QExpr_Set operation right_first right_second).
```

## `query_expr_natural_join_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4897`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4897)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_natural_join_possible_bag_schedule_transport :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_NaturalJoin left_first left_second)
      (QExpr_NaturalJoin right_first right_second).
```

## `query_expr_natural_join_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4923`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4923)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_natural_join_possible_bag_outcome_equiv :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_NaturalJoin left_first left_second)
      (QExpr_NaturalJoin right_first right_second).
```

## `query_expr_cross_join_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4939`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4939)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_cross_join_possible_bag_schedule_transport :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left_first left_second)
      (QExpr_CrossJoin right_first right_second).
```

## `query_expr_cross_join_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4960`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4960)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_cross_join_possible_bag_outcome_equiv :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left_first left_second)
      (QExpr_CrossJoin right_first right_second).
```

## `query_expr_join_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:4981`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L4981)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns a compositional possible-bag schedule transport.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient. JOIN additionally requires the displayed cross-schedule compatibility of the two actual `eval_join_bag_outcome` relations.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_join_possible_bag_schedule_transport :
  forall env kind predicate matched_select left_select right_select
         left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_first)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_second)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_second) ->
      query_binary_bag_outcome_operations_compatible
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env kind predicate
          matched_select left_select right_select)
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env kind predicate
          matched_select left_select right_select)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Join kind predicate matched_select left_select right_select
        left_first left_second)
      (QExpr_Join kind predicate matched_select left_select right_select
        right_first right_second).
```

## `query_expr_join_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5031`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5031)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts joint same-schedule transport through the named binary SQL constructor and returns possible-bag/outcome equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: Supply one joint bidirectional schedule transport relating both child pairs; independent marginal witnesses are insufficient. JOIN additionally requires the displayed cross-schedule compatibility of the two actual `eval_join_bag_outcome` relations.

Cross-index: `possible`, `outcome`, `runtime`, `join`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_join_possible_bag_outcome_equiv :
  forall env kind predicate matched_select left_select right_select
         left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_first)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_second)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_second) ->
      query_binary_bag_outcome_operations_compatible
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env kind predicate
          matched_select left_select right_select)
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env kind predicate
          matched_select left_select right_select)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Join kind predicate matched_select left_select right_select
        left_first left_second)
      (QExpr_Join kind predicate matched_select left_select right_select
        right_first right_second).
```

## `query_rows_to_bag_outcome_relation`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5109`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5109)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Names the generic relation from one actual ordered child row list to a complete successful-bag or runtime-error outcome.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_rows_to_bag_outcome_relation : Type :=
  list unary_tuple -> sql_outcome unary_bagT -> Prop.
```

## `query_actual_rows_bag_outcome_bind`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5115`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5115)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines eager unary composition over actual child row lists, passing child errors through and evaluating local work only after success.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_actual_rows_bag_outcome_bind
    (child : sql_outcome (list unary_tuple) -> Prop)
    (local : query_rows_to_bag_outcome_relation) :
    sql_outcome unary_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        exists input_rows,
          child (SqlSuccess input_rows) /\
          local input_rows (SqlSuccess output_bag)
    | SqlError error =>
        child (SqlError error) \/
        exists input_rows,
          child (SqlSuccess input_rows) /\
          local input_rows (SqlError error)
    end.
```

## `scheduled_local_rows_to_bag_contract`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5137`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5137)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Requires exact local bag/error equivalence on every reachable pair of bag-equal child lists under one matched schedule pair.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition scheduled_local_rows_to_bag_contract
    (left_child right_child : sql_outcome (list unary_tuple) -> Prop)
    (left_local right_local : query_rows_to_bag_outcome_relation) : Prop :=
  forall left_rows right_rows,
    left_child (SqlSuccess left_rows) ->
    right_child (SqlSuccess right_rows) ->
    bag_eq T (rows_bag T left_rows) (rows_bag T right_rows) ->
    outcome_relation_equiv (@bag_eq T)
      (left_local left_rows) (right_local right_rows).
```

## `outcome_alpha_success_match_left_rows`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5147`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5147)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Extracts a concrete successful-list match or exact error equivalence from an outcome-alpha possible-bag relation equivalence.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: Supply the complete outcome-alpha bag/error equivalence and the displayed concrete success or error observation; no representative is guessed.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma outcome_alpha_success_match_left_rows :
  forall (left right : sql_outcome (list unary_tuple) -> Prop) left_rows,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right) ->
    left (SqlSuccess left_rows) ->
    exists right_rows,
      right (SqlSuccess right_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
```

## `outcome_alpha_success_match_right_rows`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5170`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5170)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Extracts a concrete successful-list match or exact error equivalence from an outcome-alpha possible-bag relation equivalence.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: Supply the complete outcome-alpha bag/error equivalence and the displayed concrete success or error observation; no representative is guessed.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma outcome_alpha_success_match_right_rows :
  forall (left right : sql_outcome (list unary_tuple) -> Prop) right_rows,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right) ->
    right (SqlSuccess right_rows) ->
    exists left_rows,
      left (SqlSuccess left_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
```

## `outcome_alpha_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5192`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5192)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Extracts a concrete successful-list match or exact error equivalence from an outcome-alpha possible-bag relation equivalence.

Applicability: Use in either direction to invert or construct a goal about bag multiplicity.

Important premises: Supply the complete outcome-alpha bag/error equivalence and the displayed concrete success or error observation; no representative is guessed.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma outcome_alpha_error_iff :
  forall (left right : sql_outcome (list unary_tuple) -> Prop) error,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right) ->
    (left (SqlError error) <-> right (SqlError error)).
```

## `query_actual_rows_bag_outcome_bind_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5205`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5205)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Combines scheduled child bag/error equivalence with the exact local-row contract to transport eager unary composition.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply outcome-alpha equivalence for the two exact child relations and the reachable, bag-equal actual-row local contract; successful bags and runtime-error categories remain explicit.

Cross-index: `scheduled`, `outcome`, `runtime`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_actual_rows_bag_outcome_bind_congr :
  forall left_child right_child left_local right_local,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left_child) (@outcome_alpha T right_child) ->
    scheduled_local_rows_to_bag_contract
      left_child right_child left_local right_local ->
    outcome_relation_equiv (@bag_eq T)
      (query_actual_rows_bag_outcome_bind left_child left_local)
      (query_actual_rows_bag_outcome_bind right_child right_local).
```

## `query_project_rows_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5317`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5317)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines the constructor-local successful-bag and runtime-error relation on one actual ordered child row list.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_project_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (select_list : @query_select_list T relname)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  @outcome_alpha T
    (@eval_project_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env select_list rows).
```

## `query_row_map_rows_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5326`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5326)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines the constructor-local successful-bag and runtime-error relation on one actual ordered child row list.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_row_map_rows_bag_outcomes
    (row_map : unary_sem_tuple -> sql_outcome unary_sem_tuple)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  @outcome_alpha T
    (fun outcome => @row_map_rows_outcome T row_map rows = outcome).
```

## `query_filter_rows_bag_outcomes`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5332`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5332)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Defines the constructor-local successful-bag and runtime-error relation on one actual ordered child row list.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Definition query_filter_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T)
    (predicate : scalar_expr T relname ScalarResultBoolean)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  @outcome_alpha T
    (@eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env predicate rows).
```

## `eval_unary_project_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5407`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5407)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_unary_project_error_iff :
  forall schedule env select_list input error,
    eval_unary_sem_query schedule env (QExpr_Project select_list input)
      (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env select_list input_rows (SqlError error).
```

## `eval_unary_row_map_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5425`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5425)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_unary_row_map_error_iff :
  forall schedule env outputs row_map input error,
    eval_unary_sem_query schedule env
      (QExpr_RowMap outputs row_map input) (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @row_map_rows_outcome T row_map input_rows = SqlError error.
```

## `eval_unary_filter_error_iff`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5441`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5441)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: do not erase or identify runtime errors with NULL/empty success.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma eval_unary_filter_error_iff :
  forall schedule env predicate input error,
    eval_unary_sem_query schedule env (QExpr_Filter predicate input)
      (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env predicate input_rows (SqlError error).
```

## `query_project_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5487`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5487)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled unary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: No semantic premise is hidden: this is the exact fixed-schedule characterization of the displayed constructor-local relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_scheduled_bag_outcomes_characterization :
  forall schedule env select_list input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Project select_list input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_unary_sem_query schedule env input)
        (query_project_rows_bag_outcomes schedule env select_list)).
```

## `query_row_map_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5514`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5514)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled unary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: No semantic premise is hidden: this is the exact fixed-schedule characterization of the displayed constructor-local relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_row_map_scheduled_bag_outcomes_characterization :
  forall schedule env outputs row_map input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_RowMap outputs row_map input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_unary_sem_query schedule env input)
        (query_row_map_rows_bag_outcomes row_map)).
```

## `query_filter_scheduled_bag_outcomes_characterization`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5541`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5541)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Characterizes one exact scheduled unary parent bag/error relation through its actual child observations and constructor-local relation.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: No semantic premise is hidden: this is the exact fixed-schedule characterization of the displayed constructor-local relation.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_filter_scheduled_bag_outcomes_characterization :
  forall schedule env predicate input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter predicate input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_unary_sem_query schedule env input)
        (query_filter_rows_bag_outcomes schedule env predicate)).
```

## `query_project_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5768`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5768)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports one child bag/error relation under a matched schedule pair using the exact reachable-list local contract.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply complete child bag/error equivalence under the matched schedule pair and the exact reachable-list `scheduled_local_rows_to_bag_contract`.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_project_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env left_select right_select left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_project_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_select)
      (@query_project_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_select) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_Project left_select left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_Project right_select right)).
```

## `query_row_map_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5802`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5802)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports one child bag/error relation under a matched schedule pair using the exact reachable-list local contract.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply complete child bag/error equivalence under the matched schedule pair and the exact reachable-list `scheduled_local_rows_to_bag_contract`.

Cross-index: `scheduled`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_row_map_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_outputs right_outputs left_map right_map left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_row_map_rows_bag_outcomes T left_map)
      (@query_row_map_rows_bag_outcomes T right_map) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_RowMap left_outputs left_map left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_RowMap right_outputs right_map right)).
```

## `query_filter_scheduled_bag_outcomes_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:5833`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L5833)

Interface layer: Scheduled foundation only: this pointwise theorem is not a final SQL rewrite certificate.

Purpose/direction: Transports one child bag/error relation under a matched schedule pair using the exact reachable-list local contract.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply complete child bag/error equivalence under the matched schedule pair and the exact reachable-list `scheduled_local_rows_to_bag_contract`.

Cross-index: `scheduled`, `outcome`, `runtime`, `filter`, `bag`

Search aliases: `fixed Boolean schedule`, `foundation`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Theorem query_filter_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_predicate right_predicate left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_filter_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_predicate)
      (@query_filter_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_predicate) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_Filter left_predicate left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_Filter right_predicate right)).
```

## `query_expr_project_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6009`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6009)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_project_possible_bag_schedule_transport :
  forall env left_select right_select left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_select)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_select)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_select left) (QExpr_Project right_select right).
```

## `query_expr_project_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6049`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6049)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_project_possible_bag_outcome_equiv :
  forall env left_select right_select left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_select)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_select)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_select left) (QExpr_Project right_select right).
```

## `query_expr_row_map_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6084`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6084)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_row_map_possible_bag_schedule_transport :
  forall env left_outputs right_outputs left_map right_map left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    left_outputs = right_outputs ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_row_map_rows_bag_outcomes T left_map)
        (@query_row_map_rows_bag_outcomes T right_map)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_RowMap left_outputs left_map left)
      (QExpr_RowMap right_outputs right_map right).
```

## `query_expr_row_map_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6120`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6120)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `projection`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_row_map_possible_bag_outcome_equiv :
  forall env left_outputs right_outputs left_map right_map left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    left_outputs = right_outputs ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_row_map_rows_bag_outcomes T left_map)
        (@query_row_map_rows_bag_outcomes T right_map)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_RowMap left_outputs left_map left)
      (QExpr_RowMap right_outputs right_map right).
```

## `query_expr_filter_possible_bag_schedule_transport`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6151`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6151)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns a compositional possible-bag schedule transport.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_filter_possible_bag_schedule_transport :
  forall env left_predicate right_predicate left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_predicate)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_predicate)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_predicate left) (QExpr_Filter right_predicate right).
```

## `query_expr_filter_possible_bag_outcome_equiv`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:6189`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L6189)

Interface layer: Public possible-outcome SQL interface: its statement uses the complete possible success/error relation, or a property or transport of that relation, over legal Boolean schedules.

Purpose/direction: Lifts matched child schedule transport through the named unary SQL constructor's exact local row relation and returns possible-bag/outcome equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: Supply bidirectional child schedule transport, exact constructor output equality where displayed, and `scheduled_local_rows_to_bag_contract` for every matched schedule pair. The local contract retains actual row order, multiplicity, Bool3/aggregate behavior, and runtime errors.

Cross-index: `possible`, `outcome`, `runtime`, `filter`, `bag`

Search aliases: `possible outcome`, `all Boolean schedules`, `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Corollary query_expr_filter_possible_bag_outcome_equiv :
  forall env left_predicate right_predicate left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_predicate)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_predicate)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_predicate left) (QExpr_Filter right_predicate right).
```
