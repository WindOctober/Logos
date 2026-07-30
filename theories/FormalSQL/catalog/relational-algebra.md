# Bags, occurrences, projection, and relational algebra

Route here for: bag/list abstraction, multiplicity, filter/project/join/set operators.

This focused catalog contains 265 declarations routed at declaration granularity from `FilterFkEliminationFacts.v`, `GroupedFilterOutcomeFacts.v`, `NumericRegroupFacts.v`, `OrderedQueryFacts.v`, `OuterJoinFilterFacts.v`, `ProofAgentFacade.v`, `RelationalAlgebraFacts.v`, `SemijoinCompositionFacts.v`, `SqlQueryContexts.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `join_matched_rows_filter_inputs_exact`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:45`](../FilterFkEliminationFacts.v#L45)

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

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:245`](../FilterFkEliminationFacts.v#L245)

Purpose/direction: Characterizes successful filter bags by one stable total acceptance callback only after exact per-row formula success and no-error are supplied.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`, `stable total acceptance`, `success bag`, `non volatility`

```rocq
Theorem query_filter_success_bags_of_stable_total_acceptance :
  forall env formula input keep,
    stable_total_filter_acceptance env formula keep ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null env
        (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          query_success_bags basesort instance unknown symbol_runtime_error
            aggregate_runtime_error value_is_null env input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
```

## `query_filter_error_iff_of_stable_total_acceptance`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:266`](../FilterFkEliminationFacts.v#L266)

Purpose/direction: Characterizes filter errors under the same stable total acceptance contract, retaining child errors and exact reached formula error categories.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `stable total acceptance`, `runtime error`, `reachability`

```rocq
Theorem query_filter_error_iff_of_stable_total_acceptance :
  forall env formula input keep,
    stable_total_filter_acceptance env formula keep ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
```

## `eval_filter_rows_uniform_error_of_reached_member`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:312`](../FilterFkEliminationFacts.v#L312)

Purpose/direction: Constructs the sequential FILTER error from one reached bad occurrence when every reached row succeeds or exposes that same category.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `reached occurrence`, `exact error category`, `evaluation order`

```rocq
Theorem eval_filter_rows_uniform_error_of_reached_member :
  forall env formula rows bad error,
    In bad rows ->
    eval_formula (env_t T env bad) formula (SqlError error) ->
    (forall row,
      In row rows ->
      (exists truth,
        eval_formula (env_t T env row) formula (SqlSuccess truth)) \/
      eval_formula (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula rows (SqlError error).
```

## `eval_filter_rows_error_category_of_reached_categories`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:372`](../FilterFkEliminationFacts.v#L372)

Purpose/direction: Shows that any FILTER error has the fixed category shared by every reached formula-error observation.

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
        eval_formula (env_t T env row) formula (SqlError observed) ->
        observed = expected) ->
    eval_filter_rows env formula rows (SqlError error) ->
    error = expected.
```

## `eval_filter_rows_success_excludes_reached_exact_error`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:391`](../FilterFkEliminationFacts.v#L391)

Purpose/direction: Excludes every successful FILTER traversal when one reached occurrence has no successful formula observation.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `success exclusion`, `reached error`, `evaluation order`

```rocq
Theorem eval_filter_rows_success_excludes_reached_exact_error :
  forall env formula rows bad,
    In bad rows ->
    (forall truth,
      ~ eval_formula (env_t T env bad) formula (SqlSuccess truth)) ->
    forall output,
      ~ eval_filter_rows env formula rows (SqlSuccess output).
```

## `eval_filter_rows_reached_uniform_error_exact`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:420`](../FilterFkEliminationFacts.v#L420)

Purpose/direction: Packages FILTER error existence, success exclusion, and uniqueness of the exact runtime category from explicit reached-row premises.

Applicability: Use at the successful-outcome/runtime-error boundary for relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success.

Cross-index: `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `runtime outcome`, `runtime safety`, `error propagation`, `exact error only`, `reached occurrence`

```rocq
Theorem eval_filter_rows_reached_uniform_error_exact :
  forall env formula rows bad expected,
    In bad rows ->
    eval_formula (env_t T env bad) formula (SqlError expected) ->
    (forall row,
      In row rows ->
      (exists truth,
        eval_formula (env_t T env row) formula (SqlSuccess truth)) \/
      eval_formula (env_t T env row) formula (SqlError expected)) ->
    (forall truth,
      ~ eval_formula (env_t T env bad) formula (SqlSuccess truth)) ->
    (forall row,
      In row rows ->
      forall observed,
        eval_formula (env_t T env row) formula (SqlError observed) ->
        observed = expected) ->
    eval_filter_rows env formula rows (SqlError expected) /\
    (forall output,
      ~ eval_filter_rows env formula rows (SqlSuccess output)) /\
    (forall observed,
      eval_filter_rows env formula rows (SqlError observed) ->
      observed = expected).
```

## `eval_filter_rows_uniform_error_of_join_witness`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:459`](../FilterFkEliminationFacts.v#L459)

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
    eval_formula (env_t T env (join left_row right_row)) formula
      (SqlError error) ->
    (forall row,
      In row (join_matched_rows join accept left right) ->
      (exists truth,
        eval_formula (env_t T env row) formula (SqlSuccess truth)) \/
      eval_formula (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula
      (join_matched_rows join accept left right) (SqlError error).
```

## `eval_filter_rows_uniform_error_of_self_match`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:485`](../FilterFkEliminationFacts.v#L485)

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
    eval_formula (env_t T env (join bad bad)) formula (SqlError error) ->
    (forall row,
      In row (join_matched_rows join accept rows rows) ->
      (exists truth,
        eval_formula (env_t T env row) formula (SqlSuccess truth)) \/
      eval_formula (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula
      (join_matched_rows join accept rows rows) (SqlError error).
```

## `nonnull_foreign_key_direct_accept_has_middle`

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:514`](../FilterFkEliminationFacts.v#L514)

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

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:562`](../FilterFkEliminationFacts.v#L562)

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

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:609`](../FilterFkEliminationFacts.v#L609)

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

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:636`](../FilterFkEliminationFacts.v#L636)

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

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:663`](../FilterFkEliminationFacts.v#L663)

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

Source: [`theories/FormalSQL/FilterFkEliminationFacts.v:734`](../FilterFkEliminationFacts.v#L734)

Purpose/direction: Lifts two error-only query relations exposing the same unique category to exact outcome equivalence after successful outcomes are excluded.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`

Search aliases: `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`, `exact error only`, `error category`, `success exclusion`

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
      env first second.
```

## `formula_pred_acceptance_exact_safe`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:564`](../GroupedFilterOutcomeFacts.v#L564)

Purpose/direction: Builds an exact SQL TRUE-acceptance contract for an interpreted scalar predicate from explicit argument runtime safety.

Applicability: Use for `FExpr_Pred` only after proving its authoritative `first_runtime_error` classifier is `None`; the decision is `Bool.is_true`, not an equality between SQL FALSE and UNKNOWN.

Important premises: The displayed `first_runtime_error ... arguments = None` premise is mandatory; retain the authoritative predicate interpreter and use `Bool.is_true` only for filter acceptance.

Cross-index: `runtime`, `filter`, `scalar`

Search aliases: `relational algebra`, `filter`, `WHERE`, `predicate`, `Bool3`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma formula_pred_acceptance_exact_safe :
  forall env predicate arguments,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    formula_acceptance_exact_at env (FExpr_Pred predicate arguments)
      (Bool.is_true (B T)
        (interp_predicate T predicate
          (map (@interp_aggterm T env) arguments))).
```

## `eval_filter_rows_acceptance_exact`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:809`](../GroupedFilterOutcomeFacts.v#L809)

Purpose/direction: Characterizes row-filter outcomes exactly as successful `List.filter` under per-row exact-acceptance/no-error contracts.

Applicability: Use after proving `formula_acceptance_exact_at` for every input occurrence; the result preserves list order and duplicates and the premise excludes formula errors.

Important premises: Supply the displayed per-row `formula_acceptance_exact_at` contract, including its successful observation and no-error components; do not replace `List.filter` by a set abstraction.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Theorem eval_filter_rows_acceptance_exact :
  forall env formula rows keep,
    (forall row,
      In row rows ->
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    forall outcome,
      eval_filter_rows env formula rows outcome <->
      outcome = SqlSuccess (List.filter keep rows).
```

## `filter_formula_observation_equiv_at_sym`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:923`](../GroupedFilterOutcomeFacts.v#L923)

Purpose/direction: Reverses a proved relational algebra relation.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `equivalence`, `congruence`

```rocq
Lemma filter_formula_observation_equiv_at_sym :
  forall left_env left_formula right_env right_formula,
    filter_formula_observation_equiv_at
      left_env left_formula right_env right_formula ->
    filter_formula_observation_equiv_at
      right_env right_formula left_env left_formula.
```

## `eval_filter_rows_ordered_outcome_congr_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:961`](../GroupedFilterOutcomeFacts.v#L961)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_ordered_outcome_congr_forward :
  forall left_env left_formula left_rows left_outcome,
    eval_filter_rows left_env left_formula left_rows left_outcome ->
    forall right_env right_formula right_rows,
      ordered_rows_equiv T left_rows right_rows ->
      (forall left_row right_row,
        Oeset.compare (OTuple T) left_row right_row = Eq ->
        filter_formula_observation_equiv_at
          (env_t T left_env left_row) left_formula
          (env_t T right_env right_row) right_formula) ->
      exists right_outcome,
        eval_filter_rows right_env right_formula right_rows right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
```

## `eval_filter_rows_ordered_outcome_congr`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1048`](../GroupedFilterOutcomeFacts.v#L1048)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem eval_filter_rows_ordered_outcome_congr :
  forall left_env left_formula left_rows
      right_env right_formula right_rows,
    ordered_rows_equiv T left_rows right_rows ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    (exists left_outcome,
      eval_filter_rows left_env left_formula left_rows left_outcome) ->
    outcome_relation_equiv (ordered_rows_equiv T)
      (eval_filter_rows left_env left_formula left_rows)
      (eval_filter_rows right_env right_formula right_rows).
```

## `query_expr_filter_outcome_congr_extensional_forward`

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1121`](../GroupedFilterOutcomeFacts.v#L1121)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_outcome_congr_extensional_forward :
  forall env left_formula right_formula left_input right_input,
    @query_expr_outcome_observation_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
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

Source: [`theories/FormalSQL/GroupedFilterOutcomeFacts.v:1192`](../GroupedFilterOutcomeFacts.v#L1192)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Theorem query_expr_filter_outcome_congr_extensional :
  forall env left_formula right_formula left_input right_input,
    query_outcome_equiv env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1157`](../NumericRegroupFacts.v#L1157)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1164`](../NumericRegroupFacts.v#L1164)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1183`](../NumericRegroupFacts.v#L1183)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1201`](../NumericRegroupFacts.v#L1201)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1226`](../NumericRegroupFacts.v#L1226)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1249`](../NumericRegroupFacts.v#L1249)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1281`](../NumericRegroupFacts.v#L1281)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1300`](../NumericRegroupFacts.v#L1300)

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

Source: [`theories/FormalSQL/NumericRegroupFacts.v:1323`](../NumericRegroupFacts.v#L1323)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:580`](../OrderedQueryFacts.v#L580)

Purpose/direction: Establishes concrete-row permutation closure for successful observations at any constructor classified as a bag reset.

Applicability: Use when `query_expr_order_behavior query = BagReset` computes or is proved directly.  The conclusion concerns successful row lists only; prove SQL errors separately.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_bag_reset_success_permutation_closed :
  forall env query,
    query_expr_order_behavior query = BagReset ->
    ConcretePermutationClosed T
      (fun rows => eval_query env query (SqlSuccess rows)).
```

## `query_project_preserves_success_permutation_closed`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:591`](../OrderedQueryFacts.v#L591)

Purpose/direction: Transports concrete-row permutation closure of successful observations through pointwise projection.

Applicability: Use with `ConcretePermutationClosed` for the child, not merely `BagClosed`.  It reorders the same concrete row representatives and makes no claim about error outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:604`](../OrderedQueryFacts.v#L604)

Purpose/direction: Transports concrete-row permutation closure of successful observations through pointwise row mapping.

Applicability: Use with `ConcretePermutationClosed` for the child, not merely `BagClosed`.  It reorders the same concrete row representatives and makes no claim about error outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:618`](../OrderedQueryFacts.v#L618)

Purpose/direction: Transports concrete-row permutation closure of successful observations through pointwise filtering.

Applicability: Use with `ConcretePermutationClosed` for the child, not merely `BagClosed`.  It reorders the same concrete row representatives and makes no claim about error outcomes.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:633`](../OrderedQueryFacts.v#L633)

Purpose/direction: Turns the syntax-directed reset/Project/Filter/RowMap certificate into observation-level BagClosed for successful rows.

Applicability: Try first on a Project/Filter/RowMap stack above a bag reset; the Boolean premise usually closes by reflexivity.  It intentionally does not cross OrderBy, Offset, or Fetch, and errors remain separate.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Corollary query_structural_successes_bag_closed :
  forall env query,
    query_expr_permutation_closure_certified query = true ->
    BagClosed T
      (fun rows => eval_query env query (SqlSuccess rows)).
```

## `query_expr_cross_join_has_success`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:724`](../OrderedQueryFacts.v#L724)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:744`](../OrderedQueryFacts.v#L744)

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
        env predicate left_row right_row (accepted left_row right_row)) ->
    (forall source,
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    query_has_success env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right).
```

## `eval_query_expr_project_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1365`](../OrderedQueryFacts.v#L1365)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `projection`

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

## `eval_query_expr_project_success_length`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1385`](../OrderedQueryFacts.v#L1385)

Purpose/direction: Relates relational algebra to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `cardinality`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma eval_query_expr_project_success_length :
  forall env select_list input output,
    eval_query env (QExpr_Project select_list input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows.
```

## `eval_query_expr_table_success_cardinal`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1403`](../OrderedQueryFacts.v#L1403)

Purpose/direction: Relates bag multiplicity to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`, `cardinality`

Search aliases: `relational algebra`, `cardinality`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma eval_query_expr_table_success_cardinal :
  forall env outputs table rows,
    @query_outputs_sort T outputs =S= basesort table ->
    eval_query env (QExpr_Table outputs table) (SqlSuccess rows) ->
    Febag.cardinal (Fecol.CBag (CTuple T)) (instance table) =
      N.of_nat (length rows).
```

## `eval_query_expr_filter_success_iff`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1436`](../OrderedQueryFacts.v#L1436)

Purpose/direction: Gives necessary and sufficient conditions for relational algebra.

Applicability: Use in either direction to invert or construct a goal about relational algebra.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_query_expr_filter_success_iff :
  forall env formula input output,
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlSuccess output).
```

## `eval_query_expr_filter_success_Forall_accepted`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1454`](../OrderedQueryFacts.v#L1454)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `eval_query_expr_filter_success_Forall_accepted` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_query_expr_filter_success_Forall_accepted :
  forall env formula input output (property : tuple T -> Prop),
    (forall input_rows row truth,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = true ->
      property row) ->
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) ->
    Forall property output.
```

## `query_expr_project_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1477`](../OrderedQueryFacts.v#L1477)

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
    (forall row,
      input_property row ->
      output_property
        (projection T (env_t T env row) (@Select_List T select_list))) ->
    query_success_Forall env
      (QExpr_Project select_list input) output_property.
```

## `query_expr_filter_success_Forall`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1501`](../OrderedQueryFacts.v#L1501)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1517`](../OrderedQueryFacts.v#L1517)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1554`](../OrderedQueryFacts.v#L1554)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1655`](../OrderedQueryFacts.v#L1655)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_filter_success_bags_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1863`](../OrderedQueryFacts.v#L1863)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `query_expr_filter_has_success_exact` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma query_expr_filter_has_success_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    query_has_success env input ->
    query_has_success env (QExpr_Filter formula input).
```

## `query_filter_success_bags_functional_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:1936`](../OrderedQueryFacts.v#L1936)

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
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2008`](../OrderedQueryFacts.v#L2008)

Purpose/direction: Establishes the displayed closure property for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `filter`, `bag`

Search aliases: `relational algebra`, `filter`, `WHERE`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_expr_filter_bag_closed_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    BagClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_Filter formula input) (SqlSuccess rows)).
```

## `query_success_length_le_cross_join`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2584`](../OrderedQueryFacts.v#L2584)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2611`](../OrderedQueryFacts.v#L2611)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2658`](../OrderedQueryFacts.v#L2658)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2715`](../OrderedQueryFacts.v#L2715)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2735`](../OrderedQueryFacts.v#L2735)

Purpose/direction: Relates outer/semi/anti-join semantics to the exact list length or bag cardinality shown below.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:2775`](../OrderedQueryFacts.v#L2775)

Purpose/direction: Provides the stated reusable upper bound for outer/semi/anti-join semantics.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; retain every explicit join-kind branch and predicate/projection premise.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `cardinality`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3830`](../OrderedQueryFacts.v#L3830)

Purpose/direction: Characterizes successful filtering when every reached formula evaluation succeeds with SQL TRUE.

Applicability: Use only after proving every reached predicate outcome is exactly `SqlSuccess true3`; errors and UNKNOWN are not covered.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`

```rocq
Lemma eval_filter_rows_always_true_iff :
  forall env formula rows,
    (forall row,
      In row rows ->
      forall outcome,
        @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null (env_t T env row) formula outcome <->
        outcome = SqlSuccess (Bool.true (B T))) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula rows outcome <->
      outcome = SqlSuccess rows.
```

## `relational_permutation_map_inv`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:3932`](../OrderedQueryFacts.v#L3932)

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

## `projected_rows_same_as_mapped_bag`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4246`](../OrderedQueryFacts.v#L4246)

Purpose/direction: Bridges the two displayed representations of bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4278`](../OrderedQueryFacts.v#L4278)

Purpose/direction: States the mapped bag rows have projection preimage law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

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

## `query_row_map_success_bags_total`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4371`](../OrderedQueryFacts.v#L4371)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4501`](../OrderedQueryFacts.v#L4501)

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

## `query_project_success_bags_safe`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4579`](../OrderedQueryFacts.v#L4579)

Purpose/direction: Characterizes the possible successful bags of a locally safe projection as a multiplicity-preserving bag map of child bags.

Applicability: Use after proving scalar SELECT evaluation safe for every row; this is an exact possible-bag characterization, not an ordered-row result.

Important premises: Prove the displayed SELECT-list runtime-error equation for every row; respect `bag_eq` and duplicate multiplicity in both directions.

Cross-index: `runtime`, `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_success_bags_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    rel_equiv
      (success_bags env (QExpr_Project select_list input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T (query_project_bag env select_list input_bag) output).
```

## `query_project_bag_congr`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4748`](../OrderedQueryFacts.v#L4748)

Purpose/direction: Transports input bag equality through the declared projection bag map.

Applicability: Use to map an existing input `bag_eq` through one fixed projection.

Important premises: Supply the displayed input `bag_eq`; the environment and SELECT list stay fixed.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_project_bag_congr :
  forall env select_list left right,
    bag_eq T left right ->
    bag_eq T
      (query_project_bag env select_list left)
      (query_project_bag env select_list right).
```

## `query_values_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4960`](../OrderedQueryFacts.v#L4960)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_values_success_bags :
  forall env outputs values,
    rel_equiv
      (success_bags env (QExpr_Values outputs values))
      (fun output => bag_eq T values output).
```

## `query_table_success_bags`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:4978`](../OrderedQueryFacts.v#L4978)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5049`](../OrderedQueryFacts.v#L5049)

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

## `project_rows_success_exact`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5270`](../OrderedQueryFacts.v#L5270)

Purpose/direction: Inverts or constructs the successful evaluation branch for relational algebra.

Applicability: Use when the goal or a hypothesis matches the `project_rows_success_exact` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma project_rows_success_exact :
  forall env select_list rows output,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows = SqlSuccess output ->
    output =
      map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows.
```

## `query_project_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5299`](../OrderedQueryFacts.v#L5299)

Purpose/direction: Inverts or constructs the successful evaluation branch for bag multiplicity.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Theorem query_project_success_bags_functional :
  forall env select_list input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Project select_list input) first ->
      success_bags env (QExpr_Project select_list input) second ->
      bag_eq T first second.
```

## `query_set_success_bags_functional`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5371`](../OrderedQueryFacts.v#L5371)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5411`](../OrderedQueryFacts.v#L5411)

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

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5452`](../OrderedQueryFacts.v#L5452)

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

## `rows_key_aligned_filter`

Source: [`theories/FormalSQL/OrderedQueryFacts.v:5832`](../OrderedQueryFacts.v#L5832)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:48`](../ProofAgentFacade.v#L48)

Purpose/direction: Exposes the displayed equivalence law for the facade's semantic TNull row equality without reopening ordered-set internals.

Applicability: Use to compose generated row correspondences through the facade's semantic equality; this is not Leibniz tuple equality.

Important premises: No premises beyond the displayed row.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_refl :
  forall row, TNullRowEq row row.
```

## `tnull_row_eq_sym`

Source: [`theories/FormalSQL/ProofAgentFacade.v:55`](../ProofAgentFacade.v#L55)

Purpose/direction: Exposes the displayed equivalence law for the facade's semantic TNull row equality without reopening ordered-set internals.

Applicability: Use to compose generated row correspondences through the facade's semantic equality; this is not Leibniz tuple equality.

Important premises: Supply the displayed semantic TNull row equality in the forward direction.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_sym :
  forall left right,
    TNullRowEq left right ->
    TNullRowEq right left.
```

## `tnull_row_eq_trans`

Source: [`theories/FormalSQL/ProofAgentFacade.v:64`](../ProofAgentFacade.v#L64)

Purpose/direction: Exposes the displayed equivalence law for the facade's semantic TNull row equality without reopening ordered-set internals.

Applicability: Use to compose generated row correspondences through the facade's semantic equality; this is not Leibniz tuple equality.

Important premises: Supply both displayed semantic TNull row equalities through the same intermediate row; do not replace them by Leibniz equality.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `row extensionality`, `tuple equality`, `equivalence`, `congruence`

```rocq
Lemma tnull_row_eq_trans :
  forall first second third,
    TNullRowEq first second ->
    TNullRowEq second third ->
    TNullRowEq first third.
```

## `tnull_query_program_head_separation_sound`

Source: [`theories/FormalSQL/ProofAgentFacade.v:791`](../ProofAgentFacade.v#L791)

Purpose/direction: States the tnull query program head separation sound law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_program_head_separation_sound` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`

Search aliases: `relational algebra`

```rocq
Lemma tnull_query_program_head_separation_sound :
  forall db env left right left_tail right_tail,
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryProgramOutcomeEq db env
        (left :: left_tail) (right :: right_tail).
```

## `tnull_query_program_prefix_separation_sound`

Source: [`theories/FormalSQL/ProofAgentFacade.v:807`](../ProofAgentFacade.v#L807)

Purpose/direction: States the tnull query program prefix separation sound law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_query_program_prefix_separation_sound` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`

Search aliases: `relational algebra`

```rocq
Lemma tnull_query_program_prefix_separation_sound :
  forall db env left_prefix right_prefix left right left_tail right_tail,
    length left_prefix = length right_prefix ->
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryProgramOutcomeEq db env
        (left_prefix ++ left :: left_tail)
        (right_prefix ++ right :: right_tail).
```

## `tnull_select_lookup_head`

Source: [`theories/FormalSQL/ProofAgentFacade.v:915`](../ProofAgentFacade.v#L915)

Purpose/direction: States the tnull select lookup head law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_head` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_head :
  forall items expression attribute,
    TNullSelectLookup
      (SelectList (SelectAs expression attribute :: items)) attribute =
    Some expression.
```

## `tnull_select_lookup_cons_other`

Source: [`theories/FormalSQL/ProofAgentFacade.v:931`](../ProofAgentFacade.v#L931)

Purpose/direction: States the tnull select lookup cons other law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_cons_other` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_cons_other :
  forall items head_expression head_attribute attribute,
    Oset.eq_bool (OAtt TNull) attribute head_attribute = false ->
    TNullSelectLookup
      (SelectList (SelectAs head_expression head_attribute :: items))
      attribute =
    TNullSelectLookup (SelectList items) attribute.
```

## `tnull_select_lookup_retained`

Source: [`theories/FormalSQL/ProofAgentFacade.v:955`](../ProofAgentFacade.v#L955)

Purpose/direction: States the tnull select lookup retained law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_retained` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_retained :
  forall env select attribute expression row,
    TNullSelectLookup select attribute = Some expression ->
    attribute inS
      TNullRowLabels (TNullProjectRow env select row) /\
    TNullRowValue (TNullProjectRow env select row) attribute =
      Interp.interp_aggterm TNull (env_t TNull env row) expression.
```

## `tnull_select_lookup_some_iff_projected_label`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1017`](../ProofAgentFacade.v#L1017)

Purpose/direction: Relates successful first-match SELECT lookup exactly to membership of the corresponding projected output label.

Applicability: Use in either direction between first-match lookup and projected label presence; repeated aliases do not authorize choosing a later SELECT item.

Important premises: No alias-uniqueness premise is required: the statement follows the authoritative first-match SELECT lookup and exact projected-label membership test.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_some_iff_projected_label :
  forall env select attribute row,
    (exists expression,
      TNullSelectLookup select attribute = Some expression) <->
    attribute inS TNullRowLabels (TNullProjectRow env select row).
```

## `tnull_select_lookup_none_iff_projected_label_absent`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1064`](../ProofAgentFacade.v#L1064)

Purpose/direction: Relates failed first-match SELECT lookup exactly to Boolean absence of the corresponding projected output label.

Applicability: Use in either direction to prove concrete lookup failure or output label absence without unfolding projection-label construction.

Important premises: No alias-uniqueness premise is required: the statement follows the authoritative first-match SELECT lookup and exact projected-label membership test.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_none_iff_projected_label_absent :
  forall env select attribute row,
    TNullSelectLookup select attribute = None <->
    (attribute inS? TNullRowLabels (TNullProjectRow env select row)) = false.
```

## `tnull_select_columns_lookup_output`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1098`](../ProofAgentFacade.v#L1098)

Purpose/direction: Computes the exact first-match lookup of every present SelectColumns output without requiring output uniqueness.

Applicability: Use for a SelectColumns member instead of proving uniqueness or manually reducing first-match lookup over a concrete list.

Important premises: The attribute must belong to the displayed SelectColumns output set. Repeated identical columns remain valid under first-match semantics.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_select_columns_lookup_output :
  forall columns attribute,
    attribute inS
      (@Projection.select_list_sort TNull (SelectColumns columns)) ->
    TNullSelectLookup (SelectColumns columns) attribute =
      Some (AExpr (Dot attribute)).
```

## `tnull_select_lookup_direct_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1148`](../ProofAgentFacade.v#L1148)

Purpose/direction: States the tnull select lookup direct value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_direct_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_direct_value :
  forall env select source target row,
    TNullSelectLookup select target = Some (AExpr (Dot source)) ->
    source inS TNullRowLabels row ->
    TNullRowValue (TNullProjectRow env select row) target =
    TNullRowValue row source.
```

## `tnull_select_lookup_constant_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1170`](../ProofAgentFacade.v#L1170)

Purpose/direction: States the tnull select lookup constant value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_constant_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_constant_value :
  forall env select target value row,
    TNullSelectLookup select target = Some (AExpr (Constant value)) ->
    TNullRowValue (TNullProjectRow env select row) target = value.
```

## `tnull_select_lookup_direct_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1187`](../ProofAgentFacade.v#L1187)

Purpose/direction: States the tnull select lookup direct compose law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_direct_compose` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_direct_compose :
  forall env first second source middle target row,
    TNullSelectLookup first middle = Some (AExpr (Dot source)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    source inS TNullRowLabels row ->
    target inS
      TNullRowLabels
        (TNullProjectRow env second (TNullProjectRow env first row)) /\
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    TNullRowValue row source.
```

## `tnull_select_lookup_direct_compose_interp_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1224`](../ProofAgentFacade.v#L1224)

Purpose/direction: Composes two first-match direct projection lookups while retaining the original row-extended expression value, including correlated fallback.

Applicability: Use when both SELECT stages have the displayed first-match direct lookups.  No source-label presence premise is needed because the conclusion preserves the original row-extended interpretation.

Important premises: Both displayed lookup equalities are mandatory and use authoritative first-match semantics; the theorem deliberately has no source-presence premise.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_direct_compose_interp_value :
  forall env first second source middle target row,
    TNullSelectLookup first middle = Some (AExpr (Dot source)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    Interp.interp_aggterm TNull (env_t TNull env row)
      (AExpr (Dot source)).
```

## `tnull_select_lookup_constant_direct_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1249`](../ProofAgentFacade.v#L1249)

Purpose/direction: States the tnull select lookup constant direct compose law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_select_lookup_constant_direct_compose` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`

```rocq
Lemma tnull_select_lookup_constant_direct_compose :
  forall env first second value middle target row,
    TNullSelectLookup first middle = Some (AExpr (Constant value)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    target inS
      TNullRowLabels
        (TNullProjectRow env second (TNullProjectRow env first row)) /\
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    value.
```

## `tnull_direct_projection_preserves_attribute`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1280`](../ProofAgentFacade.v#L1280)

Purpose/direction: Shows that the indicated operator preserves the displayed relational algebra property.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_preserves_attribute` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `facade`, `projection`, `schema`

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

## `tnull_direct_projection_alias_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1299`](../ProofAgentFacade.v#L1299)

Purpose/direction: Reads an aliased direct SELECT output exactly as its present source attribute under unique output aliases, preserving NULL values.

Applicability: Use to reduce `dot` at a renamed projection output after proving the literal direct SELECT item, unique output aliases, and source attribute presence in the input row.

Important premises: The displayed direct `source -> target` item and output uniqueness are mandatory; source presence prevents lookup from falling through to the outer environment.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_alias_value :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (row : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels row ->
    TNullRowValue
      (TNullProjectRow env (@_Select_List TNull items) row) target =
    TNullRowValue row source.
```

## `tnull_direct_projection_alias_retained`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1333`](../ProofAgentFacade.v#L1333)

Purpose/direction: States the tnull direct projection alias retained law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_alias_retained` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_alias_retained :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (row : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels row ->
    target inS
      TNullRowLabels
        (TNullProjectRow env (@_Select_List TNull items) row) /\
    TNullRowValue
      (TNullProjectRow env (@_Select_List TNull items) row) target =
    TNullRowValue row source.
```

## `tnull_direct_projection_alias_reflects_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1365`](../ProofAgentFacade.v#L1365)

Purpose/direction: States the tnull direct projection alias reflects value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_alias_reflects_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_alias_reflects_value :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (left right : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels left ->
    source inS TNullRowLabels right ->
    TNullRowEq
      (TNullProjectRow env (@_Select_List TNull items) left)
      (TNullProjectRow env (@_Select_List TNull items) right) ->
    TNullRowValue left source = TNullRowValue right source.
```

## `tnull_projected_alias_int32_primary_key_matches_at_most_one`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1403`](../ProofAgentFacade.v#L1403)

Purpose/direction: States the tnull projected alias int32 primary key matches at most one law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projected_alias_int32_primary_key_matches_at_most_one` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `facade`, `schema`, `scalar`

Search aliases: `relational algebra`, `INTEGER`, `int32`, `integrity constraint`, `key`

```rocq
Lemma tnull_projected_alias_int32_primary_key_matches_at_most_one :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      source_name target_name (fixed : TNullValue)
      (raw_rows projected_rows : list TNullRow) (raw_bag : TNullRowBag),
    Forall
      (row_attribute_present_conforms (Attr_int32 source_name)) raw_rows ->
    primary_key_conforms [Attr_int32 source_name] raw_rows ->
    In
      (SelectAs (DotInt32 source_name) (AttrInt32 target_name))
      items ->
    select_list_has_unique_outputs (SelectList items) ->
    value_conforms_attribute (Attr_int32 source_name) fixed ->
    @query_same_rows_as_bag TNull raw_rows raw_bag ->
    @query_same_rows_as_bag TNull projected_rows
      (@query_project_bag TNull env (SelectList items) raw_bag) ->
    (List.length
      (filter
        (fun row =>
          postgres_int32_equal_true fixed
            (TNullRowValue row (Attr_int32 target_name)))
        projected_rows) <= 1)%nat.
```

## `tnull_direct_projection_row_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1586`](../ProofAgentFacade.v#L1586)

Purpose/direction: States the tnull direct projection row equality law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_row_eq` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1616`](../ProofAgentFacade.v#L1616)

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

## `tnull_double_projection_bag_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1629`](../ProofAgentFacade.v#L1629)

Purpose/direction: States the tnull double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `projection`, `bag`

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

## `tnull_map_theta_join_total_functional`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1671`](../ProofAgentFacade.v#L1671)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1694`](../ProofAgentFacade.v#L1694)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1724`](../ProofAgentFacade.v#L1724)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1781`](../ProofAgentFacade.v#L1781)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1847`](../ProofAgentFacade.v#L1847)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1873`](../ProofAgentFacade.v#L1873)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1907`](../ProofAgentFacade.v#L1907)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:1932`](../ProofAgentFacade.v#L1932)

Purpose/direction: States the tnull row equality of labels and values law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_row_eq_of_labels_and_values` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

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

## `tnull_project_row_eq_congr`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1950`](../ProofAgentFacade.v#L1950)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `equivalence`, `congruence`

```rocq
Lemma tnull_project_row_eq_congr :
  forall env select left right,
    TNullRowEq left right ->
    TNullRowEq
      (TNullProjectRow env select left)
      (TNullProjectRow env select right).
```

## `tnull_projected_select_item_reflects_value`

Source: [`theories/FormalSQL/ProofAgentFacade.v:1968`](../ProofAgentFacade.v#L1968)

Purpose/direction: States the tnull projected select item reflects value law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projected_select_item_reflects_value` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`

Search aliases: `relational algebra`

```rocq
Lemma tnull_projected_select_item_reflects_value :
  forall env items expression attribute left right,
    In (@Select_As TNull expression attribute) items ->
    select_list_has_unique_outputs (SelectList items) ->
    TNullRowEq
      (TNullProjectRow env (SelectList items) left)
      (TNullProjectRow env (SelectList items) right) ->
    Interp.interp_aggterm TNull (env_t TNull env left) expression =
    Interp.interp_aggterm TNull (env_t TNull env right) expression.
```

## `tnull_project_rows_select_columns_success`

Source: [`theories/FormalSQL/ProofAgentFacade.v:2705`](../ProofAgentFacade.v#L2705)

Purpose/direction: Computes direct-column projection of a row list as an exact ordered successful map, discharging all projection-local scalar errors.

Applicability: Use only for `SelectColumns`; it proves projection-local safety and the exact ordered row map, independently of any child-query outcome.

Important premises: The SELECT list must have the displayed direct-column form; the exact ordered map conclusion does not cover arbitrary scalar expressions.

Cross-index: `facade`, `runtime`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma tnull_project_rows_select_columns_success :
  forall env columns rows,
    @project_rows_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) rows =
    SqlSuccess
      (map
        (fun row => TNullProjectRow env (SelectColumns columns) row)
        rows).
```

## `tnull_projection_envs_eq_of_select_items`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3032`](../ProofAgentFacade.v#L3032)

Purpose/direction: States the tnull projection envs equality of select items law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projection_envs_eq_of_select_items` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_projection_envs_eq_of_select_items :
  forall (left_env right_env : Env.env TNull)
      (left_items right_items : list SelectItemT),
    Forall2
      (fun left right =>
        match left, right with
        | @Projection.Select_As _ left_expression left_attribute,
          @Projection.Select_As _ right_expression right_attribute =>
            left_attribute = right_attribute /\
            Interp.interp_aggterm TNull left_env left_expression =
            Interp.interp_aggterm TNull right_env right_expression
        end)
      left_items right_items ->
    TNullRowEq
      (Projection.projection TNull left_env
        (@Projection.Select_List TNull (SelectList left_items)))
      (Projection.projection TNull right_env
        (@Projection.Select_List TNull (SelectList right_items))).
```

## `tnull_projection_rows_eq_of_select_items`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3136`](../ProofAgentFacade.v#L3136)

Purpose/direction: States the tnull projection rows equality of select items law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_projection_rows_eq_of_select_items` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_projection_rows_eq_of_select_items :
  forall env left_row right_row
      (left_items right_items : list SelectItemT),
    Forall2
      (fun left right =>
        match left, right with
        | @Projection.Select_As _ left_expression left_attribute,
          @Projection.Select_As _ right_expression right_attribute =>
            left_attribute = right_attribute /\
            Interp.interp_aggterm TNull (env_t TNull env left_row)
              left_expression =
            Interp.interp_aggterm TNull (env_t TNull env right_row)
              right_expression
        end)
      left_items right_items ->
    TNullRowEq
      (TNullProjectRow env (SelectList left_items) left_row)
      (TNullProjectRow env (SelectList right_items) right_row).
```

## `tnull_projection_rows_eq_of_output_values`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3165`](../ProofAgentFacade.v#L3165)

Purpose/direction: Builds semantic equality of two projected rows from equality of their output-label sets and every observable projected cell.

Applicability: Use after proving exact equality of the two SELECT output-label sets and equality of each cell observable through that set.

Important premises: Retain exact output-label-set equality and cell equality for every attribute in the left output set; neither premise follows from arity alone.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_projection_rows_eq_of_output_values :
  forall env left_select right_select left_row right_row,
    TNullAttributeSetEq
      (@Projection.select_list_sort TNull left_select)
      (@Projection.select_list_sort TNull right_select) ->
    (forall attribute,
      attribute inS (@Projection.select_list_sort TNull left_select) ->
      TNullRowValue (TNullProjectRow env left_select left_row) attribute =
      TNullRowValue (TNullProjectRow env right_select right_row) attribute) ->
    TNullRowEq
      (TNullProjectRow env left_select left_row)
      (TNullProjectRow env right_select right_row).
```

## `tnull_direct_projection_fusion_row_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3206`](../ProofAgentFacade.v#L3206)

Purpose/direction: Fuses one direct projection with two direct projections from exact source-to-middle-to-target first-match lookup chains.

Applicability: Applies to composition of one direct projection with a two-stage direct projection after supplying the exact first-match lookup chains.

Important premises: Retain equal final output-label sets and all three first-match lookup equations for every observable target; repeated aliases cannot select a later item.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_direct_projection_fusion_row_eq :
  forall env single outer inner,
    TNullAttributeSetEq
      (@Projection.select_list_sort TNull single)
      (@Projection.select_list_sort TNull outer) ->
    (forall target,
      target inS (@Projection.select_list_sort TNull single) ->
      exists source middle,
        TNullSelectLookup single target = Some (AExpr (Dot source)) /\
        TNullSelectLookup inner middle = Some (AExpr (Dot source)) /\
        TNullSelectLookup outer target = Some (AExpr (Dot middle))) ->
    forall row,
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row)).
```

## `tnull_select_columns_projection_fusion_row_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3245`](../ProofAgentFacade.v#L3245)

Purpose/direction: Fuses direct-column single and double projections from final-label set equality and coverage of every outer label by the inner projection.

Applicability: Applies when the compared projection composition uses SelectColumns; it reduces the row law to output-set equality and outer-to-inner coverage.

Important premises: Retain exact single/outer output-set equality and outer-to-inner set coverage; coverage prevents correlated fallback for an absent inner label.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_select_columns_projection_fusion_row_eq :
  forall env single outer inner,
    TNullAttributeSetEq
      (@Projection.select_list_sort TNull (SelectColumns single))
      (@Projection.select_list_sort TNull (SelectColumns outer)) ->
    (@Projection.select_list_sort TNull (SelectColumns outer)) subS
      (@Projection.select_list_sort TNull (SelectColumns inner)) ->
    forall row,
      TNullRowEq
        (TNullProjectRow env (SelectColumns single) row)
        (TNullProjectRow env (SelectColumns outer)
          (TNullProjectRow env (SelectColumns inner) row)).
```

## `tnull_direct_projection_row_eq_on_expected_labels`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3302`](../ProofAgentFacade.v#L3302)

Purpose/direction: States the tnull direct projection row equality on expected labels law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_direct_projection_row_eq_on_expected_labels` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `facade`, `projection`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3328`](../ProofAgentFacade.v#L3328)

Purpose/direction: States the tnull bag map ext law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `bag`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3345`](../ProofAgentFacade.v#L3345)

Purpose/direction: States the tnull bag map identity law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_bag_map_identity :
  forall bag,
    TNullBagEq (TNullBagMap (fun row => row) bag) bag.
```

## `tnull_projection_bag_map_compose`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3358`](../ProofAgentFacade.v#L3358)

Purpose/direction: States the tnull projection bag map compose law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `projection`, `bag`

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3402`](../ProofAgentFacade.v#L3402)

Purpose/direction: States the tnull single double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `facade`, `projection`, `bag`

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

## `tnull_project_fusion_success_bag_contract_of_row_eq`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3428`](../ProofAgentFacade.v#L3428)

Purpose/direction: Lifts a total single-versus-double projection row law to the named reachable-child-bag fusion contract without changing multiplicities.

Applicability: Applies when the projection-composition row law is valid for every row. A law restricted to reachable rows must instead discharge the original reachable-bag contract.

Important premises: The displayed all-row semantic equality is a stronger sufficient premise; the resulting contract still ranges only over reachable child bags.

Cross-index: `facade`, `projection`, `bag`, `scalar`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `NULL`, `UNKNOWN`, `three-valued logic`, `multiplicity`, `bag semantics`, `list/bag bridge`

```rocq
Lemma tnull_project_fusion_success_bag_contract_of_row_eq :
  forall db env single outer inner input,
    (forall row,
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row))) ->
    @project_fusion_success_bag_contract TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env single outer inner input.
```

## `tnull_same_select_projection_labels`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3455`](../ProofAgentFacade.v#L3455)

Purpose/direction: States the tnull same select projection labels law for relational algebra, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `tnull_same_select_projection_labels` direction for relational algebra; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `facade`, `projection`

Search aliases: `relational algebra`, `projection`, `SELECT list`

```rocq
Lemma tnull_same_select_projection_labels :
  forall env select left right,
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select left))
      (TNullRowLabels (TNullProjectRow env select right)).
```

## `tnull_theta_join_by_witness`

Source: [`theories/FormalSQL/ProofAgentFacade.v:3522`](../ProofAgentFacade.v#L3522)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3583`](../ProofAgentFacade.v#L3583)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3618`](../ProofAgentFacade.v#L3618)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3658`](../ProofAgentFacade.v#L3658)

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

Source: [`theories/FormalSQL/ProofAgentFacade.v:3704`](../ProofAgentFacade.v#L3704)

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

## `double_projection_bag_eq`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:991`](../RelationalAlgebraFacts.v#L991)

Purpose/direction: States the double projection bag equality law for bag multiplicity, in the exact direction displayed by the declaration.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `projection`, `bag`

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

## `oeset_nb_occ_of_NoDupA`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1088`](../RelationalAlgebraFacts.v#L1088)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1124`](../RelationalAlgebraFacts.v#L1124)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1146`](../RelationalAlgebraFacts.v#L1146)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1198`](../RelationalAlgebraFacts.v#L1198)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1231`](../RelationalAlgebraFacts.v#L1231)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1244`](../RelationalAlgebraFacts.v#L1244)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1257`](../RelationalAlgebraFacts.v#L1257)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1268`](../RelationalAlgebraFacts.v#L1268)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1280`](../RelationalAlgebraFacts.v#L1280)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1291`](../RelationalAlgebraFacts.v#L1291)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1305`](../RelationalAlgebraFacts.v#L1305)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1315`](../RelationalAlgebraFacts.v#L1315)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1328`](../RelationalAlgebraFacts.v#L1328)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1341`](../RelationalAlgebraFacts.v#L1341)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1352`](../RelationalAlgebraFacts.v#L1352)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1366`](../RelationalAlgebraFacts.v#L1366)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1376`](../RelationalAlgebraFacts.v#L1376)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1389`](../RelationalAlgebraFacts.v#L1389)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1402`](../RelationalAlgebraFacts.v#L1402)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1414`](../RelationalAlgebraFacts.v#L1414)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1426`](../RelationalAlgebraFacts.v#L1426)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1439`](../RelationalAlgebraFacts.v#L1439)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1452`](../RelationalAlgebraFacts.v#L1452)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1463`](../RelationalAlgebraFacts.v#L1463)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1475`](../RelationalAlgebraFacts.v#L1475)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1487`](../RelationalAlgebraFacts.v#L1487)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1513`](../RelationalAlgebraFacts.v#L1513)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1540`](../RelationalAlgebraFacts.v#L1540)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1558`](../RelationalAlgebraFacts.v#L1558)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1576`](../RelationalAlgebraFacts.v#L1576)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1610`](../RelationalAlgebraFacts.v#L1610)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1659`](../RelationalAlgebraFacts.v#L1659)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1668`](../RelationalAlgebraFacts.v#L1668)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1699`](../RelationalAlgebraFacts.v#L1699)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1711`](../RelationalAlgebraFacts.v#L1711)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:1969`](../RelationalAlgebraFacts.v#L1969)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2277`](../RelationalAlgebraFacts.v#L2277)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2640`](../RelationalAlgebraFacts.v#L2640)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2709`](../RelationalAlgebraFacts.v#L2709)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2771`](../RelationalAlgebraFacts.v#L2771)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2934`](../RelationalAlgebraFacts.v#L2934)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2957`](../RelationalAlgebraFacts.v#L2957)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:2999`](../RelationalAlgebraFacts.v#L2999)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3024`](../RelationalAlgebraFacts.v#L3024)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3051`](../RelationalAlgebraFacts.v#L3051)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3087`](../RelationalAlgebraFacts.v#L3087)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3139`](../RelationalAlgebraFacts.v#L3139)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3313`](../RelationalAlgebraFacts.v#L3313)

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
        env predicate left rights outcome <->
      outcome = SqlSuccess (map accepted rights).
```

## `eval_join_conditions_acceptance_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3366`](../RelationalAlgebraFacts.v#L3366)

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
        env predicate lefts rights outcome <->
      outcome =
        SqlSuccess
          (map (fun left => map (accepted left) rights) lefts).
```

## `project_join_sources_outcome_exact_map`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3435`](../RelationalAlgebraFacts.v#L3435)

Purpose/direction: Lifts exact projection of every reached matched or padded join source to one ordered successful map over the source list.

Applicability: Use after proving exact successful projection only for sources in the reached source list; matched and both NULL-padded source forms must remain covered.

Important premises: Supply exact successful projection for every source occurring in the source list; do not omit matched, left-padded, or right-padded constructors that can be reached.

Cross-index: `outcome`, `runtime`, `projection`, `join`

Search aliases: `relational algebra`, `join`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`

```rocq
Lemma project_join_sources_outcome_exact_map :
  forall env matched_select left_select right_select sources
      (emit : query_join_source T -> tuple T),
    (forall source,
      In source sources ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env
      matched_select left_select right_select sources =
    SqlSuccess (map emit sources).
```

## `eval_join_bag_safe_of_acceptance_projection_exact`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3464`](../RelationalAlgebraFacts.v#L3464)

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
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    (exists output_bag,
      @eval_join_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env kind predicate matched_select left_select right_select
        left_bag right_bag (SqlSuccess output_bag)) /\
    (forall error,
      ~ @eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          env kind predicate matched_select left_select right_select
          left_bag right_bag (SqlError error)).
```

## `eval_join_row_conditions_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3556`](../RelationalAlgebraFacts.v#L3556)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`, `cardinality`

Search aliases: `relational algebra`, `join`, `cardinality`

```rocq
Lemma eval_join_row_conditions_success_length :
  forall env predicate left rights flags,
    @eval_join_row_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate left rights (SqlSuccess flags) ->
    length flags = length rights.
```

## `eval_join_conditions_success_dimensions`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3569`](../RelationalAlgebraFacts.v#L3569)

Purpose/direction: Inverts or constructs the successful evaluation branch for join semantics.

Applicability: Use when the goal or a hypothesis matches the `eval_join_conditions_success_dimensions` direction for join semantics; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `join`

Search aliases: `relational algebra`, `join`

```rocq
Lemma eval_join_conditions_success_dimensions :
  forall env predicate lefts rights matrix,
    @eval_join_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate lefts rights (SqlSuccess matrix) ->
    length matrix = length lefts /\
    Forall (fun flags => length flags = length rights) matrix.
```

## `query_join_right_single_left_sources_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3628`](../RelationalAlgebraFacts.v#L3628)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3833`](../RelationalAlgebraFacts.v#L3833)

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3868`](../RelationalAlgebraFacts.v#L3868)

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
        env predicate left_rows right_rows (SqlSuccess matrix) ->
      Forall
        (fun flags =>
          (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
        matrix) ->
    (forall left_rows right_rows left right output,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      In left left_rows ->
      In right right_rows ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceMatched T (join_tuple T left right)) =
      SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    (forall left_rows left output,
      query_same_rows_as_bag left_rows left_bag ->
      In left left_rows ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceLeft T left) = SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env QueryJoinLeft predicate matched_select left_select right_select
      left_bag right_bag (SqlSuccess joined_bag) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        project joined_bag)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        emit left_bag).
```

## `project_join_sources_success_length`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3970`](../RelationalAlgebraFacts.v#L3970)

Purpose/direction: Relates join cardinality to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about join cardinality.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `projection`, `join`, `cardinality`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:3990`](../RelationalAlgebraFacts.v#L3990)

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

## `eval_join_bag_right_single_left_success_cardinal`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4066`](../RelationalAlgebraFacts.v#L4066)

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
      symbol_runtime_error aggregate_runtime_error value_is_null env
      QueryJoinRight predicate matched_select left_select right_select
      left_bag right_bag (SqlSuccess output_bag) ->
    Febag.cardinal (Fecol.CBag (CTuple T)) output_bag =
      Febag.cardinal (Fecol.CBag (CTuple T)) right_bag.
```

## `query_grouping_sets_actual_success_bags_congr`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4113`](../RelationalAlgebraFacts.v#L4113)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `grouping`, `bag`

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

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4139`](../RelationalAlgebraFacts.v#L4139)

Purpose/direction: Transports or composes bag multiplicity across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about bag multiplicity.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`

Search aliases: `relational algebra`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_equiv_implies_success_bags :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_expr_outcome_equiv_implies_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4156`](../RelationalAlgebraFacts.v#L4156)

Purpose/direction: Projects fixed-environment error-preserving ordered equivalence to equality of possible successful bags, including the error-only case.

Applicability: Use to forget successful row order at one environment; the theorem deliberately drops error observations, so retain a separate error proof when rebuilding parent outcome equivalence.

Important premises: Supply the exact fixed-environment child outcome equivalence; this conclusion preserves successful multiplicity but intentionally does not carry the error relation.

Cross-index: `outcome`, `runtime`, `bag`

Search aliases: `relational algebra`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_expr_outcome_equiv_implies_success_bags :
  forall env left right,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
```

## `query_set_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4169`](../RelationalAlgebraFacts.v#L4169)

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `bag`

Search aliases: `relational algebra`, `set operation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_set_success_bags_congr_of_query_expr_equiv :
  forall env operation left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_Set operation left right))
      (success_bags env (QExpr_Set operation left' right')).
```

## `query_natural_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4193`](../RelationalAlgebraFacts.v#L4193)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_natural_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_NaturalJoin left right))
      (success_bags env (QExpr_NaturalJoin left' right')).
```

## `query_cross_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4211`](../RelationalAlgebraFacts.v#L4211)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_cross_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_CrossJoin left right))
      (success_bags env (QExpr_CrossJoin left' right')).
```

## `query_join_success_bags_congr_of_query_expr_equiv`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4229`](../RelationalAlgebraFacts.v#L4229)

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma query_join_success_bags_congr_of_query_expr_equiv :
  forall env kind predicate matched_select left_select right_select
         left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
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

## `query_cross_join_union_right_success_bags`

Source: [`theories/FormalSQL/RelationalAlgebraFacts.v:4256`](../RelationalAlgebraFacts.v#L4256)

Purpose/direction: Distributes CROSS JOIN over right-hand UNION ALL at the possible-bag layer while preserving duplicate multiplicity.

Applicability: Use for right-hand UNION ALL distribution only after proving both displayed sort equalities and possible-bag functionality of the duplicated left child.

Important premises: Both set-operation sort equalities and pairwise possible-bag functionality of the duplicated left child are mandatory; UNION is multiplicity-preserving UNION ALL here.

Cross-index: `join`, `bag`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `set operation`, `UNION`, `multiplicity`, `bag semantics`, `list/bag bridge`

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

Source: [`theories/FormalSQL/SemijoinCompositionFacts.v:39`](../SemijoinCompositionFacts.v#L39)

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
        env predicate left_row right_row (accepted left_row right_row)) ->
    (forall source,
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    forall error,
      ~ eval_query env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error).
```

## `partial_semijoin_projection_support_rel`

Source: [`theories/FormalSQL/SemijoinCompositionFacts.v:98`](../SemijoinCompositionFacts.v#L98)

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

## `eval_filter_rows_formula_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:550`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L550)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_formula_congr_forward :
  forall left right,
    formula_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      eval_filter_rows env left rows outcome ->
      eval_filter_rows env right rows outcome.
```

## `eval_filter_rows_formula_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:567`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L567)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_formula_congr :
  forall left right,
    formula_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      eval_filter_rows env left rows outcome <->
      eval_filter_rows env right rows outcome.
```

## `eval_filter_rows_formula_acceptance_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:585`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L585)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_formula_acceptance_congr_forward :
  forall left right,
    formula_expr_global_filter_outcome_equiv left right ->
    forall env rows outcome,
      eval_filter_rows env left rows outcome ->
      eval_filter_rows env right rows outcome.
```

## `eval_filter_rows_formula_acceptance_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:607`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L607)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_filter_rows_formula_acceptance_congr :
  forall left right,
    formula_expr_global_filter_outcome_equiv left right ->
    forall env rows outcome,
      eval_filter_rows env left rows outcome <->
      eval_filter_rows env right rows outcome.
```

## `eval_join_row_conditions_formula_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:724`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L724)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_row_conditions_formula_congr_forward :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_row_conditions env first left_rows right_rows outcome ->
      eval_join_row_conditions env second left_rows right_rows outcome.
```

## `eval_join_row_conditions_formula_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:741`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L741)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_row_conditions_formula_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_row_conditions env first left_rows right_rows outcome <->
      eval_join_row_conditions env second left_rows right_rows outcome.
```

## `eval_join_conditions_formula_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:754`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L754)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_conditions_formula_congr_forward :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome ->
      eval_join_conditions env second left_rows right_rows outcome.
```

## `eval_join_conditions_formula_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:773`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L773)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `equivalence`, `congruence`

```rocq
Lemma eval_join_conditions_formula_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome <->
      eval_join_conditions env second left_rows right_rows outcome.
```

## `eval_join_bag_formula_congr_forward`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:786`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L786)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`, `bag`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_join_bag_formula_congr_forward :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env kind matched_select left_select right_select
           left_bag right_bag outcome,
      eval_join_bag env kind first matched_select left_select right_select
        left_bag right_bag outcome ->
      eval_join_bag env kind second matched_select left_select right_select
        left_bag right_bag outcome.
```

## `eval_join_bag_formula_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:821`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L821)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; respect the exact list-versus-bag and multiplicity boundary; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`, `bag`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `multiplicity`, `bag semantics`, `list/bag bridge`, `equivalence`, `congruence`

```rocq
Lemma eval_join_bag_formula_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env kind matched_select left_select right_select
           left_bag right_bag outcome,
      eval_join_bag env kind first matched_select left_select right_select
        left_bag right_bag outcome <->
      eval_join_bag env kind second matched_select left_select right_select
        left_bag right_bag outcome.
```

## `query_expr_set_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:839`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L839)

Purpose/direction: Transports or composes SQL bag/set operations across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about SQL bag/set operations.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `schema`

Search aliases: `relational algebra`, `set operation`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_set_global_typed_congr :
  forall operation first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Set operation first second) (QExpr_Set operation first' second').
```

## `query_expr_natural_join_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:882`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L882)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`, `schema`

Search aliases: `relational algebra`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_natural_join_global_typed_congr :
  forall first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_NaturalJoin first second) (QExpr_NaturalJoin first' second').
```

## `query_expr_cross_join_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:912`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L912)

Purpose/direction: Transports or composes join semantics across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about join semantics.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`, `schema`

Search aliases: `relational algebra`, `join`, `cross product`, `CROSS JOIN`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_cross_join_global_typed_congr :
  forall first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_CrossJoin first second) (QExpr_CrossJoin first' second').
```

## `query_expr_join_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:942`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L942)

Purpose/direction: Transports or composes outer/semi/anti-join semantics across the declared equivalence.

Applicability: Use for goals whose exact QueryJoin kind selects the stated outer/semi/anti-join semantics branch; do not transfer a branch conclusion to another join kind.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; retain every explicit join-kind branch and predicate/projection premise; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `join`, `schema`

Search aliases: `relational algebra`, `outer join`, `LEFT OUTER JOIN`, `RIGHT OUTER JOIN`, `FULL OUTER JOIN`, `semi join`, `EXISTS`, `anti join`, `NOT EXISTS`, `join`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_join_global_typed_congr :
  forall kind predicate predicate' matched_select left_select right_select
         left left' right right',
    formula_expr_global_outcome_equiv predicate predicate' ->
    query_expr_global_typed_outcome_equiv left left' ->
    query_expr_global_typed_outcome_equiv right right' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Join kind predicate matched_select left_select right_select
        left right)
      (QExpr_Join kind predicate' matched_select left_select right_select
        left' right').
```

## `query_expr_project_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:991`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L991)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`, `schema`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_project_global_typed_congr :
  forall select_list first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Project select_list first) (QExpr_Project select_list second).
```

## `query_expr_scalar_project_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1006`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1006)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`, `schema`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_scalar_project_global_typed_congr :
  forall select_list first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_ScalarProject select_list first)
      (QExpr_ScalarProject select_list second).
```

## `query_expr_row_map_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1028`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1028)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `projection`, `schema`

Search aliases: `relational algebra`, `projection`, `SELECT list`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_row_map_global_typed_congr :
  forall output_attributes row_map first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_RowMap output_attributes row_map first)
      (QExpr_RowMap output_attributes row_map second).
```

## `query_expr_filter_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1044`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1044)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`, `schema`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_global_typed_congr :
  forall formula formula' input input',
    formula_expr_global_outcome_equiv formula formula' ->
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter formula input) (QExpr_Filter formula' input').
```

## `query_expr_scalar_filter_global_typed_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1064`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1064)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`, `schema`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_scalar_filter_global_typed_congr :
  forall expression first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_ScalarFilter expression first)
      (QExpr_ScalarFilter expression second).
```

## `query_expr_filter_global_typed_acceptance_congr`

Source: [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v:1089`](../../../vendor/FormalSQL/src/data/sql/SqlQueryContexts.v#L1089)

Purpose/direction: Transports or composes relational algebra across the declared equivalence.

Applicability: Use to orient, transport, or compose a semantic relation about relational algebra.

Important premises: every explicit antecedent (`->`) in the declaration is required; do not erase or identify runtime errors with NULL/empty success; keep schema/integrity conformance premises explicit; supply the declared equivalence/properness relation.

Cross-index: `outcome`, `runtime`, `filter`, `schema`

Search aliases: `relational algebra`, `filter`, `WHERE`, `query outcome`, `error-preserving outcome`, `runtime outcome`, `runtime safety`, `error propagation`, `schema conformance`, `typing`, `equivalence`, `congruence`

```rocq
Lemma query_expr_filter_global_typed_acceptance_congr :
  forall formula formula' input input',
    formula_expr_global_filter_outcome_equiv formula formula' ->
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter formula input) (QExpr_Filter formula' input').
```
