(******************************************************************************)
(** Query outcome progress remains success-or-error throughout the public API. **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData GenericInstance
  OrderedSet Values
  SqlBagAbstraction SqlErrorSemantics SqlOrder SqlOutcome SqlQuerySemantics
  SqlQuerySyntax SqlListFacts.
From Logos.FormalSQL Require Import OrderedQueryFacts ProofAgentFacade.

Import ListNotations.
Import Tuple.

(** Keep the constructor audit syntactic and exhaustive.  Semantic coverage is
    exercised below through the corresponding progress interfaces. *)
Check QExpr_Error.
Check QExpr_Values.
Check QExpr_Table.
Check QExpr_Set.
Check QExpr_NaturalJoin.
Check QExpr_CrossJoin.
Check QExpr_Join.
Check QExpr_Project.
Check QExpr_RowMap.
Check QExpr_Filter.
Check QExpr_Group.
Check QExpr_GroupingSets.
Check QExpr_Rank.
Check QExpr_Window.
Check QExpr_Distinct.
Check QExpr_OrderBy.
Check QExpr_Offset.
Check QExpr_Fetch.

(** Every constructor has a scheduled outcome-progress interface.  FILTER's
    scalar-total premise remains error-permitting; the other newly covered
    local evaluators expose the same contract directly. *)
Check query_expr_error_has_outcome.
Check query_expr_values_has_outcome.
Check query_expr_table_has_outcome.
Check query_expr_set_has_outcome.
Check query_expr_natural_join_has_outcome.
Check query_expr_cross_join_has_outcome.
Check query_expr_join_has_outcome.
Check query_expr_project_has_outcome.
Check query_expr_row_map_has_outcome.
Check query_expr_filter_has_outcome_of_scalar_total.
Check query_expr_group_has_outcome.
Check query_expr_grouping_sets_has_outcome.
Check query_expr_rank_has_outcome.
Check query_expr_window_has_outcome.
Check query_expr_distinct_has_outcome.
Check query_expr_order_by_has_outcome.
Check query_expr_offset_has_outcome.
Check query_expr_fetch_has_outcome.

Check eval_scalar_values_has_outcome.
Check eval_project_rows_has_outcome.
Check eval_join_row_conditions_has_outcome.
Check eval_join_conditions_has_outcome.
Check eval_project_join_sources_has_outcome.
Check eval_join_bag_has_outcome.
Check eval_groups_has_outcome.
Check eval_group_bag_has_outcome.
Check eval_grouping_sets_bag_has_outcome.
Check query_rank_rows_has_outcome.
Check order_by_rows_has_observation.
Check query_window_item_value_has_outcome.
Check query_window_items_has_outcome.
Check query_window_rows_has_outcome.
Check scalar_boolean_expr_runtime_safe_at.
Check scalar_value_expr_runtime_safe_at.
Check scalar_value_list_runtime_safe_at.
Check scalar_pred_runtime_safe_of_arguments.
Check scalar_value_case_runtime_safe_of_reachable_branches.
Check eval_scalar_boolean_operands_runtime_safe.
Check scalar_boolean_expr_uniform_runtime_safe_at.
Check scalar_conj_list_uniform_runtime_safe.
Check eval_filter_rows_runtime_safe_of_reachable_predicate_safe.
Check query_expr_filter_runtime_safe_of_reachable_predicate_safe.
Check query_join_rows_runtime_safe_at.
Check query_expr_join_runtime_safe_of_reachable_local_safe.
Check query_group_rows_runtime_safe_at.
Check query_expr_group_runtime_safe_of_reachable_local_safe.
Check query_window_rows_runtime_safe_at.
Check query_expr_window_runtime_safe_of_reachable_local_safe.
Check query_rank_nat_le_succ_length.
Check query_rank_values_available_through.
Check query_rank_rows_outcome_available_of_length_bound.
Check query_expr_rank_runtime_safe_of_cardinality.
Check query_window_item_runtime_safe_through.
Check query_window_row_number_runtime_safe_through.
Check query_window_prefix_aggregate_runtime_safe_through.
Check query_window_full_partition_aggregate_runtime_safe_through.
Check query_window_items_outcome_runtime_safe_through.
Check query_window_rows_outcome_runtime_safe_of_position_budget.
Check query_expr_window_runtime_safe_of_cardinality.

Section GenericOutcomeProgress.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_possible :=
  (@eval_query_expr_possible_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_project_rows :=
  (@eval_project_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_project_join_sources :=
  (@eval_project_join_sources_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_join_row_conditions :=
  (@eval_join_row_conditions_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_join_conditions :=
  (@eval_join_conditions_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_join_bag :=
  (@eval_join_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_grouping_sets_bag :=
  (@eval_grouping_sets_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_cardinality :=
  (@eval_query_cardinality_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** PROJECT returns a reached scalar error instead of requiring a successful
    value list for every row. *)
Theorem project_total_or_error_regression :
  forall env (select_list : query_select_list T relname) input,
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      forall row,
        In row input_rows ->
        exists outcome,
          eval_scalar_values (env_t T env row)
            (map fst select_list) outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome,
      eval_query env (QExpr_Project select_list input) outcome.
Proof.
intros; now eapply query_expr_project_has_outcome.
Qed.

Theorem project_local_error_regression :
  forall env (select_list : query_select_list T relname) input rows error,
    eval_query env input (SqlSuccess rows) ->
    eval_project_rows env select_list rows (SqlError error) ->
    eval_query env (QExpr_Project select_list input) (SqlError error).
Proof.
intros; eapply EQuery_ProjectRows; eassumption.
Qed.

Theorem project_success_regression :
  forall env (select_list : query_select_list T relname) input rows output,
    eval_query env input (SqlSuccess rows) ->
    eval_project_rows env select_list rows (SqlSuccess output) ->
    eval_query env (QExpr_Project select_list input) (SqlSuccess output).
Proof. intros; eapply EQuery_ProjectRows; eassumption. Qed.

Theorem project_child_error_regression :
  forall env (select_list : query_select_list T relname) input error,
    eval_query env input (SqlError error) ->
    eval_query env (QExpr_Project select_list input) (SqlError error).
Proof. intros; now apply EQuery_ProjectChildError. Qed.

(** NATURAL JOIN retains the same eager left/right child schedule as the
    existing SET and CROSS JOIN interfaces. *)
Theorem natural_join_success_regression :
  forall env left right left_rows right_rows output,
    eval_query env left (SqlSuccess left_rows) ->
    eval_query env right (SqlSuccess right_rows) ->
    query_same_rows_as_bag output
      (query_natural_join_bag value_is_null
        (query_rows_bag left_rows) (query_rows_bag right_rows)) ->
    eval_query env (QExpr_NaturalJoin left right) (SqlSuccess output).
Proof. intros; eapply EQuery_NaturalJoinSuccess; eassumption. Qed.

Theorem natural_join_right_child_error_regression :
  forall env left right left_rows error,
    eval_query env left (SqlSuccess left_rows) ->
    eval_query env right (SqlError error) ->
    eval_query env (QExpr_NaturalJoin left right) (SqlError error).
Proof. intros; eapply EQuery_NaturalJoinRightError; eassumption. Qed.

Theorem natural_join_progress_regression :
  forall env left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_NaturalJoin left right) outcome.
Proof. intros; now eapply query_expr_natural_join_has_outcome. Qed.

(** Native JOIN condition traversal preserves errors after an earlier pair or
    an earlier left row has succeeded.  These are the two tail cases that keep
    row-major, left-to-right evaluation observable. *)
Theorem join_later_pair_error_regression :
  forall env predicate left first_right remaining_rights truth error,
    eval_scalar_boolean
      (env_t T env (join_tuple T left first_right)) predicate
      (SqlSuccess truth) ->
    eval_join_row_conditions env predicate left remaining_rights
      (SqlError error) ->
    eval_join_row_conditions env predicate left
      (first_right :: remaining_rights) (SqlError error).
Proof. intros; eapply EJoinRowConditions_TailError; eassumption. Qed.

Theorem join_later_left_row_error_regression :
  forall env predicate first_left remaining_lefts rights flags error,
    eval_join_row_conditions env predicate first_left rights
      (SqlSuccess flags) ->
    eval_join_conditions env predicate remaining_lefts rights
      (SqlError error) ->
    eval_join_conditions env predicate
      (first_left :: remaining_lefts) rights (SqlError error).
Proof. intros; eapply EJoinConditions_TailError; eassumption. Qed.

(** The three projection paths are each error-producing semantic paths. *)
Theorem join_matched_projection_error_regression :
  forall env matched_select left_select right_select row error,
    eval_scalar_values (env_t T env row) (map fst matched_select)
      (SqlError error) ->
    eval_project_join_sources env matched_select left_select right_select
      [JoinSourceMatched T row] (SqlError error).
Proof. intros; now apply EProjectJoinSources_HeadError. Qed.

Theorem join_left_projection_error_regression :
  forall env matched_select left_select right_select row error,
    eval_scalar_values (env_t T env row) (map fst left_select)
      (SqlError error) ->
    eval_project_join_sources env matched_select left_select right_select
      [JoinSourceLeft T row] (SqlError error).
Proof. intros; now apply EProjectJoinSources_HeadError. Qed.

Theorem join_right_projection_error_regression :
  forall env matched_select left_select right_select row error,
    eval_scalar_values (env_t T env row) (map fst right_select)
      (SqlError error) ->
    eval_project_join_sources env matched_select left_select right_select
      [JoinSourceRight T row] (SqlError error).
Proof. intros; now apply EProjectJoinSources_HeadError. Qed.

(** FULL JOIN appends unmatched-right sources only after all sources derived
    from left rows, so an unmatched-right projection cannot move earlier in
    the modeled schedule. *)
Theorem full_join_source_order_regression :
  forall lefts rights matrix,
    query_join_sources T QueryJoinFull lefts rights matrix =
      query_join_left_sources T QueryJoinFull lefts rights matrix ++
      query_join_unmatched_right_sources_from T O rights matrix.
Proof. reflexivity. Qed.

Theorem join_local_error_regression :
  forall env kind predicate matched_select left_select right_select
      left right left_rows right_rows error,
    eval_query env left (SqlSuccess left_rows) ->
    eval_query env right (SqlSuccess right_rows) ->
    eval_join_bag env kind predicate matched_select left_select right_select
      (query_rows_bag left_rows) (query_rows_bag right_rows)
      (SqlError error) ->
    eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlError error).
Proof. intros; eapply EQuery_JoinBagError; eassumption. Qed.

Theorem join_success_regression :
  forall env kind predicate matched_select left_select right_select
      left right left_rows right_rows output_bag output,
    eval_query env left (SqlSuccess left_rows) ->
    eval_query env right (SqlSuccess right_rows) ->
    eval_join_bag env kind predicate matched_select left_select right_select
      (query_rows_bag left_rows) (query_rows_bag right_rows)
      (SqlSuccess output_bag) ->
    query_same_rows_as_bag output output_bag ->
    eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlSuccess output).
Proof. intros; eapply EQuery_JoinSuccess; eassumption. Qed.

Theorem join_left_child_error_regression :
  forall env kind predicate matched_select left_select right_select
      left right error,
    eval_query env left (SqlError error) ->
    eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlError error).
Proof. intros; now apply EQuery_JoinLeftError. Qed.

Theorem join_progress_regression :
  forall env kind predicate matched_select left_select right_select left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    (forall left_rows right_rows,
      eval_query env left (SqlSuccess left_rows) ->
      eval_query env right (SqlSuccess right_rows) ->
      exists outcome,
        eval_join_bag env kind predicate matched_select left_select right_select
          (query_rows_bag left_rows) (query_rows_bag right_rows) outcome) ->
    exists outcome,
      eval_query env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right) outcome.
Proof. intros; now eapply query_expr_join_has_outcome. Qed.

(** ROW MAP is a total Coq callback into [sql_outcome], so a callback error is
    already the exact parent outcome. *)
Theorem row_map_local_error_regression :
  forall env outputs row_map input input_rows error,
    eval_query env input (SqlSuccess input_rows) ->
    row_map_rows_outcome row_map input_rows = SqlError error ->
    eval_query env (QExpr_RowMap outputs row_map input) (SqlError error).
Proof.
intros env outputs row_map input input_rows error Hinput Hmap.
rewrite <- Hmap; now apply EQuery_RowMapRows.
Qed.

Theorem row_map_success_regression :
  forall env outputs row_map input input_rows output_rows,
    eval_query env input (SqlSuccess input_rows) ->
    row_map_rows_outcome row_map input_rows = SqlSuccess output_rows ->
    eval_query env (QExpr_RowMap outputs row_map input)
      (SqlSuccess output_rows).
Proof.
intros env outputs row_map input input_rows output_rows Hinput Hmap.
rewrite <- Hmap; now apply EQuery_RowMapRows.
Qed.

Theorem row_map_child_error_regression :
  forall env outputs row_map input error,
    eval_query env input (SqlError error) ->
    eval_query env (QExpr_RowMap outputs row_map input) (SqlError error).
Proof. intros; now apply EQuery_RowMapChildError. Qed.

Theorem row_map_progress_regression :
  forall env outputs row_map input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome,
      eval_query env (QExpr_RowMap outputs row_map input) outcome.
Proof. intros; now eapply query_expr_row_map_has_outcome. Qed.

(** GROUP key decoding is explicit, and deterministic key/aggregate checks
    may return their exact SQL error before HAVING or SELECT is reached. *)
Theorem group_key_runtime_error_regression :
  forall env select_list group_keys group_terms having input_bag
      representative error,
    scalar_group_key_terms group_keys = Some group_terms ->
    query_same_rows_as_bag representative input_bag ->
    @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
      env group_terms representative = Some error ->
    eval_group_bag env select_list group_keys having input_bag
      (SqlError error).
Proof. intros; eapply EGroupBag_KeyError; eassumption. Qed.

Theorem group_select_aggregate_error_regression :
  forall env select_list group_terms having group groups error,
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) select_list = Some error ->
    eval_groups env select_list group_terms having (group :: groups)
      (SqlError error).
Proof. intros; now apply EGroups_SelectAggregateError. Qed.

Theorem group_having_aggregate_error_regression :
  forall env select_list group_terms having group groups error,
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) select_list = None ->
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) having = Some error ->
    eval_groups env select_list group_terms having (group :: groups)
      (SqlError error).
Proof. intros; eapply EGroups_HavingAggregateError; eassumption. Qed.

Theorem group_having_runtime_error_regression :
  forall env select_list group_terms having group groups error,
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) select_list = None ->
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) having = None ->
    eval_scalar_boolean (env_g T env (Group_By T group_terms) group)
      having (SqlError error) ->
    eval_groups env select_list group_terms having (group :: groups)
      (SqlError error).
Proof. intros; eapply EGroups_HavingError; eassumption. Qed.

Theorem group_select_runtime_error_regression :
  forall env select_list group_terms having group groups truth error,
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) select_list = None ->
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error
      (env_g T env (Group_By T group_terms) group) having = None ->
    eval_scalar_boolean (env_g T env (Group_By T group_terms) group)
      having (SqlSuccess truth) ->
    Bool.is_true (B T) truth = true ->
    eval_scalar_values (env_g T env (Group_By T group_terms) group)
      (map fst select_list) (SqlError error) ->
    eval_groups env select_list group_terms having (group :: groups)
      (SqlError error).
Proof. intros; eapply EGroups_SelectError; eassumption. Qed.

Theorem group_local_error_regression :
  forall env select_list group_keys having input input_rows error,
    eval_query env input (SqlSuccess input_rows) ->
    eval_group_bag env select_list group_keys having
      (query_rows_bag input_rows) (SqlError error) ->
    eval_query env (QExpr_Group select_list group_keys having input)
      (SqlError error).
Proof. intros; eapply EQuery_GroupBagError; eassumption. Qed.

Theorem group_success_regression :
  forall env select_list group_keys having input input_rows output_bag output,
    eval_query env input (SqlSuccess input_rows) ->
    eval_group_bag env select_list group_keys having
      (query_rows_bag input_rows) (SqlSuccess output_bag) ->
    query_same_rows_as_bag output output_bag ->
    eval_query env (QExpr_Group select_list group_keys having input)
      (SqlSuccess output).
Proof. intros; eapply EQuery_GroupBagSuccess; eassumption. Qed.

Theorem group_child_error_regression :
  forall env select_list group_keys having input error,
    eval_query env input (SqlError error) ->
    eval_query env (QExpr_Group select_list group_keys having input)
      (SqlError error).
Proof. intros; now apply EQuery_GroupChildError. Qed.

Theorem group_progress_regression :
  forall env select_list group_keys group_terms having input,
    scalar_group_key_terms group_keys = Some group_terms ->
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      exists outcome,
        eval_group_bag env select_list group_keys having
          (query_rows_bag input_rows) outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome,
      eval_query env (QExpr_Group select_list group_keys having input)
        outcome.
Proof.
intros env select_list group_keys group_terms having input
  Hdecode Hgroup Hinput.
eapply query_expr_group_has_outcome with (group_terms := group_terms);
  eassumption.
Qed.

(** GROUPING SETS preserves branch order: a successful head is followed by
    the exact tail outcome, including a tail SQL error. *)
Theorem grouping_sets_tail_error_regression :
  forall env select_list group_keys grouping_sets input_bag head_bag error,
    eval_group_bag env select_list group_keys SExpr_True input_bag
      (SqlSuccess head_bag) ->
    eval_grouping_sets_bag env grouping_sets input_bag (SqlError error) ->
    eval_grouping_sets_bag env
      ((select_list, group_keys) :: grouping_sets) input_bag
      (SqlError error).
Proof. intros; eapply EGroupingSets_TailError; eassumption. Qed.

Theorem grouping_sets_success_regression :
  forall env grouping_sets input input_rows output_bag output,
    eval_query env input (SqlSuccess input_rows) ->
    eval_grouping_sets_bag env grouping_sets (query_rows_bag input_rows)
      (SqlSuccess output_bag) ->
    query_same_rows_as_bag output output_bag ->
    eval_query env (QExpr_GroupingSets grouping_sets input)
      (SqlSuccess output).
Proof. intros; eapply EQuery_GroupingSetsSuccess; eassumption. Qed.

Theorem grouping_sets_child_error_regression :
  forall env grouping_sets input error,
    eval_query env input (SqlError error) ->
    eval_query env (QExpr_GroupingSets grouping_sets input)
      (SqlError error).
Proof. intros; now apply EQuery_GroupingSetsChildError. Qed.

Theorem grouping_sets_progress_regression :
  forall env grouping_sets input,
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      exists outcome,
        eval_grouping_sets_bag env grouping_sets
          (query_rows_bag input_rows) outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome,
      eval_query env (QExpr_GroupingSets grouping_sets input) outcome.
Proof. intros; now eapply query_expr_grouping_sets_has_outcome. Qed.

(** RANK's [None] is the modeled numeric error, never absence of an
    observation. *)
Theorem rank_none_is_numeric_error_regression :
  forall env partition_keys order_keys rank_attribute rank_value input
      input_rows,
    eval_query env input (SqlSuccess input_rows) ->
    @query_rank_rows_outcome T value_is_null
      partition_keys order_keys rank_attribute rank_value
      (query_rank_bag_rows (query_rows_bag input_rows))
      (query_rank_bag_rows (query_rows_bag input_rows)) = None ->
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlError (DataException NumericValueOutOfRange)).
Proof. intros; eapply EQuery_RankValueError; eassumption. Qed.

Theorem rank_success_regression :
  forall env partition_keys order_keys rank_attribute rank_value input
      input_rows ranked_rows output,
    eval_query env input (SqlSuccess input_rows) ->
    @query_rank_rows_outcome T value_is_null
      partition_keys order_keys rank_attribute rank_value
      (query_rank_bag_rows (query_rows_bag input_rows))
      (query_rank_bag_rows (query_rows_bag input_rows)) = Some ranked_rows ->
    query_same_rows_as_bag output (query_rows_bag ranked_rows) ->
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlSuccess output).
Proof. intros; eapply EQuery_RankSuccess; eassumption. Qed.

Theorem rank_child_error_regression :
  forall env partition_keys order_keys rank_attribute rank_value input error,
    eval_query env input (SqlError error) ->
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlError error).
Proof. intros; now apply EQuery_RankChildError. Qed.

Theorem rank_progress_regression :
  forall env partition_keys order_keys rank_attribute rank_value input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome,
      eval_query env
        (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
        outcome.
Proof. intros; now eapply query_expr_rank_has_outcome. Qed.

(** WINDOW chooses a legal ordered representative, then preserves either the
    local row-evaluation error or its successful bag representative. *)
Theorem window_legal_order_representative_regression :
  forall partition_keys order_keys input_rows,
    exists ordered_rows,
      @order_by_rows T value_is_null (partition_keys ++ order_keys)
        (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows.
Proof. intros; apply order_by_rows_has_observation. Qed.

Theorem window_rows_total_or_error_regression :
  forall env partition_keys items previous position prefix rows,
    exists outcome,
      @query_window_rows_outcome T symbol_runtime_error
        aggregate_runtime_error value_is_null env partition_keys items
        previous position prefix rows = Some outcome.
Proof. intros; now apply query_window_rows_has_outcome. Qed.

Theorem window_local_error_regression :
  forall env partition_keys order_keys items input input_rows ordered_rows
      error,
    eval_query env input (SqlSuccess input_rows) ->
    @order_by_rows T value_is_null (partition_keys ++ order_keys)
      (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows ->
    @query_window_rows_outcome T symbol_runtime_error aggregate_runtime_error
      value_is_null env partition_keys items None 0 nil ordered_rows =
      Some (SqlError error) ->
    eval_query env (QExpr_Window partition_keys order_keys items input)
      (SqlError error).
Proof. intros; eapply EQuery_WindowRowsError; eassumption. Qed.

Theorem window_success_regression :
  forall env partition_keys order_keys items input input_rows ordered_rows
      window_rows output,
    eval_query env input (SqlSuccess input_rows) ->
    @order_by_rows T value_is_null (partition_keys ++ order_keys)
      (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows ->
    @query_window_rows_outcome T symbol_runtime_error aggregate_runtime_error
      value_is_null env partition_keys items None 0 nil ordered_rows =
      Some (SqlSuccess window_rows) ->
    query_same_rows_as_bag output (query_rows_bag window_rows) ->
    eval_query env (QExpr_Window partition_keys order_keys items input)
      (SqlSuccess output).
Proof. intros; eapply EQuery_WindowSuccess; eassumption. Qed.

Theorem window_child_error_regression :
  forall env partition_keys order_keys items input error,
    eval_query env input (SqlError error) ->
    eval_query env (QExpr_Window partition_keys order_keys items input)
      (SqlError error).
Proof. intros; now apply EQuery_WindowChildError. Qed.

Theorem window_progress_regression :
  forall env partition_keys order_keys items input,
    (exists outcome, eval_query env input outcome) ->
    exists outcome,
      eval_query env (QExpr_Window partition_keys order_keys items input)
        outcome.
Proof. intros; now eapply query_expr_window_has_outcome. Qed.

(** The dedicated demand evaluators remain inhabited without evaluating
    target expressions that EXISTS or cardinality legitimately elides. *)
Theorem join_cardinality_progress_regression :
  forall env kind predicate matched_select left_select right_select left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    (forall left_rows right_rows,
      eval_query env left (SqlSuccess left_rows) ->
      eval_query env right (SqlSuccess right_rows) ->
      exists outcome,
        @eval_join_cardinality_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null boolean_schedule
          env kind predicate (query_rows_bag left_rows)
          (query_rows_bag right_rows) outcome) ->
    exists outcome,
      eval_cardinality env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right) outcome.
Proof. intros; now eapply eval_query_cardinality_join_has_outcome. Qed.

Theorem group_cardinality_progress_regression :
  forall env select_list group_keys group_terms having input,
    scalar_group_key_terms group_keys = Some group_terms ->
    (exists outcome, eval_query env input outcome) ->
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      exists outcome,
        @eval_group_cardinality_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null boolean_schedule
          env select_list group_terms having
          (query_rows_bag input_rows) outcome) ->
    exists outcome,
      eval_cardinality env
        (QExpr_Group select_list group_keys having input) outcome.
Proof.
intros env select_list group_keys group_terms having input
  Hdecode Hinput Hgroup.
eapply eval_query_cardinality_group_has_outcome with
  (group_terms := group_terms); eassumption.
Qed.

Theorem grouping_sets_cardinality_progress_regression :
  forall env grouping_sets input,
    (exists outcome, eval_query env input outcome) ->
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      exists outcome,
        @eval_grouping_sets_cardinality_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null boolean_schedule
          env grouping_sets (query_rows_bag input_rows) outcome) ->
    exists outcome,
      eval_cardinality env (QExpr_GroupingSets grouping_sets input) outcome.
Proof. intros; now eapply eval_query_cardinality_grouping_sets_has_outcome. Qed.

Theorem exists_cardinality_demand_progress_regression :
  forall env query,
    query_exists_uses_cardinality query = true ->
    (exists outcome, eval_cardinality env query outcome) ->
    exists outcome, eval_exists env query outcome.
Proof. intros; now eapply eval_query_exists_cardinality_has_outcome. Qed.

Theorem filter_exists_progress_regression :
  forall env formula input,
    (exists outcome, eval_query env input outcome) ->
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      forall row,
        In row input_rows ->
        exists outcome,
          eval_scalar_boolean (env_t T env row) formula outcome) ->
    exists outcome, eval_exists env (QExpr_Filter formula input) outcome.
Proof. intros; now eapply eval_query_exists_filter_has_outcome. Qed.

Theorem fetch_zero_exists_progress_requires_analysis_clear_regression :
  forall env input,
    query_expr_contains_analysis_error input = false ->
    exists outcome, eval_exists env (QExpr_Fetch O input) outcome.
Proof. intros; now apply eval_query_exists_fetch_zero_has_outcome. Qed.

(** Public possible outcomes reuse schedule-uniform progress without asking a
    proof client to choose a schedule or a privileged result. *)
Theorem scheduled_progress_lifts_to_possible_regression :
  forall env query,
    @query_expr_scheduled_progress T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query ->
    exists outcome, eval_possible env query outcome.
Proof.
intros; now eapply query_expr_scheduled_progress_has_possible_outcome.
Qed.

End GenericOutcomeProgress.

Check eval_query_cardinality_demanded_has_outcome.
Check eval_query_cardinality_project_has_outcome.
Check eval_query_cardinality_row_map_has_outcome.
Check eval_query_cardinality_order_by_has_outcome.
Check eval_query_cardinality_fetch_has_outcome.
Check eval_query_cardinality_join_has_outcome.
Check eval_query_cardinality_group_has_outcome.
Check eval_query_cardinality_grouping_sets_has_outcome.
Check eval_query_exists_demanded_has_outcome.
Check eval_query_exists_cardinality_has_outcome.
Check eval_query_exists_project_has_outcome.
Check eval_query_exists_row_map_has_outcome.
Check eval_query_exists_filter_has_outcome.
Check eval_query_exists_distinct_has_outcome.
Check eval_query_exists_order_by_has_outcome.
Check eval_query_exists_fetch_zero_has_outcome.
Check eval_query_exists_fetch_positive_has_outcome.
Check query_expr_scheduled_progress.
Check query_expr_scheduled_progress_has_possible_outcome.

Print Assumptions query_expr_error_has_outcome.
Print Assumptions query_expr_values_has_outcome.
Print Assumptions query_expr_table_has_outcome.
Print Assumptions query_expr_set_has_outcome.
Print Assumptions query_expr_natural_join_has_outcome.
Print Assumptions query_expr_cross_join_has_outcome.
Print Assumptions query_expr_join_has_outcome.
Print Assumptions query_expr_project_has_outcome.
Print Assumptions query_expr_row_map_has_outcome.
Print Assumptions query_expr_filter_has_outcome_of_scalar_total.
Print Assumptions query_expr_group_has_outcome.
Print Assumptions query_expr_grouping_sets_has_outcome.
Print Assumptions query_expr_rank_has_outcome.
Print Assumptions query_expr_window_has_outcome.
Print Assumptions query_expr_distinct_has_outcome.
Print Assumptions query_expr_order_by_has_outcome.
Print Assumptions query_expr_offset_has_outcome.
Print Assumptions query_expr_fetch_has_outcome.

Print Assumptions eval_join_row_conditions_has_outcome.
Print Assumptions eval_join_conditions_has_outcome.
Print Assumptions eval_project_join_sources_has_outcome.
Print Assumptions eval_join_bag_has_outcome.
Print Assumptions eval_groups_has_outcome.
Print Assumptions eval_group_bag_has_outcome.
Print Assumptions eval_grouping_sets_bag_has_outcome.
Print Assumptions query_rank_rows_has_outcome.
Print Assumptions query_window_rows_has_outcome.
Print Assumptions scalar_value_case_runtime_safe_of_reachable_branches.
Print Assumptions scalar_conj_list_uniform_runtime_safe.
Print Assumptions query_expr_filter_runtime_safe_of_reachable_predicate_safe.
Print Assumptions query_expr_join_runtime_safe_of_reachable_local_safe.
Print Assumptions query_expr_group_runtime_safe_of_reachable_local_safe.
Print Assumptions query_expr_window_runtime_safe_of_reachable_local_safe.
Print Assumptions query_expr_rank_runtime_safe_of_cardinality.
Print Assumptions query_expr_window_runtime_safe_of_cardinality.
Print Assumptions eval_query_cardinality_join_has_outcome.
Print Assumptions eval_query_exists_filter_has_outcome.
Print Assumptions eval_query_exists_fetch_zero_has_outcome.
Print Assumptions query_expr_scheduled_progress_has_possible_outcome.

(** The TNull façade closes the complete mutual query/scalar demand chain from
    the existing typed, well-placed admission certificate. *)
Check query_expr_progress_ready.
Check scalar_expr_progress_ready.
Check tnull_query_expr_progress_ready_scheduled_progress.
Check tnull_query_expr_progress_ready_scheduled_cardinality_progress.
Check tnull_query_expr_progress_ready_scheduled_exists_progress.
Check tnull_scalar_expr_progress_ready_scheduled_progress.
Check tnull_query_expr_well_placed_progress_ready.
Check tnull_query_expr_well_placed_scheduled_progress.
Check tnull_query_expr_well_placed_possible_progress.

Theorem tnull_well_placed_scheduled_progress_regression :
  forall db env query,
    TNullQueryExprAdmissible (@_basesort TNull db) query ->
    forall schedule,
      exists outcome,
        @eval_query_expr_outcome TNull relname
          (@_basesort TNull db) (@_instance TNull db) unknown3
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          NullValues.is_null_value schedule env query outcome.
Proof.
intros; now eapply tnull_query_expr_well_placed_scheduled_progress.
Qed.

Theorem tnull_well_placed_possible_progress_regression :
  forall db env query,
    TNullQueryExprAdmissible (@_basesort TNull db) query ->
    exists outcome, TNullQueryExprOutcome db env query outcome.
Proof.
intros; now eapply tnull_query_expr_well_placed_possible_progress.
Qed.

Print Assumptions query_scalar_expr_well_placed_progress_ready.
Print Assumptions query_expr_well_placed_progress_ready.
Print Assumptions query_scalar_expr_progress_ready_has_outcomes.
Print Assumptions tnull_query_expr_progress_ready_scheduled_progress.
Print Assumptions
  tnull_query_expr_progress_ready_scheduled_cardinality_progress.
Print Assumptions tnull_query_expr_progress_ready_scheduled_exists_progress.
Print Assumptions tnull_scalar_expr_progress_ready_scheduled_progress.
Print Assumptions tnull_query_expr_well_placed_scheduled_progress.
Print Assumptions tnull_query_expr_well_placed_possible_progress.
