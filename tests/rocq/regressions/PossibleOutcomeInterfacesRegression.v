From Stdlib Require Import List.
From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
  SqlOutcome SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics
  SqlQueryFacts SqlQueryContexts.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts PossibleOutcomeFacts SubqueryFacts.

Import Tuple.
Import ListNotations.

Section GenericPossibleInterfaces.

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

Variable env : Env.env T.
Variables first second third : query_expr T relname.

Example all_schedules_bridge_regression :
  query_expr_uniform_scheduled_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second.
Proof.
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
Qed.

Example possible_outcome_symmetry_regression :
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env second first.
Proof.
apply query_expr_possible_outcome_equiv_sym.
Qed.

Example possible_outcome_transitivity_regression :
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env second third ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first third.
Proof.
intros; eapply query_expr_possible_outcome_equiv_trans; eassumption.
Qed.

Example possible_success_symmetry_regression :
  @query_expr_possible_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second ->
  @query_expr_possible_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env second first.
Proof.
apply query_expr_possible_equiv_sym.
Qed.

Example possible_success_transitivity_regression :
  @query_expr_possible_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second ->
  @query_expr_possible_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env second third ->
  @query_expr_possible_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first third.
Proof.
intros; eapply query_expr_possible_equiv_trans; eassumption.
Qed.

Example possible_outcome_to_safe_success_regression :
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second ->
  query_expr_possible_runtime_safe
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first ->
  query_expr_possible_runtime_safe
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env second ->
  query_expr_possible_has_success
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first ->
  @query_expr_possible_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env first second.
Proof.
apply query_expr_possible_equiv_of_possible_outcome_equiv_safe.
Qed.

Variable scalar_select :
  list (scalar_expr T relname ScalarResultValue * attribute T).
Variable scalar_predicate : scalar_expr T relname ScalarResultBoolean.
Variable scalar_group_terms : list (scalar_expr T relname ScalarResultValue).

Example scalar_project_context_plug_regression :
  plug_query_expr_context
    (QCtx_Project scalar_select QCtx_Hole) first =
  QExpr_Project scalar_select first.
Proof. reflexivity. Qed.

Example scalar_filter_context_plug_regression :
  plug_query_expr_context
    (QCtx_FilterInput scalar_predicate QCtx_Hole) first =
  QExpr_Filter scalar_predicate first.
Proof. reflexivity. Qed.

Example scalar_group_context_plug_regression :
  plug_query_expr_context
    (QCtx_GroupInput scalar_select scalar_group_terms
      scalar_predicate QCtx_Hole) first =
  QExpr_Group scalar_select scalar_group_terms
    scalar_predicate first.
Proof. reflexivity. Qed.

Example scalar_group_possible_context_regression :
  query_expr_uniform_global_typed_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null first second ->
  (exists outcome,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group scalar_select scalar_group_terms
        scalar_predicate first) outcome) ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (QExpr_Group scalar_select scalar_group_terms
      scalar_predicate first)
    (QExpr_Group scalar_select scalar_group_terms
      scalar_predicate second).
Proof.
intros Hequiv Houtcome.
eapply query_expr_context_possible_outcome_equiv with
  (context := QCtx_GroupInput scalar_select scalar_group_terms
    scalar_predicate QCtx_Hole);
  eassumption.
Qed.

Variables left_scalar_boolean right_scalar_boolean :
  scalar_expr T relname ScalarResultBoolean.
Variables left_scalar_value right_scalar_value :
  scalar_expr T relname ScalarResultValue.
Variables left_scalar_values right_scalar_values :
  list (scalar_expr T relname ScalarResultValue).
Variables left_scalar_booleans right_scalar_booleans :
  list (scalar_expr T relname ScalarResultBoolean).
Variables left_scalar_select right_scalar_select :
  list (scalar_expr T relname ScalarResultValue * attribute T).

Example scalar_conj_list_composition_regression site_rows conjunction :
  scalar_boolean_expr_list_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null left_scalar_booleans right_scalar_booleans ->
  scalar_expr_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null
    (SExpr_ConjList site_rows conjunction left_scalar_booleans)
    (SExpr_ConjList site_rows conjunction right_scalar_booleans).
Proof.
apply scalar_expr_conj_list_uniform_global_congr.
Qed.

Example scalar_subquery_typed_boundary_regression result_type null_value :
  query_expr_uniform_global_typed_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null first second ->
  scalar_expr_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null
    (SExpr_Subquery result_type null_value first)
    (SExpr_Subquery result_type null_value second).
Proof.
apply scalar_expr_subquery_uniform_global_congr.
Qed.

Example scalar_in_typed_boundary_regression :
  scalar_value_expr_list_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null left_scalar_values right_scalar_values ->
  query_expr_uniform_global_typed_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null first second ->
  scalar_expr_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null
    (SExpr_In left_scalar_values first)
    (SExpr_In right_scalar_values second).
Proof.
apply scalar_expr_in_uniform_global_congr.
Qed.

Example scalar_exists_demand_boundary_regression :
  query_expr_uniform_global_exists_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null first second ->
  scalar_expr_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null (SExpr_Exists first) (SExpr_Exists second).
Proof.
apply scalar_expr_exists_uniform_global_congr.
Qed.

Example scalar_filter_predicate_possible_regression :
  scalar_expr_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null left_scalar_boolean right_scalar_boolean ->
  (exists outcome,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_scalar_boolean first) outcome) ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (QExpr_Filter left_scalar_boolean first)
    (QExpr_Filter right_scalar_boolean first).
Proof.
apply query_expr_filter_predicate_possible_outcome_equiv.
Qed.

Example scalar_project_select_possible_regression :
  scalar_select_list_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null left_scalar_select right_scalar_select ->
  (exists outcome,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_scalar_select first) outcome) ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (QExpr_Project left_scalar_select first)
    (QExpr_Project right_scalar_select first).
Proof.
apply query_expr_project_select_possible_outcome_equiv.
Qed.

Example scalar_group_clauses_possible_regression :
  scalar_select_list_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null left_scalar_select right_scalar_select ->
  scalar_expr_uniform_global_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null left_scalar_boolean right_scalar_boolean ->
  (forall current_env,
    @eval_scalar_select_aggregate_runtime_error T relname
      symbol_runtime_error aggregate_runtime_error
      current_env left_scalar_select =
    @eval_scalar_select_aggregate_runtime_error T relname
      symbol_runtime_error aggregate_runtime_error
      current_env right_scalar_select) ->
  (forall current_env,
    @eval_scalar_expr_aggregate_runtime_error T relname
      symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
      current_env left_scalar_boolean =
    @eval_scalar_expr_aggregate_runtime_error T relname
      symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
      current_env right_scalar_boolean) ->
  (exists outcome,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_scalar_select scalar_group_terms
        left_scalar_boolean first) outcome) ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (QExpr_Group left_scalar_select scalar_group_terms
      left_scalar_boolean first)
    (QExpr_Group right_scalar_select scalar_group_terms
      right_scalar_boolean first).
Proof.
apply query_expr_group_clauses_possible_outcome_equiv.
Qed.

Variable operation : set_op.
Variables left left' right right' : query_expr T relname.

Example set_possible_uniform_regression :
  query_expr_uniform_scheduled_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left left' ->
  query_expr_uniform_scheduled_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env right right' ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (QExpr_Set operation left right)
    (QExpr_Set operation left' right').
Proof.
apply query_expr_set_possible_outcome_equiv_congr_uniform.
Qed.

Example cross_join_possible_uniform_regression :
  query_expr_uniform_scheduled_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left left' ->
  query_expr_uniform_scheduled_outcome_equiv
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env right right' ->
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (QExpr_CrossJoin left right)
    (QExpr_CrossJoin left' right').
Proof.
apply query_expr_cross_join_possible_outcome_equiv_congr_uniform.
Qed.

Check query_expr_possible_outcome_equiv_of_exact_schedule_transport.
Check query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport.
Check query_expr_scheduled_outcome_equiv_implies_possible_of_independent.
Check query_expr_possible_equiv_of_ordered_observations.
Check query_expr_possible_equiv_of_observations.
Check query_expr_possible_outcome_equiv_of_observations.
Check query_expr_possible_equiv_refl.
Check query_expr_possible_equiv_sym.
Check query_expr_possible_equiv_trans.
Check query_expr_possible_equiv_of_possible_outcome_equiv_safe.
Check eval_query_expr_possible_outcome_site_reindex_iff.
Print Assumptions eval_query_expr_possible_outcome_site_reindex_iff.
Check query_expr_context_possible_outcome_equiv.
Check query_expr_filter_possible_outcome_equiv_congr_stable_total.
Check query_expr_possible_outcome_related.
Check query_expr_possible_outcome_equiv_of_Forall2_rows.
Check scalar_value_observation_related_at.
Check eval_scalar_values_relation_forward.
Check eval_scalar_values_relation_transport.
Check scalar_call_apply_outcome.
Check eval_scalar_value_call_outcome_iff.
Check scalar_call_local_observation_related.
Check scalar_call_expression_relation_forward.
Check scalar_call_expression_relation_transport.
Check scalar_call_expression_runtime_safe_of_reachable_local_safe.
Check scalar_subquery_value_outcome_safe_of_length_le_one.
Check scalar_subquery_runtime_safe_of_cardinality.
Check row_map_observation_related_at.
Check row_map_rows_outcome_relation.
Check scalar_value_expr_exact_at.
Check scalar_value_list_exact_nil.
Check scalar_value_list_exact_cons.
Check scalar_value_expr_leaf_exact.
Check scalar_value_expr_call_exact.
Check eval_project_rows_exact_map.
Check project_row_observation_related_at.
Check eval_project_rows_relation_forward.
Check eval_project_rows_relation_transport.
Check eval_filter_rows_relation_forward.
Check eval_filter_rows_relation_transport.
Check query_expr_project_relation_forward.
Check query_expr_project_relation_transport.
Check query_expr_row_map_relation_forward.
Check query_expr_row_map_relation_transport.
Check query_expr_filter_relation_forward.
Check query_expr_filter_relation_transport.
Check query_expr_project_possible_outcome_related.
Check query_expr_row_map_possible_outcome_related.
Check query_expr_filter_possible_outcome_related.
Check query_join_rows_outcomes.
Check query_expr_join_relation_transport.
Check query_expr_join_possible_outcome_related_same_schedule.
Check query_expr_join_possible_outcome_related.
Check query_group_rows_outcomes.
Check query_expr_group_possible_outcome_transport.
Check query_expr_group_possible_outcome_equiv_of_supported_child_outcomes.
Check query_expr_window_possible_outcome_equiv_congr_uniform.
Check query_expr_filter_in_subquery_possible_outcome_equiv.
Check query_expr_filter_exists_subquery_possible_outcome_equiv.
Check scalar_expr_call_uniform_global_congr.
Check scalar_expr_case_uniform_global_congr.
Check scalar_expr_bool_value_uniform_global_congr.
Check scalar_expr_value_bool_uniform_global_congr.
Check scalar_expr_pred_uniform_global_congr.
Check scalar_expr_conj_list_uniform_global_congr.
Check scalar_expr_not_uniform_global_congr.
Check scalar_expr_subquery_uniform_global_congr.
Check scalar_expr_quant_uniform_global_congr.
Check scalar_expr_in_uniform_global_congr.
Check scalar_expr_exists_uniform_global_congr.
Check query_expr_filter_predicate_possible_outcome_equiv.
Check query_expr_project_select_possible_outcome_equiv.
Check query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes.
Check query_expr_group_possible_outcome_equiv_of_exact_local_outcomes.
Check query_expr_group_clauses_possible_outcome_equiv.
Check query_expr_possible_outcome_equiv_of_shared_exact_error.
Check query_rename_uniform_transport_implies_mapped_schema_possible_outcome_equiv.
Check query_program_possible_equiv_nil.
Check query_program_possible_equiv_cons.
Check query_program_possible_outcome_equiv_nil.
Check query_program_possible_outcome_equiv_cons.
Check query_program_possible_equiv_length.
Check query_program_possible_outcome_equiv_length.
Check query_program_possible_equiv_iff_Forall2.
Check query_program_possible_outcome_equiv_iff_Forall2.

Print Assumptions query_expr_possible_outcome_equiv_of_exact_schedule_transport.
Print Assumptions query_expr_possible_equiv_of_possible_outcome_equiv_safe.
Print Assumptions query_expr_context_possible_outcome_equiv.
Print Assumptions query_expr_filter_possible_outcome_equiv_congr_stable_total.
Print Assumptions query_expr_possible_outcome_equiv_of_Forall2_rows.
Print Assumptions eval_scalar_values_relation_transport.
Print Assumptions scalar_call_expression_relation_transport.
Print Assumptions scalar_call_expression_runtime_safe_of_reachable_local_safe.
Print Assumptions scalar_subquery_runtime_safe_of_cardinality.
Print Assumptions row_map_rows_outcome_relation.
Print Assumptions scalar_value_list_exact_cons.
Print Assumptions scalar_value_expr_leaf_exact.
Print Assumptions scalar_value_expr_call_exact.
Print Assumptions eval_project_rows_exact_map.
Print Assumptions eval_project_rows_relation_transport.
Print Assumptions eval_filter_rows_relation_transport.
Print Assumptions query_expr_project_relation_transport.
Print Assumptions query_expr_row_map_relation_transport.
Print Assumptions query_expr_filter_relation_transport.
Print Assumptions query_expr_project_possible_outcome_related.
Print Assumptions query_expr_row_map_possible_outcome_related.
Print Assumptions query_expr_filter_possible_outcome_related.
Print Assumptions query_expr_join_relation_transport.
Print Assumptions query_expr_join_possible_outcome_related_same_schedule.
Print Assumptions query_expr_join_possible_outcome_related.
Print Assumptions query_expr_group_possible_outcome_transport.
Print Assumptions query_expr_group_possible_outcome_equiv_of_supported_child_outcomes.
Print Assumptions query_expr_group_clauses_possible_outcome_equiv.
End GenericPossibleInterfaces.
