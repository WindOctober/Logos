(******************************************************************************)
(** Generic regressions for success-bag functionality and GROUPING SETS.     **)
(******************************************************************************)

From Stdlib Require Import List Lia.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet SqlErrorSemantics SqlOutcome
  OrderedSet SqlBagAbstraction SqlQueryContexts SqlQueryFacts SqlQuerySemantics
  SqlQuerySyntax.
From Logos.FormalSQL Require Import
  RelationalAlgebraFacts AggregateRuntimeFacts OrderedQueryFacts.

Import Tuple.
Import ListNotations.

Section OrderedGroupingSetsFunctionalityRegression.

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

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** No SELECT-list runtime-safety premise appears here.  The two successful
    observations themselves suffice for the projection functionality rule. *)
Theorem projected_table_success_bags_functional_without_safety :
  forall env select_list outputs table first second,
    success_bags env
      (QExpr_Project select_list (QExpr_Table outputs table)) first ->
    success_bags env
      (QExpr_Project select_list (QExpr_Table outputs table)) second ->
    bag_eq T first second.
Proof.
intros env select_list outputs table first second Hfirst Hsecond.
eapply query_project_success_bags_functional;
  [|exact Hfirst|exact Hsecond].
intros child_first child_second Hchild_first Hchild_second.
eapply query_table_success_bags_functional; eassumption.
Qed.

Theorem distinct_projected_table_success_bags_functional :
  forall env select_list outputs table first second,
    success_bags env
      (QExpr_Distinct
        (QExpr_Project select_list (QExpr_Table outputs table))) first ->
    success_bags env
      (QExpr_Distinct
        (QExpr_Project select_list (QExpr_Table outputs table))) second ->
    bag_eq T first second.
Proof.
intros env select_list outputs table first second Hfirst Hsecond.
eapply query_distinct_success_bags_functional;
  [|exact Hfirst|exact Hsecond].
intros child_first child_second Hchild_first Hchild_second.
eapply query_project_success_bags_functional;
  [|exact Hchild_first|exact Hchild_second].
intros table_first table_second Htable_first Htable_second.
eapply query_table_success_bags_functional; eassumption.
Qed.

Theorem set_of_projected_tables_success_bags_functional :
  forall env operation select_list outputs left_table right_table first second,
    success_bags env
      (QExpr_Set operation
        (QExpr_Project select_list (QExpr_Table outputs left_table))
        (QExpr_Project select_list (QExpr_Table outputs right_table))) first ->
    success_bags env
      (QExpr_Set operation
        (QExpr_Project select_list (QExpr_Table outputs left_table))
        (QExpr_Project select_list (QExpr_Table outputs right_table))) second ->
    bag_eq T first second.
Proof.
intros env operation select_list outputs left_table right_table
  first second Hfirst Hsecond.
eapply query_set_success_bags_functional;
  [| |exact Hfirst|exact Hsecond].
- intros child_first child_second Hchild_first Hchild_second.
  eapply query_project_success_bags_functional;
    [|exact Hchild_first|exact Hchild_second].
  intros table_first table_second Htable_first Htable_second.
  eapply query_table_success_bags_functional; eassumption.
- intros child_first child_second Hchild_first Hchild_second.
  eapply query_project_success_bags_functional;
    [|exact Hchild_first|exact Hchild_second].
  intros table_first table_second Htable_first Htable_second.
  eapply query_table_success_bags_functional; eassumption.
Qed.

Theorem cross_join_of_tables_success_bags_functional :
  forall env left_outputs left_table right_outputs right_table first second,
    success_bags env
      (QExpr_CrossJoin
        (QExpr_Table left_outputs left_table)
        (QExpr_Table right_outputs right_table)) first ->
    success_bags env
      (QExpr_CrossJoin
        (QExpr_Table left_outputs left_table)
        (QExpr_Table right_outputs right_table)) second ->
    bag_eq T first second.
Proof.
intros env left_outputs left_table right_outputs right_table
  first second Hfirst Hsecond.
eapply query_cross_join_success_bags_functional;
  [| |exact Hfirst|exact Hsecond].
- intros child_first child_second Hchild_first Hchild_second.
  eapply query_table_success_bags_functional; eassumption.
- intros child_first child_second Hchild_first Hchild_second.
  eapply query_table_success_bags_functional; eassumption.
Qed.

(** Arbitrary grouping-set lists are exposed one evaluator step at a time.
    These regressions deliberately stop before assembling a whole rewrite. *)
Theorem grouping_sets_nil_outcome_regression :
  forall env input outcome,
    @eval_grouping_sets_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env [] input outcome <->
    outcome = SqlSuccess (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
apply eval_grouping_sets_nil_outcome_iff.
Qed.

Theorem grouping_sets_cons_success_regression :
  forall env select_list group_terms grouping_sets input output,
    @eval_grouping_sets_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env ((select_list, group_terms) :: grouping_sets) input
      (SqlSuccess output) <->
    exists head_bag tail_bag,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env select_list group_terms FExpr_True input
        (SqlSuccess head_bag) /\
      @eval_grouping_sets_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env grouping_sets input (SqlSuccess tail_bag) /\
      output = query_set_bag Union head_bag tail_bag.
Proof.
apply eval_grouping_sets_cons_success_iff.
Qed.

Theorem grouping_sets_cons_error_regression :
  forall env select_list group_terms grouping_sets input error,
    @eval_grouping_sets_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env ((select_list, group_terms) :: grouping_sets) input
      (SqlError error) <->
    @eval_group_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env select_list group_terms FExpr_True input (SqlError error) \/
    exists head_bag,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env select_list group_terms FExpr_True input
        (SqlSuccess head_bag) /\
      @eval_grouping_sets_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env grouping_sets input (SqlError error).
Proof.
apply eval_grouping_sets_cons_error_iff.
Qed.

End OrderedGroupingSetsFunctionalityRegression.

Print Assumptions project_rows_success_exact.
Print Assumptions query_project_success_bags_functional.
Print Assumptions query_set_success_bags_functional.
Print Assumptions query_cross_join_success_bags_functional.
Print Assumptions query_distinct_success_bags_functional.
Print Assumptions eval_grouping_sets_nil_outcome_iff.
Print Assumptions eval_grouping_sets_cons_success_iff.
Print Assumptions eval_grouping_sets_cons_error_iff.
