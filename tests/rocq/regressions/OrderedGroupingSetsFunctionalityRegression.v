(******************************************************************************)
(** Generic regressions for success-bag functionality and GROUPING SETS.     **)
(******************************************************************************)

From Stdlib Require Import List Lia.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet SqlErrorSemantics SqlOutcome
  OrderedSet SqlBagAbstraction SqlQueryContexts SqlQueryFacts SqlQuerySemantics
  SqlQuerySyntax.
From Logos.FormalSQL Require Import OrderedQueryFacts.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

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
      boolean_schedule env [] input outcome <->
    outcome = SqlSuccess (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intros env input outcome; split.
- intro Heval; inversion Heval; reflexivity.
- intro Houtcome; subst; constructor.
Qed.

Theorem grouping_sets_cons_success_regression :
  forall env select_list group_keys grouping_sets input output,
    @eval_grouping_sets_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env ((select_list, group_keys) :: grouping_sets) input
      (SqlSuccess output) <->
    exists head_bag tail_bag,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list group_keys SExpr_True input
        (SqlSuccess head_bag) /\
      @eval_grouping_sets_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env grouping_sets input (SqlSuccess tail_bag) /\
      output = query_set_bag Union head_bag tail_bag.
Proof.
intros env select_list group_keys grouping_sets input output; split.
- intro Heval; inversion Heval; subst.
  eexists; eexists; repeat split; eassumption || reflexivity.
- intros [head_bag [tail_bag [Hhead [Htail Houtput]]]].
  subst output; now apply EGroupingSets_ConsSuccess.
Qed.

Theorem grouping_sets_cons_error_regression :
  forall env select_list group_keys grouping_sets input error,
    @eval_grouping_sets_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env ((select_list, group_keys) :: grouping_sets) input
      (SqlError error) <->
    @eval_group_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list group_keys SExpr_True input
      (SqlError error) \/
    exists head_bag,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list group_keys SExpr_True input
        (SqlSuccess head_bag) /\
      @eval_grouping_sets_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env grouping_sets input (SqlError error).
Proof.
intros env select_list group_keys grouping_sets input error; split.
- intro Heval; inversion Heval; subst.
  + now left.
  + right; eexists; now split; eassumption.
- intros [Hhead | [head_bag [Hhead Htail]]].
  + now apply EGroupingSets_HeadError.
  + eapply EGroupingSets_TailError with (head_bag := head_bag).
    * exact Hhead.
    * exact Htail.
Qed.

End OrderedGroupingSetsFunctionalityRegression.

Print Assumptions query_set_success_bags_functional.
Print Assumptions query_cross_join_success_bags_functional.
Print Assumptions query_distinct_success_bags_functional.
