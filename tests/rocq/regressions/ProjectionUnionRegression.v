Set Implicit Arguments.

From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
  SqlOutcome SqlErrorSemantics SqlBagAbstraction SqlQuerySyntax
  SqlQuerySemantics SqlQueryFacts SqlQueryContexts.
From Logos.FormalSQL Require Import
  RelationalAlgebraFacts OrderedQueryFacts.

Import Tuple.

Section GenericProjectionUnionRegression.

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

Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_safe :=
  (query_expr_runtime_safe basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_equiv :=
  (@query_expr_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Example safe_projection_possible_bags_are_exact :
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
Proof.
intros; now apply query_project_success_bags_safe.
Qed.

Example projected_table_success_bags_are_functional :
  forall env select_list outputs table first second,
    success_bags env (QExpr_Project select_list (QExpr_Table outputs table))
      first ->
    success_bags env (QExpr_Project select_list (QExpr_Table outputs table))
      second ->
    bag_eq T first second.
Proof.
intros env select_list outputs table first second Hfirst Hsecond.
eapply query_project_success_bags_functional;
  [| exact Hfirst | exact Hsecond].
intros first_input second_input Hfirst_input Hsecond_input.
eapply query_table_success_bags_functional; eassumption.
Qed.

Example cross_join_distributes_over_union_all_possible_bags :
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
Proof.
intros; now apply query_cross_join_union_right_success_bags.
Qed.

Example cross_join_union_all_safe_equivalence :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    query_safe env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_safe env
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)) ->
    query_has_success env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_equiv env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
Proof.
intros; now apply query_expr_cross_join_union_right_equiv_safe.
Qed.

Example cross_join_union_all_outcome_equivalence :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    query_safe env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_safe env
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)) ->
    query_has_success env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_outcome_equiv env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
Proof.
intros; now apply query_expr_cross_join_union_right_outcome_equiv_safe.
Qed.

End GenericProjectionUnionRegression.
