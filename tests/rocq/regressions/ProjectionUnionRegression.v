Set Implicit Arguments.

From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3
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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation query_safe :=
  (query_expr_runtime_safe basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation query_equiv :=
  (@query_expr_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

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
