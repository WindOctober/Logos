(******************************************************************************)
(** Generic regressions for correlated-subquery environment congruence.       **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula
  FTuples ListPermut OrderedSet Projection SqlErrorSemantics SqlOutcome
  SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import SubqueryFacts.

Import Tuple.

Theorem heterogeneous_empty_decision_permut_regression :
  forall (A B : Type) (R : A -> B -> Prop) left right,
    _permut R left right ->
    rows_empty_decision left = rows_empty_decision right.
Proof.
  intros; now apply rows_empty_decision_rel_permut with (R := R).
Qed.

Theorem list_existsb_rel_permut_regression :
  forall (A B : Type) (R : A -> B -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      left_predicate left_value = right_predicate right_value) ->
    _permut R left right ->
    existsb left_predicate left = existsb right_predicate right.
Proof.
  intros; now apply existsb_rel_permut with (R := R).
Qed.

Theorem oeset_empty_decision_permut_regression :
  forall (A : Type) (order : Oeset.Rcd A) left right,
    Oeset.permut order left right ->
    rows_empty_decision left = rows_empty_decision right.
Proof.
  intros; now apply rows_empty_decision_oeset_permut with (order := order).
Qed.

Section SubqueryEnvironmentCongruenceRegression.

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

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation formula_env_equiv :=
  (@formula_expr_env_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_env_equiv :=
  (@query_expr_env_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Theorem safe_pred_not_conj_environment_regression :
  forall left_env right_env operation predicate arguments,
    Env.equiv_env T left_env right_env ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      arguments = None ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      arguments = None ->
    formula_env_equiv left_env right_env
      (FExpr_Conj operation
        (FExpr_Not (FExpr_Pred predicate arguments))
        (FExpr_Pred predicate arguments)).
Proof.
  intros left_env right_env operation predicate arguments Henv
    Hleft_safe Hright_safe.
  apply formula_expr_conj_env_congr.
  - apply formula_expr_not_env_congr.
    now apply formula_expr_pred_env_congr_safe.
  - now apply formula_expr_pred_env_congr_safe.
Qed.

Theorem table_cross_join_environment_regression :
  forall left_env right_env left_attributes left_relation
      right_attributes right_relation,
    query_env_equiv left_env right_env
      (QExpr_CrossJoin
        (@QExpr_Table T relname left_attributes left_relation)
        (@QExpr_Table T relname right_attributes right_relation)).
Proof.
  intros.
  apply query_expr_cross_join_env_congr;
    now apply query_expr_table_env_congr.
Qed.

Theorem filter_environment_regression :
  forall left_env right_env formula input,
    query_env_equiv left_env right_env input ->
    (forall row,
      formula_env_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    query_env_equiv left_env right_env (QExpr_Filter formula input).
Proof.
  intros; now apply query_expr_filter_env_congr.
Qed.

Theorem safe_exact_project_environment_regression :
  forall left_env right_env select_list input,
    query_env_equiv left_env right_env input ->
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
    query_env_equiv left_env right_env (QExpr_Project select_list input).
Proof.
  intros; now apply query_expr_project_env_congr_safe_exact.
Qed.

Theorem in_rows_truth_environment_regression :
  forall left_env right_env select_items rows,
    Env.equiv_env T left_env right_env ->
    in_rows_truth unknown value_is_null left_env select_items rows =
    in_rows_truth unknown value_is_null right_env select_items rows.
Proof.
  intros; now apply in_rows_truth_env_congr.
Qed.

Theorem exists_environment_congruence_regression :
  forall left_env right_env subquery,
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_formula left_env (FExpr_Exists subquery) outcome <->
      eval_formula right_env (FExpr_Exists subquery) outcome.
Proof.
  intros; now apply eval_formula_exists_env_congr.
Qed.

Theorem exists_constructor_environment_regression :
  forall left_env right_env subquery,
    query_env_equiv left_env right_env subquery ->
    formula_env_equiv left_env right_env (FExpr_Exists subquery).
Proof.
  intros; now apply formula_expr_exists_env_congr.
Qed.

Theorem safe_in_environment_congruence_regression :
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
Proof.
  intros; now apply eval_formula_in_env_congr_safe.
Qed.

Theorem safe_in_constructor_environment_regression :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    query_env_equiv left_env right_env subquery ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    formula_env_equiv left_env right_env (FExpr_In select_items subquery).
Proof.
  intros; now apply formula_expr_in_env_congr_safe.
Qed.

Theorem same_bag_empty_decision_regression :
  forall first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    rows_empty_decision first = rows_empty_decision second.
Proof.
  intros first second bag Hfirst Hsecond.
  exact (@query_same_rows_as_bag_empty_decision
    T first second bag Hfirst Hsecond).
Qed.

End SubqueryEnvironmentCongruenceRegression.

Print Assumptions rows_empty_decision_rel_permut.
Print Assumptions rows_empty_decision_oeset_permut.
Print Assumptions existsb_rel_permut.
Print Assumptions query_same_rows_as_bag_empty_decision.
Print Assumptions query_tuple_equal_congr.
Print Assumptions in_row_truth_env_congr.
Print Assumptions in_rows_truth_env_congr.
Print Assumptions formula_expr_conj_env_congr.
Print Assumptions formula_expr_not_env_congr.
Print Assumptions formula_expr_pred_env_congr_safe.
Print Assumptions query_expr_table_env_congr.
Print Assumptions query_expr_cross_join_env_congr.
Print Assumptions eval_filter_rows_env_congr.
Print Assumptions query_expr_filter_env_congr.
Print Assumptions project_rows_outcome_env_congr_safe_exact.
Print Assumptions query_expr_project_env_congr_safe_exact.
Print Assumptions eval_formula_exists_env_congr.
Print Assumptions formula_expr_exists_env_congr.
Print Assumptions eval_formula_in_env_congr_safe.
Print Assumptions formula_expr_in_env_congr_safe.
Print Assumptions in_rows_truth_environment_regression.
Print Assumptions exists_environment_congruence_regression.
Print Assumptions exists_constructor_environment_regression.
Print Assumptions safe_in_environment_congruence_regression.
Print Assumptions safe_in_constructor_environment_regression.
Print Assumptions safe_pred_not_conj_environment_regression.
Print Assumptions table_cross_join_environment_regression.
Print Assumptions filter_environment_regression.
Print Assumptions safe_exact_project_environment_regression.
Print Assumptions heterogeneous_empty_decision_permut_regression.
Print Assumptions list_existsb_rel_permut_regression.
Print Assumptions oeset_empty_decision_permut_regression.
Print Assumptions same_bag_empty_decision_regression.
