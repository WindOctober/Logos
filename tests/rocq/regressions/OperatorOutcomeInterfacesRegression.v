(******************************************************************************)
(** Regressions for generic operator outcome/safety interfaces.              **)
(******************************************************************************)

From Stdlib Require Import List NArith.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet Formula Projection SqlErrorSemantics
  SqlBagAbstraction SqlOutcome SqlQueryContexts SqlQueryFacts SqlQuerySemantics
  SqlQuerySyntax.
From Logos.FormalSQL Require Import
  OrderedQueryFacts QueryCardinality RelationalAlgebraFacts.

Import Tuple.

Section OperatorOutcomeInterfacesRegression.

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

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_safe :=
  (query_expr_runtime_safe basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Theorem safe_inhabited_query_has_success_regression :
  forall env query,
    query_safe env query ->
    (exists outcome, eval_query env query outcome) ->
    query_has_success env query.
Proof.
intros; now eapply query_expr_has_success_of_runtime_safe_and_outcome.
Qed.

Theorem filter_rows_total_regression :
  forall env formula rows,
    (forall row,
      In row rows ->
      exists outcome, eval_formula (env_t T env row) formula outcome) ->
    exists outcome, eval_filter_rows env formula rows outcome.
Proof.
intros; now eapply eval_filter_rows_has_outcome_of_formula_total.
Qed.

Theorem filter_query_total_regression :
  forall env formula input,
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      forall row,
        In row input_rows ->
        exists outcome, eval_formula (env_t T env row) formula outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Filter formula input) outcome.
Proof.
intros; now eapply query_expr_filter_has_outcome_of_formula_total.
Qed.

Theorem set_runtime_safe_regression :
  forall env operation left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_Set operation left right).
Proof.
intros; now apply query_expr_set_runtime_safe.
Qed.

Theorem cross_join_runtime_safe_regression :
  forall env left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_CrossJoin left right).
Proof.
intros; now apply query_expr_cross_join_runtime_safe.
Qed.

Theorem set_success_regression :
  forall env operation left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_Set operation left right).
Proof.
intros; now apply query_expr_set_has_success.
Qed.

Theorem cross_join_success_regression :
  forall env left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_CrossJoin left right).
Proof.
intros; now apply query_expr_cross_join_has_success.
Qed.

Theorem set_inhabited_regression :
  forall env operation left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_Set operation left right) outcome.
Proof.
intros; now apply query_expr_set_has_outcome.
Qed.

Theorem cross_join_inhabited_regression :
  forall env left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_CrossJoin left right) outcome.
Proof.
intros; now apply query_expr_cross_join_has_outcome.
Qed.

Theorem project_runtime_safe_regression :
  forall env (select_list : @_select_list T) input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_safe env input ->
    query_safe env (QExpr_Project select_list input).
Proof.
intros; now apply query_expr_project_runtime_safe.
Qed.

Theorem project_inhabited_regression :
  forall env (select_list : @_select_list T) input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Project select_list input) outcome.
Proof.
intros; now apply query_expr_project_has_outcome_safe.
Qed.

(** This regression deliberately speaks only about support occurrences; no
    query shape or benchmark-specific grouping key is present. *)
Theorem boolean_separator_disjoint_regression :
  forall (left right : SqlBagAbstraction.bagT T)
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
Proof.
intros left right separate Hleft Hright row.
exact
  (@bag_occurrences_disjoint_of_boolean_separator
    T left right separate Hleft Hright row).
Qed.

End OperatorOutcomeInterfacesRegression.

(** The generic package must not introduce assumptions. *)
Print Assumptions query_expr_has_success_of_runtime_safe_and_outcome.
Print Assumptions eval_filter_rows_has_outcome_of_formula_total.
Print Assumptions query_expr_filter_has_outcome_of_formula_total.
Print Assumptions query_expr_set_runtime_safe.
Print Assumptions query_expr_cross_join_runtime_safe.
Print Assumptions query_expr_set_has_success.
Print Assumptions query_expr_cross_join_has_success.
Print Assumptions query_expr_set_has_outcome.
Print Assumptions query_expr_cross_join_has_outcome.
Print Assumptions query_expr_project_runtime_safe.
Print Assumptions query_expr_project_has_outcome_safe.
Print Assumptions bag_occurrences_disjoint_of_boolean_separator.
Print Assumptions tnull_predicate_keep_proper.
