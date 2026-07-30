From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula
  SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import GroupedFilterOutcomeFacts.
From Stdlib Require Import List.

Import ListNotations.
Import Tuple.

Section PredicateFilterExactRegression.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Definition regression_group_env
    (env : Env.env T) (group_terms : list (@aggterm T))
    (group : list (tuple T)) : Env.env T :=
  env_g T env (@Group_By T group_terms) group.

(** This composes the two public bridges exactly as a proof agent does.  The
    row decision remains [Bool.is_true] of the interpreted Bool3 predicate;
    the result is [List.filter], so duplicate accepted occurrences and their
    input order are retained. *)
Theorem predicate_filter_exact_regression :
  forall env predicate arguments rows,
    (forall row,
      In row rows ->
      first_runtime_error
        (@eval_aggterm_runtime_error T
          symbol_runtime_error aggregate_runtime_error (env_t T env row))
        arguments = None) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env (FExpr_Pred predicate arguments) rows outcome <->
      outcome = SqlSuccess
        (List.filter
          (fun row =>
            Bool.is_true (B T)
              (interp_predicate T predicate
                (map (@interp_aggterm T (env_t T env row)) arguments)))
          rows).
Proof.
  intros env predicate arguments rows Hsafe outcome.
  apply eval_filter_rows_acceptance_exact.
  intros row Hin.
  apply formula_pred_acceptance_exact_safe.
  now apply Hsafe.
Qed.

(** A rejected group never reaches scalar SELECT projection, while both
    aggregate-finalization phases and the HAVING decision are still exact. *)
Theorem all_rejected_having_skips_projection_regression :
  forall env select_list group_terms having groups,
    (forall group,
      In group groups ->
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) select_list = None /\
      @eval_formula_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (regression_group_env env group_terms group) having false) ->
    forall outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env select_list group_terms having groups outcome <->
      outcome = SqlSuccess [].
Proof.
  apply eval_groups_all_rejected_outcome_exact.
Qed.

Theorem eager_redundant_right_conjunct_regression :
  forall env left right left_accepted right_accepted,
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env left left_accepted ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env right right_accepted ->
    (left_accepted = true -> right_accepted = true) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Conj And_F left right) left_accepted.
Proof.
  intros env left right left_accepted right_accepted
    Hleft Hright Himplied.
  eapply formula_and_redundant_right_acceptance_exact
    with (right_accepted := right_accepted); eassumption.
Qed.

End PredicateFilterExactRegression.

Check query_make_groups_projected_bag_eq_of_support_rel.
Check query_make_groups_heterogeneous_projected_bag_eq.

Print Assumptions query_make_groups_heterogeneous_projected_bag_eq.
