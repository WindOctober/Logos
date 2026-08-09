From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula
  SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import GroupedFilterOutcomeFacts.
From Stdlib Require Import List String.

Import ListNotations.
Import Tuple.
Open Scope string_scope.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Definition regression_group_env
    (env : Env.env T) (group_terms : list (@aggterm T))
    (group : list (tuple T)) : Env.env T :=
  env_g T env (@Group_By T group_terms) group.

(** This composes the two public bridges exactly as a proof agent does.  The
    row decision remains [Bool.is_true] of the interpreted Bool3 predicate;
    the result is [List.filter], so duplicate accepted occurrences and their
    input order are retained. *)
Theorem predicate_filter_exact_regression :
  forall env predicate arguments (expected : tuple T -> list (value T)) rows,
    (forall row,
      In row rows ->
      @scalar_value_list_exact_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule (env_t T env row) arguments (expected row)) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env (SExpr_Pred predicate arguments) rows outcome <->
      outcome = SqlSuccess
        (List.filter
          (fun row =>
            Bool.is_true (B T)
              (interp_predicate T predicate (expected row)))
          rows).
Proof.
  intros env predicate arguments expected rows Hsafe outcome.
  apply eval_filter_rows_acceptance_exact.
  intros row Hin.
  apply scalar_expr_pred_acceptance_exact_safe.
  now apply Hsafe.
Qed.

(** A rejected group never reaches scalar SELECT projection, while both
    aggregate-finalization phases and the HAVING decision are still exact. *)
Theorem all_rejected_having_skips_projection_regression :
  forall env select_list group_terms having groups,
    (forall group,
      In group groups ->
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) select_list = None /\
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        (regression_group_env env group_terms group) having = None /\
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (regression_group_env env group_terms group) having false) ->
    forall outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env select_list group_terms having groups outcome <->
      outcome = SqlSuccess [].
Proof.
  intros env select_list group_terms having groups Hsafe.
  induction groups as [|group groups IH]; intro outcome.
  - split; intro Heval.
    + inversion Heval; reflexivity.
    + subst outcome; constructor.
  - destruct (Hsafe group (or_introl eq_refl)) as
      [Hselect_aggregates [Hhaving_aggregates Hexact]].
    destruct Hexact as
      [[truth [Htruth Htruth_false]] [Hsuccess Hscalar_error]].
    assert (Htail : forall other,
      In other groups ->
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms other) select_list = None /\
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        (regression_group_env env group_terms other) having = None /\
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (regression_group_env env group_terms other) having false).
    { intros other Hin; apply Hsafe; now right. }
    unfold regression_group_env in Hselect_aggregates,
      Hhaving_aggregates, Htruth, Htruth_false, Hsuccess, Hscalar_error.
    split; intro Heval.
    + inversion Heval; subst.
      * congruence.
      * congruence.
      * exfalso; eapply Hscalar_error; eassumption.
      * match goal with
        | Hgroups : context [eval_groups_outcome] |- _ =>
            apply (proj1 (IH Htail _)) in Hgroups;
            exact Hgroups
        end.
      * match goal with
        | Hhaving : context [eval_scalar_boolean_expr_outcome],
          Htrue : Bool.is_true (B T) ?observed = true |- _ =>
            specialize (Hsuccess observed Hhaving); congruence
        end.
      * match goal with
        | Hhaving : context [eval_scalar_boolean_expr_outcome],
          Htrue : Bool.is_true (B T) ?observed = true |- _ =>
            specialize (Hsuccess observed Hhaving); congruence
        end.
    + subst outcome.
      eapply EGroups_HavingFalse with (truth := truth).
      * exact Hselect_aggregates.
      * exact Hhaving_aggregates.
      * exact Htruth.
      * exact Htruth_false.
      * apply (proj2 (IH Htail (SqlSuccess []))); reflexivity.
Qed.

Theorem eager_redundant_right_conjunct_regression :
  forall site_rows env expressions redundant decide,
    (forall expression,
      In expression expressions ->
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        env expression (decide expression)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      redundant (decide redundant) ->
    (scalar_acceptance_fold And_F (map decide expressions) = true ->
      decide redundant = true) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_ConjList site_rows And_F (expressions ++ [redundant]))
      (scalar_acceptance_fold And_F (map decide expressions)).
Proof.
  intros site_rows env expressions redundant decide
    Hexpressions Hredundant Himplied.
  now eapply scalar_expr_conj_list_redundant_operand_acceptance_exact.
Qed.

End PredicateFilterExactRegression.

Check query_make_groups_projected_bag_eq_of_support_rel.
Check query_make_groups_heterogeneous_projected_bag_eq.

Print Assumptions query_make_groups_heterogeneous_projected_bag_eq.
