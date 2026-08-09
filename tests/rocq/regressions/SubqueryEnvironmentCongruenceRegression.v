(******************************************************************************)
(** Typed regressions for correlated-subquery environment congruence.        **)
(******************************************************************************)

From Stdlib Require Import List String.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula
  FTuples ListPermut OrderedSet SqlErrorSemantics SqlOutcome SqlQueryContexts
  SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import SubqueryFacts.

Import Tuple.
Import ListNotations.
Open Scope string_scope.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_scalar_value :=
  (@eval_scalar_value_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation scalar_boolean_env_equiv :=
  (@scalar_expr_env_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule ScalarResultBoolean).

Local Abbreviation query_env_equiv :=
  (@query_expr_env_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** The typed list conjunction retains the shared Boolean schedule.  Its
    arguments are related by the complete scalar-values outcome relation, so
    argument-side scalar-subquery errors are preserved as well as successes. *)
Theorem typed_pred_not_conj_environment_regression :
  forall left_env right_env site_rows operation predicate arguments,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    scalar_boolean_env_equiv left_env right_env
      (SExpr_ConjList site_rows operation
        [SExpr_Not (SExpr_Pred predicate arguments);
         SExpr_Pred predicate arguments]).
Proof.
intros left_env right_env site_rows operation predicate arguments Harguments.
apply scalar_expr_conj_list_env_congr.
constructor.
- apply scalar_expr_not_env_congr.
  now apply scalar_expr_pred_env_congr_safe.
- constructor; [now apply scalar_expr_pred_env_congr_safe|constructor].
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
  forall left_env right_env expression input,
    query_env_equiv left_env right_env input ->
    (forall row,
      scalar_boolean_env_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) expression) ->
    query_env_equiv left_env right_env (QExpr_Filter expression input).
Proof.
  intros; now apply query_expr_filter_env_congr.
Qed.

Theorem typed_in_environment_congruence_regression :
  forall left_env right_env arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_scalar_boolean left_env (SExpr_In arguments subquery) outcome <->
      eval_scalar_boolean right_env (SExpr_In arguments subquery) outcome.
Proof.
  intros; now apply eval_scalar_boolean_in_env_congr_safe.
Qed.

Theorem typed_in_constructor_environment_regression :
  forall left_env right_env arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    query_env_equiv left_env right_env subquery ->
    scalar_boolean_env_equiv left_env right_env
      (SExpr_In arguments subquery).
Proof.
  intros; now apply scalar_expr_in_env_congr_safe.
Qed.

(** EXISTS uses its target-list-eliding observation, not full row outcomes.
    The environments below may already contain an outer correlated row. *)
Theorem exists_correlated_demand_regression :
  forall left right outer_env outer_row,
    @query_expr_global_exists_outcome_equiv
      T relname basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule left right ->
    forall outcome,
      eval_scalar_boolean (Env.env_t T outer_env outer_row)
        (SExpr_Exists left) outcome <->
      eval_scalar_boolean (Env.env_t T outer_env outer_row)
        (SExpr_Exists right) outcome.
Proof.
intros left right outer_env outer_row Hequiv outcome.
apply eval_scalar_boolean_exists_subquery_congr.
intro observed; now apply Hequiv.
Qed.

Theorem exists_constructor_environment_regression :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    scalar_boolean_env_equiv left_env right_env (SExpr_Exists subquery).
Proof.
  intros; now apply scalar_expr_exists_env_congr.
Qed.

(** A scalar-subquery context demands typed complete-row equivalence, in
    contrast with the EXISTS context above. *)
Theorem scalar_subquery_correlated_context_regression :
  forall result_type null_value left right outer_env outer_row,
    @query_expr_global_typed_outcome_equiv
      T relname basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule left right ->
    forall outcome,
      eval_scalar_value (Env.env_t T outer_env outer_row)
        (SExpr_Subquery result_type null_value left) outcome <->
      eval_scalar_value (Env.env_t T outer_env outer_row)
        (SExpr_Subquery result_type null_value right) outcome.
Proof.
intros result_type null_value left right outer_env outer_row Hequiv outcome.
exact (@eval_scalar_value_context_correlated_congr
  T relname basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null boolean_schedule
  (@SCtx_Subquery T relname result_type null_value)
  left right outer_env outer_row outcome Hequiv).
Qed.

Theorem output_value_semantic_congruence_regression :
  forall outputs left right,
    query_row_has_outputs outputs left ->
    Oeset.compare (OTuple T) left right = Eq ->
    @query_row_output_values T outputs left =
    @query_row_output_values T outputs right.
Proof.
  intros; now apply query_row_output_values_congr.
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
Print Assumptions query_row_output_values_congr.
Print Assumptions in_row_truth_congr.
Print Assumptions scalar_expr_conj_list_env_congr.
Print Assumptions scalar_expr_not_env_congr.
Print Assumptions scalar_expr_pred_env_congr_safe.
Print Assumptions query_expr_table_env_congr.
Print Assumptions query_expr_cross_join_env_congr.
Print Assumptions eval_filter_rows_env_congr.
Print Assumptions query_expr_filter_env_congr.
Print Assumptions eval_scalar_boolean_exists_env_congr.
Print Assumptions scalar_expr_exists_env_congr.
Print Assumptions eval_scalar_boolean_in_env_congr_safe.
Print Assumptions scalar_expr_in_env_congr_safe.
Print Assumptions eval_scalar_value_context_correlated_congr.
Print Assumptions typed_pred_not_conj_environment_regression.
Print Assumptions typed_in_environment_congruence_regression.
Print Assumptions exists_correlated_demand_regression.
Print Assumptions scalar_subquery_correlated_context_regression.
Print Assumptions heterogeneous_empty_decision_permut_regression.
Print Assumptions list_existsb_rel_permut_regression.
Print Assumptions oeset_empty_decision_permut_regression.
Print Assumptions same_bag_empty_decision_regression.
Check quantified_rows_truth_congr_of_bag_eq.
Check scalar_expr_quant_acceptance_exact_of_fixed_truth.
Print Assumptions quantified_rows_truth_congr_of_bag_eq.
Print Assumptions scalar_expr_quant_acceptance_exact_of_fixed_truth.
