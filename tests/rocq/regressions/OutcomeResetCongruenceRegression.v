(******************************************************************************)
(** Generic regressions for fixed-environment bag-reset outcome congruence.   **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet SqlErrorSemantics
  SqlBagAbstraction SqlOutcome SqlQueryFacts SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import OrderedQueryFacts RelationalAlgebraFacts.

Import Tuple.

Section OutcomeResetCongruenceRegression.

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

Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Theorem outcome_to_success_bags_regression :
  forall env left right,
    query_outcome_equiv env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
Proof.
intros; now apply query_expr_outcome_equiv_implies_success_bags.
Qed.

Theorem set_outcome_congruence_regression :
  forall env operation left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
Proof.
intros; now apply query_expr_set_outcome_equiv_congr.
Qed.

Theorem cross_join_outcome_congruence_regression :
  forall env left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_CrossJoin left right)
      (QExpr_CrossJoin left' right').
Proof.
intros; now apply query_expr_cross_join_outcome_equiv_congr.
Qed.

(** Error-only children are deliberately covered: neither congruence requires
    a successful child outcome or runtime-safety premise. *)
Example set_error_only_congruence_regression :
  forall env operation outputs error,
    query_outcome_equiv env
      (QExpr_Set operation
        (QExpr_Error outputs error) (QExpr_Error outputs error))
      (QExpr_Set operation
        (QExpr_Error outputs error) (QExpr_Error outputs error)).
Proof.
intros env operation outputs error.
apply query_expr_set_outcome_equiv_congr;
  apply query_expr_outcome_equiv_refl;
  exists (SqlError error); constructor.
Qed.

Example cross_join_error_only_congruence_regression :
  forall env outputs error,
    query_outcome_equiv env
      (QExpr_CrossJoin
        (QExpr_Error outputs error) (QExpr_Error outputs error))
      (QExpr_CrossJoin
        (QExpr_Error outputs error) (QExpr_Error outputs error)).
Proof.
intros env outputs error.
apply query_expr_cross_join_outcome_equiv_congr;
  apply query_expr_outcome_equiv_refl;
  exists (SqlError error); constructor.
Qed.

End OutcomeResetCongruenceRegression.

(** These commands audit that the package contributes no assumptions. *)
Print Assumptions query_expr_outcome_equiv_implies_success_bags.
Print Assumptions eval_query_expr_set_error_iff.
Print Assumptions eval_query_expr_cross_join_error_iff.
Print Assumptions query_expr_set_outcome_equiv_congr.
Print Assumptions query_expr_cross_join_outcome_equiv_congr.
