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

End PredicateFilterExactRegression.
