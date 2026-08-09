(******************************************************************************)
(** Canonical typed SELECT-list extensionality regressions.                    **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet SqlOutcome
  SqlQueryContexts SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import ProofAgentFacade.

Import ListNotations.
Import Tuple.

Section CanonicalTypedSelectListExtensionality.

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

Variables left_first left_second right_first right_second :
  scalar_expr T relname ScalarResultValue.
Variables first_attribute second_attribute : attribute T.

Local Abbreviation scalar_equiv :=
  (@scalar_expr_global_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule ScalarResultValue).

Local Abbreviation select_equiv :=
  (@scalar_select_list_global_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null boolean_schedule).

Definition canonical_left_select : query_select_list T relname :=
  [(left_first, first_attribute); (left_second, second_attribute)].

Definition canonical_right_select : query_select_list T relname :=
  [(right_first, first_attribute); (right_second, second_attribute)].

Lemma canonical_scalar_select_list_extensionality_regression :
  scalar_equiv left_first right_first ->
  scalar_equiv left_second right_second ->
  select_equiv canonical_left_select canonical_right_select.
Proof.
intros Hfirst Hsecond.
unfold canonical_left_select, canonical_right_select, select_equiv,
  scalar_select_list_global_outcome_equiv.
constructor.
- split; [reflexivity|exact Hfirst].
- constructor.
  + split; [reflexivity|exact Hsecond].
  + constructor.
Qed.

(** The list-level fact lifts through the sole typed query projection and
    preserves both successful ordered rows and every exact SQL error. *)
Lemma canonical_query_projection_extensionality_regression :
  scalar_equiv left_first right_first ->
  scalar_equiv left_second right_second ->
  forall input,
    @query_expr_global_typed_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule
      (QExpr_Project canonical_left_select input)
      (QExpr_Project canonical_right_select input).
Proof.
intros Hfirst Hsecond input.
apply query_expr_project_select_global_typed_congr.
now apply canonical_scalar_select_list_extensionality_regression.
Qed.

End CanonicalTypedSelectListExtensionality.

Print Assumptions canonical_scalar_select_list_extensionality_regression.
Print Assumptions canonical_query_projection_extensionality_regression.
