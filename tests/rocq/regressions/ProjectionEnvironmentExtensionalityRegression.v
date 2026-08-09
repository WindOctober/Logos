(******************************************************************************)
(** Canonical typed scalar-list environment extensionality regression.        **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet SqlOutcome
  SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import SubqueryFacts.

Import Tuple.

Section CanonicalScalarEnvironmentExtensionality.

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

Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation scalar_env_equiv :=
  (@scalar_expr_env_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule ScalarResultValue).

(** Pairwise environment equivalence for the typed value expressions preserves
    the complete ordered value-list relation, including the exact first error.
    The statement therefore composes directly with typed projection. *)
Lemma scalar_value_list_environment_extensionality_regression :
  forall left_env right_env expressions,
    Forall (scalar_env_equiv left_env right_env) expressions ->
    forall outcome,
      eval_scalar_values left_env expressions outcome <->
      eval_scalar_values right_env expressions outcome.
Proof.
intros left_env right_env expressions Hequiv.
induction Hequiv as [|expression expressions Hhead _ IH]; intro outcome.
- split; intro Heval; inversion Heval; constructor.
- split; intro Heval; inversion Heval; subst.
  + apply EScalarValues_HeadError.
    now apply (proj1 (Hhead (SqlError error))).
  + eapply EScalarValues_Cons.
    * now apply (proj1 (Hhead (SqlSuccess value0))).
    * now apply (proj1 (IH tail)).
  + apply EScalarValues_HeadError.
    now apply (proj2 (Hhead (SqlError error))).
  + eapply EScalarValues_Cons.
    * now apply (proj2 (Hhead (SqlSuccess value0))).
    * now apply (proj2 (IH tail)).
Qed.

End CanonicalScalarEnvironmentExtensionality.

Print Assumptions scalar_value_list_environment_extensionality_regression.
