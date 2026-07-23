From SQLFS Require Import SqlOutcome SqlErrorSemantics SqlAlgebra SqlSyntax GenericInstance Values FiniteBag FiniteCollection FTuples.
From Logos.FormalSQL Require Import TNullSyntax.
From Stdlib Require Import List String ZArith Lia.

Import ListNotations.
Import Tuple.
Open Scope string_scope.
Open Scope Z_scope.

(** Query-level consequences of the success-only equivalence definition. *)

Lemma query_runtime_error_not_equiv_left :
  forall db q1 q2 error,
    query_runtime_error_in_state db q1 = Some error ->
    ~ query_equiv db q1 q2.
Proof.
intros db q1 q2 error Herror Hequiv.
apply query_equiv_implies_success in Hequiv.
destruct Hequiv as [Hsuccess _].
unfold query_succeeds in Hsuccess.
rewrite Herror in Hsuccess; discriminate.
Qed.

Lemma query_runtime_error_not_equiv_right :
  forall db q1 q2 error,
    query_runtime_error_in_state db q2 = Some error ->
    ~ query_equiv db q1 q2.
Proof.
intros db q1 q2 error Herror Hequiv.
apply query_equiv_implies_success in Hequiv.
destruct Hequiv as [_ Hsuccess].
unfold query_succeeds in Hsuccess.
rewrite Herror in Hsuccess; discriminate.
Qed.
