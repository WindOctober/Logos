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

Definition error_test_int32_one : int32.
Proof.
refine (Int32 1 _); unfold int32_min, int32_max; lia.
Defined.

Definition error_test_int32_zero : int32.
Proof.
refine (Int32 0 _); unfold int32_min, int32_max; lia.
Defined.

Definition ErrorTestCstInt32 (value : int32) : AggTerm :=
  AExpr (Constant (NullValues.Value_int32 (Some value))).

Definition division_by_zero_query : Query :=
  Pi
    (SelectList [
      SelectAs
        (AScalarCall (ScalarDivide ScalarInt32)
          [ErrorTestCstInt32 error_test_int32_one;
           ErrorTestCstInt32 error_test_int32_zero])
        (AttrInt32 "quotient")
    ])
    EmptyTuple.

Lemma division_by_zero_query_raises_data_exception :
  query_runtime_error_in_state init_db division_by_zero_query =
  Some (DataException DivisionByZero).
Proof.
unfold query_runtime_error_in_state, query_runtime_error_in_env,
  division_by_zero_query, Pi, EmptyTuple.
cbn [eval_query_runtime_error].
rewrite eval_query_unfold.
unfold SqlErrorSemantics.BTupleT.
destruct
  (Febag.elements_singleton
    (Fecol.CBag (CTuple TNull)) (empty_tuple TNull))
  as [row [_ Helements]].
rewrite Helements.
unfold eval_select_list_runtime_error, eval_select_runtime_error,
  SelectList, SelectAs, ErrorTestCstInt32, AExpr, Constant.
cbn [eval_aggterm_runtime_error eval_funterm_runtime_error
  Interp.interp_aggterm Interp.interp_funterm].
reflexivity.
Qed.

Lemma division_by_zero_query_not_equivalent_to_itself :
  ~ query_equiv init_db division_by_zero_query division_by_zero_query.
Proof.
apply query_runtime_error_not_equiv_left with
  (error := DataException DivisionByZero).
exact division_by_zero_query_raises_data_exception.
Qed.
