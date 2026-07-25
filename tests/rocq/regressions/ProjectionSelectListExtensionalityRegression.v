From SQLFS Require Import Env GenericInstance Interp.
From Logos.FormalSQL Require Import TNullSyntax ProofAgentFacade.
From Stdlib Require Import List.

Import ListNotations.

(** The two projections may evaluate against different input rows. *)
Lemma projection_select_list_cross_row_extensionality_regression :
  forall env left_row right_row
      (left_first left_second right_first right_second : AggTerm)
      (first_attribute second_attribute : TNullAttribute),
    Interp.interp_aggterm TNull (env_t TNull env left_row) left_first =
      Interp.interp_aggterm TNull (env_t TNull env right_row) right_first ->
    Interp.interp_aggterm TNull (env_t TNull env left_row) left_second =
      Interp.interp_aggterm TNull (env_t TNull env right_row) right_second ->
    TNullRowEq
      (TNullProjectRow env
        (SelectList [
          SelectAs left_first first_attribute;
          SelectAs left_second second_attribute]) left_row)
      (TNullProjectRow env
        (SelectList [
          SelectAs right_first first_attribute;
          SelectAs right_second second_attribute]) right_row).
Proof.
intros env left_row right_row
  left_first left_second right_first right_second
  first_attribute second_attribute Hfirst Hsecond.
apply tnull_projection_rows_eq_of_select_items.
constructor.
- cbn [SelectAs]. split; [reflexivity | exact Hfirst].
- constructor.
  + cbn [SelectAs]. split; [reflexivity | exact Hsecond].
  + constructor.
Qed.

(** A pairwise SELECT-item proof should remain linear in the list length and
    avoid reducing the concrete tuple comparator. *)
Lemma projection_select_list_extensionality_regression :
  forall env row
      (left_first left_second right_first right_second : AggTerm)
      (first_attribute second_attribute : TNullAttribute),
    Interp.interp_aggterm TNull (env_t TNull env row) left_first =
      Interp.interp_aggterm TNull (env_t TNull env row) right_first ->
    Interp.interp_aggterm TNull (env_t TNull env row) left_second =
      Interp.interp_aggterm TNull (env_t TNull env row) right_second ->
    TNullRowEq
      (TNullProjectRow env
        (SelectList [
          SelectAs left_first first_attribute;
          SelectAs left_second second_attribute]) row)
      (TNullProjectRow env
        (SelectList [
          SelectAs right_first first_attribute;
          SelectAs right_second second_attribute]) row).
Proof.
intros env row left_first left_second right_first right_second
  first_attribute second_attribute Hfirst Hsecond.
apply tnull_projection_rows_eq_of_select_items.
constructor.
- cbn [SelectAs]. split; [reflexivity | exact Hfirst].
- constructor.
  + cbn [SelectAs]. split; [reflexivity | exact Hsecond].
  + constructor.
Qed.

Print Assumptions tnull_projection_rows_eq_of_select_items.
Print Assumptions projection_select_list_cross_row_extensionality_regression.
Print Assumptions projection_select_list_extensionality_regression.
