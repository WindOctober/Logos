From Logos.FormalSQL Require Import RelationalAlgebraFacts.
From Stdlib Require Import List.

Example support_filter_reached_properness_regression :
  forall A B (R : A -> B -> Prop)
      (left_keep : A -> bool) (right_keep : B -> bool) left right,
    list_support_rel R left right ->
    (forall left_row right_row,
      R left_row right_row ->
      left_keep left_row = right_keep right_row) ->
    list_support_rel R
      (filter left_keep left) (filter right_keep right).
Proof.
intros; now apply list_support_rel_filter_transport.
Qed.

Print Assumptions support_filter_reached_properness_regression.
