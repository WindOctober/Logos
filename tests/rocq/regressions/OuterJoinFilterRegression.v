From Logos.FormalSQL Require Import OuterJoinFilterFacts.
From Stdlib Require Import List Sorting.Permutation.

Import ListNotations.

(** The regression keeps duplicate left and right occurrences symbolic; the
    exact list theorem, rather than set support, performs the rewrite. *)
Example full_to_left_null_rejecting_guard_regression :
  forall (A B C : Type) (join : A -> B -> C)
      (pad_left : A -> C) (pad_right : B -> C)
      (accept : A -> B -> bool) (guard_left : A -> bool)
      (guard_output : C -> bool) left right,
    (forall left_row right_row,
      guard_output (join left_row right_row) = guard_left left_row) ->
    (forall left_row,
      guard_output (pad_left left_row) = guard_left left_row) ->
    (forall right_row, guard_output (pad_right right_row) = false) ->
    filter guard_output
      (full_outer_scheduler_rows
        join pad_left pad_right accept left right) =
    left_outer_scheduler_rows join pad_left accept
      (filter guard_left left) right.
Proof.
intros; now apply full_outer_filter_to_left_outer_exact.
Qed.

Print Assumptions full_to_left_null_rejecting_guard_regression.

Example left_right_outer_swap_regression :
  forall (A B C : Type) (join : A -> B -> C) (pad_left : A -> C)
      (accept : A -> B -> bool) left right,
    Permutation
      (left_outer_scheduler_rows join pad_left accept left right)
      (right_outer_scheduler_rows
        (fun right_row left_row => join left_row right_row)
        pad_left
        (fun right_row left_row => accept left_row right_row)
        right left).
Proof.
intros; apply left_right_outer_scheduler_swap_Permutation.
Qed.

Print Assumptions left_right_outer_swap_regression.

Example left_outer_null_rejection_regression :
  forall (A B C : Type) (join : A -> B -> C) (pad_left : A -> C)
      (accept : A -> B -> bool) (guard_output : C -> bool) left right,
    (forall left_row, guard_output (pad_left left_row) = false) ->
    filter guard_output
      (left_outer_scheduler_rows join pad_left accept left right) =
    filter guard_output (join_matched_rows join accept left right).
Proof.
intros; now apply left_outer_null_reject_to_inner_exact.
Qed.

Print Assumptions left_outer_null_rejection_regression.
