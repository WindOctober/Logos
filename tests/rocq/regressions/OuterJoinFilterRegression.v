(******************************************************************************)
(** Regression routes for operator-local outer-join list primitives.        **)
(******************************************************************************)

From Logos.FormalSQL Require Import OuterJoinFilterFacts.

Check join_matched_rows_transpose_Permutation.
Check filter_join_matched_rows_guard_left.
Check filter_join_unmatched_left_rows_guard_left.
Check filter_join_unmatched_right_rows_false.

Print Assumptions join_matched_rows_transpose_Permutation.
Print Assumptions filter_join_matched_rows_guard_left.
Print Assumptions filter_join_unmatched_left_rows_guard_left.
Print Assumptions filter_join_unmatched_right_rows_false.
