(******************************************************************************)
(** Regression routes for functional outer-join scheduler primitives.       **)
(******************************************************************************)

From Logos.FormalSQL Require Import CardinalityCombinators.

Check map_left_join_functional_permut.
Check map_left_join_functional_branch_permut.

Print Assumptions map_left_join_functional_permut.
Print Assumptions map_left_join_functional_branch_permut.
