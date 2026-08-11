(******************************************************************************)
(** GROUP-key support and DISTINCT multiplicity regression.                   **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import ATerms Env FTuples OrderedSet SqlBagAbstraction
  SqlQuerySemantics.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts GroupingRewriteFacts ProofAgentFacade.

Import ListNotations.
Import Tuple.

Section GenericSingleKeyBridge.

Context {T : Tuple.Rcd}.

Variable env : Env.env T.
Variable rows : list (tuple T).
Variable group_term : aggterm T.
Variables project : tuple T -> tuple T.
Variables emit : list (tuple T) -> tuple T.

Hypothesis emitted_group_is_its_projected_key :
  forall group row,
    In group (@query_make_groups T env rows [group_term]) ->
    In row group ->
    Oeset.compare (OTuple T) (project row) (emit group) = Eq.

Hypothesis projected_key_reflects_grouping_key :
  forall left right,
    Oeset.compare (OTuple T) (project left) (project right) = Eq ->
    query_grouping_key env [group_term] left =
    query_grouping_key env [group_term] right.

Example single_key_group_is_distinct_projected_support :
  bag_eq T
    (rows_bag T
      (map emit (@query_make_groups T env rows [group_term])))
    (query_distinct_bag (rows_bag T (map project rows))).
Proof.
eapply query_make_groups_single_key_projected_distinct_bag_eq;
  eassumption.
Qed.

End GenericSingleKeyBridge.

Print Assumptions query_make_groups_projected_distinct_bag_eq.
Print Assumptions query_make_groups_single_key_projected_distinct_bag_eq.
