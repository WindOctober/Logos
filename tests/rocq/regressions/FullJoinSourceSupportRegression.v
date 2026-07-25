Set Implicit Arguments.

From Stdlib Require Import List SetoidList.
From SQLFS Require Import
  FlatData OrderedSet SqlBagAbstraction SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import RelationalAlgebraFacts.

Import Tuple.

Section FullJoinSourceSupportRegression.

Context {T : Tuple.Rcd}.

Example native_full_join_source_classification :
  forall (matches : tuple T -> tuple T -> bool) lefts rights output,
    In output
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun left => map (matches left) rights) lefts)) ->
    (exists left right,
      In left lefts /\
      In right rights /\
      matches left right = true /\
      JoinSourceMatched T (join_tuple T left right) = output) \/
    (exists left,
      In left lefts /\
      (forall right, In right rights -> matches left right = false) /\
      JoinSourceLeft T left = output) \/
    (exists right,
      In right rights /\
      (forall left, In left lefts -> matches left right = false) /\
      JoinSourceRight T right = output).
Proof.
intros matches lefts rights output Houtput.
now apply (proj1
  (query_join_full_sources_member_iff matches lefts rights output)).
Qed.

Example native_full_join_matched_source :
  forall (matches : tuple T -> tuple T -> bool) lefts rights left right,
    In left lefts ->
    In right rights ->
    matches left right = true ->
    In (JoinSourceMatched T (join_tuple T left right))
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun row => map (matches row) rights) lefts)).
Proof.
intros matches lefts rights left right Hleft Hright Hmatch.
apply (proj2
  (query_join_full_sources_member_iff matches lefts rights
    (JoinSourceMatched T (join_tuple T left right)))).
left; exists left, right; repeat split; try assumption.
Qed.

Example native_full_join_left_padded_source :
  forall (matches : tuple T -> tuple T -> bool) lefts rights left,
    In left lefts ->
    (forall right, In right rights -> matches left right = false) ->
    In (JoinSourceLeft T left)
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun row => map (matches row) rights) lefts)).
Proof.
intros matches lefts rights left Hleft Hnone.
apply (proj2
  (query_join_full_sources_member_iff matches lefts rights
    (JoinSourceLeft T left))).
right; left; exists left; repeat split; assumption.
Qed.

Example native_full_join_right_padded_source :
  forall (matches : tuple T -> tuple T -> bool) lefts rights right,
    In right rights ->
    (forall left, In left lefts -> matches left right = false) ->
    In (JoinSourceRight T right)
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun left => map (matches left) rights) lefts)).
Proof.
intros matches lefts rights right Hright Hnone.
apply (proj2
  (query_join_full_sources_member_iff matches lefts rights
    (JoinSourceRight T right))).
right; right; exists right; repeat split; assumption.
Qed.

(** The input relations are intentionally abstract rather than tuple equality:
    this locks the projected/grouped-input use case while the existing tests
    above separately lock all three native FULL source branches. *)
Theorem native_full_join_heterogeneous_projected_support :
  forall (left_rel right_rel output_rel : tuple T -> tuple T -> Prop)
      (left_match right_match : tuple T -> tuple T -> bool)
      (left_emit right_emit : query_join_source T -> tuple T)
      left_rows left_rows' right_rows right_rows',
    list_support_rel left_rel left_rows left_rows' ->
    list_support_rel right_rel right_rows right_rows' ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      left_match left right = right_match left' right') ->
    (forall left left' right right',
      left_rel left left' ->
      right_rel right right' ->
      output_rel
        (left_emit
          (JoinSourceMatched T (join_tuple T left right)))
        (right_emit
          (JoinSourceMatched T (join_tuple T left' right')))) ->
    (forall left left',
      left_rel left left' ->
      output_rel
        (left_emit (JoinSourceLeft T left))
        (right_emit (JoinSourceLeft T left'))) ->
    (forall right right',
      right_rel right right' ->
      output_rel
        (left_emit (JoinSourceRight T right))
        (right_emit (JoinSourceRight T right'))) ->
    list_support_rel output_rel
      (map left_emit
        (query_join_sources T QueryJoinFull left_rows right_rows
          (map (fun left => map (left_match left) right_rows) left_rows)))
      (map right_emit
        (query_join_sources T QueryJoinFull left_rows' right_rows'
          (map
            (fun left => map (right_match left) right_rows') left_rows'))).
Proof.
intros left_rel right_rel output_rel left_match right_match
  left_emit right_emit left_rows left_rows' right_rows right_rows'
  Hleft Hright Hmatch Hmatched Hunmatched_left Hunmatched_right.
eapply query_join_full_projected_support_rel; eassumption.
Qed.

(** Once a later reset has made both row lists semantic sets, the same
    bidirectional support interface recovers exact bag equality. *)
Theorem nodup_semantic_support_rows_bag_regression :
  forall (left right : list (tuple T)),
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left ->
    NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      right ->
    bag_eq T (rows_bag T left) (rows_bag T right).
Proof.
intros left right Hsupport Hleft Hright.
eapply rows_bag_eq_of_nodup_support_rel; eassumption.
Qed.

Print Assumptions query_join_full_projected_support_rel.
Print Assumptions native_full_join_heterogeneous_projected_support.
Print Assumptions rows_bag_eq_of_nodup_support_rel.
Print Assumptions nodup_semantic_support_rows_bag_regression.

End FullJoinSourceSupportRegression.
