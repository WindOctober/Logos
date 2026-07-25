(******************************************************************************)
(** Regressions for reusable finite-bag homomorphism and singleton-cross APIs. *)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlBagAbstraction
  SqlQueryFacts SqlQuerySemantics SqlQuerySyntax SqlSyntax.
From Logos.FormalSQL Require Import RelationalAlgebraFacts.

Import Tuple.

Section BagHomomorphismInterfacesRegression.

Context {T : Tuple.Rcd}.

Local Definition bagT := Febag.bag (Fecol.CBag (CTuple T)).

Example filter_union_regression :
  forall (keep : tuple T -> bool) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) keep
        (query_set_bag Union left right))
      (query_set_bag Union
        (Febag.filter (Fecol.CBag (CTuple T)) keep left)
        (Febag.filter (Fecol.CBag (CTuple T)) keep right)).
Proof.
intros; now apply query_bag_filter_union.
Qed.

Example filter_map_fusion_regression :
  forall (keep : tuple T -> bool) mapping (bag : bagT),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      Oeset.compare (OTuple T) (mapping left) (mapping right) = Eq) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) keep
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping bag))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping
        (Febag.filter (Fecol.CBag (CTuple T))
          (fun row => keep (mapping row)) bag)).
Proof.
intros; now apply query_bag_filter_map_fusion.
Qed.

Example pairwise_map_cardinal_regression :
  forall (left_map right_map : tuple T -> tuple T) (left right : bagT),
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
      Febag.cardinal (Fecol.CBag (CTuple T)) right ->
    (forall left_row right_row,
      In left_row (Febag.elements (Fecol.CBag (CTuple T)) left) ->
      In right_row (Febag.elements (Fecol.CBag (CTuple T)) right) ->
      Oeset.compare (OTuple T) (left_map left_row) (right_map right_row) =
        Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        left_map left)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        right_map right).
Proof.
intros; now apply query_bag_map_pairwise_equiv_of_cardinal.
Qed.

Example right_singleton_cross_regression :
  forall (left : bagT) right_row,
    bag_eq T
      (query_cross_join_bag left
        (Febag.singleton (Fecol.CBag (CTuple T)) right_row))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun left_row => join_tuple T left_row right_row) left).
Proof.
intros; now apply query_cross_join_bag_singleton_right_map.
Qed.

End BagHomomorphismInterfacesRegression.

Check query_bag_map_union.
Check query_bag_map_congr.
Check query_bag_filter_commute.

Print Assumptions query_bag_filter_union.
Print Assumptions query_bag_map_union.
Print Assumptions query_bag_map_congr.
Print Assumptions query_bag_filter_commute.
Print Assumptions query_bag_filter_map_fusion.
Print Assumptions query_bag_map_pairwise_equiv_of_cardinal.
Print Assumptions query_cross_join_bag_singleton_right_map.
