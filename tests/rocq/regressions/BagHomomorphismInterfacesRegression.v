(******************************************************************************)
(** Regressions for reusable finite-bag homomorphism interfaces. *)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  ListPermut OrderedSet FiniteSet FiniteBag FiniteCollection FlatData SqlBagAbstraction
  SqlQueryFacts SqlQuerySemantics SqlQuerySyntax SqlSyntax.
From Logos.FormalSQL Require Import RelationalAlgebraFacts.

Import Tuple.

Section RelationalPermutationInterfacesRegression.

Context {A B C D E F : Type}.

Example heterogeneous_flat_map_permutation_regression :
  forall (R : A -> B -> Prop) (S : C -> D -> Prop)
      (left_block : A -> list C) (right_block : B -> list D)
      left right,
    _permut R left right ->
    (forall left_value right_value,
      In left_value left ->
      In right_value right ->
      R left_value right_value ->
      _permut S (left_block left_value) (right_block right_value)) ->
    _permut S
      (flat_map left_block left)
      (flat_map right_block right).
Proof.
intros R S left_block right_block left right Houter Hblocks.
eapply list_flat_map_permut_rel; [exact Houter|exact Hblocks].
Qed.

Example heterogeneous_theta_permutation_regression :
  forall (outer_rel : A -> B -> Prop)
      (inner_rel : C -> D -> Prop)
      (output_rel : E -> F -> Prop)
      (left_accept : A -> C -> bool)
      (right_accept : B -> D -> bool)
      (left_emit : A -> C -> E)
      (right_emit : B -> D -> F)
      left_outer right_outer left_inner right_inner,
    _permut outer_rel left_outer right_outer ->
    _permut inner_rel left_inner right_inner ->
    (forall left_row right_row left_value right_value,
      In left_row left_outer ->
      In right_row right_outer ->
      In left_value left_inner ->
      In right_value right_inner ->
      outer_rel left_row right_row ->
      inner_rel left_value right_value ->
      left_accept left_row left_value =
        right_accept right_row right_value) ->
    (forall left_row right_row left_value right_value,
      In left_row left_outer ->
      In right_row right_outer ->
      In left_value left_inner ->
      In right_value right_inner ->
      outer_rel left_row right_row ->
      inner_rel left_value right_value ->
      output_rel
        (left_emit left_row left_value)
        (right_emit right_row right_value)) ->
    _permut output_rel
      (flat_map
        (fun left_row =>
          map (left_emit left_row)
            (filter (left_accept left_row) left_inner))
        left_outer)
      (flat_map
        (fun right_row =>
          map (right_emit right_row)
            (filter (right_accept right_row) right_inner))
        right_outer).
Proof.
intros outer_rel inner_rel output_rel
  left_accept right_accept left_emit right_emit
  left_outer right_outer left_inner right_inner
  Houter Hinner Haccept Hemit.
eapply theta_filter_map_permut_rel;
  [exact Houter|exact Hinner|exact Haccept|exact Hemit].
Qed.

End RelationalPermutationInterfacesRegression.

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
Print Assumptions list_flat_map_permut_rel.
Print Assumptions theta_filter_map_permut_rel.
