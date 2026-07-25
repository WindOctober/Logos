(************************************************************************************)
(** Reusable algebraic facts for FormalSQL relations, bags, and reset boundaries.  **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Arith NArith Lia SetoidList.
From SQLFS Require Import
  ListPermut OrderedSet FiniteSet FiniteBag FiniteCollection Join ListFacts FlatData Env Bool3 Formula
  SqlOutcome SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics
  SqlQueryFacts.

Import Tuple.

(** A direct column reference reads the current row at the head of [env_t].
    The presence premise is essential: absent columns fall through to the
    outer environment instead. *)
Lemma interp_direct_attribute_in_env_t :
  forall (T : Tuple.Rcd) env row attribute,
    attribute inS labels T row ->
    interp_aggterm T (env_t T env row)
      (@A_Expr T (@F_Dot T attribute)) =
    dot T row attribute.
Proof.
intros T env row attribute Hpresent.
rewrite interp_aggterm_unfold, interp_funterm_unfold, interp_dot_unfold.
unfold env_t; rewrite ListSort.quicksort_1, Hpresent; reflexivity.
Qed.

(** Pointwise relation equivalence is an equivalence relation, and inclusion
    transports through the list-to-bag abstraction. *)

(** Bidirectional support correspondence under an arbitrary relation.  This
    deliberately ignores multiplicity: callers use it at a later bag-reset or
    duplicate-elimination boundary.  The relation may connect rows with
    different visible schemas, as is needed when one side of a join has been
    projected or grouped before evaluation. *)
Definition list_support_rel {A B : Type} (R : A -> B -> Prop)
    (left : list A) (right : list B) : Prop :=
  (forall x, In x left -> exists y, In y right /\ R x y) /\
  (forall y, In y right -> exists x, In x left /\ R x y).

(** Bidirectional support relations compose without introducing multiplicity
    claims.  These list-level laws are useful when a semantic view crosses
    several projection, grouping, or aliasing boundaries before the next bag
    reset. *)
Lemma list_support_rel_compose :
  forall A B C (R : A -> B -> Prop) (S : B -> C -> Prop)
      (U : A -> C -> Prop) left middle right,
    list_support_rel R left middle ->
    list_support_rel S middle right ->
    (forall x y z, R x y -> S y z -> U x z) ->
    list_support_rel U left right.
Proof.
intros A B C R S U left middle right
  [HRforward HRbackward] [HSforward HSbackward] Hcompose.
split.
- intros x Hx.
  destruct (HRforward x Hx) as [y [Hy HR]].
  destruct (HSforward y Hy) as [z [Hz HS]].
  exists z; split; [exact Hz|].
  exact (Hcompose x y z HR HS).
- intros z Hz.
  destruct (HSbackward z Hz) as [y [Hy HS]].
  destruct (HRbackward y Hy) as [x [Hx HR]].
  exists x; split; [exact Hx|].
  exact (Hcompose x y z HR HS).
Qed.

(** Pointwise relation preservation transports support through maps on both
    sides.  In particular, semantic row equality may be pushed through a
    proper projection without reopening list membership proofs. *)
Lemma list_support_rel_map_transport :
  forall A B C D (R : A -> B -> Prop) (S : C -> D -> Prop)
      (left_map : A -> C) (right_map : B -> D) left right,
    list_support_rel R left right ->
    (forall x y, R x y -> S (left_map x) (right_map y)) ->
    list_support_rel S (map left_map left) (map right_map right).
Proof.
intros A B C D R S left_map right_map left right
  [Hforward Hbackward] Hmap.
split.
- intros output Houtput.
  apply in_map_iff in Houtput.
  destruct Houtput as [x [Houtput Hx]]; subst output.
  destruct (Hforward x Hx) as [y [Hy Hrel]].
  exists (right_map y); split.
  + apply in_map; exact Hy.
  + exact (Hmap x y Hrel).
- intros output Houtput.
  apply in_map_iff in Houtput.
  destruct Houtput as [y [Houtput Hy]]; subst output.
  destruct (Hbackward y Hy) as [x [Hx Hrel]].
  exists (left_map x); split.
  + apply in_map; exact Hx.
  + exact (Hmap x y Hrel).
Qed.

(** When both presentations are maps, support can be stated directly on the
    preimages.  No injectivity premise is needed because this property tracks
    only existence of related representatives. *)
Lemma list_support_rel_map_iff :
  forall A B C D (R : B -> D -> Prop)
      (left_map : A -> B) (right_map : C -> D) left right,
    list_support_rel R (map left_map left) (map right_map right) <->
    list_support_rel
      (fun x y => R (left_map x) (right_map y)) left right.
Proof.
intros A B C D R left_map right_map left right; split.
- intros [Hforward Hbackward]; split.
  + intros x Hx.
    destruct (Hforward (left_map x)) as [mapped [Hmapped HR]].
    * now apply in_map.
    * apply in_map_iff in Hmapped.
      destruct Hmapped as [y [Hmapped Hy]]; subst mapped.
      exists y; now split.
  + intros y Hy.
    destruct (Hbackward (right_map y)) as [mapped [Hmapped HR]].
    * now apply in_map.
    * apply in_map_iff in Hmapped.
      destruct Hmapped as [x [Hmapped Hx]]; subst mapped.
      exists x; now split.
- intro Hsupport.
  eapply list_support_rel_map_transport; [exact Hsupport|].
  intros x y Hxy; exact Hxy.
Qed.

(** Remove a mapped presentation on the left while retaining the map in the
    support relation. *)
Lemma list_support_rel_unmap_left :
  forall A B C (R : B -> C -> Prop) (mapping : A -> B) left right,
    list_support_rel R (map mapping left) right ->
    list_support_rel (fun x y => R (mapping x) y) left right.
Proof.
intros A B C R mapping left right [Hforward Hbackward].
split.
- intros x Hx.
  apply Hforward.
  now apply in_map.
- intros y Hy.
  destruct (Hbackward y Hy) as [mapped [Hmapped HR]].
  apply in_map_iff in Hmapped.
  destruct Hmapped as [x [Hmapped Hx]]; subst mapped.
  exists x; now split.
Qed.

(** Mapping the left list may retain an existential raw-row witness in the
    relation.  This is useful when a later join predicate needs an attribute
    hidden by an intermediate projection. *)
Lemma list_support_rel_map_left_with_witness :
  forall A B C (R : A -> C -> Prop) (mapping : A -> B) left right,
    list_support_rel R left right ->
    list_support_rel
      (fun mapped output =>
        exists original, mapped = mapping original /\ R original output)
      (map mapping left) right.
Proof.
intros A B C R mapping left right [Hforward Hbackward].
split.
- intros mapped Hmapped.
  apply in_map_iff in Hmapped.
  destruct Hmapped as [original [Hmapped Horiginal]]; subst mapped.
  destruct (Hforward original Horiginal) as [output [Houtput HR]].
  exists output; split; [exact Houtput|].
  exists original; now split.
- intros output Houtput.
  destruct (Hbackward output Houtput) as [original [Horiginal HR]].
  exists (mapping original); split.
  + now apply in_map.
  + exists original; now split.
Qed.

(** [ListFacts.all_diff] of mapped keys is precisely duplicate-freedom under
    equality of those keys. *)
Lemma all_diff_map_key_NoDupA :
  forall (A B : Type) (key : A -> B) rows,
    ListFacts.all_diff (map key rows) ->
    SetoidList.NoDupA
      (fun left right => key left = key right) rows.
Proof.
intros A B key rows.
induction rows as [|first rest IH]; intro Hdiff.
- constructor.
- rewrite ListFacts.all_diff_unfold in Hdiff.
  constructor.
  + intro Hin.
    apply SetoidList.InA_alt in Hin.
    destruct Hin as [other [Hkey Hother]].
    apply (proj1 Hdiff (key other)).
    * now apply in_map.
    * exact Hkey.
  + apply IH; exact (proj2 Hdiff).
Qed.

Lemma rel_equiv_refl :
  forall (A : Type) (relation : A -> Prop),
    rel_equiv relation relation.
Proof.
intros A relation value; split; intro H; exact H.
Qed.

Lemma rel_equiv_sym :
  forall (A : Type) (left right : A -> Prop),
    rel_equiv left right -> rel_equiv right left.
Proof.
intros A left right Hequiv value.
destruct (Hequiv value) as [Hforward Hbackward].
split; [exact Hbackward | exact Hforward].
Qed.

Lemma rel_equiv_trans :
  forall (A : Type) (first second third : A -> Prop),
    rel_equiv first second ->
    rel_equiv second third ->
    rel_equiv first third.
Proof.
intros A first second third Hfirst Hsecond value.
destruct (Hfirst value) as [Hfirst_forward Hfirst_backward].
destruct (Hsecond value) as [Hsecond_forward Hsecond_backward].
split.
- intro H; apply Hsecond_forward, Hfirst_forward, H.
- intro H; apply Hfirst_backward, Hsecond_backward, H.
Qed.

Lemma rel_incl_refl :
  forall (A : Type) (relation : A -> Prop),
    rel_incl relation relation.
Proof.
intros A relation value Hvalue; exact Hvalue.
Qed.

Lemma rel_incl_trans :
  forall (A : Type) (first second third : A -> Prop),
    rel_incl first second ->
    rel_incl second third ->
    rel_incl first third.
Proof.
intros A first second third Hfirst Hsecond value Hvalue.
now apply Hsecond, Hfirst.
Qed.

Lemma rel_equiv_iff_mutual_incl :
  forall (A : Type) (left right : A -> Prop),
    rel_equiv left right <->
    rel_incl left right /\ rel_incl right left.
Proof.
intros A left right; split.
- intro Hequiv; split; intros value Hvalue.
  + now apply (proj1 (Hequiv value)).
  + now apply (proj2 (Hequiv value)).
- intros [Hforward Hbackward] value; split.
  + apply Hforward.
  + apply Hbackward.
Qed.

Lemma alpha_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_incl left right ->
    rel_incl (alpha T left) (alpha T right).
Proof.
intros T left right Hincl bag [rows [Hrows Hbag]].
exists rows; split; [now apply Hincl | exact Hbag].
Qed.

Lemma bag_closed_rel_equiv_transport :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    BagClosed T left ->
    BagClosed T right.
Proof.
intros T left right Hequiv Hclosed desired Hpossible.
assert (Hleft_possible : alpha T left (rows_bag T desired)).
{ now apply (proj2 (alpha_congr T Hequiv (rows_bag T desired))). }
destruct (Hclosed desired Hleft_possible) as [actual [Hactual Hordered]].
exists actual; split; [now apply (proj1 (Hequiv actual)) | exact Hordered].
Qed.

Lemma bag_closed_union :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows \/ right rows).
Proof.
intros T left right Hleft Hright desired
  [source [[Hsource | Hsource] Hbags]].
- destruct (Hleft desired) as [actual [Hactual Hordered]].
  { unfold alpha; exists source; now split. }
  exists actual; now repeat split; try left.
- destruct (Hright desired) as [actual [Hactual Hordered]].
  { unfold alpha; exists source; now split. }
  exists actual; now repeat split; try right.
Qed.

Lemma bag_closed_exists :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => exists index, family index rows).
Proof.
intros T I family Hfamily desired [source [[index Hsource] Hbags]].
destruct (Hfamily index desired) as [actual [Hactual Hordered]].
{ unfold alpha; exists source; now split. }
exists actual; split; [now exists index | exact Hordered].
Qed.

(** Ordered equality and represented-bag equality expose useful occurrence
    and cardinality interfaces without unfolding query evaluation. *)

Lemma ordered_rows_equiv_length :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    length left = length right.
Proof.
intros T left right Hequiv.
unfold ordered_rows_equiv, mk_oelists in Hequiv; cbn in Hequiv.
now apply comparelA_eq_length_eq in Hequiv.
Qed.

Lemma ordered_rows_equiv_occ :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    forall row,
      Oeset.nb_occ (OTuple T) row left =
      Oeset.nb_occ (OTuple T) row right.
Proof.
intros T left right Hequiv row.
unfold ordered_rows_equiv, mk_oelists in Hequiv; cbn in Hequiv.
now apply Oeset.nb_occ_eq_2.
Qed.

Lemma rows_bag_occ :
  forall (T : Tuple.Rcd) (rows : list (tuple T)) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T rows) =
    Oeset.nb_occ (OTuple T) row rows.
Proof.
intros T rows row.
unfold rows_bag, SqlBagAbstraction.BTupleT.
apply Febag.nb_occ_mk_bag.
Qed.

Lemma bag_eq_iff_occurrences :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right <->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right.
Proof.
intros T left right.
unfold bag_eq, SqlBagAbstraction.BTupleT.
apply Febag.nb_occ_equal.
Qed.

Lemma bag_eq_cardinal :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    Febag.cardinal (Fecol.CBag (CTuple T)) left =
    Febag.cardinal (Fecol.CBag (CTuple T)) right.
Proof.
intros T left right Heq.
unfold bag_eq, SqlBagAbstraction.BTupleT in Heq.
now apply Febag.cardinal_eq.
Qed.

(** A Boolean classifier that assigns every supported row of two bags to
    opposite classes proves that their supports are disjoint.  The statement
    intentionally exposes only occurrence counts, so clients may reuse it for
    grouping channels, filtered partitions, or set operators without importing
    a query-specific notion of disjointness. *)
Lemma bag_occurrences_disjoint_of_boolean_separator :
  forall (T : Tuple.Rcd)
      (left right : SqlBagAbstraction.bagT T)
      (separate : tuple T -> bool),
    (forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left <> 0%N ->
      separate row = false) ->
    (forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right <> 0%N ->
      separate row = true) ->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left = 0%N \/
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right = 0%N.
Proof.
intros T left right separate Hleft Hright row.
destruct
  (Febag.nb_occ (Fecol.CBag (CTuple T)) row left)
  as [|left_count] eqn:Hleft_count.
- now left.
- destruct
    (Febag.nb_occ (Fecol.CBag (CTuple T)) row right)
    as [|right_count] eqn:Hright_count.
  + now right.
  + exfalso.
    assert (Hleft_nonzero :
      Febag.nb_occ (Fecol.CBag (CTuple T)) row left <> 0%N).
    { rewrite Hleft_count; discriminate. }
    assert (Hright_nonzero :
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right <> 0%N).
    { rewrite Hright_count; discriminate. }
    pose proof (Hleft row Hleft_nonzero) as Hfalse.
    pose proof (Hright row Hright_nonzero) as Htrue.
    congruence.
Qed.

(** Support-aware congruence for finite-bag filtering.  The input bags may use
    different representatives and the two predicates need agree only on
    semantic tuple occurrences actually present in the left input.  This is
    the appropriate interface when an environment-dependent SQL predicate has
    first been shown independent of that environment on table-row support. *)
Lemma bag_filter_congr_on_support :
  forall (T : Tuple.Rcd)
      (left_keep right_keep : tuple T -> bool)
      (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    (forall left_row right_row,
      (Febag.nb_occ (Fecol.CBag (CTuple T)) left_row left >= 1)%N ->
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      left_keep left_row = right_keep right_row) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) left_keep left)
      (Febag.filter (Fecol.CBag (CTuple T)) right_keep right).
Proof.
intros T left_keep right_keep left right Hequal Hkeep.
unfold bag_eq, SqlBagAbstraction.BTupleT in *.
now apply Febag.filter_eq.
Qed.

Lemma rows_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T)),
    Febag.cardinal (Fecol.CBag (CTuple T)) (rows_bag T rows) =
    N.of_nat (length rows).
Proof.
intros T rows.
unfold rows_bag, SqlBagAbstraction.BTupleT.
apply Febag.cardinal_mk_bag.
Qed.

Lemma query_same_rows_as_bag_cardinal :
  forall (T : Tuple.Rcd) (rows : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag rows bag ->
    Febag.cardinal (Fecol.CBag (CTuple T)) bag =
    N.of_nat (length rows).
Proof.
intros T rows bag Hrows.
apply query_same_rows_as_bag_iff_bag_eq in Hrows.
pose proof (bag_eq_cardinal Hrows) as Hcardinal.
rewrite rows_bag_cardinal in Hcardinal.
now symmetry.
Qed.

Lemma query_same_rows_as_bag_length :
  forall (T : Tuple.Rcd) (first second : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag first bag ->
    query_same_rows_as_bag second bag ->
    length first = length second.
Proof.
intros T first second bag Hfirst Hsecond.
pose proof (query_same_rows_as_bag_cardinal Hfirst) as Hfirst_cardinal.
pose proof (query_same_rows_as_bag_cardinal Hsecond) as Hsecond_cardinal.
apply Nat2N.inj.
now rewrite <- Hfirst_cardinal, <- Hsecond_cardinal.
Qed.

Lemma query_same_rows_as_bag_iff_occurrences :
  forall (T : Tuple.Rcd) (rows : list (tuple T))
         (bag : SqlBagAbstraction.bagT T),
    query_same_rows_as_bag rows bag <->
    forall row,
      Oeset.nb_occ (OTuple T) row rows =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
Proof.
intros T rows bag.
rewrite query_same_rows_as_bag_iff_bag_eq.
rewrite bag_eq_iff_occurrences.
split; intros H row.
- rewrite <- (rows_bag_occ T rows row); apply H.
- rewrite (rows_bag_occ T rows row); apply H.
Qed.

(** A proposition about rows may cross a bag-representative boundary only
    when it respects FormalSQL's semantic tuple equality.  In particular,
    structural Rocq equality is neither required nor inferred. *)
Definition tuple_property_semantic_invariant
    {T : Tuple.Rcd} (property : tuple T -> Prop) : Prop :=
  forall left right,
    Oeset.compare (OTuple T) left right = Eq ->
    (property left <-> property right).

Local Lemma semantic_permut_Forall_transport :
  forall (T : Tuple.Rcd) (property : tuple T -> Prop) left right,
    tuple_property_semantic_invariant property ->
    _permut
      (fun first second => Oeset.compare (OTuple T) first second = Eq)
      left right ->
    Forall property left ->
    Forall property right.
Proof.
intros T property left right Hproper Hpermut Hforall.
rewrite Forall_forall in Hforall |- *.
intros row Hrow.
destruct (in_split row right Hrow) as [before [after Hright]].
subst right.
destruct
  (_permut_inv_right_strong
    (R := fun first second =>
      Oeset.compare (OTuple T) first second = Eq)
    row before after Hpermut)
  as [source [left_before [left_after [Hequal [Hleft _]]]]].
apply (proj1 (Hproper source row Hequal)).
apply Hforall.
rewrite Hleft; apply in_or_app; right; now left.
Qed.

(** Every concrete list representing a finite bag is a multiplicity-preserving
    semantic permutation of the bag's canonical element list. *)
Lemma query_same_rows_as_bag_semantic_permut_elements :
  forall (T : Tuple.Rcd) rows bag,
    @query_same_rows_as_bag T rows bag ->
    _permut
      (fun left right => Oeset.compare (OTuple T) left right = Eq)
      rows (Febag.elements (Fecol.CBag (CTuple T)) bag).
Proof.
intros T rows bag Hrows.
apply Oeset.nb_occ_permut; intro row.
pose proof
  (proj1 (query_same_rows_as_bag_iff_occurrences T rows bag) Hrows row)
  as Hocc.
rewrite Febag.nb_occ_elements in Hocc.
exact Hocc.
Qed.

(** A semantic row property is independent of the concrete ordered
    representative chosen for the same bag.  Both [query_same_rows_as_bag]
    premises retain duplicate counts; the conclusion intentionally forgets
    order but not which semantic row occurrences are present. *)
Lemma query_same_rows_as_bag_Forall_transport :
  forall (T : Tuple.Rcd) (property : tuple T -> Prop) first second bag,
    tuple_property_semantic_invariant property ->
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    Forall property first ->
    Forall property second.
Proof.
intros T property first second bag Hproper Hfirst Hsecond Hforall.
pose proof
  (@query_same_rows_as_bag_semantic_permut_elements T first bag Hfirst)
  as Hfirst_permut.
pose proof
  (@query_same_rows_as_bag_semantic_permut_elements T second bag Hsecond)
  as Hsecond_permut.
assert (Helements :
  Forall property (Febag.elements (Fecol.CBag (CTuple T)) bag)).
{
  eapply semantic_permut_Forall_transport;
    [exact Hproper | exact Hfirst_permut | exact Hforall].
}
eapply semantic_permut_Forall_transport.
- exact Hproper.
- exact (Oeset.permut_sym Hsecond_permut).
- exact Helements.
Qed.

(** Filtering a list representative and filtering its bag abstraction retain
    exactly the same multiplicities.  The predicate must respect semantic
    tuple equality; structural Rocq equality is neither required nor assumed. *)
Lemma query_same_rows_as_bag_filter :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool) rows bag,
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    @query_same_rows_as_bag T rows bag ->
    @query_same_rows_as_bag T (filter keep rows)
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag).
Proof.
intros T keep rows bag Hproper Hrows.
apply query_same_rows_as_bag_iff_occurrences.
pose proof
  (proj1 (query_same_rows_as_bag_iff_occurrences T rows bag) Hrows)
  as Hocc.
intro row.
rewrite Oeset.nb_occ_filter.
2: intros left right _ Hequal; now apply Hproper.
rewrite Febag.nb_occ_filter.
2: intros left right _ Hequal; now apply Hproper.
rewrite Hocc.
destruct (keep row); cbn; lia.
Qed.

(** Canonicalization changes only the representative chosen for a successful
    bag.  This bridge avoids repeatedly unfolding [query_canonical_rows] and
    finite-bag elements in downstream proofs. *)
Lemma query_canonical_rows_same_as_bag :
  forall (T : Tuple.Rcd) rows bag,
    @query_same_rows_as_bag T rows bag ->
    @query_same_rows_as_bag T (@query_canonical_rows T rows) bag.
Proof.
intros T rows bag Hrows.
unfold query_canonical_rows.
eapply query_same_rows_as_bag_bag_transport.
- apply query_elements_same_rows_as_bag.
- now apply query_same_rows_as_bag_iff_bag_eq in Hrows.
Qed.

(** Two canonicalized list representatives of the same bag retain the same
    number of SQL row occurrences. *)
Lemma query_canonical_rows_length_between :
  forall (T : Tuple.Rcd) first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    List.length (@query_canonical_rows T first) =
    List.length (@query_canonical_rows T second).
Proof.
intros T first second bag Hfirst Hsecond.
eapply query_same_rows_as_bag_length with (bag := bag).
- now apply query_canonical_rows_same_as_bag.
- now apply query_canonical_rows_same_as_bag.
Qed.

(** Filtering one canonical representative and canonicalizing a representative
    of the filtered bag differ only by a semantic permutation.  Multiplicity,
    including duplicate accepted rows, is preserved exactly. *)
Lemma query_canonical_rows_filter_permut :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool) left right original,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    @query_same_rows_as_bag T left (rows_bag T original) ->
    @query_same_rows_as_bag T right
      (rows_bag T (List.filter keep original)) ->
    Oeset.permut (OTuple T)
      (List.filter keep (@query_canonical_rows T left))
      (@query_canonical_rows T right).
Proof.
intros T keep left right original Hproper Hleft Hright.
set (filtered_bag :=
  Febag.filter (Fecol.CBag (CTuple T)) keep (rows_bag T original)).
assert (Hleft_canonical :
  query_same_rows_as_bag (query_canonical_rows left)
    (rows_bag T original)).
{ now apply query_canonical_rows_same_as_bag. }
assert (Hleft_filtered :
  query_same_rows_as_bag
    (List.filter keep (query_canonical_rows left)) filtered_bag).
{
  unfold filtered_bag.
  now apply query_same_rows_as_bag_filter.
}
assert (Horiginal :
  query_same_rows_as_bag original (rows_bag T original)).
{ apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl. }
assert (Horiginal_filtered :
  query_same_rows_as_bag (List.filter keep original) filtered_bag).
{
  unfold filtered_bag.
  now apply query_same_rows_as_bag_filter.
}
assert (Hright_canonical :
  query_same_rows_as_bag (query_canonical_rows right)
    (rows_bag T (List.filter keep original))).
{ now apply query_canonical_rows_same_as_bag. }
assert (Hright_filtered :
  query_same_rows_as_bag (query_canonical_rows right) filtered_bag).
{
  eapply query_same_rows_as_bag_bag_transport.
  - exact Hright_canonical.
  - now apply query_same_rows_as_bag_iff_bag_eq in Horiginal_filtered.
}
apply Oeset.nb_occ_permut; intro row.
pose proof
  (proj1
    (query_same_rows_as_bag_iff_occurrences T
      (List.filter keep (query_canonical_rows left)) filtered_bag)
    Hleft_filtered row) as Hleft_occ.
pose proof
  (proj1
    (query_same_rows_as_bag_iff_occurrences T
      (query_canonical_rows right) filtered_bag)
    Hright_filtered row) as Hright_occ.
now rewrite Hleft_occ, Hright_occ.
Qed.

(** Every representative of a filtered bag is the literal filter of some
    representative of the input bag.  Rejected occurrences are reconstructed
    from the complementary bag, so duplicates and semantic tuple equality are
    preserved exactly. *)
Lemma query_same_rows_as_filtered_bag_preimage :
  forall (T : Tuple.Rcd) rows bag (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    @query_same_rows_as_bag T rows
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag) ->
    exists input_rows,
      @query_same_rows_as_bag T input_rows bag /\
      filter keep input_rows = rows.
Proof.
intros T rows bag keep Hproper Hrows.
pose proof
  (proj1
    (query_same_rows_as_bag_iff_occurrences T rows
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag)) Hrows)
  as Haccepted_occ.
set (rejected :=
  Febag.filter (Fecol.CBag (CTuple T)) (fun row => negb (keep row)) bag).
set (rejected_rows := Febag.elements (Fecol.CBag (CTuple T)) rejected).
exists (rows ++ rejected_rows); split.
- apply query_same_rows_as_bag_iff_occurrences.
  intro row.
  rewrite Oeset.nb_occ_app, Haccepted_occ.
  unfold rejected_rows.
  rewrite <- Febag.nb_occ_elements.
  unfold rejected.
  rewrite 2 Febag.nb_occ_filter.
  2: intros left right _ Hequal;
     exact (f_equal negb (Hproper left right Hequal)).
  2: intros left right _ Hequal; now apply Hproper.
  destruct (keep row); cbn; lia.
- rewrite ListFacts.filter_app.
  assert (Haccepted : forall row, In row rows -> keep row = true).
  {
    intros row Hrow.
    destruct (keep row) eqn:Hkeep; [reflexivity|].
    exfalso.
    pose proof (Oeset.In_nb_occ (OTuple T) row rows Hrow) as Hnonzero.
    rewrite Haccepted_occ in Hnonzero.
    rewrite Febag.nb_occ_filter in Hnonzero.
    2: intros left right _ Hequal; now apply Hproper.
    rewrite Hkeep in Hnonzero; cbn in Hnonzero.
    rewrite N.mul_0_r in Hnonzero.
    now apply Hnonzero.
  }
  assert (Hrejected :
    forall row, In row rejected_rows -> keep row = false).
  {
    intros row Hrow.
    destruct (keep row) eqn:Hkeep; [|reflexivity].
    exfalso.
    pose proof
      (Oeset.In_nb_occ (OTuple T) row rejected_rows Hrow) as Hnonzero.
    unfold rejected_rows in Hnonzero.
    rewrite <- Febag.nb_occ_elements in Hnonzero.
    unfold rejected in Hnonzero.
    rewrite Febag.nb_occ_filter in Hnonzero.
    2: intros left right _ Hequal;
       exact (f_equal negb (Hproper left right Hequal)).
    rewrite Hkeep in Hnonzero; cbn in Hnonzero.
    rewrite N.mul_0_r in Hnonzero.
    now apply Hnonzero.
  }
  transitivity (rows ++ nil).
  + apply f_equal2.
    * now apply ListFacts.filter_true.
    * now apply ListFacts.filter_false.
  + now rewrite app_nil_r.
Qed.

(** Two nested projection pipelines are bag-equivalent whenever their
    composed row maps are pointwise equal under semantic tuple equality. *)
Lemma double_projection_bag_eq :
  forall (T : Tuple.Rcd) (env : Env.env T)
      (outer_left inner_left outer_right inner_right : _select_list T)
      (bag : SqlQuerySemantics.bagT T),
    (forall row,
      Oeset.compare (OTuple T)
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_left)))
          (@Select_List T outer_left))
        (projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_right)))
          (@Select_List T outer_right)) = Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row => projection T (env_t T env row) (@Select_List T outer_left))
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          (fun row => projection T (env_t T env row) (@Select_List T inner_left))
          bag))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row => projection T (env_t T env row) (@Select_List T outer_right))
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          (fun row => projection T (env_t T env row) (@Select_List T inner_right))
          bag)).
Proof.
intros T env outer_left inner_left outer_right inner_right bag Hrows.
unfold bag_eq; rewrite Febag.nb_occ_equal; intro output.
transitivity
  (Fecol.nb_occ output
    (Fecol.map (CTuple T)
      (fun row => projection T
        (env_t T env
          (projection T (env_t T env row) (@Select_List T inner_left)))
        (@Select_List T outer_left))
      (Fecol.Fbag bag))).
- assert (Hmap :
    Fecol.nb_occ output
      (Fecol.map (CTuple T)
        (fun row => projection T (env_t T env row) (@Select_List T outer_left))
        (Fecol.map (CTuple T)
          (fun row => projection T (env_t T env row) (@Select_List T inner_left))
          (Fecol.Fbag bag))) =
    Fecol.nb_occ output
      (Fecol.map (CTuple T)
        (fun row => projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_left)))
          (@Select_List T outer_left))
        (Fecol.Fbag bag))).
  {
    apply Fecol.nb_occ_map_map.
    intros left right _ _ Hequal.
    apply projection_eq, env_t_eq_2; exact Hequal.
  }
  rewrite Fecol.nb_occ_bag.
  rewrite 2 Fecol.nb_occ_bag in Hmap.
  cbn [Fecol.map Fecol.to_bag] in Hmap.
  exact Hmap.
- transitivity
    (Fecol.nb_occ output
      (Fecol.map (CTuple T)
        (fun row => projection T
          (env_t T env
            (projection T (env_t T env row) (@Select_List T inner_right)))
          (@Select_List T outer_right))
        (Fecol.Fbag bag))).
  + apply Fecol.nb_occ_map_eq2.
    intros row _; apply Hrows.
  + symmetry.
    assert (Hmap :
      Fecol.nb_occ output
        (Fecol.map (CTuple T)
          (fun row => projection T (env_t T env row) (@Select_List T outer_right))
          (Fecol.map (CTuple T)
            (fun row => projection T (env_t T env row) (@Select_List T inner_right))
            (Fecol.Fbag bag))) =
      Fecol.nb_occ output
        (Fecol.map (CTuple T)
          (fun row => projection T
            (env_t T env
              (projection T (env_t T env row) (@Select_List T inner_right)))
            (@Select_List T outer_right))
          (Fecol.Fbag bag))).
    {
      apply Fecol.nb_occ_map_map.
      intros left right _ _ Hequal.
      apply projection_eq, env_t_eq_2; exact Hequal.
    }
    rewrite Fecol.nb_occ_bag.
    rewrite 2 Fecol.nb_occ_bag in Hmap.
    cbn [Fecol.map Fecol.to_bag] in Hmap.
    exact Hmap.
Qed.

(** A semantic-duplicate-free list has multiplicity zero or one, determined
    entirely by support membership. *)
Lemma oeset_nb_occ_of_NoDupA :
  forall (A : Type) (ordered : Oeset.Rcd A) values,
    SetoidList.NoDupA
      (fun left right => Oeset.compare ordered left right = Eq) values ->
    forall value,
      Oeset.nb_occ ordered value values =
      if Oeset.mem_bool ordered value values then 1%N else 0%N.
Proof.
intros A ordered values Hnodup.
induction Hnodup as [|head tail Hhead Htail IH]; intro value.
- reflexivity.
- rewrite Oeset.nb_occ_unfold, Oeset.mem_bool_unfold.
  destruct (Oeset.compare ordered value head) eqn:Hcompare.
  + assert (Htail_mem : Oeset.mem_bool ordered value tail = false).
    {
      destruct (Oeset.mem_bool ordered value tail) eqn:Hmember;
        [|reflexivity].
      exfalso.
      rewrite Oeset.mem_bool_true_iff in Hmember.
      destruct Hmember as [other [Hother Hother_in]].
      apply Hhead, InA_alt.
      exists other; split.
      - eapply Oeset.compare_eq_trans.
        * apply Oeset.compare_eq_sym; exact Hcompare.
        * exact Hother.
      - exact Hother_in.
    }
    rewrite (IH value), Htail_mem; reflexivity.
  + rewrite IH.
    destruct (Oeset.mem_bool ordered value tail); reflexivity.
  + rewrite IH.
    destruct (Oeset.mem_bool ordered value tail); reflexivity.
Qed.

(** For semantic sets represented as lists, support equality is already
    sufficient for occurrence equality. *)
Lemma oeset_NoDupA_same_support_same_occurrences :
  forall (A : Type) (ordered : Oeset.Rcd A) left right,
    SetoidList.NoDupA
      (fun first second => Oeset.compare ordered first second = Eq) left ->
    SetoidList.NoDupA
      (fun first second => Oeset.compare ordered first second = Eq) right ->
    (forall value,
      Oeset.mem_bool ordered value left =
      Oeset.mem_bool ordered value right) ->
    forall value,
      Oeset.nb_occ ordered value left = Oeset.nb_occ ordered value right.
Proof.
intros A ordered left right Hleft Hright Hsupport value.
rewrite (@oeset_nb_occ_of_NoDupA A ordered left Hleft value).
rewrite (@oeset_nb_occ_of_NoDupA A ordered right Hright value).
now rewrite Hsupport.
Qed.

(** Duplicate-free row lists represent equal bags when their semantic
    supports correspond bidirectionally.  This is the list-level companion to
    duplicate-free finite-bag support equality and avoids exposing occurrence
    arithmetic to callers at a grouping or DISTINCT reset. *)
Lemma rows_bag_eq_of_nodup_support_rel :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    SetoidList.NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left ->
    SetoidList.NoDupA
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      right ->
    bag_eq T (rows_bag T left) (rows_bag T right).
Proof.
intros T left right [Hforward Hbackward] Hleft Hright.
unfold bag_eq, rows_bag.
rewrite Febag.nb_occ_equal; intro row.
rewrite 2 Febag.nb_occ_mk_bag.
apply oeset_NoDupA_same_support_same_occurrences; try assumption.
intro value.
destruct (Oeset.mem_bool (OTuple T) value left) eqn:Hleft_mem.
- pose proof Hleft_mem as Hleft_in.
  rewrite Oeset.mem_bool_true_iff in Hleft_in.
  destruct Hleft_in as [candidate [Hequal Hcandidate]].
  destruct (Hforward candidate Hcandidate)
    as [other [Hother Hequal_other]].
  symmetry.
  apply Oeset.mem_bool_true_iff.
  exists other; split; [|exact Hother].
  eapply Oeset.compare_eq_trans;
    [exact Hequal|exact Hequal_other].
- destruct (Oeset.mem_bool (OTuple T) value right) eqn:Hright_mem;
    [|reflexivity].
  pose proof Hright_mem as Hright_in.
  rewrite Oeset.mem_bool_true_iff in Hright_in.
  destruct Hright_in as [candidate [Hequal Hcandidate]].
  destruct (Hbackward candidate Hcandidate)
    as [other [Hother Hequal_other]].
  exfalso.
  assert (Hleft_true :
    Oeset.mem_bool (OTuple T) value left = true).
  {
    apply Oeset.mem_bool_true_iff.
    exists other; split; [|exact Hother].
    eapply Oeset.compare_eq_trans; [exact Hequal|].
    apply Oeset.compare_eq_sym; exact Hequal_other.
  }
  congruence.
Qed.

Lemma alpha_membership_iff_occurrence_representative :
  forall (T : Tuple.Rcd) (observations : list (tuple T) -> Prop)
         (bag : SqlBagAbstraction.bagT T),
    alpha T observations bag <->
    exists rows,
      observations rows /\
      forall row,
        Oeset.nb_occ (OTuple T) row rows =
        Febag.nb_occ (Fecol.CBag (CTuple T)) row bag.
Proof.
intros T observations bag.
unfold alpha.
split.
- intros [rows [Hrows Hbag]].
  exists rows; split; [exact Hrows |].
  pose proof
    (proj1 (@bag_eq_iff_occurrences T (rows_bag T rows) bag) Hbag)
    as Hocc.
  intro row; rewrite <- (rows_bag_occ T rows row); apply Hocc.
- intros [rows [Hrows Hocc]].
  exists rows; split; [exact Hrows |].
  apply (proj2 (@bag_eq_iff_occurrences T (rows_bag T rows) bag)).
  intro row; rewrite (rows_bag_occ T rows row); apply Hocc.
Qed.

(** Algebraic laws for the concrete bag operations used by exact reset nodes. *)

Section BagOperations.

Context {T : Tuple.Rcd}.

Local Definition bagT := Febag.bag (Fecol.CBag (CTuple T)).

Lemma query_set_union_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union, Febag.nb_occ_empty.
apply N.add_0_l.
Qed.

Lemma query_set_union_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Union bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union, Febag.nb_occ_empty.
apply N.add_0_r.
Qed.

Lemma query_set_union_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Union left right)
             (query_set_bag Union right left).
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite 2 Febag.nb_occ_union.
apply N.add_comm.
Qed.

Lemma query_set_union_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Union (query_set_bag Union first second) third)
      (query_set_bag Union first (query_set_bag Union second third)).
Proof.
intros first second third; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite 4 Febag.nb_occ_union.
symmetry; apply N.add_assoc.
Qed.

Lemma query_set_union_max_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag UnionMax left right)
             (query_set_bag UnionMax right left).
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite 2 Febag.nb_occ_union_max.
apply N.max_comm.
Qed.

Lemma query_set_union_max_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (query_set_bag UnionMax first second) third)
      (query_set_bag UnionMax first
        (query_set_bag UnionMax second third)).
Proof.
intros first second third; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite 4 Febag.nb_occ_union_max.
symmetry; apply N.max_assoc.
Qed.

Lemma query_set_union_max_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag UnionMax bag bag) bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union_max.
apply N.max_id.
Qed.

Lemma query_set_union_max_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union_max, Febag.nb_occ_empty.
apply N.max_0_l.
Qed.

Lemma query_set_union_max_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag UnionMax bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union_max, Febag.nb_occ_empty.
apply N.max_0_r.
Qed.

Lemma query_set_inter_comm :
  forall left right : bagT,
    bag_eq T (query_set_bag Inter left right)
             (query_set_bag Inter right left).
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite 2 Febag.nb_occ_inter.
apply N.min_comm.
Qed.

Lemma query_set_inter_assoc :
  forall first second third : bagT,
    bag_eq T
      (query_set_bag Inter
        (query_set_bag Inter first second) third)
      (query_set_bag Inter first
        (query_set_bag Inter second third)).
Proof.
intros first second third; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite 4 Febag.nb_occ_inter.
symmetry; apply N.min_assoc.
Qed.

Lemma query_set_inter_idempotent :
  forall bag : bagT,
    bag_eq T (query_set_bag Inter bag bag) bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_inter.
apply N.min_id.
Qed.

Lemma query_set_inter_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_inter, 2 Febag.nb_occ_empty.
apply N.min_0_l.
Qed.

Lemma query_set_inter_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Inter bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_inter, 2 Febag.nb_occ_empty.
apply N.min_0_r.
Qed.

Lemma query_set_union_max_inter_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag UnionMax left (query_set_bag Inter left right))
      left.
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union_max, Febag.nb_occ_inter.
apply N.min_max_absorption.
Qed.

Lemma query_set_inter_union_max_absorb :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Inter left (query_set_bag UnionMax left right))
      left.
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_inter, Febag.nb_occ_union_max.
apply N.max_min_absorption.
Qed.

Lemma query_set_diff_empty_left :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_diff, 2 Febag.nb_occ_empty.
apply N.sub_0_l.
Qed.

Lemma query_set_diff_empty_right :
  forall bag : bagT,
    bag_eq T
      (query_set_bag Diff bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      bag.
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_diff, Febag.nb_occ_empty.
apply N.sub_0_r.
Qed.

Lemma query_set_diff_self_empty :
  forall bag : bagT,
    bag_eq T (query_set_bag Diff bag bag)
             (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_diff, Febag.nb_occ_empty.
apply N.sub_diag.
Qed.

Lemma query_set_diff_union_cancel_right :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) right)
      left.
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_diff, Febag.nb_occ_union.
apply N.add_sub.
Qed.

Lemma query_set_diff_union_cancel_left :
  forall left right : bagT,
    bag_eq T
      (query_set_bag Diff (query_set_bag Union left right) left)
      right.
Proof.
intros left right; apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_diff, Febag.nb_occ_union, N.add_comm.
apply N.add_sub.
Qed.

Lemma query_cross_join_empty :
  forall bag : bagT,
    bag_eq T
      (query_cross_join_bag
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))) /\
    bag_eq T
      (query_cross_join_bag bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intro bag; split; apply bag_eq_iff_occurrences; intro row;
  unfold query_cross_join_bag;
  rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_empty, Febag.elements_empty.
- reflexivity.
- assert (Hempty : forall rows : list (tuple T),
    brute_left_join_list (tuple T) (join_tuple T) rows nil = nil).
  {
    intro rows.
    induction rows as [|head tail IH]; [reflexivity |].
    cbn [brute_left_join_list theta_join_list d_join_list].
    exact IH.
  }
  rewrite Hempty; reflexivity.
Qed.

Lemma query_natural_join_empty :
  forall (value_is_null : value T -> bool) (bag : bagT),
    bag_eq T
      (query_natural_join_bag value_is_null
        (Febag.empty (Fecol.CBag (CTuple T))) bag)
      (Febag.empty (Fecol.CBag (CTuple T))) /\
    bag_eq T
      (query_natural_join_bag value_is_null bag
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intros value_is_null bag; split; apply bag_eq_iff_occurrences; intro row;
  unfold query_natural_join_bag;
  rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_empty, Febag.elements_empty.
- reflexivity.
- assert (Hempty : forall rows : list (tuple T),
    theta_join_list (tuple T) (join_tuple T)
      (query_natural_join_compatible value_is_null) rows nil = nil).
  {
    intro rows.
    induction rows as [|head tail IH]; [reflexivity |].
    cbn [theta_join_list d_join_list].
    exact IH.
  }
  rewrite Hempty; reflexivity.
Qed.

Lemma query_distinct_bag_empty :
  bag_eq T
    (query_distinct_bag (Febag.empty (Fecol.CBag (CTuple T))))
    (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
apply bag_eq_iff_occurrences; intro row.
unfold query_distinct_bag.
rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_empty, Febag.elements_empty.
pose proof
  (Feset.elements_mk_set_elements
    (Fecol.CSet (CTuple T))
    (Feset.empty (Fecol.CSet (CTuple T)))) as Hset.
rewrite Feset.elements_empty in Hset.
pose proof (Oeset.nb_occ_eq_2 (OTuple T) row _ _ Hset) as Hocc.
cbn in Hocc.
exact Hocc.
Qed.

Lemma query_distinct_bag_idempotent :
  forall bag : bagT,
    bag_eq T (query_distinct_bag (query_distinct_bag bag))
             (query_distinct_bag bag).
Proof.
intro bag; apply bag_eq_iff_occurrences; intro row.
unfold query_distinct_bag.
rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.nb_occ_eq_2.
apply Feset.elements_spec1.
apply Feset.mk_set_eq.
intro item.
rewrite <- 2 Febag.mem_unfold.
rewrite Febag.mem_mk_bag.
rewrite <- Feset.mem_elements, Feset.mem_mk_set.
apply Febag.mem_unfold.
Qed.

Lemma query_cross_join_bag_cardinal :
  forall left right : bagT,
    Febag.cardinal (Fecol.CBag (CTuple T))
      (query_cross_join_bag left right) =
    (Febag.cardinal (Fecol.CBag (CTuple T)) left *
     Febag.cardinal (Fecol.CBag (CTuple T)) right)%N.
Proof.
intros left right.
unfold query_cross_join_bag.
rewrite Febag.cardinal_mk_bag.
assert (Hproduct : forall left_rows : list (tuple T),
  length (brute_left_join_list (tuple T) (join_tuple T)
    left_rows (Febag.elements (Fecol.CBag (CTuple T)) right)) =
  (length left_rows *
   length (Febag.elements (Fecol.CBag (CTuple T)) right))%nat).
{
  intro left_rows.
  unfold brute_left_join_list, theta_join_list, d_join_list.
  assert (Htrue :
    filter (fun _ : tuple T => true)
      (Febag.elements (Fecol.CBag (CTuple T)) right) =
    Febag.elements (Fecol.CBag (CTuple T)) right).
  {
    apply ListFacts.filter_true; intros; reflexivity.
  }
  rewrite Htrue.
  induction left_rows as [|left_row left_rows IH]; cbn.
  - reflexivity.
  - rewrite length_app, length_map, IH; lia.
}
rewrite Hproduct, Nat2N.inj_mul.
reflexivity.
Qed.

Lemma query_natural_join_bag_cardinal_le :
  forall (value_is_null : value T -> bool) (left right : bagT),
    (Febag.cardinal (Fecol.CBag (CTuple T))
       (query_natural_join_bag value_is_null left right) <=
     Febag.cardinal (Fecol.CBag (CTuple T)) left *
     Febag.cardinal (Fecol.CBag (CTuple T)) right)%N.
Proof.
intros value_is_null left right.
unfold query_natural_join_bag.
rewrite Febag.cardinal_mk_bag.
assert (Hbound : forall left_rows : list (tuple T),
  (length (theta_join_list (tuple T) (join_tuple T)
      (query_natural_join_compatible value_is_null) left_rows
      (Febag.elements (Fecol.CBag (CTuple T)) right)) <=
   length left_rows *
      length (Febag.elements (Fecol.CBag (CTuple T)) right))%nat).
{
  intro left_rows.
  unfold theta_join_list, d_join_list.
  induction left_rows as [|left_row left_rows IH]; cbn.
  - apply Nat.le_refl.
  - rewrite length_app, length_map.
    pose proof (filter_length_le
      (query_natural_join_compatible value_is_null left_row)
      (Febag.elements (Fecol.CBag (CTuple T)) right)) as Hfilter.
    exact (Nat.add_le_mono _ _ _ _ Hfilter IH).
}
pose proof
  (Hbound (Febag.elements (Fecol.CBag (CTuple T)) left)) as Hrows.
change
  (N.of_nat
      (length (theta_join_list (tuple T) (join_tuple T)
        (query_natural_join_compatible value_is_null)
        (Febag.elements (Fecol.CBag (CTuple T)) left)
        (Febag.elements (Fecol.CBag (CTuple T)) right))) <=
   N.of_nat (length (Febag.elements (Fecol.CBag (CTuple T)) left)) *
   N.of_nat (length (Febag.elements (Fecol.CBag (CTuple T)) right)))%N.
rewrite <- Nat2N.inj_mul.
apply (proj1 (N.compare_le_iff _ _)).
rewrite <- Nat2N.inj_compare.
apply (proj2 (Nat.compare_le_iff _ _)).
exact Hrows.
Qed.

(** Join-source bounds count SQL row occurrences before the three select-list
    projections.  They are deliberately indexed by join kind: semi/anti
    produce at most one source per left row, whereas outer joins may add
    unmatched sources. *)

Lemma query_join_matched_sources_length_le :
  forall (left : tuple T) rights flags,
    length (query_join_matched_sources T left rights flags) <= length rights.
Proof.
intros left rights.
induction rights as [|right rights IH]; intros [|flag flags]; cbn; try lia.
destruct flag; cbn; specialize (IH flags); lia.
Qed.

Lemma query_join_left_sources_length_le :
  forall kind lefts rights matrix,
    length (query_join_left_sources T kind lefts rights matrix) <=
    match kind with
    | QueryJoinInner | QueryJoinRight => length lefts * length rights
    | QueryJoinLeft | QueryJoinFull =>
        length lefts * Nat.max 1 (length rights)
    | QueryJoinSemi | QueryJoinAnti => length lefts
    end.
Proof.
intros kind lefts; revert kind.
induction lefts as [|left lefts IH];
  intros kind rights [|flags matrix]; cbn; try lia.
pose proof (query_join_matched_sources_length_le left rights flags)
  as Hmatched.
specialize (IH kind rights matrix).
pose proof (Nat.le_max_l 1 (length rights)) as Hone.
pose proof (Nat.le_max_r 1 (length rights)) as Hrights.
destruct kind; cbn in *.
- rewrite length_app; lia.
- destruct (query_join_row_has_match flags); cbn.
  + rewrite length_app; lia.
  + lia.
- rewrite length_app; lia.
- destruct (query_join_row_has_match flags); cbn.
  + rewrite length_app; lia.
  + lia.
- destruct (query_join_row_has_match flags); cbn; lia.
- destruct (query_join_row_has_match flags); cbn; lia.
Qed.

Lemma query_join_unmatched_right_sources_length_le :
  forall index rights matrix,
    length
      (query_join_unmatched_right_sources_from T index rights matrix) <=
    length rights.
Proof.
intros index rights; revert index.
induction rights as [|right rights IH]; intros index matrix; cbn; [lia|].
destruct (query_join_column_has_match index matrix); cbn;
  specialize (IH (S index) matrix); lia.
Qed.

Lemma query_join_sources_length_le :
  forall kind lefts rights matrix,
    length (query_join_sources T kind lefts rights matrix) <=
    match kind with
    | QueryJoinInner => length lefts * length rights
    | QueryJoinLeft => length lefts * Nat.max 1 (length rights)
    | QueryJoinRight => length lefts * length rights + length rights
    | QueryJoinFull =>
        length lefts * Nat.max 1 (length rights) + length rights
    | QueryJoinSemi | QueryJoinAnti => length lefts
    end.
Proof.
intros kind lefts rights matrix.
unfold query_join_sources.
rewrite length_app.
pose proof (query_join_left_sources_length_le kind lefts rights matrix)
  as Hleft.
pose proof
  (query_join_unmatched_right_sources_length_le 0 rights matrix) as Hright.
destruct kind; cbn in *; lia.
Qed.

(** The native FULL JOIN source scheduler consumes a row-major Boolean
    condition matrix and uses column indices to detect unmatched right rows.
    The helpers below stay local; the public boundary is the final support
    characterization, not a second outer-join evaluator. *)
Local Lemma list_existsb_false_iff :
  forall (A : Type) (test : A -> bool) values,
    existsb test values = false <->
    forall value, In value values -> test value = false.
Proof.
intros A test values; induction values as [|head tail IH]; cbn.
- split; [intros _ value Hin; contradiction|reflexivity].
- destruct (test head) eqn:Hhead; cbn.
  + split; [discriminate|].
    intro H; specialize (H head (or_introl eq_refl)); congruence.
  + rewrite IH. split.
    * intros H value [Hvalue|Hvalue].
      -- now subst value.
      -- now apply H.
    * intros H value Hvalue. apply H. now right.
Qed.

Local Lemma query_join_row_has_match_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) left rights,
    existsb (fun flag : bool => flag) (map (matches left) rights) =
    existsb (matches left) rights.
Proof.
intros matches left rights; induction rights as [|right rights IH]; cbn.
- reflexivity.
- now rewrite IH.
Qed.

Local Lemma query_join_matched_sources_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) left rights,
    query_join_matched_sources T left rights (map (matches left) rights) =
    map (fun right => JoinSourceMatched T (join_tuple T left right))
      (filter (matches left) rights).
Proof.
intros matches left rights; induction rights as [|head tail IH].
- reflexivity.
- rewrite (ListFacts.map_unfold (matches left) (head :: tail)).
  rewrite (ListFacts.filter_unfold (matches left) (head :: tail)).
  rewrite ListFacts.map_if.
  cbn [query_join_matched_sources].
  destruct (matches left head).
  + transitivity
      (JoinSourceMatched T (join_tuple T left head) ::
       map (fun right => JoinSourceMatched T (join_tuple T left right))
         (filter (matches left) tail)).
    * f_equal. exact IH.
    * symmetry. apply ListFacts.map_unfold.
  + exact IH.
Qed.

Local Lemma query_join_matched_sources_boolean_matrix_member_iff :
  forall (matches : tuple T -> tuple T -> bool) left rights output,
    In output
      (query_join_matched_sources T left rights
        (map (matches left) rights)) <->
    exists right,
      In right rights /\
      matches left right = true /\
      JoinSourceMatched T (join_tuple T left right) = output.
Proof.
intros matches left rights output.
rewrite query_join_matched_sources_boolean_matrix, in_map_iff.
split.
- intros [right [Houtput Hright]].
  apply filter_In in Hright.
  destruct Hright as [Hright Hmatch].
  exists right; repeat split; assumption.
- intros [right [Hright [Hmatch Houtput]]].
  exists right; split; [exact Houtput|].
  apply filter_In; now split.
Qed.

Local Lemma query_join_left_full_sources_boolean_matrix_member_iff :
  forall (matches : tuple T -> tuple T -> bool) lefts rights output,
    In output
      (query_join_left_sources T QueryJoinFull lefts rights
        (map (fun left => map (matches left) rights) lefts)) <->
    (exists left right,
      In left lefts /\
      In right rights /\
      matches left right = true /\
      JoinSourceMatched T (join_tuple T left right) = output) \/
    (exists left,
      In left lefts /\
      (forall right, In right rights -> matches left right = false) /\
      JoinSourceLeft T left = output).
Proof.
intros matches lefts; induction lefts as [|left lefts IH];
  intros rights output.
- cbn [query_join_left_sources]; split; [contradiction|].
  intros [[first [right [Hfirst _]]] | [first [Hfirst _]]]; contradiction.
- rewrite (ListFacts.map_unfold
    (fun left => map (matches left) rights) (left :: lefts)).
  cbn [query_join_left_sources].
  rewrite query_join_row_has_match_boolean_matrix.
  destruct (existsb (matches left) rights) eqn:Hexists.
  + rewrite List.in_app_iff,
      query_join_matched_sources_boolean_matrix_member_iff, IH.
    split.
    * intros
        [[right [Hright [Hmatch Houtput]]] |
         [[first [right [Hfirst [Hright [Hmatch Houtput]]]]] |
          [first [Hfirst [Hnone Houtput]]]]].
      -- left. exists left, right. repeat split; try assumption. now left.
      -- left. exists first, right. repeat split; try assumption. now right.
      -- right. exists first. repeat split; try assumption. now right.
    * intros
        [[first [right [[Hfirst|Hfirst] [Hright [Hmatch Houtput]]]]] |
         [first [[Hfirst|Hfirst] [Hnone Houtput]]]].
      -- subst first. left. exists right; repeat split; assumption.
      -- right; left. exists first, right. repeat split; assumption.
      -- subst first.
         exfalso.
         assert (Hfalse : existsb (matches left) rights = false).
         { apply (proj2 (list_existsb_false_iff
             (matches left) rights)); exact Hnone. }
         congruence.
      -- right; right. exists first; repeat split; assumption.
  + rewrite List.in_app_iff, IH; cbn.
    pose proof
      (proj1 (list_existsb_false_iff (matches left) rights) Hexists)
      as Hnone_left.
    split.
    * intros
        [[Houtput|Hnil] |
         [[first [right [Hfirst [Hright [Hmatch Hmatched]]]]] |
          [first [Hfirst [Hnone Hleft]]]]].
      -- right. exists left; repeat split; try assumption. now left.
      -- contradiction.
      -- left. exists first, right. repeat split; try assumption. now right.
      -- right. exists first; repeat split; try assumption. now right.
    * intros
        [[first [right [[Hfirst|Hfirst] [Hright [Hmatch Houtput]]]]] |
         [first [[Hfirst|Hfirst] [Hnone Houtput]]]].
      -- subst first; specialize (Hnone_left right Hright); congruence.
      -- right; left. exists first, right. repeat split; assumption.
      -- subst first; left; now left.
      -- right; right. exists first; repeat split; assumption.
Qed.

Local Lemma nth_map_at_app_boundary :
  forall (A B : Type) (mapping : A -> B) prefix head tail default,
    nth (length prefix) (map mapping (prefix ++ head :: tail)) default =
    mapping head.
Proof.
intros A B mapping prefix; induction prefix as [|first prefix IH];
  intros head tail default.
- cbn [List.app length].
  transitivity (nth 0 (mapping head :: map mapping tail) default).
  + exact (f_equal (fun values => nth 0 values default)
      (ListFacts.map_unfold mapping (head :: tail))).
  + reflexivity.
- cbn [List.app length].
  transitivity
    (nth (S (length prefix))
      (mapping first :: map mapping (prefix ++ head :: tail)) default).
  + exact (f_equal (fun values => nth (S (length prefix)) values default)
      (ListFacts.map_unfold mapping
        (first :: prefix ++ head :: tail))).
  + cbn [nth]. apply IH.
Qed.

Local Lemma query_join_column_boolean_matrix_at_prefix :
  forall (matches : tuple T -> tuple T -> bool) lefts prefix head tail,
    query_join_column_has_match (length prefix)
      (map (fun left => map (matches left) (prefix ++ head :: tail)) lefts) =
    existsb (fun left => matches left head) lefts.
Proof.
intros matches lefts; induction lefts as [|left lefts IH];
  intros prefix head tail.
- reflexivity.
- rewrite (ListFacts.map_unfold
    (fun left => map (matches left) (prefix ++ head :: tail))
    (left :: lefts)).
  unfold query_join_column_has_match.
  change
    (orb
      (nth (length prefix) (map (matches left) (prefix ++ head :: tail))
        false)
      (existsb (fun flags => nth (length prefix) flags false)
        (map (fun left => map (matches left) (prefix ++ head :: tail))
          lefts)) =
     orb (matches left head)
      (existsb (fun left => matches left head) lefts)).
  rewrite nth_map_at_app_boundary.
  f_equal.
  specialize (IH prefix head tail).
  unfold query_join_column_has_match in IH.
  exact IH.
Qed.

Local Lemma query_join_unmatched_right_sources_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) lefts prefix rights,
    query_join_unmatched_right_sources_from T (length prefix) rights
      (map (fun left => map (matches left) (prefix ++ rights)) lefts) =
    map (JoinSourceRight T)
      (filter
        (fun right => negb (existsb (fun left => matches left right) lefts))
        rights).
Proof.
intros matches lefts prefix rights.
induction rights as [|right rights IH] in prefix |- *.
- reflexivity.
- cbn [query_join_unmatched_right_sources_from].
  rewrite query_join_column_boolean_matrix_at_prefix.
  rewrite (ListFacts.filter_unfold
    (fun right => negb (existsb (fun left => matches left right) lefts))
    (right :: rights)).
  destruct (existsb (fun left => matches left right) lefts) eqn:Hmatch.
  + cbn.
    specialize (IH (prefix ++ (right :: nil))).
    replace (length (prefix ++ (right :: nil)))
      with (S (length prefix)) in IH.
    2: { rewrite length_app; cbn; lia. }
    replace ((prefix ++ (right :: nil)) ++ rights)
      with (prefix ++ right :: rights) in IH by now rewrite <- app_assoc.
    exact IH.
  + cbn.
    f_equal.
    specialize (IH (prefix ++ (right :: nil))).
    replace (length (prefix ++ (right :: nil)))
      with (S (length prefix)) in IH.
    2: { rewrite length_app; cbn; lia. }
    replace ((prefix ++ (right :: nil)) ++ rights)
      with (prefix ++ right :: rights) in IH by now rewrite <- app_assoc.
    exact IH.
Qed.

(** Exact support of the native FULL JOIN source scheduler for a concrete
    row-major Boolean match matrix.  The three disjuncts correspond precisely
    to a TRUE cell, a left row with no TRUE cell, and a right column with no
    TRUE cell.  Thus FALSE/UNKNOWN rejection remains represented by [false],
    and the native right-column index schedule is not abstracted away. *)
Theorem query_join_full_sources_member_iff :
  forall (matches : tuple T -> tuple T -> bool) lefts rights output,
    In output
      (query_join_sources T QueryJoinFull lefts rights
        (map (fun left => map (matches left) rights) lefts)) <->
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
intros matches lefts rights output.
unfold query_join_sources; cbn.
rewrite List.in_app_iff,
  query_join_left_full_sources_boolean_matrix_member_iff.
pose proof
  (query_join_unmatched_right_sources_boolean_matrix
    matches lefts (nil : list (tuple T)) rights) as Hunmatched.
cbn [length List.app] in Hunmatched.
rewrite Hunmatched.
split.
- intros [[Hmatched|Hleft]|Hright].
  + now left.
  + now right; left.
  + right; right.
    apply in_map_iff in Hright.
    destruct Hright as [right [Houtput Hright]].
    apply filter_In in Hright.
    destruct Hright as [Hinright Hnone].
    apply Bool.negb_true_iff in Hnone.
    pose proof
      (proj1
        (list_existsb_false_iff
          (fun left => matches left right) lefts) Hnone) as Hnone_left.
    exists right; repeat split; try assumption.
- intros [Hmatched|[Hleft|Hright]].
  + now left; left.
  + now left; right.
  + right. apply in_map_iff.
    destruct Hright as [right [Hright [Hnone Houtput]]].
    exists right; split; [exact Houtput|].
    apply filter_In; split; [exact Hright|].
    apply Bool.negb_true_iff.
    apply (proj2
      (list_existsb_false_iff
        (fun left => matches left right) lefts)).
    exact Hnone.
Qed.

(** FULL JOIN source support transports across arbitrary bidirectional input
    relations.  This is intentionally relation-parametric: a raw input row
    may correspond to a projected or grouped row with a different label set.
    The three emission premises retain the matched, left-unmatched, and
    right-unmatched branches separately. *)
Theorem query_join_full_projected_support_rel :
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
  [Hleft_forward Hleft_backward]
  [Hright_forward Hright_backward]
  Hmatch Hemit_matched Hemit_left Hemit_right.
split.
- intros output Houtput.
  apply in_map_iff in Houtput.
  destruct Houtput as [source [Houtput Hsource]]; subst output.
  apply query_join_full_sources_member_iff in Hsource.
  destruct Hsource as
    [[left [right [Hleft [Hright [Hmatches Hsource]]]]] |
     [[left [Hleft [Hnone Hsource]]] |
      [right [Hright [Hnone Hsource]]]]].
  + subst source.
    destruct (Hleft_forward left Hleft)
      as [left' [Hleft' Hleft_rel]].
    destruct (Hright_forward right Hright)
      as [right' [Hright' Hright_rel]].
    exists
      (right_emit
        (JoinSourceMatched T (join_tuple T left' right'))).
    split.
    * apply in_map_iff.
      exists (JoinSourceMatched T (join_tuple T left' right')).
      split; [reflexivity|].
      apply query_join_full_sources_member_iff.
      left; exists left', right'; repeat split; try assumption.
      now rewrite <-
        (Hmatch left left' right right' Hleft_rel Hright_rel).
    * now apply Hemit_matched.
  + subst source.
    destruct (Hleft_forward left Hleft)
      as [left' [Hleft' Hleft_rel]].
    exists (right_emit (JoinSourceLeft T left')).
    split.
    * apply in_map_iff; exists (JoinSourceLeft T left').
      split; [reflexivity|].
      apply query_join_full_sources_member_iff; right; left.
      exists left'; repeat split; try assumption.
      intros right' Hright'.
      destruct (Hright_backward right' Hright')
        as [right [Hright Hright_rel]].
      specialize (Hnone right Hright).
      now rewrite <-
        (Hmatch left left' right right' Hleft_rel Hright_rel).
    * now apply Hemit_left.
  + subst source.
    destruct (Hright_forward right Hright)
      as [right' [Hright' Hright_rel]].
    exists (right_emit (JoinSourceRight T right')).
    split.
    * apply in_map_iff; exists (JoinSourceRight T right').
      split; [reflexivity|].
      apply query_join_full_sources_member_iff; right; right.
      exists right'; repeat split; try assumption.
      intros left' Hleft'.
      destruct (Hleft_backward left' Hleft')
        as [left [Hleft Hleft_rel]].
      specialize (Hnone left Hleft).
      now rewrite <-
        (Hmatch left left' right right' Hleft_rel Hright_rel).
    * now apply Hemit_right.
- intros output Houtput.
  apply in_map_iff in Houtput.
  destruct Houtput as [source [Houtput Hsource]]; subst output.
  apply query_join_full_sources_member_iff in Hsource.
  destruct Hsource as
    [[left' [right' [Hleft' [Hright' [Hmatches Hsource]]]]] |
     [[left' [Hleft' [Hnone Hsource]]] |
      [right' [Hright' [Hnone Hsource]]]]].
  + subst source.
    destruct (Hleft_backward left' Hleft')
      as [left [Hleft Hleft_rel]].
    destruct (Hright_backward right' Hright')
      as [right [Hright Hright_rel]].
    exists
      (left_emit
        (JoinSourceMatched T (join_tuple T left right))).
    split.
    * apply in_map_iff.
      exists (JoinSourceMatched T (join_tuple T left right)).
      split; [reflexivity|].
      apply query_join_full_sources_member_iff.
      left; exists left, right; repeat split; try assumption.
      now rewrite
        (Hmatch left left' right right' Hleft_rel Hright_rel).
    * now apply Hemit_matched.
  + subst source.
    destruct (Hleft_backward left' Hleft')
      as [left [Hleft Hleft_rel]].
    exists (left_emit (JoinSourceLeft T left)).
    split.
    * apply in_map_iff; exists (JoinSourceLeft T left).
      split; [reflexivity|].
      apply query_join_full_sources_member_iff; right; left.
      exists left; repeat split; try assumption.
      intros right Hright.
      destruct (Hright_forward right Hright)
        as [right' [Hright' Hright_rel]].
      specialize (Hnone right' Hright').
      now rewrite
        (Hmatch left left' right right' Hleft_rel Hright_rel).
    * now apply Hemit_left.
  + subst source.
    destruct (Hright_backward right' Hright')
      as [right [Hright Hright_rel]].
    exists (left_emit (JoinSourceRight T right)).
    split.
    * apply in_map_iff; exists (JoinSourceRight T right).
      split; [reflexivity|].
      apply query_join_full_sources_member_iff; right; right.
      exists right; repeat split; try assumption.
      intros left Hleft.
      destruct (Hleft_forward left Hleft)
        as [left' [Hleft' Hleft_rel]].
      specialize (Hnone left' Hleft').
      now rewrite
        (Hmatch left left' right right' Hleft_rel Hright_rel).
    * now apply Hemit_right.
Qed.

(** Multiplicity-preserving finite-bag homomorphisms used below and by
    query-level rewrites.  Their properness premises are semantic: neither a
    predicate nor a row map may distinguish [OTuple]-equal representatives. *)
Lemma query_bag_filter_union :
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
intros keep left right Hproper.
apply bag_eq_iff_occurrences; intro row.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_filter.
2: intros first second _ Hequal; now apply Hproper.
rewrite 2 Febag.nb_occ_union.
rewrite 2 Febag.nb_occ_filter.
2,3: intros first second _ Hequal; now apply Hproper.
destruct (keep row); cbn; rewrite ?N.mul_1_r, ?N.mul_0_r; reflexivity.
Qed.

Lemma query_bag_map_union :
  forall (mapping : tuple T -> tuple T) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping (query_set_bag Union left right))
      (query_set_bag Union
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping left)
        (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
          mapping right)).
Proof.
intros mapping left right Hproper.
apply bag_eq_iff_occurrences; intro output.
unfold query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union.
unfold Febag.map.
rewrite 3 Febag.nb_occ_mk_bag.
rewrite <- Oeset.nb_occ_app, <- map_app.
apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
- intros first second Hequal; now apply Hproper.
- intro row.
  rewrite Oeset.nb_occ_app.
  rewrite <- 3 Febag.nb_occ_elements.
  apply Febag.nb_occ_union.
Qed.

Local Lemma query_bag_map_empty :
  forall mapping : tuple T -> tuple T,
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T)) mapping
        (Febag.empty (Fecol.CBag (CTuple T))))
      (Febag.empty (Fecol.CBag (CTuple T))).
Proof.
intro mapping; apply bag_eq_iff_occurrences; intro output.
unfold Febag.map.
rewrite Febag.elements_empty, Febag.nb_occ_mk_bag, Febag.nb_occ_empty.
reflexivity.
Qed.

Lemma query_bag_map_congr :
  forall (mapping : tuple T -> tuple T) (left right : bagT),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    bag_eq T left right ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping left)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping right).
Proof.
intros mapping left right Hproper Hbags.
apply bag_eq_iff_occurrences; intro output.
unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
- intros first second Hequal; now apply Hproper.
- intro row; rewrite <- 2 Febag.nb_occ_elements.
now apply (proj1 (bag_eq_iff_occurrences T left right) Hbags).
Qed.

(** Two independent semantic predicates commute as finite-bag filters.  This
    preserves every input multiplicity and does not identify FALSE with any
    other predicate result: the predicates here are already Boolean keep
    decisions. *)
Lemma query_bag_filter_commute :
  forall (first second : tuple T -> bool) (bag : bagT),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      first left = first right) ->
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      second left = second right) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) first
        (Febag.filter (Fecol.CBag (CTuple T)) second bag))
      (Febag.filter (Fecol.CBag (CTuple T)) second
        (Febag.filter (Fecol.CBag (CTuple T)) first bag)).
Proof.
intros first second bag Hfirst Hsecond.
apply bag_eq_iff_occurrences; intro row.
rewrite 4 Febag.nb_occ_filter;
  try solve
    [ intros left right _ Hequal; now apply Hfirst
    | intros left right _ Hequal; now apply Hsecond ].
destruct (first row), (second row); cbn;
  rewrite ?N.mul_0_r, ?N.mul_1_r; reflexivity.
Qed.

(** Filtering after a semantic row map is the same as filtering its input by
    the pulled-back predicate and then mapping.  This is a bag law, so it
    retains duplicate counts even when [mapping] merges several input rows. *)
Lemma query_bag_filter_map_fusion :
  forall (keep : tuple T -> bool) (mapping : tuple T -> tuple T) (bag : bagT),
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
intros keep mapping bag Hkeep Hmapping.
apply bag_eq_iff_occurrences; intro output.
pose proof
  (@Fecol.nb_occ_filter_map
    (tuple T) (tuple T)
    (OTuple T) (CTuple T) (OTuple T) (CTuple T)
    (Fecol.Fbag bag) mapping keep
    (fun left right _ Hequal => Hkeep left right Hequal)
    (fun left right _ _ Hequal => Hmapping left right Hequal)
    output) as Hfusion.
unfold Fecol.nb_occ in Hfusion.
cbn [Fecol.filter Fecol.map Fecol.elements] in Hfusion.
rewrite 2 Febag.nb_occ_elements.
exact Hfusion.
Qed.

(** Pairwise-equivalent maps of equally large bags produce the same output
    bag.  The equivalence premise is restricted to actual representatives of
    the two inputs; no global constant-map or nonemptiness premise is needed. *)
Lemma query_bag_map_pairwise_equiv_of_cardinal :
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
intros left_map right_map left right Hcardinal Hpairwise.
unfold Febag.cardinal in Hcardinal.
apply Nat2N.inj in Hcardinal.
apply bag_eq_iff_occurrences; intro output.
unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.permut_nb_occ.
remember (Febag.elements (Fecol.CBag (CTuple T)) left) as left_rows.
remember (Febag.elements (Fecol.CBag (CTuple T)) right) as right_rows.
assert (Hpermut :
  Oeset.permut (OTuple T)
    (map left_map left_rows) (map right_map right_rows)).
{
  subst left_rows right_rows.
  revert Hcardinal Hpairwise.
  generalize (Febag.elements (Fecol.CBag (CTuple T)) right).
  induction (Febag.elements (Fecol.CBag (CTuple T)) left)
    as [|left_row left_rows IH];
    intros right_rows Hlength Hequal.
  - destruct right_rows as [|right_row right_rows];
      [constructor | discriminate].
  - destruct right_rows as [|right_row right_rows]; [discriminate|].
    cbn in Hlength |- *.
    apply ListPermut.Pcons with
      (l1 := nil) (l2 := map right_map right_rows).
    + apply Hequal; [now left | now left].
    + apply IH.
      * now injection Hlength.
      * intros left' right' Hleft Hright.
        apply Hequal; [now right | now right].
}
exact Hpermut.
Qed.

(** Crossing a bag with one right occurrence is just a semantic row map of
    the left bag.  [Febag.elements] may choose an [OTuple]-equal singleton
    representative, hence the conclusion is bag equality rather than Rocq
    equality of the underlying bag implementations. *)
Lemma query_cross_join_bag_singleton_right_map :
  forall (left : bagT) right_row,
    bag_eq T
      (query_cross_join_bag left
        (Febag.singleton (Fecol.CBag (CTuple T)) right_row))
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun left_row => join_tuple T left_row right_row) left).
Proof.
intros left right_row.
destruct
  (Febag.elements_singleton (Fecol.CBag (CTuple T)) right_row)
  as [right_row' [Hright Hsingleton]].
assert (Hright_permut :
  Oeset.permut (OTuple T)
    (Febag.elements (Fecol.CBag (CTuple T))
      (Febag.singleton (Fecol.CBag (CTuple T)) right_row))
    (right_row :: nil)).
{
  rewrite Hsingleton.
  apply ListPermut.Pcons with (l1 := nil) (l2 := nil).
  - now apply Oeset.compare_eq_sym.
  - constructor.
}
apply bag_eq_iff_occurrences; intro output.
unfold query_cross_join_bag, Febag.map.
rewrite 2 Febag.nb_occ_mk_bag.
assert (Hcross :
  brute_left_join_list (tuple T) (join_tuple T)
    (Febag.elements (Fecol.CBag (CTuple T)) left) (right_row :: nil) =
  map (fun left_row => join_tuple T left_row right_row)
    (Febag.elements (Fecol.CBag (CTuple T)) left)).
{
  unfold brute_left_join_list, theta_join_list.
  induction (Febag.elements (Fecol.CBag (CTuple T)) left)
    as [|left_row left_rows IH]; [reflexivity|].
  rewrite ListFacts.flat_map_unfold.
  cbn [d_join_list].
  now f_equal.
}
apply Oeset.permut_nb_occ.
unfold brute_left_join_list.
eapply Oeset.permut_trans.
- apply (theta_join_list_permut_eq
    (tuple T) (OTuple T) (join_tuple T)
    (join_tuple_eq_1 T) (join_tuple_eq_2 T)
    (fun _ _ : tuple T => true)).
  + intros; reflexivity.
  + apply Oeset.permut_refl.
  + exact Hright_permut.
- rewrite <- Hcross.
  apply Oeset.permut_refl.
Qed.

Local Lemma query_set_union_elements_permut :
  forall left right : bagT,
    Oeset.permut (OTuple T)
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_set_bag Union left right))
      (Febag.elements (Fecol.CBag (CTuple T)) left ++
       Febag.elements (Fecol.CBag (CTuple T)) right).
Proof.
intros left right; apply Oeset.nb_occ_permut; intro row.
rewrite Oeset.nb_occ_app.
rewrite <- 3 Febag.nb_occ_elements.
unfold query_set_bag, Febag.interp_set_op; cbn.
apply Febag.nb_occ_union.
Qed.

Local Lemma query_cross_join_union_left :
  forall first second right : bagT,
    bag_eq T
      (query_cross_join_bag (query_set_bag Union first second) right)
      (query_set_bag Union
        (query_cross_join_bag first right)
        (query_cross_join_bag second right)).
Proof.
intros first second right.
apply bag_eq_iff_occurrences; intro output.
unfold query_cross_join_bag, query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union, 3 Febag.nb_occ_mk_bag.
rewrite <- Oeset.nb_occ_app.
apply Oeset.permut_nb_occ.
unfold brute_left_join_list.
eapply Oeset.permut_trans.
- apply (theta_join_list_permut_eq
    (tuple T) (OTuple T) (join_tuple T)
    (join_tuple_eq_1 T) (join_tuple_eq_2 T)
    (fun _ _ : tuple T => true)).
  + intros; reflexivity.
  + apply query_set_union_elements_permut.
  + apply Oeset.permut_refl.
- rewrite theta_join_list_app_1.
  apply Oeset.permut_refl.
Qed.

Local Lemma query_cross_join_union_right :
  forall left first second : bagT,
    bag_eq T
      (query_cross_join_bag left (query_set_bag Union first second))
      (query_set_bag Union
        (query_cross_join_bag left first)
        (query_cross_join_bag left second)).
Proof.
intros left first second.
apply bag_eq_iff_occurrences; intro output.
unfold query_cross_join_bag, query_set_bag, Febag.interp_set_op; cbn.
rewrite Febag.nb_occ_union, 3 Febag.nb_occ_mk_bag.
rewrite <- Oeset.nb_occ_app.
apply Oeset.permut_nb_occ.
unfold brute_left_join_list.
eapply Oeset.permut_trans.
- apply (theta_join_list_permut_eq
    (tuple T) (OTuple T) (join_tuple T)
    (join_tuple_eq_1 T) (join_tuple_eq_2 T)
    (fun _ _ : tuple T => true)).
  + intros; reflexivity.
  + apply Oeset.permut_refl.
  + apply query_set_union_elements_permut.
- apply _permut_incl with (@eq (tuple T)).
  + intros first_row second_row ->; apply Oeset.compare_eq_refl.
  + apply theta_join_list_app_2.
Qed.

End BagOperations.

(** Query-level facts connect the exact semantics to its possible-bag
    abstraction without introducing a second query language. *)

Section QueryBridges.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.

Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** Exact SQL-filter acceptance for one pair considered by a join.  The
    contract deliberately fixes only [Bool.is_true]: SQL FALSE and UNKNOWN
    may remain distinct formula outcomes, but both reject the pair.  The
    success witness and the explicit exclusion of errors are both essential;
    neither totality nor runtime safety is inferred from the Boolean flag. *)
Definition join_condition_acceptance_exact_at
    (env : Env.env T) (predicate : formula_expr T relname)
    (left right : tuple T) (accepted : bool) : Prop :=
  (exists truth,
    eval_formula (env_t T env (join_tuple T left right)) predicate
      (SqlSuccess truth) /\
    Bool.is_true (B T) truth = accepted) /\
  (forall truth,
    eval_formula (env_t T env (join_tuple T left right)) predicate
      (SqlSuccess truth) ->
    Bool.is_true (B T) truth = accepted) /\
  (forall error,
    ~ eval_formula (env_t T env (join_tuple T left right)) predicate
        (SqlError error)).

(** Pointwise exact acceptance determines the complete row-condition
    outcome.  In particular, this one theorem supplies both a successful flag
    list and the fact that condition evaluation cannot fail. *)
Lemma eval_join_row_conditions_acceptance_exact :
  forall env predicate left rights (accepted : tuple T -> bool),
    (forall right,
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted right)) ->
    forall outcome,
      @eval_join_row_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate left rights outcome <->
      outcome = SqlSuccess (map accepted rights).
Proof.
intros env predicate left rights.
induction rights as [|right rights IH]; intros accepted Haccepted outcome.
- split.
  + intro Heval; inversion Heval; reflexivity.
  + intro Houtcome; subst outcome; constructor.
- assert (Hhead :
    join_condition_acceptance_exact_at
      env predicate left right (accepted right)).
  { apply Haccepted; now left. }
  assert (Htail :
    forall tail,
      In tail rights ->
      join_condition_acceptance_exact_at
        env predicate left tail (accepted tail)).
  { intros tail Htail; apply Haccepted; now right. }
  destruct Hhead as
    [[truth [Htruth Htruth_accepted]]
      [Hsuccess_accepted Hno_error]].
  split.
  + intro Heval; inversion Heval; subst.
    * exfalso; eapply Hno_error; eassumption.
    * match goal with
      | Hformula : eval_formula _ predicate (SqlSuccess ?actual_truth),
        Hrest : context [eval_join_row_conditions_outcome] |- _ =>
          pose proof (Hsuccess_accepted actual_truth Hformula)
            as Hactual_accepted;
          apply (proj1 (IH accepted Htail _)) in Hrest;
          inversion Hrest; subst
      end.
      now rewrite Hactual_accepted.
  + intro Houtcome; subst outcome.
    cbn [map]; rewrite <- Htruth_accepted.
    eapply EJoinRowConditions_Cons with (truth := truth).
    * exact Htruth.
    * apply (proj2 (IH accepted Htail _)); reflexivity.
Qed.

(** Row-major lifting of
    [eval_join_row_conditions_acceptance_exact].  The resulting matrix is
    canonical for the given acceptance function, while the underlying Bool3
    successes may still be nondeterministic between FALSE and UNKNOWN. *)
Lemma eval_join_conditions_acceptance_exact :
  forall env predicate lefts rights
      (accepted : tuple T -> tuple T -> bool),
    (forall left right,
      In left lefts ->
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)) ->
    forall outcome,
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate lefts rights outcome <->
      outcome =
        SqlSuccess
          (map (fun left => map (accepted left) rights) lefts).
Proof.
intros env predicate lefts.
induction lefts as [|left lefts IH];
  intros rights accepted Haccepted outcome.
- split.
  + intro Heval; inversion Heval; reflexivity.
  + intro Houtcome; subst outcome; constructor.
- assert (Hrow :
    forall right,
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)).
  { intros right Hright; eapply Haccepted; [now left|exact Hright]. }
  assert (Htail :
    forall tail right,
      In tail lefts ->
      In right rights ->
      join_condition_acceptance_exact_at
        env predicate tail right (accepted tail right)).
  { intros tail right Htail Hright.
    eapply Haccepted; [now right|exact Hright]. }
  split.
  + intro Heval; inversion Heval; subst.
    * apply (proj1
        (eval_join_row_conditions_acceptance_exact
          (env := env) (predicate := predicate) (left := left)
          rights (accepted left) Hrow (SqlError _))) in H4.
      discriminate.
    * match goal with
      | Hrow_success : context [eval_join_row_conditions_outcome],
        Hrest : context [eval_join_conditions_outcome] |- _ =>
          apply (proj1
            (eval_join_row_conditions_acceptance_exact
              (env := env) (predicate := predicate) (left := left)
              rights (accepted left) Hrow
              (SqlSuccess _))) in Hrow_success;
          apply (proj1 (IH rights accepted Htail _)) in Hrest;
          inversion Hrow_success; inversion Hrest; subst
      end.
      reflexivity.
  + intro Houtcome; subst outcome.
    constructor.
    * apply (proj2
        (eval_join_row_conditions_acceptance_exact
          (env := env) (predicate := predicate) (left := left)
          rights (accepted left) Hrow _)).
      reflexivity.
    * apply (proj2 (IH rights accepted Htail _)); reflexivity.
Qed.

(** Exact per-source projection lifts to the complete source list without
    reopening the recursive [project_join_sources_outcome] implementation.
    The premise is intentionally restricted to sources that occur in the
    input list, so callers need not prove facts about unreachable branches. *)
Lemma project_join_sources_outcome_exact_map :
  forall env matched_select left_select right_select sources
      (emit : query_join_source T -> tuple T),
    (forall source,
      In source sources ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env
      matched_select left_select right_select sources =
    SqlSuccess (map emit sources).
Proof.
intros env matched_select left_select right_select sources.
induction sources as [|source sources IH]; intros emit Hexact.
- reflexivity.
- cbn [project_join_sources_outcome].
  rewrite (Hexact source (or_introl eq_refl)).
  rewrite (IH emit (fun tail Htail => Hexact tail (or_intror Htail))).
  reflexivity.
Qed.

(** A join whose reached condition evaluations and branch projections are
    exact is operationally safe: it has a successful bag outcome and cannot
    derive any SQL runtime error.  The theorem is independent of join kind
    and of the shape of either SELECT list.  All semantic safety is explicit
    in [Hconditions] and [Hprojection]; in particular, the theorem does not
    infer safety from schema membership, NULL behavior, or a Boolean model. *)
Theorem eval_join_bag_safe_of_acceptance_projection_exact :
  forall env kind predicate matched_select left_select right_select
      (accepted : tuple T -> tuple T -> bool)
      (emit : query_join_source T -> tuple T)
      left_bag right_bag,
    (forall left right,
      join_condition_acceptance_exact_at
        env predicate left right (accepted left right)) ->
    (forall source,
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    (exists output_bag,
      @eval_join_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env kind predicate matched_select left_select right_select
        left_bag right_bag (SqlSuccess output_bag)) /\
    (forall error,
      ~ @eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          env kind predicate matched_select left_select right_select
          left_bag right_bag (SqlError error)).
Proof.
intros env kind predicate matched_select left_select right_select
  accepted emit left_bag right_bag Hconditions Hprojection.
set (left_rows :=
  Febag.elements (Fecol.CBag (CTuple T)) left_bag).
set (right_rows :=
  Febag.elements (Fecol.CBag (CTuple T)) right_bag).
set (matrix :=
  map (fun left => map (accepted left) right_rows) left_rows).
set (sources :=
  query_join_sources T kind left_rows right_rows matrix).
set (projected := map emit sources).
assert (Hleft_rows : query_same_rows_as_bag left_rows left_bag).
{ unfold left_rows; apply query_elements_same_rows_as_bag. }
assert (Hright_rows : query_same_rows_as_bag right_rows right_bag).
{ unfold right_rows; apply query_elements_same_rows_as_bag. }
assert (Hcondition_success :
  @eval_join_conditions_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env predicate left_rows right_rows (SqlSuccess matrix)).
{
  unfold matrix.
  apply (proj2
    (eval_join_conditions_acceptance_exact
      (env := env) (predicate := predicate)
      left_rows right_rows accepted
      (fun left right _ _ => Hconditions left right)
      (SqlSuccess
        (map (fun left => map (accepted left) right_rows) left_rows)))).
  reflexivity.
}
assert (Hprojection_success :
  @project_join_sources_outcome T symbol_runtime_error
    aggregate_runtime_error env
    matched_select left_select right_select sources =
  SqlSuccess projected).
{
  unfold projected.
  apply project_join_sources_outcome_exact_map.
  intros source Hsource; apply Hprojection.
}
split.
- exists (rows_bag T projected).
  eapply EJoinBag_Success with
    (left_rows := left_rows) (right_rows := right_rows)
    (matrix := matrix) (projected := projected).
  + exact Hleft_rows.
  + exact Hright_rows.
  + exact Hcondition_success.
  + exact Hprojection_success.
  + apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl.
- intros error Heval.
  inversion Heval; subst.
  + apply (proj1
      (eval_join_conditions_acceptance_exact
        (env := env) (predicate := predicate)
        left_rows0 right_rows0 accepted
        (fun left right _ _ => Hconditions left right)
        (SqlError error))) in H9.
    discriminate.
  + pose proof
      (project_join_sources_outcome_exact_map
        env matched_select left_select right_select
        (query_join_sources T kind left_rows0 right_rows0 matrix0)
        emit (fun source _ => Hprojection source))
      as Hexact.
    rewrite Hexact in H10; discriminate.
Qed.

Lemma eval_join_row_conditions_success_length :
  forall env predicate left rights flags,
    @eval_join_row_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate left rights (SqlSuccess flags) ->
    length flags = length rights.
Proof.
intros env predicate left rights.
induction rights as [|right rights IH]; intros flags Heval.
- inversion Heval; reflexivity.
- inversion Heval; subst.
  cbn; f_equal; eapply IH; eassumption.
Qed.

Lemma eval_join_conditions_success_dimensions :
  forall env predicate lefts rights matrix,
    @eval_join_conditions_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate lefts rights (SqlSuccess matrix) ->
    length matrix = length lefts /\
    Forall (fun flags => length flags = length rights) matrix.
Proof.
intros env predicate lefts rights.
induction lefts as [|left lefts IH]; intros matrix Heval.
- inversion Heval; subst; split; [reflexivity|constructor].
- inversion Heval; subst.
  match goal with
  | Hrow : context [eval_join_row_conditions_outcome],
    Htail : context [eval_join_conditions_outcome] |- _ =>
      pose proof (eval_join_row_conditions_success_length Hrow) as Hflags;
      pose proof (IH _ Htail) as [Hlength Hforall]
  end.
  split; [cbn; now f_equal|constructor; assumption].
Qed.

(** Internal list facts for the partial-functional LEFT JOIN bridge below.
    They stay local so the agent-facing API exposes the semantic bag theorem,
    not the condition-matrix implementation. *)
Local Lemma query_join_matched_sources_length_exact :
  forall left rights flags,
    length flags = length rights ->
    length (query_join_matched_sources T left rights flags) =
    length (filter (fun flag : bool => flag) flags).
Proof.
intros left rights flags; revert flags.
induction rights as [|right rights IH];
  intros [|flag flags] Hlength; cbn in Hlength |- *;
  try discriminate; try reflexivity.
apply Nat.succ_inj in Hlength.
destruct flag; cbn; rewrite (IH flags Hlength); reflexivity.
Qed.

Local Lemma query_join_matched_sources_shape :
  forall left rights flags source,
    In source (query_join_matched_sources T left rights flags) ->
    exists right,
      In right rights /\
      source = JoinSourceMatched T (join_tuple T left right).
Proof.
intros left rights flags source; revert flags source.
induction rights as [|right rights IH];
  intros [|flag flags] source Hsource; cbn in Hsource;
  try contradiction.
destruct flag; cbn in Hsource.
- destruct Hsource as [Hsource|Hsource].
  + subst source; exists right; split; [now left|reflexivity].
  + destruct (IH flags source Hsource) as [matched [Hmatched Hshape]].
    exists matched; split; [now right|exact Hshape].
- destruct (IH flags source Hsource) as [matched [Hmatched Hshape]].
  exists matched; split; [now right|exact Hshape].
Qed.

Local Lemma query_join_left_row_sources_functional_singleton :
  forall left rights flags,
    length flags = length rights ->
    (length (filter (fun flag : bool => flag) flags) <= 1)%nat ->
    exists source,
      query_join_left_sources T QueryJoinLeft (left :: nil) rights
        (flags :: nil) = source :: nil /\
      (source = JoinSourceLeft T left \/
       exists right,
         In right rights /\
         source = JoinSourceMatched T (join_tuple T left right)).
Proof.
intros left rights flags Hdimension Hfunctional.
unfold query_join_row_has_match.
destruct (existsb (fun flag : bool => flag) flags) eqn:Hmatch.
- assert (Hfilter_nonempty :
    filter (fun flag : bool => flag) flags <> nil).
  { intro Hempty.
    apply existsb_exists in Hmatch as [flag [Hflag Htrue]].
    assert (Hin : In flag (filter (fun flag : bool => flag) flags)).
    { apply filter_In; now split. }
    now rewrite Hempty in Hin. }
  assert (Hfilter_length :
    length (filter (fun flag : bool => flag) flags) = 1).
  { destruct (filter (fun flag : bool => flag) flags)
      as [|flag tail] eqn:Hfilter; [contradiction|].
    destruct tail as [|second tail]; [reflexivity|].
    cbn in Hfunctional; lia. }
  pose proof
    (query_join_matched_sources_length_exact left rights flags Hdimension)
    as Hmatched_length.
  rewrite Hfilter_length in Hmatched_length.
  destruct (query_join_matched_sources T left rights flags)
    as [|source tail] eqn:Hmatched; cbn in Hmatched_length; [discriminate|].
  destruct tail as [|second tail]; [|cbn in Hmatched_length; discriminate].
  exists source; split.
  + cbn [query_join_left_sources].
    unfold query_join_row_has_match; rewrite Hmatch, Hmatched; reflexivity.
  + right.
    apply query_join_matched_sources_shape with
      (left := left) (flags := flags).
    rewrite Hmatched; now left.
- exists (JoinSourceLeft T left); split.
  + cbn [query_join_left_sources].
    unfold query_join_row_has_match; rewrite Hmatch; reflexivity.
  + now left.
Qed.

Local Lemma query_join_left_functional_projected_rows_permut :
  forall env matched_select left_select right_select
      (project emit : tuple T -> tuple T) lefts rights matrix projected,
    length matrix = length lefts ->
    Forall (fun flags => length flags = length rights) matrix ->
    Forall
      (fun flags =>
        (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
      matrix ->
    (forall left right output,
      In left lefts ->
      In right rights ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceMatched T (join_tuple T left right)) =
      SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    (forall left output,
      In left lefts ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceLeft T left) = SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env matched_select left_select right_select
      (query_join_sources T QueryJoinLeft lefts rights matrix) =
      SqlSuccess projected ->
    Oeset.permut (OTuple T) (map project projected) (map emit lefts).
Proof.
intros env matched_select left_select right_select project emit lefts.
induction lefts as [|left lefts IH];
  intros rights matrix projected Hlength Hdimensions Hfunctional
    Hmatched Hleft Hprojected.
- destruct matrix as [|flags matrix]; cbn in Hlength; [|discriminate].
  cbn [query_join_sources query_join_left_sources
    project_join_sources_outcome] in Hprojected.
  inversion Hprojected; subst projected; apply Oeset.permut_refl.
- destruct matrix as [|flags matrix]; cbn in Hlength; [discriminate|].
  apply Nat.succ_inj in Hlength.
  inversion Hdimensions as [|? ? Hdimension Hdimensions_tail]; subst.
  inversion Hfunctional as [|? ? Hfunctional_head Hfunctional_tail]; subst.
  assert (Hmatched_tail :
    forall tail_left right output,
      In tail_left lefts ->
      In right rights ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceMatched T (join_tuple T tail_left right)) =
      SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit tail_left) = Eq).
  { intros tail_left right output Htail Hright Hsource.
    exact (Hmatched tail_left right output
      (or_intror Htail) Hright Hsource). }
  assert (Hleft_tail :
    forall tail_left output,
      In tail_left lefts ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceLeft T tail_left) = SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit tail_left) = Eq).
  { intros tail_left output Htail Hsource.
    exact (Hleft tail_left output (or_intror Htail) Hsource). }
  destruct
    (query_join_left_row_sources_functional_singleton
      left rights flags Hdimension Hfunctional_head)
    as [source [Hrow_sources Hshape]].
  assert (Hsources :
    query_join_sources T QueryJoinLeft (left :: lefts) rights
      (flags :: matrix) =
    source :: query_join_sources T QueryJoinLeft lefts rights matrix).
  { unfold query_join_sources.
    cbn [query_join_left_sources] in Hrow_sources |- *.
    rewrite app_nil_r in Hrow_sources.
    rewrite Hrow_sources; reflexivity. }
  rewrite Hsources in Hprojected.
  cbn [project_join_sources_outcome] in Hprojected.
  destruct (@project_join_source_outcome T symbol_runtime_error
    aggregate_runtime_error env matched_select left_select right_select
    source) as [output|error] eqn:Hsource; [|discriminate].
  destruct (@project_join_sources_outcome T symbol_runtime_error
    aggregate_runtime_error env matched_select left_select right_select
    (query_join_sources T QueryJoinLeft lefts rights matrix))
    as [outputs|error] eqn:Htail; [|discriminate].
  inversion Hprojected; subst projected.
  assert (Hhead :
    Oeset.compare (OTuple T) (project output) (emit left) = Eq).
  { destruct Hshape as [Hshape|[right [Hright Hshape]]]; subst source.
    - exact (Hleft left output (or_introl eq_refl) Hsource).
    - exact (Hmatched left right output
        (or_introl eq_refl) Hright Hsource). }
  apply (proj1
    (Oeset.permut_cons (OTuple T)
      (project output) (emit left)
      (map project outputs) (map emit lefts) Hhead)).
  eapply IH; eassumption.
Qed.

(** Mapping a concrete representative and mapping its finite bag agree up to
    FormalSQL's semantic tuple equality, including duplicate counts.  This is
    the reusable boundary for deterministic row maps; it does not assert
    structural equality or choose a particular output order. *)
Lemma query_same_rows_as_bag_map :
  forall (mapping : tuple T -> tuple T) rows bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq) ->
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map mapping rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        mapping bag).
Proof.
intros mapping rows bag Hproper Hrows.
apply query_same_rows_as_bag_iff_bag_eq.
unfold bag_eq, rows_bag.
rewrite Febag.map_unfold, Febag.nb_occ_equal.
intro output; rewrite 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
- exact Hproper.
- intro row; apply Oeset.permut_nb_occ, Oeset.nb_occ_permut.
  intro input.
  rewrite <- Febag.nb_occ_elements.
  unfold query_same_rows_as_bag, query_rows_bag in Hrows.
  rewrite Febag.nb_occ_equal in Hrows.
  specialize (Hrows input).
  now rewrite Febag.nb_occ_mk_bag in Hrows.
Qed.

(** A successful partial-functional LEFT JOIN whose final projection erases
    the right payload is bag-equivalent to mapping the left input directly.
    The projection laws are scoped to representatives of the two input bags,
    so callers may discharge them from schema facts that hold only for rows
    produced by the input queries.  No total-match premise is present: a
    zero-match left occurrence is emitted through [left_select].  Runtime-error
    equivalence remains a separate obligation when this success-bag law is
    lifted to outcome equivalence. *)
Theorem query_join_left_functional_projection_bag_on_representatives :
  forall env predicate matched_select left_select right_select
      (project emit : tuple T -> tuple T) left_bag right_bag joined_bag,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (project first) (project second) = Eq) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    (forall left_rows right_rows matrix,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      @eval_join_conditions_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate left_rows right_rows (SqlSuccess matrix) ->
      Forall
        (fun flags =>
          (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
        matrix) ->
    (forall left_rows right_rows left right output,
      query_same_rows_as_bag left_rows left_bag ->
      query_same_rows_as_bag right_rows right_bag ->
      In left left_rows ->
      In right right_rows ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceMatched T (join_tuple T left right)) =
      SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    (forall left_rows left output,
      query_same_rows_as_bag left_rows left_bag ->
      In left left_rows ->
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env matched_select left_select right_select
        (JoinSourceLeft T left) = SqlSuccess output ->
      Oeset.compare (OTuple T) (project output) (emit left) = Eq) ->
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env QueryJoinLeft predicate matched_select left_select right_select
      left_bag right_bag (SqlSuccess joined_bag) ->
    bag_eq T
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        project joined_bag)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        emit left_bag).
Proof.
intros env predicate matched_select left_select right_select project emit
  left_bag right_bag joined_bag Hproject_proper Hemit_proper Hfunctional
  Hmatched Hleft Heval.
inversion Heval; subst.
pose proof (eval_join_conditions_success_dimensions H2)
  as [Hmatrix_length Hmatrix_dimensions].
pose proof (Hfunctional left_rows right_rows matrix H0 H1 H2)
  as Hmatrix_functional.
assert (Hmatched_rows :
  forall left right output,
    In left left_rows ->
    In right right_rows ->
    @project_join_source_outcome T symbol_runtime_error
      aggregate_runtime_error env matched_select left_select right_select
      (JoinSourceMatched T (join_tuple T left right)) =
    SqlSuccess output ->
    Oeset.compare (OTuple T) (project output) (emit left) = Eq).
{ intros left right output Hleft_in Hright_in Hsource.
  eapply Hmatched; eassumption. }
assert (Hleft_rows :
  forall left output,
    In left left_rows ->
    @project_join_source_outcome T symbol_runtime_error
      aggregate_runtime_error env matched_select left_select right_select
      (JoinSourceLeft T left) = SqlSuccess output ->
    Oeset.compare (OTuple T) (project output) (emit left) = Eq).
{ intros left output Hleft_in Hsource.
  eapply Hleft; eassumption. }
pose proof
  (query_join_left_functional_projected_rows_permut
    env matched_select left_select right_select project emit
    left_rows right_rows (matrix := matrix) (projected := projected)
    Hmatrix_length
    Hmatrix_dimensions Hmatrix_functional Hmatched_rows Hleft_rows H3)
  as Hpermut.
pose proof
  (query_same_rows_as_bag_map project
    (rows := projected) (bag := joined_bag) Hproject_proper H11)
  as Hjoined_map.
pose proof
  (query_same_rows_as_bag_map emit
    (rows := left_rows) (bag := left_bag) Hemit_proper H0)
  as Hleft_map.
apply query_same_rows_as_bag_iff_bag_eq in Hjoined_map, Hleft_map.
assert (Hrows :
  bag_eq T
    (rows_bag T (map project projected))
    (rows_bag T (map emit left_rows))).
{ unfold bag_eq, rows_bag.
  rewrite Febag.nb_occ_equal; intro row.
  rewrite 2 Febag.nb_occ_mk_bag.
  now apply Oeset.permut_nb_occ. }
eapply bag_eq_trans; [apply bag_eq_sym; exact Hjoined_map|].
eapply bag_eq_trans; [exact Hrows|exact Hleft_map].
Qed.

Lemma project_join_sources_success_length :
  forall env matched_select left_select right_select sources output,
    @project_join_sources_outcome T symbol_runtime_error
      aggregate_runtime_error env matched_select left_select right_select
      sources = SqlSuccess output ->
    length output = length sources.
Proof.
intros env matched_select left_select right_select sources.
induction sources as [|source sources IH]; intro output; cbn.
- inversion 1; reflexivity.
- destruct (@project_join_source_outcome T symbol_runtime_error
    aggregate_runtime_error env matched_select left_select right_select
    source); [|discriminate].
  destruct (@project_join_sources_outcome T symbol_runtime_error
    aggregate_runtime_error env matched_select left_select right_select
    sources) eqn:Htail; [|discriminate].
  inversion 1; subst output; cbn; f_equal.
  now apply IH with (output := l).
Qed.

Theorem eval_join_bag_success_cardinal_le :
  forall env kind predicate matched_select left_select right_select
         left_bag right_bag output_bag,
    @eval_join_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env kind
      predicate matched_select left_select right_select left_bag right_bag
      (SqlSuccess output_bag) ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) output_bag <=
     match kind with
     | QueryJoinInner =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinLeft =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         N.max 1 (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag)
     | QueryJoinRight =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag +
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinFull =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag *
         N.max 1 (Febag.cardinal (Fecol.CBag (CTuple T)) right_bag) +
         Febag.cardinal (Fecol.CBag (CTuple T)) right_bag
     | QueryJoinSemi | QueryJoinAnti =>
         Febag.cardinal (Fecol.CBag (CTuple T)) left_bag
     end)%N.
Proof.
intros env kind predicate matched_select left_select right_select
  left_bag right_bag output_bag Heval.
inversion Heval; subst.
pose proof (query_same_rows_as_bag_cardinal H0) as Hleft_cardinal.
pose proof (query_same_rows_as_bag_cardinal H1) as Hright_cardinal.
pose proof (query_same_rows_as_bag_cardinal H11) as Houtput_cardinal.
pose proof
  (project_join_sources_success_length env matched_select left_select right_select
    (query_join_sources T kind left_rows right_rows matrix) H3)
  as Hproject_length.
pose proof
  (query_join_sources_length_le kind left_rows right_rows matrix)
  as Hsource_bound.
assert (Hproject_bound :
  length projected <=
  match kind with
  | QueryJoinInner => length left_rows * length right_rows
  | QueryJoinLeft =>
      length left_rows * Nat.max 1 (length right_rows)
  | QueryJoinRight =>
      length left_rows * length right_rows + length right_rows
  | QueryJoinFull =>
      length left_rows * Nat.max 1 (length right_rows) +
      length right_rows
  | QueryJoinSemi | QueryJoinAnti => length left_rows
  end).
{
  rewrite Hproject_length.
  exact Hsource_bound.
}
rewrite Houtput_cardinal.
rewrite Hleft_cardinal, Hright_cardinal.
destruct kind; cbn in Hproject_bound |- *.
all: try replace (1%N) with (N.of_nat 1) by reflexivity.
all: try rewrite <- Nat2N.inj_max.
all: try rewrite <- Nat2N.inj_mul.
all: try rewrite <- Nat2N.inj_add.
all: apply (proj1 (N.compare_le_iff _ _));
  rewrite <- Nat2N.inj_compare;
  apply (proj2 (Nat.compare_le_iff _ _));
  exact Hproject_bound.
Qed.

Lemma query_grouping_sets_actual_success_bags_congr :
  forall env grouping_sets left right,
    rel_equiv (success_bags env left) (success_bags env right) ->
    rel_equiv
      (success_bags env (QExpr_GroupingSets grouping_sets left))
      (success_bags env (QExpr_GroupingSets grouping_sets right)).
Proof.
intros env grouping_sets left right Hinputs output_bag.
pose proof
  (query_grouping_sets_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env grouping_sets left output_bag) as Hleft.
pose proof
  (query_grouping_sets_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env grouping_sets right output_bag) as Hright.
pose proof
  (lift_possible_bag_unary_congr
    (query_grouping_sets_bag_relation basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env grouping_sets) Hinputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Hright), (proj1 Hlift), (proj1 Hleft), Hresult.
- apply (proj2 Hleft), (proj2 Hlift), (proj1 Hright), Hresult.
Qed.

Lemma query_expr_equiv_implies_success_bags :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
Proof.
intros env left right [_ Hobservations].
unfold query_expr_observation_equiv in Hobservations.
destruct Hobservations as [_ [_ [_ [Hforward Hbackward]]]].
now apply query_success_bags_of_success_rel_equiv.
Qed.

(** Error-preserving ordered equivalence also identifies the possible
    successful bags.  This projection requires neither runtime safety nor a
    successful outcome: if both exact relations are error-only, both possible
    success-bag relations are empty. *)
Lemma query_expr_outcome_equiv_implies_success_bags :
  forall env left right,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
Proof.
intros env left right [_ Hobservations].
unfold query_expr_outcome_observation_equiv in Hobservations.
destruct Hobservations as [_ [_ [Hforward [Hbackward _]]]].
now apply query_success_bags_of_success_rel_equiv.
Qed.

Lemma query_set_success_bags_congr_of_query_expr_equiv :
  forall env operation left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_Set operation left right))
      (success_bags env (QExpr_Set operation left' right')).
Proof.
intros env operation left left' right right' Hleft Hright.
pose proof (query_expr_equiv_implies_success_bags Hleft) as Hleft_bags.
pose proof (query_expr_equiv_implies_success_bags Hright) as Hright_bags.
destruct Hleft as [Hleft_outputs _].
destruct Hright as [Hright_outputs _].
apply query_set_success_bags_congr.
- now apply query_expr_outputs_eq_sort_eq.
- now apply query_expr_outputs_eq_sort_eq.
- exact Hleft_bags.
- exact Hright_bags.
Qed.

Lemma query_natural_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_NaturalJoin left right))
      (success_bags env (QExpr_NaturalJoin left' right')).
Proof.
intros env left left' right right' Hleft Hright.
apply query_natural_join_actual_success_bags_congr.
- now apply query_expr_equiv_implies_success_bags.
- now apply query_expr_equiv_implies_success_bags.
Qed.

Lemma query_cross_join_success_bags_congr_of_query_expr_equiv :
  forall env left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env (QExpr_CrossJoin left right))
      (success_bags env (QExpr_CrossJoin left' right')).
Proof.
intros env left left' right right' Hleft Hright.
apply query_cross_join_actual_success_bags_congr.
- now apply query_expr_equiv_implies_success_bags.
- now apply query_expr_equiv_implies_success_bags.
Qed.

Lemma query_join_success_bags_congr_of_query_expr_equiv :
  forall env kind predicate matched_select left_select right_select
         left left' right right',
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env right right' ->
    rel_equiv
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left' right')).
Proof.
intros env kind predicate matched_select left_select right_select
  left left' right right' Hleft Hright.
apply query_join_success_bags_congr.
- now apply query_expr_equiv_implies_success_bags.
- now apply query_expr_equiv_implies_success_bags.
Qed.

(** CROSS JOIN distributes over right-hand UNION ALL at the possible-success
    bag layer when the syntactically duplicated left child has a functional
    possible-bag relation.  Both set-operation sort tests remain explicit. *)
Theorem query_cross_join_union_right_success_bags :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    rel_equiv
      (success_bags env
        (QExpr_CrossJoin left (QExpr_Set Union first second)))
      (success_bags env
        (QExpr_Set Union
          (QExpr_CrossJoin left first)
          (QExpr_CrossJoin left second))).
Proof.
intros env left first second Hsource_sort Htarget_sort Hfunctional output.
split; intro Houtput.
- apply (proj1
    (query_cross_join_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left (QExpr_Set Union first second) output)) in Houtput.
  destruct Houtput as [left_bag [union_bag [Hleft [Hunion Hcross]]]].
  apply (proj1
    (query_set_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env Union first second union_bag)) in Hunion.
  destruct Hunion as [first_bag [second_bag
    [Hfirst [Hsecond Hunion]]]].
  unfold query_set_bag_relation, binary_bag_graph,
    query_set_bag_function in Hunion.
  rewrite (Fset.equal_eq_1 _ _ _ _ Hsource_sort), Fset.equal_refl in Hunion.
  apply (proj2
    (query_set_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env Union (QExpr_CrossJoin left first)
      (QExpr_CrossJoin left second) output)).
  exists (query_cross_join_bag left_bag first_bag).
  exists (query_cross_join_bag left_bag second_bag).
  split.
  + apply (proj2
      (query_cross_join_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left first (query_cross_join_bag left_bag first_bag))).
    exists left_bag, first_bag; split; [exact Hleft |].
    split; [exact Hfirst |].
    unfold query_cross_join_bag_relation, binary_bag_graph.
    apply bag_eq_refl.
  + split.
    * apply (proj2
        (query_cross_join_success_bags basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          env left second (query_cross_join_bag left_bag second_bag))).
      exists left_bag, second_bag; split; [exact Hleft |].
      split; [exact Hsecond |].
      unfold query_cross_join_bag_relation, binary_bag_graph.
      apply bag_eq_refl.
    * unfold query_set_bag_relation, binary_bag_graph,
        query_set_bag_function.
      rewrite (Fset.equal_eq_1 _ _ _ _ Htarget_sort), Fset.equal_refl.
      eapply bag_eq_trans.
      -- apply bag_eq_sym, query_cross_join_union_right.
      -- eapply bag_eq_trans.
         ++ apply query_cross_join_bag_congr;
              [apply bag_eq_refl | exact Hunion].
         ++ exact Hcross.
- apply (proj1
    (query_set_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env Union (QExpr_CrossJoin left first)
      (QExpr_CrossJoin left second) output)) in Houtput.
  destruct Houtput as [first_cross [second_cross
    [Hfirst_cross [Hsecond_cross Houter]]]].
  apply (proj1
    (query_cross_join_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left first first_cross)) in Hfirst_cross.
  apply (proj1
    (query_cross_join_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left second second_cross)) in Hsecond_cross.
  destruct Hfirst_cross as [left_bag [first_bag
    [Hleft [Hfirst Hfirst_cross]]]].
  destruct Hsecond_cross as [left_bag' [second_bag
    [Hleft' [Hsecond Hsecond_cross]]]].
  pose proof (Hfunctional _ _ Hleft Hleft') as Hleft_bags.
  apply (proj2
    (query_cross_join_success_bags basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left (QExpr_Set Union first second) output)).
  exists left_bag, (query_set_bag Union first_bag second_bag).
  split; [exact Hleft |].
  split.
  + apply (proj2
      (query_set_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env Union first second
        (query_set_bag Union first_bag second_bag))).
    exists first_bag, second_bag; split; [exact Hfirst |].
    split; [exact Hsecond |].
    unfold query_set_bag_relation, binary_bag_graph,
      query_set_bag_function.
    rewrite (Fset.equal_eq_1 _ _ _ _ Hsource_sort), Fset.equal_refl.
    apply bag_eq_refl.
  + unfold query_cross_join_bag_relation, binary_bag_graph.
    eapply bag_eq_trans.
    * apply query_cross_join_union_right.
    * eapply bag_eq_trans.
      -- apply query_set_bag_congr.
         ++ exact Hfirst_cross.
         ++ eapply bag_eq_trans.
            ** apply query_cross_join_bag_congr;
                 [exact Hleft_bags | apply bag_eq_refl].
            ** exact Hsecond_cross.
      -- unfold query_set_bag_relation, binary_bag_graph,
           query_set_bag_function in Houter.
         rewrite (Fset.equal_eq_1 _ _ _ _ Htarget_sort), Fset.equal_refl
           in Houter.
         exact Houter.
Qed.

End QueryBridges.
