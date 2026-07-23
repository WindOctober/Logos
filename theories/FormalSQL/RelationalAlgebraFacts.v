(************************************************************************************)
(** Reusable algebraic facts for FormalSQL relations, bags, and reset boundaries.  **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Arith NArith Lia SetoidList.
From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection Join ListFacts FlatData Env Bool3 Formula
  SqlAlgebra SqlOutcome SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics
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

Lemma gamma_rel_equiv :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T -> Prop),
    rel_equiv left right ->
    rel_equiv (gamma T left) (gamma T right).
Proof.
intros T left right Hequiv rows.
unfold gamma.
apply Hequiv.
Qed.

Lemma gamma_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : SqlBagAbstraction.bagT T -> Prop),
    rel_incl left right ->
    rel_incl (gamma T left) (gamma T right).
Proof.
intros T left right Hincl rows Hrows.
unfold gamma in *.
now apply Hincl.
Qed.

Lemma permutation_closure_rel_incl :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_incl left right ->
    rel_incl
      (permutation_closure T left)
      (permutation_closure T right).
Proof.
intros T left right Hincl rows Hrows.
unfold permutation_closure, gamma in *.
now apply (alpha_rel_incl Hincl).
Qed.

Lemma permutation_closure_rel_equiv :
  forall (T : Tuple.Rcd)
         (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    rel_equiv
      (permutation_closure T left)
      (permutation_closure T right).
Proof.
intros T left right Hequiv.
apply (proj2 (rel_equiv_iff_mutual_incl
  (permutation_closure T left) (permutation_closure T right))).
split; apply permutation_closure_rel_incl.
- intros rows Hrows; now apply (proj1 (Hequiv rows)).
- intros rows Hrows; now apply (proj2 (Hequiv rows)).
Qed.

Lemma permutation_closure_idempotent :
  forall (T : Tuple.Rcd) (observations : list (tuple T) -> Prop),
    rel_equiv
      (permutation_closure T (permutation_closure T observations))
      (permutation_closure T observations).
Proof.
intros T observations.
apply (proj1 (bag_closed_iff_fixed_point
  T (permutation_closure T observations))).
apply (@permutation_closure_bag_closed T observations).
Qed.

Lemma permutation_closure_least_bag_closed :
  forall (T : Tuple.Rcd)
         (observations target : list (tuple T) -> Prop),
    rel_incl observations target ->
    BagClosed T target ->
    rel_incl (permutation_closure T observations) target.
Proof.
intros T observations target Hincl Hclosed rows Hrows.
unfold permutation_closure, gamma, alpha in Hrows.
destruct Hrows as [source [Hsource Hbags]].
apply (proj1 (Hclosed source rows Hbags)).
now apply Hincl.
Qed.

Lemma bag_closed_rel_equiv_transport :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    rel_equiv left right ->
    BagClosed T left ->
    BagClosed T right.
Proof.
intros T left right Hequiv Hclosed first second Hbags.
destruct (Hequiv first) as [Hfirst_forward Hfirst_backward].
destruct (Hequiv second) as [Hsecond_forward Hsecond_backward].
destruct (Hclosed first second Hbags) as [Hclosed_forward Hclosed_backward].
split.
- intro H; apply Hsecond_forward, Hclosed_forward, Hfirst_backward, H.
- intro H; apply Hfirst_forward, Hclosed_backward, Hsecond_backward, H.
Qed.

Lemma bag_closed_intersection :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows /\ right rows).
Proof.
intros T left right Hleft Hright first second Hbags.
destruct (Hleft first second Hbags) as [Hleft_forward Hleft_backward].
destruct (Hright first second Hbags) as [Hright_forward Hright_backward].
split.
- intros [Hfirst_left Hfirst_right].
  split; [now apply Hleft_forward | now apply Hright_forward].
- intros [Hsecond_left Hsecond_right].
  split; [now apply Hleft_backward | now apply Hright_backward].
Qed.

Lemma bag_closed_union :
  forall (T : Tuple.Rcd) (left right : list (tuple T) -> Prop),
    BagClosed T left ->
    BagClosed T right ->
    BagClosed T (fun rows => left rows \/ right rows).
Proof.
intros T left right Hleft Hright first second Hbags.
destruct (Hleft first second Hbags) as [Hleft_forward Hleft_backward].
destruct (Hright first second Hbags) as [Hright_forward Hright_backward].
split.
- intros [Hfirst | Hfirst].
  + left; now apply Hleft_forward.
  + right; now apply Hright_forward.
- intros [Hsecond | Hsecond].
  + left; now apply Hleft_backward.
  + right; now apply Hright_backward.
Qed.

Lemma bag_closed_complement :
  forall (T : Tuple.Rcd) (predicate : list (tuple T) -> Prop),
    BagClosed T predicate ->
    BagClosed T (fun rows => ~ predicate rows).
Proof.
intros T predicate Hclosed first second Hbags.
destruct (Hclosed first second Hbags) as [Hforward Hbackward].
split.
- intros Hnot Hsecond; apply Hnot; now apply Hbackward.
- intros Hnot Hfirst; apply Hnot; now apply Hforward.
Qed.

Lemma bag_closed_exists :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => exists index, family index rows).
Proof.
intros T I family Hfamily first second Hbags; split.
- intros [index Hfirst].
  exists index.
  now apply (proj1 (Hfamily index first second Hbags)).
- intros [index Hsecond].
  exists index.
  now apply (proj2 (Hfamily index first second Hbags)).
Qed.

Lemma bag_closed_forall :
  forall (T : Tuple.Rcd) (I : Type)
         (family : I -> list (tuple T) -> Prop),
    (forall index, BagClosed T (family index)) ->
    BagClosed T (fun rows => forall index, family index rows).
Proof.
intros T I family Hfamily first second Hbags; split.
- intros Hfirst index.
  now apply (proj1 (Hfamily index first second Hbags)).
- intros Hsecond index.
  now apply (proj2 (Hfamily index first second Hbags)).
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

Corollary double_projection_query_bag_eq :
  forall (T : Tuple.Rcd) (relname : Type)
      (basesort : relname -> Fset.set (A T))
      (instance : relname -> Febag.bag (Fecol.CBag (CTuple T)))
      unknown contains_nulls env
      (outer_left inner_left outer_right inner_right : _select_list T)
      (input : query T relname),
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
      (@eval_query T relname basesort instance unknown contains_nulls env
        (@Q_Pi T relname outer_left (@Q_Pi T relname inner_left input)))
      (@eval_query T relname basesort instance unknown contains_nulls env
        (@Q_Pi T relname outer_right (@Q_Pi T relname inner_right input))).
Proof.
intros T relname basesort instance unknown contains_nulls env
  outer_left inner_left outer_right inner_right input Hrows.
rewrite (@eval_query_unfold T relname basesort instance unknown contains_nulls
  env (@Q_Pi T relname outer_left (@Q_Pi T relname inner_left input))).
rewrite (@eval_query_unfold T relname basesort instance unknown contains_nulls
  env (@Q_Pi T relname outer_right (@Q_Pi T relname inner_right input))).
now apply double_projection_bag_eq.
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

End BagOperations.

(** Query-level bridges: reset congruence, exact-to-bag abstraction, and the
    equivalence structure of deterministic bag queries. *)

Section QueryBridges.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable contains_nulls : tuple T -> bool.
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.

Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Lemma eval_join_row_conditions_success_length :
  forall env predicate left rights flags,
    @eval_join_row_conditions_outcome T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
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
    @eval_join_conditions_outcome T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null env predicate lefts rights (SqlSuccess matrix) ->
    length matrix = length lefts /\
    Forall (fun flags => length flags = length rights) matrix.
Proof.
intros env predicate lefts rights.
induction lefts as [|left lefts IH]; intros matrix Heval.
- inversion Heval; subst; split; [reflexivity|constructor].
- inversion Heval; subst.
  match goal with
  | Hrow : @eval_join_row_conditions_outcome
      _ _ _ _ _ _ _ _ _ _ _ _ _ (SqlSuccess ?flags),
    Htail : @eval_join_conditions_outcome
      _ _ _ _ _ _ _ _ _ _ _ _ _ (SqlSuccess ?tail) |- _ =>
      pose proof (eval_join_row_conditions_success_length Hrow) as Hflags;
      pose proof (IH tail Htail) as [Hlength Hforall]
  end.
  split; [cbn; now f_equal|constructor; assumption].
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
    @eval_join_bag_outcome T relname basesort instance unknown contains_nulls
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
  (query_grouping_sets_success_bags basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null
    env grouping_sets left output_bag) as Hleft.
pose proof
  (query_grouping_sets_success_bags basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null
    env grouping_sets right output_bag) as Hright.
pose proof
  (lift_possible_bag_unary_congr
    (query_grouping_sets_bag_relation basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env grouping_sets) Hinputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Hright), (proj1 Hlift), (proj1 Hleft), Hresult.
- apply (proj2 Hleft), (proj2 Hlift), (proj1 Hright), Hresult.
Qed.

Lemma query_expr_equiv_implies_success_bags :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    rel_equiv (success_bags env left) (success_bags env right).
Proof.
intros env left right [_ Hobservations].
unfold query_expr_observation_equiv in Hobservations.
destruct Hobservations as [_ [_ [_ [Hforward Hbackward]]]].
now apply query_success_bags_of_success_rel_equiv.
Qed.

Lemma query_set_success_bags_congr_of_query_expr_equiv :
  forall env operation left left' right right',
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
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
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
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
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
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
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left left' ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
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

Lemma qexpr_bag_equiv_iff_safe_occurrences :
  forall env outputs left right,
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (QExpr_Bag outputs left) (QExpr_Bag outputs right) <->
    bag_query_runtime_error basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env left = None /\
    bag_query_runtime_error basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env right = None /\
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (@eval_query T relname basesort instance unknown contains_nulls env left) =
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (@eval_query T relname basesort instance unknown contains_nulls env right).
Proof.
intros env outputs left right.
pose proof
  (@bag_query_expr_equiv_iff_bag_query_equiv
    T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null
    env outputs outputs left right eq_refl) as Hbridge.
split.
- intro Hequiv.
  apply (proj1 Hbridge) in Hequiv.
  apply bag_query_equiv_iff_success_and_bag_equality in Hequiv.
  destruct Hequiv as [Hleft [Hright Hbags]].
  split; [exact Hleft | split; [exact Hright |]].
  rewrite Febag.nb_occ_equal in Hbags.
  exact Hbags.
- intros [Hleft [Hright Hocc]].
  apply (proj2 Hbridge).
  apply bag_query_equiv_intro; [exact Hleft | exact Hright |].
  rewrite Febag.nb_occ_equal.
  exact Hocc.
Qed.

Lemma bag_query_equiv_refl_safe :
  forall env query,
    bag_query_runtime_error basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query query.
Proof.
intros env query Hsafe.
apply bag_query_equiv_intro; [exact Hsafe | exact Hsafe |].
apply Febag.equal_refl.
Qed.

Lemma bag_query_equiv_sym :
  forall env left right,
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env left right ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env right left.
Proof.
intros env left right Hequiv.
apply bag_query_equiv_iff_success_and_bag_equality in Hequiv.
destruct Hequiv as [Hleft [Hright Hbags]].
apply bag_query_equiv_intro; [exact Hright | exact Hleft |].
now apply Febag.equal_sym.
Qed.

Lemma bag_query_equiv_trans :
  forall env first second third,
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env first second ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env second third ->
    bag_query_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env first third.
Proof.
intros env first second third Hfirst Hsecond.
apply bag_query_equiv_iff_success_and_bag_equality in Hfirst.
apply bag_query_equiv_iff_success_and_bag_equality in Hsecond.
destruct Hfirst as [Hfirst_safe [_ Hfirst_bags]].
destruct Hsecond as [_ [Hthird_safe Hsecond_bags]].
apply bag_query_equiv_intro; [exact Hfirst_safe | exact Hthird_safe |].
eapply Febag.equal_trans; [exact Hfirst_bags | exact Hsecond_bags].
Qed.

End QueryBridges.
