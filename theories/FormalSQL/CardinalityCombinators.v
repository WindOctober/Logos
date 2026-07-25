(************************************************************************************)
(** Reusable list, bag, finite-domain, join, and grouping cardinality combinators. **)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  OrderedSet Join Partition ListFacts ListPermut SchemaConstraints.
From Stdlib Require Import List SetoidList PeanoNat NArith Lia.

Import ListNotations.
Import Tuple.

(** Mapping a bag may merge equal output values, but it preserves the sum of
    all occurrence multiplicities. *)
Lemma bag_map_cardinal :
  forall (A B : Type) (OA : Oeset.Rcd A) (OB : Oeset.Rcd B)
      (CA : Fecol.Rcd OA) (CB : Fecol.Rcd OB)
      (mapping : A -> B) (bag : Febag.bag (Fecol.CBag CA)),
    Febag.cardinal (Fecol.CBag CB)
      (Febag.map (Fecol.CBag CA) (Fecol.CBag CB) mapping bag) =
    Febag.cardinal (Fecol.CBag CA) bag.
Proof.
intros A B OA OB CA CB mapping bag.
unfold Febag.map.
rewrite Febag.cardinal_mk_bag, length_map.
reflexivity.
Qed.

(** A semantically proper Boolean filter cannot increase bag cardinality. *)
Lemma bag_filter_cardinal_le :
  forall (A : Type) (OA : Oeset.Rcd A) (CA : Fecol.Rcd OA)
      (keep : A -> bool) (bag : Febag.bag (Fecol.CBag CA)),
    (forall left right,
      (Febag.nb_occ (Fecol.CBag CA) left bag >= 1)%N ->
      Oeset.compare OA left right = Eq ->
      keep left = keep right) ->
    (Febag.cardinal (Fecol.CBag CA)
       (Febag.filter (Fecol.CBag CA) keep bag) <=
     Febag.cardinal (Fecol.CBag CA) bag)%N.
Proof.
intros A OA CA keep bag Hproper.
pose proof
  (@Febag.mk_bag_filter A OA (Fecol.CBag CA) keep bag Hproper) as Hequal.
pose proof
  (@Febag.cardinal_eq A OA (Fecol.CBag CA) _ _ Hequal) as Hcardinal.
rewrite Febag.cardinal_mk_bag in Hcardinal.
unfold Febag.cardinal in Hcardinal |- *.
eapply N.le_trans with
  (m := N.of_nat
    (length (filter keep (Febag.elements (Fecol.CBag CA) bag)))).
- now rewrite Hcardinal.
- apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare.
  apply Nat.compare_le_iff, List.filter_length_le.
Qed.

(** Independent Boolean filters commute while preserving occurrence order. *)
Lemma filter_filter_commute :
  forall (A : Type) (first second : A -> bool) rows,
    filter first (filter second rows) =
    filter second (filter first rows).
Proof.
intros A first second rows.
rewrite !ListFacts.filter_filter.
apply ListFacts.filter_eq.
intros row _.
apply Bool.andb_comm.
Qed.

(** A uniformly bounded expansion multiplies the input occurrence bound. *)
Lemma flat_map_uniform_length_le :
  forall (A B : Type) (expand : A -> list B) rows bound,
    (forall row,
      In row rows ->
      (List.length (expand row) <= bound)%nat) ->
    (List.length (flat_map expand rows) <=
      List.length rows * bound)%nat.
Proof.
intros A B expand rows.
induction rows as [|row rows IH]; intros bound Hbound; cbn.
- lia.
- rewrite length_app.
  pose proof (Hbound row (or_introl eq_refl)) as Hhead.
  specialize (IH bound (fun other Hother =>
    Hbound other (or_intror _ Hother))).
  nia.
Qed.

(** Nonempty groups consume at least one occurrence apiece. *)
Lemma nonempty_groups_count_le_total_length :
  forall (A Group : Type) (members : Group -> list A) groups,
    Forall (fun group => members group <> nil) groups ->
    (List.length groups <= List.length (flat_map members groups))%nat.
Proof.
intros A Group members groups Hgroups.
induction Hgroups as [|group groups Hgroup Hgroups IH]; cbn.
- lia.
- rewrite length_app.
  destruct (members group) as [|member rest] eqn:Hmembers.
  + exfalso; now apply Hgroup.
  + cbn; lia.
Qed.

(** Pairwise-related accepted members of a semantic-duplicate-free list form
    an at-most-one lookup result.  No reflexivity or structural equality is
    assumed for the relation. *)
Lemma NoDupA_pairwise_filter_length_le_one :
  forall (A : Type) (relation : A -> A -> Prop)
      (keep : A -> bool) rows,
    NoDupA relation rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      keep left = true ->
      keep right = true ->
      relation left right) ->
    (List.length (filter keep rows) <= 1)%nat.
Proof.
intros A relation keep rows Hnodup.
induction Hnodup as [|first rest Hfirst Hrest IH]; intro Hpairwise; cbn.
- lia.
- destruct (keep first) eqn:Hkeep; cbn.
  + assert (Hempty : filter keep rest = nil).
    {
      apply ListFacts.filter_false.
      intros other Hother.
      destruct (keep other) eqn:Hother_keep; [|reflexivity].
      exfalso.
      apply Hfirst.
      apply InA_alt.
      exists other.
      split.
      - eapply Hpairwise.
        + now left.
        + now right.
        + exact Hkeep.
        + exact Hother_keep.
      - exact Hother.
    }
    rewrite Hempty; cbn; lia.
  + apply IH.
    intros left right Hleft Hright Hleft_keep Hright_keep.
    eapply Hpairwise; [now right|now right| |]; eassumption.
Qed.

(** A nonempty Boolean selection with at most one occurrence is a singleton.
    This packages the existence and uniqueness obligations commonly obtained
    from a foreign key plus a referenced UNIQUE or PRIMARY KEY constraint. *)
Lemma filter_singleton_of_nonempty_length_le_one :
  forall (A : Type) (keep : A -> bool) rows,
    (exists row, In row rows /\ keep row = true) ->
    (List.length (filter keep rows) <= 1)%nat ->
    exists row, filter keep rows = [row].
Proof.
intros A keep rows [row [Hin Hkeep]] Hlength.
assert (Hnonempty : filter keep rows <> nil).
{
  intro Hempty.
  assert (In row (filter keep rows)).
  { apply filter_In; now split. }
  now rewrite Hempty in H.
}
destruct (filter keep rows) as [|first rest] eqn:Hfilter; [contradiction|].
destruct rest as [|second rest].
- now exists first.
- cbn in Hlength; lia.
Qed.

(** If every left row has exactly one accepted right row and the final
    projection erases the right payload, mapping a theta join is exactly a
    pointwise map of the left input.  Duplicate left rows remain duplicated. *)
Lemma map_theta_join_total_functional :
  forall (A B : Type)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project : A -> B) (emit : A -> B) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (theta_join_list A join accept left right) = map emit left.
Proof.
intros A B join accept project emit left right Hproject Htotal Hfunctional.
induction left as [|left_row left_rows IH]; [reflexivity|].
change
  (map project
    (map (join left_row) (filter (accept left_row) right) ++
      theta_join_list A join accept left_rows right) =
   emit left_row :: map emit left_rows).
destruct
  (filter_singleton_of_nonempty_length_le_one A (accept left_row) right)
  as [right_row Hright].
- apply Htotal; now left.
- apply Hfunctional; now left.
- rewrite Hright; cbn; rewrite Hproject, IH; [reflexivity| |].
  + intros row Hrow; apply Htotal; now right.
  + intros row Hrow; apply Hfunctional; now right.
Qed.

(** A partial-functional theta join is a semijoin after projecting away the
    right payload.  Each left occurrence with an accepted match contributes
    exactly one output occurrence; left occurrences without a match contribute
    none.  The projection law is required only for accepted input pairs, and
    semantic permutation preserves arbitrary equal representatives. *)
Lemma map_theta_join_functional_permut_filter_exists :
  forall (A B : Type) (OB : Oeset.Rcd B)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project emit : A -> B) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      Oeset.compare OB (project (join left_row right_row))
        (emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    Oeset.permut OB
      (map project (theta_join_list A join accept left right))
      (map emit
        (filter
          (fun left_row => existsb (accept left_row) right) left)).
Proof.
intros A B OB join accept project emit left right Hproject Hfunctional.
unfold theta_join_list.
induction left as [|left_row left_rows IH]; cbn.
- apply Oeset.permut_refl.
- destruct (existsb (accept left_row) right) eqn:Hexists.
  + apply existsb_exists in Hexists as [right_row [Hright Haccept]].
    destruct
      (filter_singleton_of_nonempty_length_le_one A
        (accept left_row) right)
      as [only Hmatches].
    * exists right_row; now split.
    * apply Hfunctional; now left.
    * assert (Hselected : In only (filter (accept left_row) right)).
      { rewrite Hmatches; now left. }
      apply filter_In in Hselected as [Honly Honly_accept].
      unfold d_join_list.
      rewrite Hmatches; cbn.
      apply
        (proj1
          (Oeset.permut_cons OB
            (project (join left_row only)) (emit left_row)
            (map project
              (flat_map
                (fun row => d_join_list A join accept row right)
                left_rows))
            (map emit
              (filter
                (fun row => existsb (accept row) right) left_rows))
            (Hproject left_row only
              (or_introl eq_refl) Honly Honly_accept))).
      apply IH.
      -- intros row other Hrow Hother Haccepted.
         apply Hproject; [now right | exact Hother | exact Haccepted].
      -- intros row Hrow; apply Hfunctional; now right.
  + assert (Hmatches : filter (accept left_row) right = nil).
    {
      destruct (filter (accept left_row) right)
        as [|right_row rest] eqn:Hfilter; [reflexivity|].
      assert (Hselected : In right_row (filter (accept left_row) right)).
      { rewrite Hfilter; now left. }
      apply filter_In in Hselected as [Hright Haccept].
      assert (Htrue : existsb (accept left_row) right = true).
      { apply existsb_exists; exists right_row; now split. }
      rewrite Hexists in Htrue; discriminate.
    }
    unfold d_join_list.
    rewrite Hmatches; cbn.
    apply IH.
    * intros row other Hrow Hother Haccepted.
      apply Hproject; [now right | exact Hother | exact Haccepted].
    * intros row Hrow; apply Hfunctional; now right.
Qed.

(** Total matching makes the unmatched-left branch of an anti join empty. *)
Lemma anti_filter_empty_of_total_match :
  forall (A B : Type) (accept : A -> B -> bool) left right,
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    filter
      (fun left_row => negb (existsb (accept left_row) right)) left = nil.
Proof.
intros A B accept left right Htotal.
induction left as [|left_row left_rows IH]; [reflexivity|].
destruct (Htotal left_row) as [right_row [Hright Haccept]].
{ now left. }
assert (Hexists : existsb (accept left_row) right = true).
{ apply existsb_exists; exists right_row; now split. }
cbn; rewrite Hexists; cbn; apply IH.
intros row Hrow; apply Htotal; now right.
Qed.

(** Under total functional matching, the projected expansion of a left join
    is the same pointwise map as its inner-join branch; the NULL-padded branch
    is unreachable. *)
Lemma map_left_join_total_functional :
  forall (A B : Type)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project : A -> B) (emit : A -> B) (pad : A -> A) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left -> project (pad left_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (theta_join_list A join accept left right) ++
      map project
        (map pad
          (filter
            (fun left_row => negb (existsb (accept left_row) right)) left)) =
    map emit left.
Proof.
intros A B join accept project emit pad left right
  Hproject Hpad Htotal Hfunctional.
rewrite (anti_filter_empty_of_total_match A A accept left right Htotal).
cbn [map]; rewrite app_nil_r.
now apply map_theta_join_total_functional.
Qed.

(** If every left occurrence has at most one accepted right occurrence and the
    final projection erases the right payload, a left join preserves exactly
    the multiplicity of the left input.  Unlike the total-functional law above,
    this theorem permits zero matches: the NULL-padded branch then supplies the
    corresponding output occurrence.  The conclusion is permutation rather
    than list equality because matched and padded rows occupy separate branches
    of the list implementation. *)
Lemma map_left_join_functional_permut :
  forall (A B : Type) (OB : Oeset.Rcd B)
      (join : A -> A -> A) (accept : A -> A -> bool)
      (project : A -> B) (emit : A -> B) (pad : A -> A) left right,
    (forall left_row right_row,
      Oeset.compare OB (project (join left_row right_row))
        (emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      Oeset.compare OB (project (pad left_row)) (emit left_row) = Eq) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    Oeset.permut OB
      (map project
        (theta_join_list A join accept left right ++
         map pad
           (filter
             (fun left_row => negb (existsb (accept left_row) right)) left)))
      (map emit left).
Proof.
intros A B OB join accept project emit pad left right
  Hproject Hpad Hfunctional.
induction left as [|left_row rest IH]; [apply Oeset.permut_refl|].
specialize (IH
  (fun row Hrow => Hpad row (or_intror _ Hrow))
  (fun row Hrow => Hfunctional row (or_intror _ Hrow))).
unfold theta_join_list, d_join_list in IH.
unfold List.flat_map in IH.
unfold theta_join_list.
unfold List.flat_map at 1.
unfold d_join_list.
destruct (existsb (accept left_row) right) eqn:Hexists; cbn [filter].
- pose proof Hexists as Hexists_eq.
  apply existsb_exists in Hexists as [matched [Hmatched Haccept]].
  destruct
    (filter_singleton_of_nonempty_length_le_one A (accept left_row) right)
    as [only Hmatches].
  { exists matched; now split. }
  { apply Hfunctional; now left. }
  rewrite Hmatches, Hexists_eq; cbn.
  apply (proj1
    (Oeset.permut_cons OB _ _ _ _ (Hproject left_row only))).
  exact IH.
- assert (Hmatches : filter (accept left_row) right = nil).
  { destruct (filter (accept left_row) right) as [|matched tail] eqn:Hfilter;
      [reflexivity|].
    assert (Hin : In matched (filter (accept left_row) right)).
    { rewrite Hfilter; now left. }
    apply filter_In in Hin as [Hmatched Haccept].
    assert (Htrue : existsb (accept left_row) right = true).
    { apply existsb_exists; exists matched; now split. }
    rewrite Hexists in Htrue; discriminate. }
  rewrite Hmatches, Hexists; cbn.
  rewrite map_app; cbn.
  rewrite map_app in IH.
  match goal with
  | |- Oeset.permut OB
      (?before ++ project (pad left_row) :: ?after)
      (emit left_row :: ?target) =>
    eapply Oeset.permut_trans;
    [ apply Oeset.permut_sym;
      apply (proj1
        (Oeset.permut_cons_inside OB
          (project (pad left_row)) (project (pad left_row))
          (before ++ after) before after
          (Oeset.compare_eq_refl OB _)));
      apply Oeset.permut_refl
    | apply (proj1
        (Oeset.permut_cons OB
          (project (pad left_row)) (emit left_row)
          (before ++ after) target
          (Hpad left_row (or_introl eq_refl))));
      exact IH ]
  end.
Qed.

(** Semantic duplicate-freedom of a mapped list pulls back to the source
    through the induced relation, without assuming that the map is injective. *)
Lemma NoDupA_map_preimage :
  forall (A B : Type) (relation : B -> B -> Prop)
      (project : A -> B) rows,
    NoDupA relation (map project rows) ->
    NoDupA
      (fun left right => relation (project left) (project right)) rows.
Proof.
intros A B relation project rows.
induction rows as [|first rest IH]; intro Hnodup; cbn in Hnodup |- *.
- constructor.
- inversion Hnodup as [|? ? Hfirst Hrest]; subst.
  constructor.
  + intro Hin.
    apply InA_alt in Hin as [other [Hrelated Hother]].
    apply Hfirst.
    apply InA_alt.
    exists (project other).
    split.
    * exact Hrelated.
    * now apply in_map.
  + now apply IH.
Qed.

(** Semantic duplicate-freedom transports forward through a map whenever
    equality of mapped outputs reflects the source relation on represented
    inputs.  No global injectivity or equivalence instance is required. *)
Lemma NoDupA_map_of_reflection :
  forall (A B : Type) (source_relation : A -> A -> Prop)
      (target_relation : B -> B -> Prop) (project : A -> B) rows,
    NoDupA source_relation rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      target_relation (project left) (project right) ->
      source_relation left right) ->
    NoDupA target_relation (map project rows).
Proof.
intros A B source_relation target_relation project rows Hnodup.
induction Hnodup as [|first rest Hfirst Hrest IH]; intro Hreflect; cbn.
- constructor.
- constructor.
  + intro Hin.
    apply InA_alt in Hin as [projected [Hrelated Hin]].
    apply in_map_iff in Hin as [other [Heq Hother]].
    subst projected.
    apply Hfirst.
    apply InA_alt.
    exists other; split.
    * apply Hreflect; [now left | now right | exact Hrelated].
    * exact Hother.
  + apply IH.
    intros left right Hleft Hright Hrelated.
    apply Hreflect; [now right | now right | exact Hrelated].
Qed.

(** A functional filtered expansion preserves duplicate-freedom whenever
    equality of two accepted outputs reflects a source relation.  The right
    side may be empty for any source occurrence; total matching is unnecessary.
    Both relations are intentionally arbitrary, so callers may use a primary
    key relation on source rows and semantic tuple equality on outputs. *)
Lemma NoDupA_flat_map_filter_map_functional_reflection :
  forall (Left Right Output : Type)
      (source_relation : Left -> Left -> Prop)
      (target_relation : Output -> Output -> Prop)
      (accept : Left -> Right -> bool)
      (emit : Left -> Right -> Output)
      left right,
    NoDupA source_relation left ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (forall left_first left_second right_first right_second,
      In left_first left -> In left_second left ->
      In right_first right -> In right_second right ->
      accept left_first right_first = true ->
      accept left_second right_second = true ->
      target_relation
        (emit left_first right_first) (emit left_second right_second) ->
      source_relation left_first left_second) ->
    NoDupA target_relation
      (flat_map
        (fun left_row =>
          map (emit left_row) (filter (accept left_row) right)) left).
Proof.
intros Left Right Output source_relation target_relation accept emit
  left right Hleft.
induction Hleft as [|head tail Hhead Htail IH];
  intros Hfunctional Hreflect; cbn.
- constructor.
- pose proof (Hfunctional head (or_introl eq_refl)) as Hheadfun.
  destruct (filter (accept head) right) as [|matched rest] eqn:Hmatches.
  + cbn. apply IH.
    * intros row Hrow; apply Hfunctional; now right.
    * intros l1 l2 r1 r2 Hl1 Hl2 Hr1 Hr2 Ha1 Ha2 Hout.
      eapply Hreflect with (right_first := r1) (right_second := r2);
        [now right|now right|exact Hr1|exact Hr2|exact Ha1|exact Ha2|exact Hout].
  + destruct rest as [|other rest].
    * assert (Hmatched : In matched right /\ accept head matched = true).
      { apply filter_In. rewrite Hmatches; now left. }
      cbn. constructor.
      -- intro Hin.
         apply InA_alt in Hin as [out [Hout Hin]].
         apply in_flat_map in Hin as [tail_row [Htail_row Hin]].
         apply in_map_iff in Hin as [right_row [Heq Hright_row]].
         subst out.
         apply filter_In in Hright_row as [Hright_row Haccept_right].
         apply Hhead, InA_alt.
         exists tail_row; split.
         ++ eapply Hreflect.
            ** now left.
            ** now right.
            ** exact (proj1 Hmatched).
            ** exact Hright_row.
            ** exact (proj2 Hmatched).
            ** exact Haccept_right.
            ** exact Hout.
         ++ exact Htail_row.
      -- apply IH.
         ++ intros row Hrow; apply Hfunctional; now right.
         ++ intros l1 l2 r1 r2 Hl1 Hl2 Hr1 Hr2 Ha1 Ha2 Hout.
            eapply Hreflect with (right_first := r1) (right_second := r2);
              [now right|now right|exact Hr1|exact Hr2|exact Ha1|exact Ha2|exact Hout].
    * cbn in Hheadfun; lia.
Qed.

(** A locally exact semantic-equality code gives an iff between [NoDupA] and
    structural duplicate-freedom of the coded list. *)
Lemma NoDupA_map_iff_NoDup_on :
  forall (A Code : Type) (relation : A -> A -> Prop)
      (code : A -> Code) rows,
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <-> code left = code right)) ->
    (NoDupA relation rows <-> NoDup (map code rows)).
Proof.
intros A Code relation code rows.
induction rows as [|first rest IH]; intro Hbridge; cbn.
- split; intro Hempty; constructor.
- split.
  + intro Hnodup.
    inversion Hnodup as [|? ? Hfirst Hrest]; subst.
    constructor.
    * intro Hin.
      apply in_map_iff in Hin as [other [Hequal Hother]].
      apply Hfirst.
      apply InA_alt.
      exists other.
      split.
      -- apply (proj2 (Hbridge first other (or_introl eq_refl)
            (or_intror _ Hother))).
         exact (eq_sym Hequal).
      -- exact Hother.
    * apply (proj1 (IH (fun left right Hleft Hright =>
        Hbridge left right (or_intror _ Hleft) (or_intror _ Hright)))).
      exact Hrest.
  + intro Hnodup.
    inversion Hnodup as [|? ? Hfirst Hrest]; subst.
    constructor.
    * intro Hin.
      apply InA_alt in Hin as [other [Hrelated Hother]].
      apply Hfirst.
      apply in_map_iff.
      exists other.
      split.
      -- exact (eq_sym (proj1
           (Hbridge first other (or_introl eq_refl)
             (or_intror _ Hother)) Hrelated)).
      -- exact Hother.
    * apply (proj2 (IH (fun left right Hleft Hright =>
        Hbridge left right (or_intror _ Hleft) (or_intror _ Hright)))).
      exact Hrest.
Qed.

(** Finite-image pigeonhole bound under an explicit semantic/code bridge. *)
Theorem NoDupA_finite_image_length_le :
  forall (A Code : Type) (relation : A -> A -> Prop)
      (code : A -> Code) rows domain,
    NoDupA relation rows ->
    (forall row, In row rows -> In (code row) domain) ->
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <-> code left = code right)) ->
    (List.length rows <= List.length domain)%nat.
Proof.
intros A Code relation code rows domain Hnodup Hrange Hbridge.
pose proof
  (proj1 (NoDupA_map_iff_NoDup_on
    A Code relation code rows Hbridge) Hnodup) as Hcodes.
assert (Hincluded : incl (map code rows) domain).
{
  intros value Hvalue.
  apply in_map_iff in Hvalue as [row [<- Hrow]].
  now apply Hrange.
}
pose proof (NoDup_incl_length Hcodes Hincluded) as Hlength.
now rewrite length_map in Hlength.
Qed.

(** Independent finite component domains multiply. *)
Corollary NoDupA_finite_product_code_length_le :
  forall (A Left Right : Type) (relation : A -> A -> Prop)
      (left_code : A -> Left) (right_code : A -> Right)
      rows left_domain right_domain,
    NoDupA relation rows ->
    (forall row, In row rows -> In (left_code row) left_domain) ->
    (forall row, In row rows -> In (right_code row) right_domain) ->
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <->
       (left_code left, right_code left) =
       (left_code right, right_code right))) ->
    (List.length rows <=
      List.length left_domain * List.length right_domain)%nat.
Proof.
intros A Left Right relation left_code right_code rows
  left_domain right_domain Hnodup Hleft Hright Hbridge.
pose proof
  (NoDupA_finite_image_length_le
    A (Left * Right)%type relation
    (fun row => (left_code row, right_code row))
    rows (list_prod left_domain right_domain)
    Hnodup) as Hfinite.
specialize Hfinite with (1 := fun row Hrow =>
  @in_prod Left Right left_domain right_domain
    (left_code row) (right_code row)
    (Hleft row Hrow) (Hright row Hrow)) (2 := Hbridge).
now rewrite length_prod in Hfinite.
Qed.

(** An optional finite code has one additional structural value.  The exact
    bridge premise makes explicit when that extra value is duplicate-free. *)
Corollary NoDupA_finite_option_code_length_le :
  forall (A Code : Type) (relation : A -> A -> Prop)
      (code : A -> option Code) rows domain,
    NoDupA relation rows ->
    (forall row,
      In row rows ->
      match code row with
      | None => True
      | Some value => In value domain
      end) ->
    (forall left right,
      In left rows ->
      In right rows ->
      (relation left right <-> code left = code right)) ->
    (List.length rows <= S (List.length domain))%nat.
Proof.
intros A Code relation code rows domain Hnodup Hrange Hbridge.
pose proof
  (NoDupA_finite_image_length_le
    A (option Code) relation code rows
    (None :: map (@Some Code) domain) Hnodup) as Hfinite.
specialize Hfinite with (2 := Hbridge).
assert (Hinside : forall row,
  In row rows -> In (code row) (None :: map (@Some Code) domain)).
{
  intros row Hrow.
  specialize (Hrange row Hrow).
  destruct (code row) as [value|] eqn:Hcode.
  - right; apply in_map; exact Hrange.
  - now left.
}
specialize (Hfinite Hinside).
cbn in Hfinite.
now rewrite length_map in Hfinite.
Qed.

(** Every setoid occurrence count is bounded by the list occurrence count. *)
Lemma oeset_nb_occ_le_length :
  forall (A : Type) (ordered : Oeset.Rcd A) value rows,
    (Oeset.nb_occ ordered value rows <=
      N.of_nat (List.length rows))%N.
Proof.
intros A ordered value rows.
induction rows as [|row rows IH].
- rewrite Oeset.nb_occ_unfold; reflexivity.
- rewrite Oeset.nb_occ_unfold.
  change
    ((match Oeset.compare ordered value row with
      | Eq => 1
      | _ => 0
      end + Oeset.nb_occ ordered value rows <=
      N.of_nat (S (List.length rows)))%N).
  rewrite Nat2N.inj_succ.
  destruct (Oeset.compare ordered value row) eqn:Hcompare.
  + rewrite N.add_1_l.
    apply (proj1 (N.succ_le_mono _ _)); exact IH.
  + eapply N.le_trans; [exact IH|apply N.le_succ_diag_r].
  + eapply N.le_trans; [exact IH|apply N.le_succ_diag_r].
Qed.

(** The stored-bag multiplicity of a row cannot exceed the number of stored
    list occurrences exposed by [instance_rows]. *)
Corollary instance_row_multiplicity_le_length :
  forall db relation row,
    (Febag.nb_occ
      (Fecol.CBag (CTuple TNull)) row
      (@_instance TNull db relation) <=
     N.of_nat (List.length (instance_rows db relation)))%N.
Proof.
intros db relation row.
rewrite instance_rows_nb_occ.
apply oeset_nb_occ_le_length.
Qed.

(** Positive bag multiplicity forces a nonempty stored occurrence list. *)
Corollary instance_row_positive_multiplicity_nonempty :
  forall db relation row,
    (0 < Febag.nb_occ
      (Fecol.CBag (CTuple TNull)) row
      (@_instance TNull db relation))%N ->
    instance_rows db relation <> nil.
Proof.
intros db relation row Hpositive Hempty.
pose proof (instance_row_multiplicity_le_length db relation row) as Hbound.
rewrite Hempty in Hbound.
change
  ((Febag.nb_occ
    (Fecol.CBag (CTuple TNull)) row
    (@_instance TNull db relation) <= 0)%N) in Hbound.
exact (N.lt_irrefl 0 (N.lt_le_trans 0 _ 0 Hpositive Hbound)).
Qed.

(** A theta join with per-left degree [bound] has at most the corresponding
    multiplicative number of output occurrences. *)
Lemma theta_join_list_degree_length_le :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) left right bound,
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= bound)%nat) ->
    (List.length (theta_join_list row join accept left right) <=
      List.length left * bound)%nat.
Proof.
intros row join accept left right bound Hdegree.
unfold theta_join_list, d_join_list.
apply flat_map_uniform_length_le.
intros left_row Hleft.
rewrite length_map.
now apply Hdegree.
Qed.

(** Without a degree certificate, the Cartesian product is a universal theta
    join bound. *)
Corollary theta_join_list_length_le_product :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) left right,
    (List.length (theta_join_list row join accept left right) <=
      List.length left * List.length right)%nat.
Proof.
intros row join accept left right.
apply theta_join_list_degree_length_le.
intros left_row _.
pose proof (filter_length (accept left_row) right).
lia.
Qed.

(** A post-join filter cannot invalidate a certified theta-join degree bound. *)
Corollary filter_theta_join_list_degree_length_le :
  forall (row : Type) (join : row -> row -> row)
      (accept : row -> row -> bool) (keep : row -> bool)
      left right bound,
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= bound)%nat) ->
    (List.length
      (filter keep (theta_join_list row join accept left right)) <=
      List.length left * bound)%nat.
Proof.
intros row join accept keep left right bound Hdegree.
pose proof
  (filter_length keep (theta_join_list row join accept left right))
  as Hfilter.
pose proof
  (theta_join_list_degree_length_le
    row join accept left right bound Hdegree) as Hjoin.
lia.
Qed.

(** Arbitrarily long occurrence-expansion pipelines multiply their certified
    stage degrees; no query topology is fixed by this definition. *)
Fixpoint expansion_pipeline
    (A : Type) (stages : list (A -> list A)) (rows : list A) : list A :=
  match stages with
  | nil => rows
  | stage :: rest => expansion_pipeline A rest (flat_map stage rows)
  end.

Definition expansion_pipeline_bounds
    {A : Type} (stages : list (A -> list A)) (bounds : list nat) : Prop :=
  Forall2
    (fun stage bound =>
      forall row, (List.length (stage row) <= bound)%nat)
    stages bounds.

Definition multiply_bounds (bounds : list nat) : nat :=
  fold_right Nat.mul 1 bounds.

Theorem expansion_pipeline_length_le :
  forall (A : Type) stages bounds rows,
    @expansion_pipeline_bounds A stages bounds ->
    (List.length (expansion_pipeline A stages rows) <=
      List.length rows * multiply_bounds bounds)%nat.
Proof.
intros A stages bounds rows Hbounds.
revert rows.
induction Hbounds as [|stage bound stages bounds Hstage Hbounds IH];
  intro rows; cbn [expansion_pipeline multiply_bounds].
- now rewrite Nat.mul_1_r.
- eapply Nat.le_trans.
  + apply IH.
  + pose proof
      (flat_map_uniform_length_le
        A A stage rows bound (fun row _ => Hstage row)) as Hflat.
    change
      (List.length (flat_map stage rows) * multiply_bounds bounds <=
       List.length rows * (bound * multiply_bounds bounds))%nat.
    rewrite Nat.mul_assoc.
    now apply Nat.mul_le_mono_r.
Qed.

(** Partitioning preserves the total number of input occurrences exactly. *)
Lemma partition_flatten_length :
  forall (A Key : Type) (ordered : Oset.Rcd Key)
      (key_of : A -> Key) rows,
    List.length
      (flat_map snd (@Partition.partition A Key ordered key_of rows)) =
    List.length rows.
Proof.
intros A Key ordered key_of rows.
symmetry.
pose proof
  (@Partition.partition_permut A Key ordered key_of rows) as Hpartition.
exact (_permut_length Hpartition).
Qed.

(** A partition creates no more nonempty groups than input occurrences. *)
Theorem partition_group_count_le :
  forall (A Key : Type) (ordered : Oset.Rcd Key)
      (key_of : A -> Key) rows,
    (List.length (@Partition.partition A Key ordered key_of rows) <=
      List.length rows)%nat.
Proof.
intros A Key ordered key_of rows.
assert (Hnonempty :
  Forall
    (fun group : Key * list A => snd group <> nil)
    (@Partition.partition A Key ordered key_of rows)).
{
  rewrite Forall_forall.
  intros [key group] Hgroup; cbn.
  eapply Partition.in_partition_diff_nil; exact Hgroup.
}
pose proof
  (nonempty_groups_count_le_total_length
    A (Key * list A)%type (@snd Key (list A))
    (@Partition.partition A Key ordered key_of rows) Hnonempty)
  as Hgroups.
rewrite partition_flatten_length in Hgroups.
exact Hgroups.
Qed.
