(******************************************************************************)
(** Exact, reusable grouping/filter facts for normalized FormalSQL queries.   **)
(******************************************************************************)

From SQLFS Require Import
  Env FiniteBag FiniteSet FlatData ListPermut OrderedSet Partition SqlQuerySemantics
  SqlQuerySyntax SqlQueryWellFormed.
From Stdlib Require Import Bool List Sorting.Permutation.

Import ListNotations.
Import Tuple.

(** Canonicalization changes only the semantic permutation chosen for a row
    bag.  This statement intentionally avoids exposing a concrete finite-bag
    implementation or a particular sorting algorithm. *)
Lemma query_canonical_rows_permut :
  forall (T : Tuple.Rcd) rows,
    Oeset.permut (OTuple T) (@query_canonical_rows T rows) rows.
Proof.
intros T rows.
apply Oeset.nb_occ_permut; intro row.
unfold query_canonical_rows, query_rows_bag.
rewrite <- Febag.nb_occ_elements.
now rewrite Febag.nb_occ_mk_bag.
Qed.

(** Canonical representatives commute up to semantic permutation with a
    representation change that is proper for tuple equality.  The pointwise
    factor premise captures projection/renaming composition, while the proper
    premise prevents the map from distinguishing two equivalent bag elements. *)
Theorem query_canonical_rows_map_factor_permut :
  forall (T : Tuple.Rcd) (A : Type)
      (first second : A -> tuple T) (rename : tuple T -> tuple T),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      Oeset.compare (OTuple T) (rename left) (rename right) = Eq) ->
    (forall item, rename (first item) = second item) ->
    forall rows,
      Oeset.permut (OTuple T)
        (@query_canonical_rows T (map second rows))
        (map rename (@query_canonical_rows T (map first rows))).
Proof.
intros T A first second rename Hproper Hfactor rows.
eapply ListPermut._permut_trans with (l2 := map second rows).
- intros left middle right _ _ _ Hleft Hright.
  eapply Oeset.compare_eq_trans; eassumption.
- apply query_canonical_rows_permut.
- assert (Hmapped : map second rows = map rename (map first rows)).
  { rewrite map_map; apply map_ext; intro item; symmetry; apply Hfactor. }
  rewrite Hmapped.
  apply Oeset.permut_sym.
  eapply ListPermut._permut_map
    with
      (R := fun left right => Oeset.compare (OTuple T) left right = Eq)
      (R' := fun left right => Oeset.compare (OTuple T) left right = Eq)
      (f1 := rename) (f2 := rename).
  + intros left right _ _ Hequal; now apply Hproper.
  + apply query_canonical_rows_permut.
Qed.

(** [Partition.partition] retains the first occurrence order of keys and the
    exact occurrence order chosen for every member list.  Filtering by a
    predicate of the key therefore commutes with partitioning as literal list
    equality: no quotient, sorting, duplicate elimination, or permutation is
    involved. *)
Section PartitionFilter.

Context {A Key : Type}.
Variable key_order : Oset.Rcd Key.

Lemma filter_insert_in_partition_by_key :
  forall (keep : Key -> bool) key row groups,
    filter (fun group => keep (fst group))
      (@Partition.insert_in_partition A Key key_order key row groups) =
    if keep key
    then @Partition.insert_in_partition A Key key_order key row
           (filter (fun group => keep (fst group)) groups)
    else filter (fun group => keep (fst group)) groups.
Proof.
  intros keep key row groups.
  induction groups as [|[other members] groups IH]; cbn.
  - now destruct (keep key).
  - destruct (Oset.eq_bool key_order key other) eqn:Hkey.
    + apply Oset.eq_bool_true_iff in Hkey; subst other.
      destruct (keep key) eqn:Hkeep; cbn; rewrite Hkeep; cbn;
        [rewrite Oset.eq_bool_refl|]; reflexivity.
    + destruct (keep other) eqn:Hother;
        destruct (keep key) eqn:Hkeep; cbn;
        rewrite ?Hother, ?Hkeep, ?Hkey, ?IH; reflexivity.
Qed.

Lemma filter_partition_rec_by_key :
  forall (keep : Key -> bool) (key_of : A -> Key) rows groups,
    filter (fun group => keep (fst group))
      (@Partition.partition_rec A Key key_order key_of groups rows) =
    @Partition.partition_rec A Key key_order key_of
      (filter (fun group => keep (fst group)) groups)
      (filter (fun row => keep (key_of row)) rows).
Proof.
  intros keep key_of rows.
  induction rows as [|row rows IH]; intro groups; cbn.
  - reflexivity.
  - rewrite IH, filter_insert_in_partition_by_key.
    now destruct (keep (key_of row)).
Qed.

Theorem partition_filter_by_key_exact :
  forall (keep : Key -> bool) (key_of : A -> Key) rows,
    @Partition.partition A Key key_order key_of
      (filter (fun row => keep (key_of row)) rows) =
    filter (fun group => keep (fst group))
      (@Partition.partition A Key key_order key_of rows).
Proof.
  intros keep key_of rows.
  symmetry.
  apply filter_partition_rec_by_key.
Qed.

(** Dropping the explicit keys yields the same exact result as filtering the
    nonempty member lists by their first member.  Homogeneity connects that
    member back to the stored partition key. *)
Lemma map_snd_filter_keyed_groups :
  forall (keep : Key -> bool) (key_of : A -> Key) groups,
    (forall key members,
      In (key, members) groups ->
      exists row rest, members = row :: rest /\ key_of row = key) ->
    map snd (filter (fun group => keep (fst group)) groups) =
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (key_of row)
        end)
      (map snd groups).
Proof.
  intros keep key_of groups Hgroups.
  induction groups as [|[key members] groups IH]; cbn.
  - reflexivity.
  - destruct (Hgroups key members (or_introl eq_refl))
      as [row [rest [Hmembers Hkey]]].
    subst members; cbn.
    rewrite Hkey.
    assert (Htail :
      map snd (filter (fun group => keep (fst group)) groups) =
      filter
        (fun nested =>
          match nested with
          | nil => false
          | nested_row :: _ => keep (key_of nested_row)
          end)
        (map snd groups)).
    {
      apply IH.
      intros other other_members Hin.
      apply (Hgroups other other_members (or_intror Hin)).
    }
    destruct (keep key); cbn; now rewrite Htail.
Qed.

Theorem partition_members_filter_by_key_exact :
  forall (keep : Key -> bool) (key_of : A -> Key) rows,
    map snd
      (@Partition.partition A Key key_order key_of
        (filter (fun row => keep (key_of row)) rows)) =
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (key_of row)
        end)
      (map snd (@Partition.partition A Key key_order key_of rows)).
Proof.
  intros keep key_of rows.
  rewrite partition_filter_by_key_exact.
  apply map_snd_filter_keyed_groups.
  intros key members Hin.
  assert (Hnonempty : members <> nil).
  { eapply Partition.in_partition_diff_nil; exact Hin. }
  destruct members as [|row rest]; [contradiction|].
  exists row, rest; split; [reflexivity|].
  eapply Partition.partition_homogeneous_values; [exact Hin|].
  now left.
Qed.

(** Looking up one exact key in a partition exposes both absence and the
    unique accumulator-ordered member list.  The result retains every matching
    input occurrence and makes the implementation's reversal explicit. *)
Theorem partition_lookup_key_exact :
  forall (key_of : A -> Key) rows key,
    filter
      (fun group => Oset.eq_bool key_order (fst group) key)
      (@Partition.partition A Key key_order key_of rows) =
    match
      filter
        (fun row => Oset.eq_bool key_order (key_of row) key)
        rows
    with
    | nil => nil
    | _ :: _ =>
        [(key,
          rev
            (filter
              (fun row => Oset.eq_bool key_order (key_of row) key)
              rows))]
    end.
Proof.
  intros key_of rows key.
  rewrite <- (partition_filter_by_key_exact
    (fun candidate => Oset.eq_bool key_order candidate key)
    key_of rows).
  apply Partition.partition_cst.
  intros row Hrow.
  apply filter_In in Hrow as [_ Hkey].
  now apply Oset.eq_bool_true_iff in Hkey.
Qed.

End PartitionFilter.

(** Mapping partition members may change their type, provided that the map
    preserves the key used on each source occurrence.  This heterogeneous
    form is intentionally stronger than [Partition.partition_map], whose map
    is an endofunction. *)
Local Lemma partition_insert_map_heterogeneous :
  forall (A B Key : Type) (key_order : Oset.Rcd Key)
      (emit : A -> B) key row groups,
    @Partition.insert_in_partition B Key key_order key (emit row)
      (map (fun group => (fst group, map emit (snd group))) groups) =
    map (fun group => (fst group, map emit (snd group)))
      (@Partition.insert_in_partition A Key key_order key row groups).
Proof.
  intros A B Key key_order emit key row groups.
  induction groups as [|[other members] groups IH]; cbn; [reflexivity|].
  destruct (Oset.eq_bool key_order key other); cbn;
    [reflexivity|now rewrite IH].
Qed.

Theorem partition_map_heterogeneous :
  forall (A B Key : Type) (key_order : Oset.Rcd Key)
      (keyA : A -> Key) (keyB : B -> Key) (emit : A -> B) rows,
    (forall row, In row rows -> keyB (emit row) = keyA row) ->
    @Partition.partition B Key key_order keyB (map emit rows) =
    map (fun group => (fst group, map emit (snd group)))
      (@Partition.partition A Key key_order keyA rows).
Proof.
  intros A B Key key_order keyA keyB emit rows Hkeys.
  unfold Partition.partition.
  assert (Hrec : forall remaining,
    (forall row, In row remaining -> keyB (emit row) = keyA row) ->
    forall groups,
      @Partition.partition_rec B Key key_order keyB
        (map (fun group => (fst group, map emit (snd group))) groups)
        (map emit remaining) =
      map (fun group => (fst group, map emit (snd group)))
        (@Partition.partition_rec A Key key_order keyA groups remaining)).
  {
    intro remaining; induction remaining as [|row remaining IH];
      intros Hremaining groups; cbn; [reflexivity|].
    rewrite (Hremaining row (or_introl eq_refl)).
    rewrite partition_insert_map_heterogeneous.
    apply IH.
    intros current Hcurrent.
    apply Hremaining; now right.
  }
  exact (Hrec rows Hkeys nil).
Qed.

(** Two key functions induce the same partition members when they make the
    same equality decision for every pair of input occurrences.  Stored key
    values may differ: this is the representation-independent boundary needed
    when a GROUP BY list is reordered or consistently renamed. *)
Local Definition partition_key_alignment
    {A Key : Type} (key_order : Oset.Rcd Key) (universe : list A)
    (left_key right_key : A -> Key)
    (left right : list (Key * list A)) : Prop :=
  Forall2
    (fun left_group right_group =>
      exists representative,
        In representative universe /\
        fst left_group = left_key representative /\
        fst right_group = right_key representative /\
        snd left_group = snd right_group)
    left right.

Local Lemma partition_key_alignment_insert :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      universe (left_key right_key : A -> Key) row left right,
    In row universe ->
    (forall first second,
      In first universe ->
      In second universe ->
      Oset.eq_bool key_order (left_key first) (left_key second) =
      Oset.eq_bool key_order (right_key first) (right_key second)) ->
    partition_key_alignment key_order universe left_key right_key left right ->
    partition_key_alignment key_order universe left_key right_key
      (@Partition.insert_in_partition A Key key_order
        (left_key row) row left)
      (@Partition.insert_in_partition A Key key_order
        (right_key row) row right).
Proof.
  intros A Key key_order universe left_key right_key row left right
    Hrow Hdecisions Haligned.
  induction Haligned as
    [|[left_stored left_members] [right_stored right_members]
       left_tail right_tail Hhead Htail IH].
  - cbn [Partition.insert_in_partition].
    constructor.
    + exists row; repeat split; assumption || reflexivity.
    + constructor.
  - destruct Hhead as
      [representative
        [Hrepresentative [Hleft_key [Hright_key Hmembers]]]].
    cbn in Hleft_key, Hright_key, Hmembers.
    subst left_stored right_stored right_members.
    cbn [Partition.insert_in_partition].
    rewrite (Hdecisions row representative Hrow Hrepresentative).
    destruct
      (Oset.eq_bool key_order
        (right_key row) (right_key representative)).
    + constructor.
      * exists representative; repeat split; assumption || reflexivity.
      * exact Htail.
    + constructor.
      * exists representative; repeat split; assumption || reflexivity.
      * exact IH.
Qed.

Local Lemma partition_key_alignment_rec :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      universe rows (left_key right_key : A -> Key) left right,
    Forall (fun row => In row universe) rows ->
    (forall first second,
      In first universe ->
      In second universe ->
      Oset.eq_bool key_order (left_key first) (left_key second) =
      Oset.eq_bool key_order (right_key first) (right_key second)) ->
    partition_key_alignment key_order universe left_key right_key left right ->
    partition_key_alignment key_order universe left_key right_key
      (@Partition.partition_rec A Key key_order left_key left rows)
      (@Partition.partition_rec A Key key_order right_key right rows).
Proof.
  intros A Key key_order universe rows.
  induction rows as [|row rows IH];
    intros left_key right_key left right Hrows Hdecisions Haligned.
  - exact Haligned.
  - inversion Hrows as [|? ? Hrow Htail]; subst.
    cbn [Partition.partition_rec].
    apply IH; [exact Htail|exact Hdecisions|].
    now apply partition_key_alignment_insert.
Qed.

Local Lemma partition_key_alignment_members :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      universe (left_key right_key : A -> Key) left right,
    partition_key_alignment key_order universe left_key right_key left right ->
    map snd left = map snd right.
Proof.
  intros A Key key_order universe left_key right_key left right Haligned.
  induction Haligned as
    [|left_group right_group left_tail right_tail
       [representative [_ [_ [_ Hmembers]]]] Htail IH].
  - reflexivity.
  - cbn; now rewrite Hmembers, IH.
Qed.

Theorem partition_members_equal_of_key_decisions :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (left_key right_key : A -> Key) rows,
    (forall first second,
      In first rows ->
      In second rows ->
      Oset.eq_bool key_order (left_key first) (left_key second) =
      Oset.eq_bool key_order (right_key first) (right_key second)) ->
    map snd (@Partition.partition A Key key_order left_key rows) =
    map snd (@Partition.partition A Key key_order right_key rows).
Proof.
  intros A Key key_order left_key right_key rows Hdecisions.
  eapply (@partition_key_alignment_members
    A Key key_order rows left_key right_key).
  unfold Partition.partition.
  apply partition_key_alignment_rec.
  - apply Forall_forall; trivial.
  - exact Hdecisions.
  - constructor.
Qed.

(** FormalSQL's historical occurrence permutation specializes to Stdlib's
    ordinary [Permutation] when its relation is Leibniz equality. *)
Lemma list_permut_eq_implies_Permutation :
  forall (A : Type) (left right : list A),
    ListPermut._permut (@eq A) left right ->
    Sorting.Permutation.Permutation left right.
Proof.
  intros A left right Hpermut.
  induction Hpermut as
    [|first second tail before after Hequal Htail IH].
  - constructor.
  - subst second.
    eapply Sorting.Permutation.Permutation_trans with
      (l' := first :: before ++ after).
    + now apply Sorting.Permutation.perm_skip.
    + apply Sorting.Permutation.Permutation_middle.
Qed.

Local Lemma all_diff_implies_NoDup :
  forall (A : Type) (items : list A),
    ListFacts.all_diff items -> NoDup items.
Proof.
  intros A items.
  induction items as [|item items IH]; intro Hdiff.
  - constructor.
  - constructor.
    + destruct items as [|next rest].
      * exact (fun Hin => Hin).
      * rewrite ListFacts.all_diff_unfold in Hdiff.
        intro Hin; exact ((proj1 Hdiff item Hin) eq_refl).
    + apply IH.
      destruct items as [|next rest].
      * exact I.
      * rewrite ListFacts.all_diff_unfold in Hdiff.
        exact (proj2 Hdiff).
Qed.

(** The keys materialized by [Partition.partition] are permutation-equivalent
    to every duplicate-free list having exactly the input key support.  This
    exposes the representation boundary needed by GROUP BY/DISTINCT proofs
    without choosing a particular key type or deduplication algorithm. *)
Theorem partition_keys_Permutation_of_NoDup_support :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows selected,
    NoDup selected ->
    (forall key, In key selected <-> In key (map key_of rows)) ->
    Sorting.Permutation.Permutation
      (map fst (@Partition.partition A Key key_order key_of rows))
      selected.
Proof.
  intros A Key key_order key_of rows selected Hselected Hsupport.
  apply Sorting.Permutation.NoDup_Permutation.
  - apply all_diff_implies_NoDup.
    apply Partition.partition_all_diff_values.
  - exact Hselected.
  - intro key.
    assert (Hpartition :
      In key (map fst (@Partition.partition A Key key_order key_of rows)) <->
      In key (map key_of rows)).
    {
      split.
      - intro Hkey.
        apply in_map_iff in Hkey.
        destruct Hkey as [[found members] [Hfound Hmembers]].
        cbn in Hfound; subst found.
        pose proof
          (@Partition.in_partition_diff_nil A Key key_order
            key_of rows key members Hmembers) as Hnonempty.
        destruct members as [|row members]; [contradiction|].
        apply in_map_iff.
        exists row; split.
        + apply (@Partition.partition_homogeneous_values
            A Key key_order key_of rows key (row :: members)
            Hmembers row).
          now left.
        + eapply @Partition.in_partition.
          * exact Hmembers.
          * now left.
      - intro Hkey.
        apply in_map_iff in Hkey.
        destruct Hkey as [row [Hrow_key Hrow]].
        pose proof
          (proj1
            (@ListPermut.in_permut_in A rows
              (flat_map
                (fun item : Key * list A => snd item)
                (@Partition.partition A Key key_order key_of rows))
              (@Partition.partition_permut
                A Key key_order key_of rows) row) Hrow) as Hflat.
        apply in_flat_map in Hflat.
        destruct Hflat as [[found members] [Hmembers Hrow_members]].
        apply in_map_iff.
        exists (found, members); split; [cbn|exact Hmembers].
        transitivity (key_of row); [|exact Hrow_key].
        symmetry.
        apply (@Partition.partition_homogeneous_values
          A Key key_order key_of rows found members
          Hmembers row Hrow_members).
    }
    rewrite Hpartition.
    symmetry; apply Hsupport.
Qed.

(** The key list of [Partition.partition] is an ordered nub: new keys are
    appended at their first occurrence and later occurrences leave that list
    unchanged.  These local definitions and facts expose that implementation
    invariant only for the ordered-refinement proof below. *)
Local Definition ordered_key_insert
    {Key : Type} (key_order : Oset.Rcd Key)
    (key : Key) (keys : list Key) : list Key :=
  if Oset.mem_bool key_order key keys then keys else keys ++ [key].

Local Definition ordered_key_sequence
    {Key : Type} (key_order : Oset.Rcd Key)
    (keys : list Key) : list Key :=
  fold_left (fun seen key => ordered_key_insert key_order key seen) keys nil.

Local Lemma ordered_key_insert_seen :
  forall (Key : Type) (key_order : Oset.Rcd Key) key keys,
    In key keys -> ordered_key_insert key_order key keys = keys.
Proof.
  intros Key key_order key keys Hin.
  unfold ordered_key_insert.
  rewrite (proj2 (Oset.mem_bool_true_iff key_order key keys) Hin).
  reflexivity.
Qed.

Local Lemma ordered_key_insert_owns :
  forall (Key : Type) (key_order : Oset.Rcd Key) key keys,
    In key (ordered_key_insert key_order key keys).
Proof.
  intros Key key_order key keys.
  unfold ordered_key_insert.
  destruct (Oset.mem_bool key_order key keys) eqn:Hmember.
  - now apply Oset.mem_bool_true_iff in Hmember.
  - apply in_or_app; right; now left.
Qed.

Local Lemma ordered_key_insert_preserves :
  forall (Key : Type) (key_order : Oset.Rcd Key) key current keys,
    In current keys ->
    In current (ordered_key_insert key_order key keys).
Proof.
  intros Key key_order key current keys Hin.
  unfold ordered_key_insert.
  destruct (Oset.mem_bool key_order key keys).
  - exact Hin.
  - apply in_or_app; now left.
Qed.

Local Lemma fold_left_ordered_key_insert_preserves :
  forall (Key : Type) (key_order : Oset.Rcd Key) additions initial current,
    In current initial ->
    In current
      (fold_left
        (fun seen key => ordered_key_insert key_order key seen)
        additions initial).
Proof.
  intros Key key_order additions.
  induction additions as [|key additions IH]; intros initial current Hin; cbn.
  - exact Hin.
  - apply IH.
    now apply ordered_key_insert_preserves.
Qed.

Local Lemma ordered_key_sequence_contains :
  forall (Key : Type) (key_order : Oset.Rcd Key) key keys,
    In key keys -> In key (ordered_key_sequence key_order keys).
Proof.
  intros Key key_order key keys Hin.
  apply in_split in Hin as [before [after ->]].
  unfold ordered_key_sequence.
  rewrite fold_left_app; cbn.
  apply fold_left_ordered_key_insert_preserves.
  apply ordered_key_insert_owns.
Qed.

Local Lemma ordered_key_sequence_app_singleton :
  forall (Key : Type) (key_order : Oset.Rcd Key) keys key,
    ordered_key_sequence key_order (keys ++ [key]) =
    ordered_key_insert key_order key
      (ordered_key_sequence key_order keys).
Proof.
  intros Key key_order keys key.
  unfold ordered_key_sequence.
  rewrite fold_left_app.
  reflexivity.
Qed.

Local Lemma ordered_key_sequence_insert_factor :
  forall (Fine Coarse : Type)
      (fine_order : Oset.Rcd Fine) (coarse_order : Oset.Rcd Coarse)
      (factor : Fine -> Coarse) fine fine_keys,
    ordered_key_sequence coarse_order
      (map factor (ordered_key_insert fine_order fine fine_keys)) =
    ordered_key_insert coarse_order (factor fine)
      (ordered_key_sequence coarse_order (map factor fine_keys)).
Proof.
  intros Fine Coarse fine_order coarse_order factor fine fine_keys.
  unfold ordered_key_insert at 1.
  destruct (Oset.mem_bool fine_order fine fine_keys) eqn:Hfine.
  - apply Oset.mem_bool_true_iff in Hfine.
    symmetry.
    apply ordered_key_insert_seen.
    apply ordered_key_sequence_contains.
    apply in_map.
    exact Hfine.
  - rewrite map_app; cbn.
    apply ordered_key_sequence_app_singleton.
Qed.

Local Lemma ordered_key_sequence_map_factor :
  forall (Fine Coarse : Type)
      (fine_order : Oset.Rcd Fine) (coarse_order : Oset.Rcd Coarse)
      (factor : Fine -> Coarse) fine_keys,
    ordered_key_sequence coarse_order
      (map factor (ordered_key_sequence fine_order fine_keys)) =
    ordered_key_sequence coarse_order (map factor fine_keys).
Proof.
  intros Fine Coarse fine_order coarse_order factor fine_keys.
  induction fine_keys using rev_ind.
  - reflexivity.
  - rewrite (@ordered_key_sequence_app_singleton
      Fine fine_order fine_keys x).
    rewrite ordered_key_sequence_insert_factor.
    rewrite IHfine_keys.
    rewrite map_app; cbn.
    symmetry.
    apply (@ordered_key_sequence_app_singleton Coarse coarse_order).
Qed.

Local Lemma map_fst_insert_in_partition :
  forall (A Key : Type) (key_order : Oset.Rcd Key) key row groups,
    map fst (@Partition.insert_in_partition A Key key_order key row groups) =
    ordered_key_insert key_order key (map fst groups).
Proof.
  intros A Key key_order key row groups.
  induction groups as [|[other members] groups IH]; cbn.
  - reflexivity.
  - destruct (Oset.eq_bool key_order key other) eqn:Hequal; cbn.
    + unfold ordered_key_insert; cbn; now rewrite Hequal.
    + rewrite IH.
      unfold ordered_key_insert; cbn; rewrite Hequal.
      fold (Oset.mem_bool key_order key (map fst groups)).
      destruct (Oset.mem_bool key_order key (map fst groups)); reflexivity.
Qed.

Local Lemma map_fst_partition_rec :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows groups,
    map fst (@Partition.partition_rec A Key key_order key_of groups rows) =
    fold_left
      (fun keys row => ordered_key_insert key_order (key_of row) keys)
      rows (map fst groups).
Proof.
  intros A Key key_order key_of rows.
  induction rows as [|row rows IH]; intro groups; cbn.
  - reflexivity.
  - rewrite IH, map_fst_insert_in_partition.
    reflexivity.
Qed.

Local Lemma fold_left_ordered_key_insert_map :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows initial,
    fold_left
      (fun keys row => ordered_key_insert key_order (key_of row) keys)
      rows initial =
    fold_left
      (fun keys key => ordered_key_insert key_order key keys)
      (map key_of rows) initial.
Proof.
  intros A Key key_order key_of rows.
  induction rows as [|row rows IH]; intro initial; cbn.
  - reflexivity.
  - apply IH.
Qed.

Local Lemma map_fst_partition_ordered_key_sequence :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows,
    map fst (@Partition.partition A Key key_order key_of rows) =
    ordered_key_sequence key_order (map key_of rows).
Proof.
  intros A Key key_order key_of rows.
  unfold Partition.partition, ordered_key_sequence.
  rewrite map_fst_partition_rec.
  apply fold_left_ordered_key_insert_map.
Qed.

Local Lemma partition_factored_key_order_exact :
  forall (A Fine Coarse : Type)
      (fine_order : Oset.Rcd Fine) (coarse_order : Oset.Rcd Coarse)
      (fine_key : A -> Fine) (coarse_key : A -> Coarse)
      (factor : Fine -> Coarse) rows,
    (forall row, In row rows -> coarse_key row = factor (fine_key row)) ->
    map fst (@Partition.partition A Coarse coarse_order coarse_key rows) =
    map fst
      (@Partition.partition (Fine * list A) Coarse coarse_order
        (fun fine_group => factor (fst fine_group))
        (@Partition.partition A Fine fine_order fine_key rows)).
Proof.
  intros A Fine Coarse fine_order coarse_order
    fine_key coarse_key factor rows Hkeys.
  rewrite (@Partition.partition_eq_1_strong
    A Coarse coarse_order coarse_key
    (fun row => factor (fine_key row)) rows Hkeys).
  repeat rewrite map_fst_partition_ordered_key_sequence.
  rewrite <- (@map_map A Fine Coarse fine_key factor rows).
  rewrite <- (@map_map (Fine * list A) Fine Coarse
    (@fst Fine (list A)) factor
    (@Partition.partition A Fine fine_order fine_key rows)).
  rewrite map_fst_partition_ordered_key_sequence.
  symmetry.
  apply ordered_key_sequence_map_factor.
Qed.

(** A stored partition group is exactly the reverse of the input occurrences
    whose key equals that stored key. *)
Theorem partition_member_exact_key_filter :
  forall (A Key : Type) (key_order : Oset.Rcd Key)
      (key_of : A -> Key) rows key members,
    In (key, members)
      (@Partition.partition A Key key_order key_of rows) ->
    members =
      rev
        (filter
          (fun row => Oset.eq_bool key_order (key_of row) key)
          rows).
Proof.
  intros A Key key_order key_of rows key members Hgroup.
  assert (Hselected : In (key, members)
    (filter
      (fun group => Oset.eq_bool key_order (fst group) key)
      (@Partition.partition A Key key_order key_of rows))).
  {
    apply filter_In; split; [exact Hgroup|].
    cbn.
    apply Oset.eq_bool_refl.
  }
  rewrite (@partition_lookup_key_exact
    A Key key_order key_of rows key) in Hselected.
  destruct
    (filter
      (fun row => Oset.eq_bool key_order (key_of row) key)
      rows)
    as [|first rest] eqn:Hrows;
    cbn in Hselected; [contradiction|].
  destruct Hselected as [Hequal|[]].
  injection Hequal as Hmembers.
  subst members.
  reflexivity.
Qed.

Local Lemma keyed_lists_Forall2_of_fst_eq :
  forall (Key Left Right : Type)
      (R : Left -> Right -> Prop)
      (left : list (Key * Left)) (right : list (Key * Right)),
    map fst left = map fst right ->
    (forall key left_members right_members,
      In (key, left_members) left ->
      In (key, right_members) right ->
      R left_members right_members) ->
    Forall2
      (fun left_group right_group =>
        fst left_group = fst right_group /\
        R (snd left_group) (snd right_group))
      left right.
Proof.
  intros Key Left Right R left.
  induction left as [|[left_key left_members] left IH];
    intros [|[right_key right_members] right] Hkeys Hmembers;
    cbn in Hkeys; try discriminate.
  - constructor.
  - injection Hkeys as Hkey Htail.
    subst right_key.
    constructor.
    + split; [reflexivity|].
      apply (Hmembers left_key left_members right_members); now left.
    + apply IH; [exact Htail|].
      intros key left_tail right_tail Hleft Hright.
      apply (Hmembers key left_tail right_tail); now right.
Qed.

Local Lemma partition_factored_members_Permutation :
  forall (A Fine Coarse : Type)
      (fine_order : Oset.Rcd Fine) (coarse_order : Oset.Rcd Coarse)
      (fine_key : A -> Fine) (coarse_key : A -> Coarse)
      (factor : Fine -> Coarse) rows key coarse_members fine_groups,
    (forall row, In row rows -> coarse_key row = factor (fine_key row)) ->
    In (key, coarse_members)
      (@Partition.partition A Coarse coarse_order coarse_key rows) ->
    In (key, fine_groups)
      (@Partition.partition (Fine * list A) Coarse coarse_order
        (fun fine_group => factor (fst fine_group))
        (@Partition.partition A Fine fine_order fine_key rows)) ->
    Sorting.Permutation.Permutation coarse_members
      (concat (map snd fine_groups)).
Proof.
  intros A Fine Coarse fine_order coarse_order fine_key coarse_key
    factor rows key coarse_members fine_groups Hkeys Hcoarse Hfine.
  pose proof (partition_member_exact_key_filter
    A Coarse coarse_order coarse_key rows key coarse_members Hcoarse)
    as Hcoarse_exact.
  pose proof (partition_member_exact_key_filter
    (Fine * list A) Coarse coarse_order
    (fun fine_group => factor (fst fine_group))
    (@Partition.partition A Fine fine_order fine_key rows)
    key fine_groups Hfine) as Hfine_exact.
  rewrite Hcoarse_exact, Hfine_exact.
  assert (Hfilters :
    filter
      (fun row => Oset.eq_bool coarse_order (coarse_key row) key)
      rows =
    filter
      (fun row =>
        Oset.eq_bool coarse_order (factor (fine_key row)) key)
      rows).
  {
    apply filter_ext_in.
    intros row Hrow.
    now rewrite (Hkeys row Hrow).
  }
  rewrite Hfilters.
  pose proof
    (@Partition.partition_permut A Fine fine_order fine_key
      (filter
        (fun row =>
          Oset.eq_bool coarse_order (factor (fine_key row)) key)
        rows)) as Hpartition.
  apply list_permut_eq_implies_Permutation in Hpartition.
  rewrite (@partition_filter_by_key_exact
    A Fine fine_order
    (fun fine => Oset.eq_bool coarse_order (factor fine) key)
    fine_key rows) in Hpartition.
  assert (Hconcat : forall groups : list (Fine * list A),
    concat (map snd groups) = flat_map snd groups).
  {
    intro groups.
    induction groups as [|[fine members] groups IH]; cbn.
    - reflexivity.
    - now rewrite IH.
  }
  rewrite Hconcat.
  eapply Sorting.Permutation.Permutation_trans.
  - apply Sorting.Permutation.Permutation_sym.
    apply Sorting.Permutation.Permutation_rev.
  - eapply Sorting.Permutation.Permutation_trans; [exact Hpartition|].
    apply Sorting.Permutation.Permutation_flat_map.
    apply Sorting.Permutation.Permutation_rev.
Qed.

(** Ordered factored-key refinement.  Directly partitioning rows by a coarse
    key and first partitioning by a fine key before coarsening the stored fine
    keys discover coarse groups in the same order.  Corresponding coarse
    groups contain exactly the same row occurrences, although the two-stage
    accumulation order may differ. *)
Theorem partition_factored_key_refinement_Forall2 :
  forall (A Fine Coarse : Type)
      (fine_order : Oset.Rcd Fine) (coarse_order : Oset.Rcd Coarse)
      (fine_key : A -> Fine) (coarse_key : A -> Coarse)
      (factor : Fine -> Coarse) rows,
    (forall row, In row rows -> coarse_key row = factor (fine_key row)) ->
    Forall2
      (fun coarse_group refined_group =>
        fst coarse_group = fst refined_group /\
        Sorting.Permutation.Permutation
          (snd coarse_group)
          (concat (map snd (snd refined_group))))
      (@Partition.partition A Coarse coarse_order coarse_key rows)
      (@Partition.partition (Fine * list A) Coarse coarse_order
        (fun fine_group => factor (fst fine_group))
        (@Partition.partition A Fine fine_order fine_key rows)).
Proof.
  intros A Fine Coarse fine_order coarse_order fine_key coarse_key
    factor rows Hkeys.
  eapply (@keyed_lists_Forall2_of_fst_eq
    Coarse (list A) (list (Fine * list A))
    (fun coarse_members fine_groups =>
      Sorting.Permutation.Permutation coarse_members
        (concat (map snd fine_groups)))).
  - now apply partition_factored_key_order_exact.
  - intros key coarse_members fine_groups Hcoarse Hfine.
    now apply (partition_factored_members_Permutation
      A Fine Coarse fine_order coarse_order fine_key coarse_key
      factor rows key).
Qed.

(** The grouping key used by [query_make_groups], exposed only to keep the
    theorem below readable.  It is definitionally the key in
    [FlatData.make_groups]. *)
Definition query_grouping_key
    (T : Tuple.Rcd) (env : Env.env T)
    (group_terms : list (@aggterm T)) (row : tuple T) : list (value T) :=
  map (fun term => interp_aggterm T (env_t T env row) term) group_terms.

Arguments query_grouping_key {T} _ _ _.

(** Applying the same permutation to two mapped lists preserves whether the
    maps are equal.  This is stronger than ordinary [map] permutation: the
    same positional rewrite is applied on both sides of the equality test. *)
Local Lemma map_pair_equality_Permutation :
  forall (Index Value : Type) (left right : list Index)
      (first second : Index -> Value),
    Sorting.Permutation.Permutation left right ->
    (map first left = map second left <->
     map first right = map second right).
Proof.
  intros Index Value left right first second Hpermutation.
  induction Hpermutation.
  - tauto.
  - cbn; split; intro Hequal; injection Hequal as Hhead Htail.
    + now rewrite Hhead, (proj1 IHHpermutation Htail).
    + now rewrite Hhead, (proj2 IHHpermutation Htail).
  - cbn; split; intro Hequal;
      injection Hequal as Hfirst Hsecond Htail; congruence.
  - tauto.
Qed.

Lemma query_grouping_key_decision_Permutation :
  forall (T : Tuple.Rcd) (env : Env.env T) left_terms right_terms left right,
    Sorting.Permutation.Permutation left_terms right_terms ->
    Oset.eq_bool (OrderedSet.mk_olists (OVal T))
      (query_grouping_key env left_terms left)
      (query_grouping_key env left_terms right) =
    Oset.eq_bool (OrderedSet.mk_olists (OVal T))
      (query_grouping_key env right_terms left)
      (query_grouping_key env right_terms right).
Proof.
  intros T env left_terms right_terms left right Hterms.
  unfold query_grouping_key.
  pose proof
    (map_pair_equality_Permutation
      (@aggterm T) (value T) left_terms right_terms
      (fun term => interp_aggterm T (env_t T env left) term)
      (fun term => interp_aggterm T (env_t T env right) term)
      Hterms) as Hequality.
  destruct
    (Oset.eq_bool (OrderedSet.mk_olists (OVal T))
      (map (fun term => interp_aggterm T (env_t T env left) term) left_terms)
      (map (fun term => interp_aggterm T (env_t T env right) term) left_terms))
    eqn:Hleft;
  destruct
    (Oset.eq_bool (OrderedSet.mk_olists (OVal T))
      (map (fun term => interp_aggterm T (env_t T env left) term) right_terms)
      (map (fun term => interp_aggterm T (env_t T env right) term) right_terms))
    eqn:Hright; try reflexivity.
  - apply Oset.eq_bool_true_iff in Hleft.
    apply (proj1 Hequality) in Hleft.
    apply (proj2
      (Oset.eq_bool_true_iff (OrderedSet.mk_olists (OVal T)) _ _))
      in Hleft.
    congruence.
  - apply Oset.eq_bool_true_iff in Hright.
    apply (proj2 Hequality) in Hright.
    apply (proj2
      (Oset.eq_bool_true_iff (OrderedSet.mk_olists (OVal T)) _ _))
      in Hright.
    congruence.
Qed.

(** Reordering GROUP BY expressions changes only the representation of each
    grouping key.  Every pair of rows receives the same equality decision, so
    the partition contains exactly the same member lists, including duplicate
    occurrences and the global-empty-group correction. *)
Theorem query_make_groups_group_terms_Permutation :
  forall (T : Tuple.Rcd) (env : Env.env T) rows left_terms right_terms,
    Sorting.Permutation.Permutation left_terms right_terms ->
    @query_make_groups T env rows left_terms =
    @query_make_groups T env rows right_terms.
Proof.
  intros T env rows left_terms right_terms Hterms.
  destruct rows as [|row rows].
  - destruct left_terms as [|left_term left_terms].
    + apply Sorting.Permutation.Permutation_nil in Hterms.
      subst right_terms; reflexivity.
    + destruct right_terms as [|right_term right_terms].
      * symmetry in Hterms.
        apply Sorting.Permutation.Permutation_nil in Hterms.
        discriminate.
      * reflexivity.
  - destruct left_terms as [|left_term left_terms];
      destruct right_terms as [|right_term right_terms].
    + reflexivity.
    + apply Sorting.Permutation.Permutation_nil in Hterms; discriminate.
    + symmetry in Hterms.
      apply Sorting.Permutation.Permutation_nil in Hterms; discriminate.
    + unfold query_make_groups, FlatData.make_groups.
      apply partition_members_equal_of_key_decisions.
      intros first second Hfirst Hsecond.
      change
        (Oset.eq_bool (OrderedSet.mk_olists (OVal T))
          (query_grouping_key env (left_term :: left_terms) first)
          (query_grouping_key env (left_term :: left_terms) second) =
         Oset.eq_bool (OrderedSet.mk_olists (OVal T))
          (query_grouping_key env (right_term :: right_terms) first)
          (query_grouping_key env (right_term :: right_terms) second)).
      exact
        (query_grouping_key_decision_Permutation
          T env (left_term :: left_terms) (right_term :: right_terms)
          first second Hterms).
Qed.

(** Recover a fine grouping key from the representative at the head of a
    materialized group.  The empty branch is only a totality default; ordinary
    nonempty-key [query_make_groups] groups are nonempty. *)
Definition query_grouping_head_key
    (T : Tuple.Rcd) (env : Env.env T)
    (group_terms : list (@aggterm T))
    (group : list (tuple T)) : list (value T) :=
  match group with
  | nil => nil
  | row :: _ => query_grouping_key env group_terms row
  end.

Arguments query_grouping_head_key {T} _ _ _.

(** The rows being grouped may be produced by a schema-changing projection.
    If that projection preserves each source grouping key, grouping the
    projected rows is exactly the pointwise image of the source partition. *)
Theorem query_make_groups_map_heterogeneous :
  forall (T : Tuple.Rcd) (A : Type) env group_terms
      (keyA : A -> list (value T)) (emit : A -> tuple T) rows,
    group_terms <> nil ->
    (forall item, In item rows ->
      query_grouping_key env group_terms (emit item) = keyA item) ->
    @query_make_groups T env (map emit rows) group_terms =
    map (fun keyed => map emit (snd keyed))
      (@Partition.partition A (list (value T))
        (OrderedSet.mk_olists (OVal T)) keyA rows).
Proof.
  intros T A env group_terms keyA emit rows Hterms Hkeys.
  destruct group_terms as [|term terms]; [contradiction|].
  unfold query_make_groups, FlatData.make_groups.
  pose proof (partition_map_heterogeneous
    A (tuple T) (list (value T))
    (OrderedSet.mk_olists (OVal T)) keyA
    (fun row =>
      map
        (fun current =>
          interp_aggterm T (env_t T env row) current)
        (term :: terms)) emit rows) as Hpartition.
  assert (Hkey_exact : forall item, In item rows ->
    (fun row =>
      map
        (fun current =>
          interp_aggterm T (env_t T env row) current)
        (term :: terms)) (emit item) = keyA item).
  {
    intros item Hitem.
    exact (Hkeys item Hitem).
  }
  specialize (Hpartition Hkey_exact).
  rewrite Hpartition, map_map.
  apply map_ext; intros [key members].
  reflexivity.
Qed.

(** Query-level ordered refinement.  When the coarse grouping key factors
    through the fine grouping key, direct coarse grouping aligns position by
    position with fine grouping followed by coarsening the representative fine
    keys.  Each aligned pair contains the same row occurrences. *)
Theorem query_make_groups_factored_refinement_Forall2 :
  forall (T : Tuple.Rcd) (env : Env.env T) rows
      fine_terms coarse_terms
      (factor : list (value T) -> list (value T)),
    fine_terms <> nil ->
    coarse_terms <> nil ->
    (forall row, In row rows ->
      query_grouping_key env coarse_terms row =
      factor (query_grouping_key env fine_terms row)) ->
    Forall2 (@Sorting.Permutation.Permutation (tuple T))
      (@query_make_groups T env rows coarse_terms)
      (map
        (fun coarse_group => concat (snd coarse_group))
        (@Partition.partition
          (list (tuple T)) (list (value T))
          (OrderedSet.mk_olists (OVal T))
          (fun fine_group =>
            factor (query_grouping_head_key env fine_terms fine_group))
          (@query_make_groups T env rows fine_terms))).
Proof.
  intros T env rows [|fine_term fine_terms] [|coarse_term coarse_terms]
    factor Hfine Hcoarse Hkeys; try contradiction.
  set (key_order := OrderedSet.mk_olists (OVal T)).
  set (fine_key := query_grouping_key env (fine_term :: fine_terms)).
  set (coarse_key := query_grouping_key env (coarse_term :: coarse_terms)).
  set (fine_partition :=
    @Partition.partition (tuple T) (list (value T))
      key_order fine_key rows).
  set (refined_partition :=
    @Partition.partition (list (value T) * list (tuple T))
      (list (value T)) key_order
      (fun fine_group => factor (fst fine_group)) fine_partition).
  pose proof
    (partition_factored_key_refinement_Forall2
      (tuple T) (list (value T)) (list (value T))
      key_order key_order fine_key coarse_key factor rows Hkeys)
    as Hrefinement.
  fold fine_partition in Hrefinement.
  fold refined_partition in Hrefinement.
  assert (Hmapped :
    Forall2 (@Sorting.Permutation.Permutation (tuple T))
      (map snd
        (@Partition.partition (tuple T) (list (value T))
          key_order coarse_key rows))
      (map
        (fun refined_group =>
          concat (map snd (snd refined_group)))
        refined_partition)).
  {
    induction Hrefinement as
      [|coarse_group refined_group coarse_tail refined_tail
        [_ Hmembers] _ IH].
    - constructor.
    - constructor; assumption.
  }
  assert (Hmapped_partition :
    @Partition.partition (list (tuple T)) (list (value T)) key_order
      (fun fine_group =>
        factor
          (query_grouping_head_key env
            (fine_term :: fine_terms) fine_group))
      (map snd fine_partition) =
    map
      (fun refined_group =>
        (fst refined_group, map snd (snd refined_group)))
      refined_partition).
  {
    unfold refined_partition.
    apply partition_map_heterogeneous.
    intros [fine_value members] Hmember; cbn.
    assert (Hnonempty : members <> nil).
    {
      eapply Partition.in_partition_diff_nil.
      exact Hmember.
    }
    destruct members as [|first rest]; [contradiction|].
    pose proof
      (@Partition.partition_homogeneous_values
        (tuple T) (list (value T)) key_order fine_key rows
        fine_value (first :: rest) Hmember first
        (or_introl eq_refl)) as Hfirst.
    cbn [query_grouping_head_key].
    unfold fine_key in Hfirst.
    now rewrite Hfirst.
  }
  change (Forall2 (@Sorting.Permutation.Permutation (tuple T))
    (map snd
      (@Partition.partition (tuple T) (list (value T))
        key_order coarse_key rows))
    (map (fun coarse_group => concat (snd coarse_group))
      (@Partition.partition (list (tuple T)) (list (value T)) key_order
        (fun fine_group =>
          factor
            (query_grouping_head_key env
              (fine_term :: fine_terms) fine_group))
        (map snd fine_partition)))).
  rewrite Hmapped_partition, map_map.
  exact Hmapped.
Qed.

(** This lift deliberately requires at least one grouping term.  Empty global
    grouping has one empty group on empty input, so treating it as an ordinary
    partition/filter rewrite would be false. *)
Theorem query_make_groups_filter_by_key_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms rows
      (keep : list (value T) -> bool),
    group_terms <> nil ->
    @query_make_groups T env
      (filter
        (fun row => keep (query_grouping_key env group_terms row)) rows)
      group_terms =
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (query_grouping_key env group_terms row)
        end)
      (@query_make_groups T env rows group_terms).
Proof.
  intros T env group_terms rows keep Hgroup_terms.
  destruct group_terms as [|term group_terms]; [contradiction|].
  cbn [query_make_groups make_groups query_grouping_key].
  apply partition_members_filter_by_key_exact.
Qed.

(** Flattening the groups selected by a key predicate contains exactly the
    selected input occurrences, modulo FormalSQL's semantic tuple equality. *)
Theorem query_make_groups_selected_members_permut :
  forall (T : Tuple.Rcd) env rows group_terms keep,
    group_terms <> nil ->
    Oeset.permut (OTuple T)
      (filter
        (fun row => keep (query_grouping_key env group_terms row)) rows)
      (concat
        (filter
          (fun members =>
            match members with
            | nil => false
            | row :: _ => keep (query_grouping_key env group_terms row)
            end)
          (@query_make_groups T env rows group_terms))).
Proof.
  intros T env rows group_terms keep Hterms.
  rewrite <- (query_make_groups_filter_by_key_exact
    T env group_terms rows keep Hterms).
  destruct group_terms as [|term terms]; [contradiction|].
  unfold query_make_groups, FlatData.make_groups.
  assert (Hconcat : forall groups :
    list (list (value T) * list (tuple T)),
    concat (map snd groups) =
    flat_map (fun group => snd group) groups).
  {
    intro groups; induction groups as [|[key members] groups IH];
      cbn; now rewrite ?IH.
  }
  rewrite Hconcat.
  apply ListPermut._permut_incl with (@eq (tuple T)).
  - intros left right ->; apply Oeset.compare_eq_refl.
  - apply Partition.partition_permut.
Qed.

(** The same selected-member fact under literal row equality, ready for
    Stdlib results such as permutation-invariant folds and sums. *)
Theorem query_make_groups_selected_members_Permutation :
  forall (T : Tuple.Rcd) env rows group_terms keep,
    group_terms <> nil ->
    Sorting.Permutation.Permutation
      (filter
        (fun row => keep (query_grouping_key env group_terms row)) rows)
      (concat
        (filter
          (fun members =>
            match members with
            | nil => false
            | row :: _ => keep (query_grouping_key env group_terms row)
            end)
          (@query_make_groups T env rows group_terms))).
Proof.
  intros T env rows group_terms keep Hterms.
  rewrite <- (query_make_groups_filter_by_key_exact
    T env group_terms rows keep Hterms).
  destruct group_terms as [|term terms]; [contradiction|].
  unfold query_make_groups, FlatData.make_groups.
  assert (Hconcat : forall groups :
    list (list (value T) * list (tuple T)),
    concat (map snd groups) =
    flat_map (fun group => snd group) groups).
  {
    intro groups; induction groups as [|[key members] groups IH];
      cbn; now rewrite ?IH.
  }
  rewrite Hconcat.
  apply list_permut_eq_implies_Permutation.
  apply Partition.partition_permut.
Qed.

(** All rows with one exact nonempty grouping key form one group.  The member
    order is [rev rows] because [Partition.partition] accumulates at the head.
    Empty global grouping is deliberately excluded: on empty input it has one
    empty group rather than no groups. *)
Theorem query_make_groups_constant_nonempty_key :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms
      (key : list (value T)),
    group_terms <> nil ->
    (forall row,
      In row rows ->
      query_grouping_key env group_terms row = key) ->
    @query_make_groups T env rows group_terms =
      match rows with
      | nil => nil
      | _ :: _ => rev rows :: nil
      end.
Proof.
  intros T env rows [|term terms] key Hnonempty Hconstant;
    [contradiction|].
  unfold query_make_groups, make_groups.
  rewrite (@Partition.partition_cst _ _ _ _ key rows).
  - destruct rows; reflexivity.
  - exact Hconstant.
Qed.

(** Combining exact key filtering with constant-key grouping yields either no
    selected group or the one exact accumulator-ordered selected group. *)
Theorem query_make_groups_matching_one_key_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms rows
      (keep : list (value T) -> bool) key,
    group_terms <> nil ->
    (forall row,
      In row
        (filter
          (fun item =>
            keep (query_grouping_key env group_terms item)) rows) ->
      query_grouping_key env group_terms row = key) ->
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (query_grouping_key env group_terms row)
        end)
      (@query_make_groups T env rows group_terms) =
    match
      filter
        (fun item =>
          keep (query_grouping_key env group_terms item)) rows
    with
    | nil => nil
    | _ :: _ =>
        [rev
          (filter
            (fun item =>
              keep (query_grouping_key env group_terms item)) rows)]
    end.
Proof.
  intros T env group_terms rows keep key Hterms Hconstant.
  rewrite <-
    (query_make_groups_filter_by_key_exact
      T env group_terms rows keep Hterms).
  exact
    (@query_make_groups_constant_nonempty_key T env
      (filter
        (fun item =>
          keep (query_grouping_key env group_terms item)) rows)
      group_terms key Hterms Hconstant).
Qed.

(** Lookup form used by scalar-aggregate decorrelation.  Filtering the
    materialized groups by one outer correlation key yields no group exactly
    when no input row has that key; otherwise it yields the single group whose
    members are the matching input occurrences.  The [rev] is the internal
    partition accumulator order and can be discharged by permutation-stable
    aggregate facts. *)
Theorem query_make_groups_lookup_key_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms rows key,
    group_terms <> nil ->
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ =>
            Oset.eq_bool (OrderedSet.mk_olists (OVal T))
              (query_grouping_key env group_terms row) key
        end)
      (@query_make_groups T env rows group_terms) =
    match
      filter
        (fun row =>
          Oset.eq_bool (OrderedSet.mk_olists (OVal T))
            (query_grouping_key env group_terms row) key)
        rows
    with
    | nil => nil
    | _ :: _ =>
        [rev
          (filter
            (fun row =>
              Oset.eq_bool (OrderedSet.mk_olists (OVal T))
                (query_grouping_key env group_terms row) key)
            rows)]
    end.
Proof.
  intros T env group_terms rows key Hterms.
  eapply (@query_make_groups_matching_one_key_exact
    T env group_terms rows
    (fun candidate =>
      Oset.eq_bool (OrderedSet.mk_olists (OVal T)) candidate key)
    key); [exact Hterms|].
  intros row Hrow.
  apply filter_In in Hrow as [_ Hkey].
  now apply Oset.eq_bool_true_iff in Hkey.
Qed.

(** Every two members of an ordinary nonempty-key group have the same complete
    grouping-key vector. *)
Lemma query_make_groups_members_same_key_nonempty :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms group left right,
    group_terms <> nil ->
    In group (@query_make_groups T env rows group_terms) ->
    In left group ->
    In right group ->
    query_grouping_key env group_terms left =
    query_grouping_key env group_terms right.
Proof.
  intros T env rows [|term terms] group left right Hterms Hgroup Hleft Hright;
    [contradiction|].
  unfold query_make_groups in Hgroup.
  cbn [FlatData.make_groups] in Hgroup.
  unfold query_grouping_key.
  apply in_map_iff in Hgroup as [[key members] [Hequal Hin]].
  cbn in Hequal; subst members.
  pose proof
    (@Partition.partition_homogeneous_values
      _ _ _ _ _ _ _ Hin left Hleft) as Hleft_key.
  pose proof
    (@Partition.partition_homogeneous_values
      _ _ _ _ _ _ _ Hin right Hright) as Hright_key.
  now rewrite Hleft_key, Hright_key.
Qed.

(** A concrete group is exactly the reverse of the input rows whose complete
    key equals the key of any chosen member.  This is the row-selection bridge
    used before applying permutation-invariant aggregate regrouping facts. *)
Theorem query_make_groups_member_exact_key_filter :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms group row,
    group_terms <> nil ->
    In group (@query_make_groups T env rows group_terms) ->
    In row group ->
    group =
      rev
        (filter
          (fun item =>
            Oset.eq_bool (OrderedSet.mk_olists (OVal T))
              (query_grouping_key env group_terms item)
              (query_grouping_key env group_terms row))
          rows).
Proof.
  intros T env rows group_terms group row Hterms Hgroup Hrow.
  set (key_order := OrderedSet.mk_olists (OVal T)).
  set (chosen := query_grouping_key env group_terms row).
  set (keep := fun key => Oset.eq_bool key_order key chosen).
  assert (Hconstant : forall item,
    In item
      (filter
        (fun candidate =>
          keep (query_grouping_key env group_terms candidate)) rows) ->
    query_grouping_key env group_terms item = chosen).
  {
    intros item Hitem.
    apply filter_In in Hitem; destruct Hitem as [_ Hkeep].
    unfold keep in Hkeep.
    now apply Oset.eq_bool_true_iff in Hkeep.
  }
  pose proof (query_make_groups_matching_one_key_exact
    T env group_terms rows keep chosen Hterms Hconstant) as Hmatching.
  assert (Hgroup_selected : In group
    (filter
      (fun members =>
        match members with
        | nil => false
        | first :: _ => keep (query_grouping_key env group_terms first)
        end)
      (@query_make_groups T env rows group_terms))).
  {
    apply filter_In; split; [exact Hgroup|].
    destruct group as [|first rest]; [contradiction|].
    unfold keep.
    apply Oset.eq_bool_true_iff.
    unfold chosen.
    exact (query_make_groups_members_same_key_nonempty
      T env rows group_terms (first :: rest) first row
      Hterms Hgroup (or_introl eq_refl) Hrow).
  }
  rewrite Hmatching in Hgroup_selected.
  assert (Hrow_selected : In row
    (filter
      (fun item => keep (query_grouping_key env group_terms item)) rows)).
  {
    apply filter_In; split.
    - destruct group_terms as [|term terms]; [contradiction|].
      unfold query_make_groups in Hgroup.
      cbn [FlatData.make_groups] in Hgroup.
      eapply Partition.in_map_snd_partition; eassumption.
    - unfold keep, chosen.
      apply Oset.eq_bool_true_iff.
      reflexivity.
  }
  destruct
    (filter
      (fun item => keep (query_grouping_key env group_terms item)) rows)
    as [|first rest] eqn:Hselected; [contradiction|].
  cbn in Hgroup_selected.
  destruct Hgroup_selected as [Hequal | []].
  subst group.
  unfold keep, key_order, chosen in Hselected |- *.
  now rewrite Hselected.
Qed.

(** Aggregate clients normally need only occurrence preservation, not the
    accumulator-specific [rev] exposed by the exact partition theorem. *)
Corollary query_make_groups_member_key_filter_Permutation :
  forall (T : Tuple.Rcd) (env : Env.env T) rows group_terms group row,
    group_terms <> nil ->
    In group (@query_make_groups T env rows group_terms) ->
    In row group ->
    Sorting.Permutation.Permutation group
      (filter
        (fun item =>
          Oset.eq_bool (OrderedSet.mk_olists (OVal T))
            (query_grouping_key env group_terms item)
            (query_grouping_key env group_terms row))
        rows).
Proof.
intros T env rows group_terms group row Hterms Hgroup Hrow.
rewrite (query_make_groups_member_exact_key_filter
  T env rows group_terms group row Hterms Hgroup Hrow).
apply Sorting.Permutation.Permutation_sym.
apply Sorting.Permutation.Permutation_rev.
Qed.

(** Global grouping always forms exactly one logical group, including the SQL
    empty-input group.  The exact member order remains the partition helper's
    accumulator order; the length corollary is the preferred public consumer. *)
Theorem query_make_groups_global_exact :
  forall (T : Tuple.Rcd) (env : Env.env T) rows,
    @query_make_groups T env rows [] = [rev rows].
Proof.
intros T env [|row rows]; [reflexivity|].
unfold query_make_groups, FlatData.make_groups.
rewrite (@Partition.partition_cst _ _ _ _
  ([] : list (value T)) (row :: rows)).
- reflexivity.
- intros; reflexivity.
Qed.

Corollary query_make_groups_global_length_one :
  forall (T : Tuple.Rcd) (env : Env.env T) rows,
    length (@query_make_groups T env rows []) = 1%nat.
Proof.
intros; now rewrite query_make_groups_global_exact.
Qed.

(** For a nonempty grouping key, semantic permutation of the input rows
    induces semantic permutation of the resulting groups.  Group comparison
    itself is permutation-aware through [OLTuple], so neither the order in
    which groups are discovered nor the accumulator order within a group is
    exposed by this statement.  Empty global grouping is excluded because its
    empty-input correction is not the ordinary [make_groups] partition. *)
Lemma query_make_groups_permut_nonempty :
  forall (T : Tuple.Rcd) (env : Env.env T) group_terms left right,
    group_terms <> nil ->
    Oeset.permut (OTuple T) left right ->
    Oeset.permut (OLTuple T)
      (@query_make_groups T env left group_terms)
      (@query_make_groups T env right group_terms).
Proof.
  intros T env [|term group_terms] left right Hnonempty Hrows;
    [contradiction|].
  apply Oeset.nb_occ_permut; intro group.
  cbn [query_make_groups].
  eapply FlatData.make_groups_eq.
  - apply Env.equiv_env_refl.
  - exact Hrows.
Qed.

(** Filtering and projecting semantically permuted groups preserves semantic
    row permutation whenever both operations respect semantic group equality.
    This packages the relation-sensitive [permut_filter_eq]/[_permut_map]
    combination used after HAVING. *)
Lemma group_filter_map_permutation :
  forall (T : Tuple.Rcd) left right
      (keep : list (tuple T) -> bool)
      (emit : list (tuple T) -> tuple T),
    (forall first second,
      Oeset.compare (OLTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall first second,
      Oeset.compare (OLTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    Oeset.permut (OLTuple T) left right ->
    Oeset.permut (OTuple T)
      (map emit (filter keep left))
      (map emit (filter keep right)).
Proof.
  intros T left right keep emit Hkeep Hemit Hgroups.
  eapply (@ListPermut._permut_map
    (list (tuple T)) (list (tuple T)) (tuple T) (tuple T)
    (fun first second => Oeset.compare (OLTuple T) first second = Eq)
    (fun first second => Oeset.compare (OTuple T) first second = Eq)
    emit emit (filter keep left) (filter keep right)).
  - intros first second Hfirst Hsecond Hequal; now apply Hemit.
  - apply ListPermut.permut_filter_eq.
    + intros first second Hfirst Hequal; now apply Hkeep.
    + exact Hgroups.
Qed.
