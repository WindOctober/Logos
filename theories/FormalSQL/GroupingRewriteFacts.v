(******************************************************************************)
(** Exact, reusable grouping/filter facts for normalized FormalSQL queries.   **)
(******************************************************************************)

From SQLFS Require Import
  Env FiniteSet FlatData OrderedSet Partition SqlAlgebra SqlQuerySemantics
  SqlQuerySyntax SqlQueryWellFormed.
From Stdlib Require Import Bool List.

Import ListNotations.
Import Tuple.

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

End PartitionFilter.

(** The grouping key used by [query_make_groups], exposed only to keep the
    theorem below readable.  It is definitionally the key in
    [FlatData.make_groups]. *)
Definition query_grouping_key
    (T : Tuple.Rcd) (env : Env.env T)
    (group_terms : list (@aggterm T)) (row : tuple T) : list (value T) :=
  map (fun term => interp_aggterm T (env_t T env row) term) group_terms.

Arguments query_grouping_key {T} _ _ _.

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

(** Admissibility is syntax directed.  These small constructors preserve all
    of the premises in [SqlQueryWellFormed] instead of asking each generated
    proof to unfold the mutual fixpoint. *)
Section AdmissibilityConstructors.

Context {T : Tuple.Rcd} {relname : Type}.
Variable basesort : relname -> SqlQueryWellFormed.setA T.

Lemma formula_expr_admissible_conj_intro :
  forall operation left right,
    @formula_expr_admissible T relname basesort left ->
    @formula_expr_admissible T relname basesort right ->
    @formula_expr_admissible T relname basesort
      (FExpr_Conj operation left right).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_bag_intro :
  forall outputs query,
    @query_output_attributes_unique T outputs ->
    @bag_query_admissible T relname basesort query ->
    @query_outputs_sort T outputs =S=
      @SqlAlgebra.sort T relname basesort query ->
    @query_expr_admissible T relname basesort
      (QExpr_Bag outputs query).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_set_intro :
  forall operation left right,
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    query_expr_outputs left = query_expr_outputs right ->
    @query_expr_admissible T relname basesort
      (QExpr_Set operation left right).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_natural_join_intro :
  forall left right,
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    @query_expr_admissible T relname basesort
      (QExpr_NaturalJoin left right).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_cross_join_intro :
  forall left right,
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    @query_output_sorts_disjoint T
      (query_expr_sort left) (query_expr_sort right) ->
    @query_expr_admissible T relname basesort
      (QExpr_CrossJoin left right).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_join_intro :
  forall kind predicate matched_select left_select right_select left right,
    @formula_expr_admissible T relname basesort predicate ->
    @query_expr_admissible T relname basesort left ->
    @query_expr_admissible T relname basesort right ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    @query_expr_admissible T relname basesort
      (QExpr_Join kind predicate matched_select left_select right_select
        left right).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_project_intro :
  forall select_list input,
    @query_expr_admissible T relname basesort input ->
    query_select_list_outputs_unique select_list ->
    @query_expr_admissible T relname basesort
      (QExpr_Project select_list input).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_filter_intro :
  forall formula input,
    @query_expr_admissible T relname basesort input ->
    @formula_expr_admissible T relname basesort formula ->
    @query_expr_admissible T relname basesort
      (QExpr_Filter formula input).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_group_intro :
  forall select_list group_terms having input,
    @query_expr_admissible T relname basesort input ->
    @formula_expr_admissible T relname basesort having ->
    query_select_list_outputs_unique select_list ->
    @query_expr_admissible T relname basesort
      (QExpr_Group select_list group_terms having input).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_grouping_sets_intro :
  forall grouping_sets input,
    @query_expr_admissible T relname basesort input ->
    query_grouping_sets_well_formed grouping_sets ->
    @query_expr_admissible T relname basesort
      (QExpr_GroupingSets grouping_sets input).
Proof. intros; cbn; tauto. Qed.

Lemma query_expr_admissible_distinct_intro :
  forall input,
    @query_expr_admissible T relname basesort input ->
    @query_expr_admissible T relname basesort (QExpr_Distinct input).
Proof. intros; cbn; assumption. Qed.

Lemma query_expr_admissible_offset_intro :
  forall count input,
    @query_expr_admissible T relname basesort input ->
    @query_expr_admissible T relname basesort (QExpr_Offset count input).
Proof. intros; cbn; assumption. Qed.

Lemma query_expr_admissible_fetch_intro :
  forall count input,
    @query_expr_admissible T relname basesort input ->
    @query_expr_admissible T relname basesort (QExpr_Fetch count input).
Proof. intros; cbn; assumption. Qed.

Lemma query_expr_admissible_order_by_intro :
  forall keys input,
    @query_expr_admissible T relname basesort input ->
    query_sort_keys_in_scope (query_expr_sort input) keys ->
    @query_expr_admissible T relname basesort (QExpr_OrderBy keys input).
Proof. intros; cbn; tauto. Qed.

End AdmissibilityConstructors.
