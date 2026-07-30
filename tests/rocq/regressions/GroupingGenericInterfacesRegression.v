From SQLFS Require Import
  Env FlatData ListPermut OrderedSet Partition SqlQuerySemantics
  SqlQuerySyntax.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts GroupingRewriteFacts.
From Stdlib Require Import List Sorting.Permutation.

Import ListNotations.
Import Tuple.

(** Lock the bridge from FormalSQL's occurrence permutation to Stdlib's
    literal permutation. *)
Theorem list_permut_eq_bridge_regression :
  forall (A : Type) (left right : list A),
    ListPermut._permut (@eq A) left right ->
    Sorting.Permutation.Permutation left right.
Proof.
  exact list_permut_eq_implies_Permutation.
Qed.

(** Lock the schema-changing partition interface used by projection/grouping
    rewrites. *)
Theorem partition_map_heterogeneous_regression :
  forall (A B Key : Type) (key_order : Oset.Rcd Key)
      (keyA : A -> Key) (keyB : B -> Key) (emit : A -> B) rows,
    (forall row, In row rows -> keyB (emit row) = keyA row) ->
    @Partition.partition B Key key_order keyB (map emit rows) =
    map (fun group => (fst group, map emit (snd group)))
      (@Partition.partition A Key key_order keyA rows).
Proof.
  exact partition_map_heterogeneous.
Qed.

Theorem partition_factored_key_refinement_regression :
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
  exact partition_factored_key_refinement_Forall2.
Qed.

(** Lock the representation-independent canonical-row bridge used when a
    projection or rename is moved across a bag-reset operator. *)
Theorem canonical_rows_map_factor_permutation_regression :
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
  exact query_canonical_rows_map_factor_permut.
Qed.

Section QueryGroupingInterfaces.

Context {T : Tuple.Rcd}.

Theorem query_make_groups_map_heterogeneous_regression :
  forall (A : Type) env group_terms
      (keyA : A -> list (value T)) (emit : A -> tuple T) rows,
    group_terms <> nil ->
    (forall item, In item rows ->
      query_grouping_key env group_terms (emit item) = keyA item) ->
    @query_make_groups T env (map emit rows) group_terms =
    map (fun keyed => map emit (snd keyed))
      (@Partition.partition A (list (value T))
        (OrderedSet.mk_olists (OVal T)) keyA rows).
Proof.
  exact (@query_make_groups_map_heterogeneous T).
Qed.

(** Lock the arity-independent GROUP BY reordering bridge.  This replaces
    case-local proofs that expanded a fixed two-, four-, or five-column key. *)
Theorem query_make_groups_group_terms_permutation_regression :
  forall env rows left_terms right_terms,
    Sorting.Permutation.Permutation left_terms right_terms ->
    @query_make_groups T env rows left_terms =
    @query_make_groups T env rows right_terms.
Proof.
  exact (@query_make_groups_group_terms_Permutation T).
Qed.

Theorem query_make_groups_factored_refinement_regression :
  forall env rows fine_terms coarse_terms
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
  exact (@query_make_groups_factored_refinement_Forall2 T).
Qed.

Theorem query_make_groups_selected_members_regression :
  forall env rows group_terms keep,
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
  exact (@query_make_groups_selected_members_Permutation T).
Qed.

Theorem query_make_groups_member_exact_key_filter_regression :
  forall env rows group_terms group row,
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
  exact (@query_make_groups_member_exact_key_filter T).
Qed.

Theorem query_make_groups_lookup_key_exact_regression :
  forall env group_terms rows key,
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
  exact (@query_make_groups_lookup_key_exact T).
Qed.

Theorem query_make_groups_member_key_filter_permutation_regression :
  forall env rows group_terms group row,
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
  exact (@query_make_groups_member_key_filter_Permutation T).
Qed.

Theorem query_make_groups_global_shape_regression :
  forall env rows,
    @query_make_groups T env rows [] = [rev rows].
Proof.
  exact (@query_make_groups_global_exact T).
Qed.

End QueryGroupingInterfaces.

Check query_make_groups_selected_members_permut.
Check query_make_groups_matching_one_key_exact.
Check query_make_groups_members_same_key_nonempty.
Check partition_member_exact_key_filter.
Check query_grouping_head_key.
Check rows_permut_implies_bag_eq.
Check rows_reverse_permut_congr.
Check eval_groups_global_true_outcome_exact.
Check group_projection_permutation_stable.
Check eval_group_bag_global_true_success_for_representative.
Check eval_group_bag_global_true_success_exists.
Check eval_group_bag_global_true_success_bag_unique_if_stable.

Print Assumptions list_permut_eq_bridge_regression.
Print Assumptions partition_map_heterogeneous_regression.
Print Assumptions partition_factored_key_refinement_regression.
Print Assumptions canonical_rows_map_factor_permutation_regression.
Print Assumptions query_make_groups_map_heterogeneous_regression.
Print Assumptions query_make_groups_group_terms_permutation_regression.
Print Assumptions query_make_groups_factored_refinement_regression.
Print Assumptions query_make_groups_selected_members_regression.
Print Assumptions query_make_groups_member_exact_key_filter_regression.
Print Assumptions query_make_groups_lookup_key_exact_regression.
Print Assumptions query_make_groups_member_key_filter_permutation_regression.
Print Assumptions query_make_groups_global_shape_regression.
Print Assumptions rows_permut_implies_bag_eq.
Print Assumptions rows_reverse_permut_congr.
Print Assumptions eval_groups_global_true_outcome_exact.
Print Assumptions group_projection_permutation_stable.
Print Assumptions eval_group_bag_global_true_success_for_representative.
Print Assumptions eval_group_bag_global_true_success_exists.
Print Assumptions eval_group_bag_global_true_success_bag_unique_if_stable.
