(*****************************************************************************)
(** Occurrence-exact filter laws for outer-join scheduler branches.          **)
(*****************************************************************************)

From Stdlib Require Import Bool List Sorting.Permutation.
From SQLFS Require Import ListFacts.
From Logos.FormalSQL Require Import CardinalityCombinators.

Import ListNotations.

(** These list constructors expose the three semantic branches of an outer
    join without choosing a SQL row representation.  Duplicate input
    occurrences remain duplicate output occurrences. *)
Definition join_matched_rows {A B C : Type}
    (join : A -> B -> C) (accept : A -> B -> bool)
    (left : list A) (right : list B) : list C :=
  flat_map
    (fun left_row => map (join left_row) (filter (accept left_row) right))
    left.

Definition join_unmatched_left_rows {A B C : Type}
    (pad_left : A -> C) (accept : A -> B -> bool)
    (left : list A) (right : list B) : list C :=
  map pad_left
    (filter
      (fun left_row => negb (existsb (accept left_row) right)) left).

Definition join_unmatched_right_rows {A B C : Type}
    (pad_right : B -> C) (accept : A -> B -> bool)
    (left : list A) (right : list B) : list C :=
  map pad_right
    (filter
      (fun right_row =>
        negb (existsb (fun left_row => accept left_row right_row) left))
      right).

Definition left_outer_scheduler_rows {A B C : Type}
    (join : A -> B -> C) (pad_left : A -> C)
    (accept : A -> B -> bool) (left : list A) (right : list B) : list C :=
  join_matched_rows join accept left right ++
  join_unmatched_left_rows pad_left accept left right.

Definition full_outer_scheduler_rows {A B C : Type}
    (join : A -> B -> C) (pad_left : A -> C) (pad_right : B -> C)
    (accept : A -> B -> bool) (left : list A) (right : list B) : list C :=
  join_matched_rows join accept left right ++
  join_unmatched_left_rows pad_left accept left right ++
  join_unmatched_right_rows pad_right accept left right.

Definition right_outer_scheduler_rows {A B C : Type}
    (join : A -> B -> C) (pad_right : B -> C)
    (accept : A -> B -> bool) (left : list A) (right : list B) : list C :=
  join_matched_rows join accept left right ++
  join_unmatched_right_rows pad_right accept left right.

Local Lemma flat_map_optional_cons_Permutation :
  forall (A C : Type) (select : A -> bool)
      (head : A -> C) (tail : A -> list C) rows,
    Permutation
      (flat_map
        (fun row => if select row then head row :: tail row else tail row)
        rows)
      (map head (filter select rows) ++ flat_map tail rows).
Proof.
  intros A C select head tail rows.
  induction rows as [|row rows IH]; [constructor|].
  cbn [flat_map].
  destruct (select row) eqn:Hselect; cbn [filter].
  - rewrite Hselect; cbn [map filter].
    apply perm_skip.
    eapply Permutation_trans.
    + apply Permutation_app_head; exact IH.
    + eapply Permutation_trans with
        (l' :=
          (map head (filter select rows) ++ tail row) ++
          flat_map tail rows).
      * rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
      * change
          (Permutation
            ((map head (filter select rows) ++ tail row) ++
             flat_map tail rows)
            (map head (filter select rows) ++
             (tail row ++ flat_map tail rows))).
        rewrite (app_assoc
          (map head (filter select rows)) (tail row) (flat_map tail rows)).
        apply Permutation_refl.
  - rewrite Hselect; cbn [map filter].
    eapply Permutation_trans.
    + apply Permutation_app_head; exact IH.
    + eapply Permutation_trans with
        (l' :=
          (map head (filter select rows) ++ tail row) ++
          flat_map tail rows).
      * rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
      * change
          (Permutation
            ((map head (filter select rows) ++ tail row) ++
             flat_map tail rows)
            (map head (filter select rows) ++
             (tail row ++ flat_map tail rows))).
        rewrite (app_assoc
          (map head (filter select rows)) (tail row) (flat_map tail rows)).
        apply Permutation_refl.
Qed.

Local Lemma join_matched_rows_transpose_Permutation :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) left right,
    Permutation
      (join_matched_rows join accept left right)
      (join_matched_rows
        (fun right_row left_row => join left_row right_row)
        (fun right_row left_row => accept left_row right_row)
        right left).
Proof.
  intros A B C join accept left.
  induction left as [|left_row left IH]; intro right.
  - unfold join_matched_rows.
    induction right as [|right_row right IHright];
      cbn [flat_map]; [constructor|exact IHright].
  - change
      (Permutation
        (map (join left_row) (filter (accept left_row) right) ++
         join_matched_rows join accept left right)
        (flat_map
          (fun right_row =>
            map (fun current => join current right_row)
              (filter (fun current => accept current right_row)
                (left_row :: left))) right)).
    eapply Permutation_trans.
    + apply Permutation_app.
      * apply Permutation_refl.
      * apply IH.
    + symmetry.
      assert (Hcolumns :
        flat_map
          (fun right_row =>
            map (fun current => join current right_row)
              (filter (fun current => accept current right_row)
                (left_row :: left))) right =
        flat_map
          (fun right_row =>
            if accept left_row right_row
            then
              join left_row right_row ::
              map (fun current => join current right_row)
                (filter (fun current => accept current right_row) left)
            else
              map (fun current => join current right_row)
                (filter (fun current => accept current right_row) left))
          right).
      { apply flat_map_ext; intro right_row.
        destruct (accept left_row right_row) eqn:Hcell;
          cbn [map filter]; now rewrite Hcell. }
      unfold join_matched_rows.
      rewrite Hcolumns.
      apply flat_map_optional_cons_Permutation.
Qed.

(** LEFT and RIGHT outer schedulers are exact occurrence permutations after
    swapping operands and transposing both the match decision and matched-row
    emitter.  The unmatched preserved-side emitter is literally the same
    function.  This theorem is list-level only: SQL condition/projection
    errors and semantic row equality must be transported separately. *)
Theorem left_right_outer_scheduler_swap_Permutation :
  forall (A B C : Type) (join : A -> B -> C) (pad_left : A -> C)
      (accept : A -> B -> bool) left right,
    Permutation
      (left_outer_scheduler_rows join pad_left accept left right)
      (right_outer_scheduler_rows
        (fun right_row left_row => join left_row right_row)
        pad_left
        (fun right_row left_row => accept left_row right_row)
        right left).
Proof.
  intros A B C join pad_left accept left right.
  unfold left_outer_scheduler_rows, right_outer_scheduler_rows.
  apply Permutation_app.
  - apply join_matched_rows_transpose_Permutation.
  - apply Permutation_refl.
Qed.

Local Lemma filter_join_matched_rows_guard_left :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) (guard_left : A -> bool)
      (guard_output : C -> bool) left right,
    (forall left_row right_row,
      guard_output (join left_row right_row) = guard_left left_row) ->
    filter guard_output (join_matched_rows join accept left right) =
    join_matched_rows join accept (filter guard_left left) right.
Proof.
  intros A B C join accept guard_left guard_output left.
  induction left as [|left_row left IH]; intros right Hguard; [reflexivity|].
  change
    (filter guard_output
      (map (join left_row) (filter (accept left_row) right) ++
       join_matched_rows join accept left right) =
     join_matched_rows join accept
       (if guard_left left_row
        then left_row :: filter guard_left left
        else filter guard_left left) right).
  rewrite ListFacts.filter_app, ListFacts.filter_map, IH by exact Hguard.
  destruct (guard_left left_row) eqn:Hleft; cbn [join_matched_rows flat_map].
  - assert (Hkeep :
      filter (fun right_row => guard_output (join left_row right_row))
        (filter (accept left_row) right) =
      filter (accept left_row) right).
    { apply ListFacts.filter_true.
      intros right_row Hright.
      now rewrite Hguard, Hleft. }
    now rewrite Hkeep.
  - assert (Hempty :
      filter (fun right_row => guard_output (join left_row right_row))
        (filter (accept left_row) right) = []).
    { apply ListFacts.filter_false.
      intros right_row Hright.
      now rewrite Hguard, Hleft. }
    now rewrite Hempty.
Qed.

Local Lemma filter_join_unmatched_left_rows_guard_left :
  forall (A B C : Type) (pad_left : A -> C)
      (accept : A -> B -> bool) (guard_left : A -> bool)
      (guard_output : C -> bool) left right,
    (forall left_row,
      guard_output (pad_left left_row) = guard_left left_row) ->
    filter guard_output
      (join_unmatched_left_rows pad_left accept left right) =
    join_unmatched_left_rows pad_left accept
      (filter guard_left left) right.
Proof.
  intros A B C pad_left accept guard_left guard_output left right Hguard.
  unfold join_unmatched_left_rows.
  rewrite ListFacts.filter_map.
  f_equal.
  rewrite (ListFacts.filter_eq
    (fun left_row => guard_output (pad_left left_row))
    guard_left
    (filter
      (fun left_row => negb (existsb (accept left_row) right)) left)).
  - apply filter_filter_commute.
  - intros left_row Hleft; apply Hguard.
Qed.

Local Lemma filter_join_unmatched_right_rows_false :
  forall (A B C : Type) (pad_right : B -> C)
      (accept : A -> B -> bool) (guard_output : C -> bool) left right,
    (forall right_row, guard_output (pad_right right_row) = false) ->
    filter guard_output
      (join_unmatched_right_rows pad_right accept left right) = [].
Proof.
  intros A B C pad_right accept guard_output left right Hguard.
  unfold join_unmatched_right_rows.
  rewrite ListFacts.filter_map.
  assert (Hempty :
    filter (fun right_row => guard_output (pad_right right_row))
      (filter
        (fun right_row =>
          negb (existsb (fun left_row => accept left_row right_row) left))
        right) = []).
  { apply ListFacts.filter_false.
    intros right_row Hright; apply Hguard. }
  now rewrite Hempty.
Qed.

(** Filtering a FULL outer join by a proper total guard that observes only
    the preserved left payload yields the same occurrence list as filtering
    the left input before a LEFT outer join.  The right-padded branch must be
    rejected explicitly.  This is a pure scheduler law: SQL formula
    totality, non-volatility, and exact runtime-error equivalence remain
    separate premises at the query-outcome boundary. *)
Theorem full_outer_filter_to_left_outer_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (pad_left : A -> C) (pad_right : B -> C)
      (accept : A -> B -> bool) (guard_left : A -> bool)
      (guard_output : C -> bool) left right,
    (forall left_row right_row,
      guard_output (join left_row right_row) = guard_left left_row) ->
    (forall left_row,
      guard_output (pad_left left_row) = guard_left left_row) ->
    (forall right_row,
      guard_output (pad_right right_row) = false) ->
    filter guard_output
      (full_outer_scheduler_rows
        join pad_left pad_right accept left right) =
    left_outer_scheduler_rows join pad_left accept
      (filter guard_left left) right.
Proof.
  intros A B C join pad_left pad_right accept guard_left guard_output
    left right Hmatched Hleft Hright.
  unfold full_outer_scheduler_rows, left_outer_scheduler_rows.
  rewrite !ListFacts.filter_app.
  rewrite (filter_join_matched_rows_guard_left
    A B C join accept guard_left guard_output left right Hmatched).
  rewrite (filter_join_unmatched_left_rows_guard_left
    A B C pad_left accept guard_left guard_output left right Hleft).
  rewrite (filter_join_unmatched_right_rows_false
    A B C pad_right accept guard_output left right Hright).
  now rewrite app_nil_r.
Qed.

(** A total null-rejecting consumer removes precisely the NULL-padded branch
    of a LEFT outer scheduler.  Matched-row filtering remains in place; moving
    that predicate into a join condition or another input would require
    additional properness, volatility, and runtime-error proofs. *)
Theorem left_outer_null_reject_to_inner_exact :
  forall (A B C : Type) (join : A -> B -> C) (pad_left : A -> C)
      (accept : A -> B -> bool) (guard_output : C -> bool) left right,
    (forall left_row, guard_output (pad_left left_row) = false) ->
    filter guard_output
      (left_outer_scheduler_rows join pad_left accept left right) =
    filter guard_output (join_matched_rows join accept left right).
Proof.
  intros A B C join pad_left accept guard_output left right Hpad.
  unfold left_outer_scheduler_rows.
  rewrite ListFacts.filter_app.
  assert (Hempty :
    filter guard_output
      (join_unmatched_left_rows pad_left accept left right) = []).
  { unfold join_unmatched_left_rows.
    rewrite ListFacts.filter_map.
    assert (Hfiltered :
      filter (fun left_row => guard_output (pad_left left_row))
        (filter
          (fun left_row => negb (existsb (accept left_row) right)) left) =
      []).
    { apply ListFacts.filter_false.
      intros left_row Hleft; apply Hpad. }
    now rewrite Hfiltered. }
  now rewrite Hempty, app_nil_r.
Qed.
