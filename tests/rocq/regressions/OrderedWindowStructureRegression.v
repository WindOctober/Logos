From Stdlib Require Import List Lia PeanoNat.
From Logos.FormalSQL Require Import OrderedQueryFacts.

Import ListNotations.

Example numbered_duplicate_prefix_is_exact :
  map snd
    (filter (fun numbered => Nat.leb (fst numbered) 3%nat)
      (position_rows_from 1%nat [4%nat; 4%nat; 7%nat; 9%nat])) =
  [4%nat; 4%nat; 7%nat].
Proof.
rewrite position_rows_from_filter_le_prefix.
reflexivity.
Qed.

Example duplicate_occurrence_has_its_own_position :
  nth_error (position_rows_from 5%nat [4%nat; 4%nat; 9%nat]) 1%nat =
  Some (6%nat, 4%nat).
Proof.
rewrite position_rows_from_nth_error.
reflexivity.
Qed.

Example equal_key_partition_runs_are_exact :
  concat
    (partition_runs_by_compare Nat.compare
      [1%nat; 1%nat; 2%nat; 2%nat; 3%nat]) =
    [1%nat; 1%nat; 2%nat; 2%nat; 3%nat] /\
  compare_partition_blocks_well_formed Nat.compare
    (partition_runs_by_compare Nat.compare
      [1%nat; 1%nat; 2%nat; 2%nat; 3%nat]).
Proof.
apply partition_runs_by_compare_exact_well_formed.
Qed.

Definition peer_left : list (nat * nat) :=
  [(1%nat, 10%nat); (1%nat, 20%nat); (2%nat, 30%nat)].

Definition peer_right : list (nat * nat) :=
  [(1%nat, 20%nat); (1%nat, 10%nat); (2%nat, 30%nat)].

Example peer_payload_order_is_hidden_at_the_key_view :
  rows_key_aligned eq fst fst peer_left peer_right.
Proof.
unfold rows_key_aligned, peer_left, peer_right.
repeat constructor.
Qed.

Example fetch_prefix_preserves_peer_key_alignment :
  rows_key_aligned eq fst fst
    (firstn 2%nat peer_left) (firstn 2%nat peer_right).
Proof.
apply rows_key_aligned_firstn.
exact peer_payload_order_is_hidden_at_the_key_view.
Qed.

Example offset_suffix_preserves_peer_key_alignment :
  rows_key_aligned eq fst fst
    (skipn 1%nat peer_left) (skipn 1%nat peer_right).
Proof.
apply rows_key_aligned_skipn.
exact peer_payload_order_is_hidden_at_the_key_view.
Qed.

Example key_only_filter_preserves_peer_key_alignment :
  rows_key_aligned eq fst fst
    (filter (fun row => Nat.leb (fst row) 1%nat) peer_left)
    (filter (fun row => Nat.leb (fst row) 1%nat) peer_right).
Proof.
eapply (@rows_key_aligned_filter
  (nat * nat) (nat * nat) nat nat eq fst fst
  (fun key => Nat.leb key 1%nat) (fun key => Nat.leb key 1%nat)).
- intros left_key right_key Hkey. now subst right_key.
- exact peer_payload_order_is_hidden_at_the_key_view.
Qed.

Definition increment_payload (row : nat * nat) : nat * nat :=
  (fst row, S (snd row)).

Definition double_payload (row : nat * nat) : nat * nat :=
  (fst row, 2%nat * snd row).

Example total_key_preserving_maps_transport_peer_alignment :
  rows_key_aligned eq fst fst
    (map increment_payload peer_left)
    (map double_payload peer_right).
Proof.
eapply (@rows_key_aligned_total_map_transport
  (nat * nat) (nat * nat) (nat * nat) (nat * nat)
  nat nat nat nat eq eq fst fst fst fst
  increment_payload double_payload).
- intros left_row right_row Hkey. exact Hkey.
- exact peer_payload_order_is_hidden_at_the_key_view.
Qed.
