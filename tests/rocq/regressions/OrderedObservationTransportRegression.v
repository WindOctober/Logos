(******************************************************************************)
(** Generic tie-aware and total-map ordered-observation interface checks.    **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  OrderedSet FlatData SqlOutcome SqlErrorSemantics SqlOrder
  SqlBagAbstraction SqlQuerySemantics.
From Logos.FormalSQL Require Import OrderedObservationTransportFacts.

Import Tuple.
Import ListNotations.

Example adjacent_peer_order_permutation_regression :
  forall (A : Type) (peer : A -> A -> Prop)
      before first second after,
    peer first second ->
    peer_order_permutation peer
      (before ++ first :: second :: after)
      (before ++ second :: first :: after).
Proof.
intros; now apply PeerOrderAdjacent.
Qed.

Section SemanticOrderedInterfaces.

Context {T : Tuple.Rcd} {A : Type}.

Variable observe : A -> list A -> option (tuple T).
Variable peer : A -> A -> Prop.

(** The regression keeps the downstream observation and exact error relation
    explicit.  It cannot be discharged from peer permutation alone. *)
Example peer_prefix_outcome_transport_regression :
  forall left right left_errors right_errors outcome,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer_order_permutation peer left right ->
    (forall error, left_errors error <-> right_errors error) ->
    prefix_scan_outcome_observation observe left_errors left outcome <->
    prefix_scan_outcome_observation observe right_errors right outcome.
Proof.
intros.
eapply prefix_scan_outcome_peer_transport_iff; eassumption.
Qed.

Example partitioned_peer_prefix_transport_regression :
  forall left_blocks right_blocks,
    prefix_scan_adjacent_peer_contract peer observe ->
    Forall2 (peer_order_permutation peer) left_blocks right_blocks ->
    tuple_list_semantic_rel T
      (partitioned_prefix_scan_observation observe left_blocks)
      (partitioned_prefix_scan_observation observe right_blocks).
Proof.
intros.
eapply partitioned_prefix_scan_observation_peer_transport; eassumption.
Qed.

Variable value_is_null : value T -> bool.
Variable mapping : tuple T -> tuple T.

(** Every legal tied ORDER BY representative participates in the equivalence;
    no deterministic representative or bag-to-list coercion is selected. *)
Example total_map_order_fetch_transport_regression :
  forall left_keys right_keys count input output,
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    map_after_order_fetch_observation
      value_is_null mapping left_keys count input output <->
    order_fetch_after_map_observation
      value_is_null mapping right_keys count input output.
Proof.
intros; now apply total_map_order_fetch_observation_iff.
Qed.

(** Exact error-category equality remains a separate premise at the outcome
    boundary, including for otherwise total row maps. *)
Example total_map_order_fetch_outcome_transport_regression :
  forall left_keys right_keys count input left_errors right_errors outcome,
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    (forall error, left_errors error <-> right_errors error) ->
    map_after_order_fetch_outcome_observation
      value_is_null mapping left_keys count input left_errors outcome <->
    order_fetch_after_map_outcome_observation
      value_is_null mapping right_keys count input right_errors outcome.
Proof.
intros.
eapply total_map_order_fetch_outcome_observation_iff; eassumption.
Qed.

End SemanticOrderedInterfaces.
