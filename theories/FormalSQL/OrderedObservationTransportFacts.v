(******************************************************************************)
(** Tie-aware prefix observations and total-map ORDER/FETCH transport.       **)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Sorting.Permutation.
From SQLFS Require Import
  OrderedSet FlatData SqlOutcome SqlErrorSemantics SqlOrder
  SqlBagAbstraction SqlListFacts SqlQuerySemantics SqlQueryFacts.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts OrderedQueryFacts.

Import Tuple.
Import ListNotations.

(** Exact ordered observation equality uses FormalSQL semantic tuple equality
    pointwise.  It retains order and duplicate occurrences. *)
Definition tuple_list_semantic_rel (T : Tuple.Rcd)
    (left right : list (tuple T)) : Prop :=
  Forall2
    (fun first second =>
      Oeset.compare (OTuple T) first second = Eq)
    left right.

Lemma tuple_list_semantic_rel_refl :
  forall (T : Tuple.Rcd) (rows : list (tuple T)),
    tuple_list_semantic_rel T rows rows.
Proof.
intros T rows; induction rows as [|row rows IH].
- constructor.
- constructor; [apply Oeset.compare_eq_refl|exact IH].
Qed.

Lemma tuple_list_semantic_rel_sym :
  forall (T : Tuple.Rcd) (left right : list (tuple T)),
    tuple_list_semantic_rel T left right ->
    tuple_list_semantic_rel T right left.
Proof.
intros T left right Hrows.
induction Hrows as [|left_row right_row left right Hrow Hrows IH].
- constructor.
- constructor; [now apply Oeset.compare_eq_sym|exact IH].
Qed.

Lemma tuple_list_semantic_rel_trans :
  forall (T : Tuple.Rcd) (first second third : list (tuple T)),
    tuple_list_semantic_rel T first second ->
    tuple_list_semantic_rel T second third ->
    tuple_list_semantic_rel T first third.
Proof.
intros T first second third Hfirst.
revert third.
induction Hfirst as
  [|first_row second_row first second Hrow Hrows IH];
  intros third Hsecond.
- inversion Hsecond; constructor.
- inversion Hsecond as
    [|middle_row third_row middle third_rows Hnext Htail]; subst.
  constructor.
  + eapply Oeset.compare_eq_trans; eassumption.
  + now apply IH.
Qed.

Lemma tuple_list_semantic_rel_app :
  forall (T : Tuple.Rcd) left left' right right',
    tuple_list_semantic_rel T left left' ->
    tuple_list_semantic_rel T right right' ->
    tuple_list_semantic_rel T (left ++ right) (left' ++ right').
Proof.
intros T left left' right right' Hleft Hright.
unfold tuple_list_semantic_rel in *.
now apply Forall2_app.
Qed.

Definition optional_observation_rows {T : Tuple.Rcd}
    (observed : option (tuple T)) : list (tuple T) :=
  match observed with
  | None => []
  | Some row => [row]
  end.

(** [observe row prefix] packages only a successful cumulative observation
    after any downstream total filter/projection.  [None] means the row is
    hidden.  SQL evaluation errors are deliberately kept outside this total
    function and reintroduced by [prefix_scan_outcome_observation] below. *)
Fixpoint prefix_scan_observation
    {T : Tuple.Rcd} {A : Type}
    (observe : A -> list A -> option (tuple T))
    (prefix rows : list A) : list (tuple T) :=
  match rows with
  | [] => []
  | row :: rest =>
      let current_prefix := prefix ++ [row] in
      optional_observation_rows (observe row current_prefix) ++
      prefix_scan_observation observe current_prefix rest
  end.

Lemma prefix_scan_observation_app :
  forall (T : Tuple.Rcd) (A : Type)
      (observe : A -> list A -> option (tuple T)) prefix left right,
    prefix_scan_observation observe prefix (left ++ right) =
    prefix_scan_observation observe prefix left ++
      prefix_scan_observation observe (prefix ++ left) right.
Proof.
intros T A observe prefix left.
revert prefix.
induction left as [|row left IH]; intros prefix right.
- cbn [prefix_scan_observation]. now rewrite app_nil_r.
- cbn [app prefix_scan_observation].
  rewrite (IH (prefix ++ [row]) right), app_assoc.
  replace ((prefix ++ [row]) ++ left) with (prefix ++ row :: left).
  + reflexivity.
  + now rewrite <- app_assoc.
Qed.

(** Pointwise semantic agreement for the suffix after a peer swap.  This is
    intentionally observation-level: a cumulative aggregate may have
    different hidden intermediate values, provided the exact downstream
    observation agrees. *)
Fixpoint prefix_scan_tail_semantic_rel
    {T : Tuple.Rcd} {A : Type}
    (observe : A -> list A -> option (tuple T))
    (left_prefix right_prefix rows : list A) : Prop :=
  match rows with
  | [] => True
  | row :: rest =>
      tuple_list_semantic_rel T
        (optional_observation_rows
          (observe row (left_prefix ++ [row])))
        (optional_observation_rows
          (observe row (right_prefix ++ [row]))) /\
      prefix_scan_tail_semantic_rel observe
        (left_prefix ++ [row]) (right_prefix ++ [row]) rest
  end.

Theorem prefix_scan_observation_tail_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (observe : A -> list A -> option (tuple T))
      left_prefix right_prefix rows,
    prefix_scan_tail_semantic_rel observe
      left_prefix right_prefix rows ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe left_prefix rows)
      (prefix_scan_observation observe right_prefix rows).
Proof.
intros T A observe left_prefix right_prefix rows.
revert left_prefix right_prefix.
induction rows as [|row rows IH]; intros left_prefix right_prefix Hrows.
- constructor.
- cbn [prefix_scan_tail_semantic_rel] in Hrows.
  destruct Hrows as [Hhead Htail].
  cbn [prefix_scan_observation].
  apply tuple_list_semantic_rel_app; [exact Hhead|].
  now apply IH.
Qed.

Definition prefix_scan_pair_observation
    {T : Tuple.Rcd} {A : Type}
    (observe : A -> list A -> option (tuple T))
    (prefix : list A) (first second : A) : list (tuple T) :=
  optional_observation_rows (observe first (prefix ++ [first])) ++
  optional_observation_rows
    (observe second ((prefix ++ [first]) ++ [second])).

(** A peer swap is admissible only when the two affected observed positions
    agree semantically and every later observed row agrees after the swapped
    prefixes.  This is the fail-closed boundary that prevents a raw
    ROWS-window peer swap from being declared sound. *)
Definition prefix_scan_adjacent_peer_contract
    {T : Tuple.Rcd} {A : Type}
    (peer : A -> A -> Prop)
    (observe : A -> list A -> option (tuple T)) : Prop :=
  forall prefix first second tail,
    peer first second ->
    tuple_list_semantic_rel T
      (prefix_scan_pair_observation observe prefix first second)
      (prefix_scan_pair_observation observe prefix second first) /\
    prefix_scan_tail_semantic_rel observe
      ((prefix ++ [first]) ++ [second])
      ((prefix ++ [second]) ++ [first]) tail.

Theorem prefix_scan_observation_adjacent_peer :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      prefix first second tail,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer first second ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe prefix (first :: second :: tail))
      (prefix_scan_observation observe prefix (second :: first :: tail)).
Proof.
intros T A peer observe prefix first second tail Hcontract Hpeer.
destruct (Hcontract prefix first second tail Hpeer) as [Hpair Htail].
cbn [prefix_scan_observation].
unfold prefix_scan_pair_observation in Hpair.
rewrite !app_assoc.
apply tuple_list_semantic_rel_app; [exact Hpair|].
now apply prefix_scan_observation_tail_transport.
Qed.

(** Equivalence closure of adjacent swaps that a caller has proved are SQL
    peers.  The relation preserves length and occurrences by construction,
    but does not claim that arbitrary permutations are legal peer orders. *)
Inductive peer_order_permutation {A : Type} (peer : A -> A -> Prop) :
    list A -> list A -> Prop :=
| PeerOrderRefl : forall rows,
    peer_order_permutation peer rows rows
| PeerOrderAdjacent : forall before first second after,
    peer first second ->
    peer_order_permutation peer
      (before ++ first :: second :: after)
      (before ++ second :: first :: after)
| PeerOrderSym : forall left right,
    peer_order_permutation peer left right ->
    peer_order_permutation peer right left
| PeerOrderTrans : forall first second third,
    peer_order_permutation peer first second ->
    peer_order_permutation peer second third ->
    peer_order_permutation peer first third.

Theorem prefix_scan_observation_adjacent_peer_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      prefix before first second after,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer first second ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe prefix
        (before ++ first :: second :: after))
      (prefix_scan_observation observe prefix
        (before ++ second :: first :: after)).
Proof.
intros T A peer observe prefix before first second after Hcontract Hpeer.
rewrite !prefix_scan_observation_app.
apply tuple_list_semantic_rel_app.
- apply tuple_list_semantic_rel_refl.
- eapply (prefix_scan_observation_adjacent_peer (peer := peer));
    eassumption.
Qed.

(** Every legal peer order generated by the caller's [peer] relation has the
    same post-filter semantic observation.  This does not assert equality of
    hidden window rows or their bags. *)
Theorem prefix_scan_observation_peer_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      prefix left right,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer_order_permutation peer left right ->
    tuple_list_semantic_rel T
      (prefix_scan_observation observe prefix left)
      (prefix_scan_observation observe prefix right).
Proof.
intros T A peer observe prefix left right Hcontract Hpermutation.
induction Hpermutation as
  [rows
  |before first second after Hpeer
  |left right Hpermutation IH
  |first second third Hfirst IHfirst Hsecond IHsecond].
- apply tuple_list_semantic_rel_refl.
- eapply (prefix_scan_observation_adjacent_peer_transport (peer := peer));
    eassumption.
- now apply tuple_list_semantic_rel_sym.
- eapply tuple_list_semantic_rel_trans; eassumption.
Qed.

(** Partitioned cumulative windows reset the prefix at every block.  The
    supplied block relation must align partitions in their observable order;
    it may vary only the peer order inside each paired block. *)
Fixpoint partitioned_prefix_scan_observation
    {T : Tuple.Rcd} {A : Type}
    (observe : A -> list A -> option (tuple T))
    (blocks : list (list A)) : list (tuple T) :=
  match blocks with
  | [] => []
  | block :: rest =>
      prefix_scan_observation observe [] block ++
      partitioned_prefix_scan_observation observe rest
  end.

Theorem partitioned_prefix_scan_observation_peer_transport :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      left_blocks right_blocks,
    prefix_scan_adjacent_peer_contract peer observe ->
    Forall2 (peer_order_permutation peer) left_blocks right_blocks ->
    tuple_list_semantic_rel T
      (partitioned_prefix_scan_observation observe left_blocks)
      (partitioned_prefix_scan_observation observe right_blocks).
Proof.
intros T A peer observe left_blocks right_blocks Hcontract Hblocks.
induction Hblocks as
  [|left_block right_block left_blocks right_blocks Hblock Hblocks IH].
- constructor.
- cbn [partitioned_prefix_scan_observation].
  apply tuple_list_semantic_rel_app; [|exact IH].
  exact
    (@prefix_scan_observation_peer_transport
      T A peer observe [] left_block right_block Hcontract Hblock).
Qed.

Definition prefix_scan_outcome_observation
    {T : Tuple.Rcd} {A : Type}
    (observe : A -> list A -> option (tuple T))
    (errors : sql_runtime_error -> Prop)
    (rows : list A) (outcome : sql_outcome (list (tuple T))) : Prop :=
  match outcome with
  | SqlSuccess output =>
      tuple_list_semantic_rel T output
        (prefix_scan_observation observe [] rows)
  | SqlError error => errors error
  end.

(** Exact outcome lifting remains explicit about errors.  The peer law proves
    the successful observation relation; callers must separately prove that
    the two SQL evaluation schedules expose the same error categories. *)
Theorem prefix_scan_outcome_peer_transport_iff :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      (left_errors right_errors : sql_runtime_error -> Prop)
      left right,
    prefix_scan_adjacent_peer_contract peer observe ->
    peer_order_permutation peer left right ->
    (forall error, left_errors error <-> right_errors error) ->
    forall outcome,
      prefix_scan_outcome_observation observe left_errors left outcome <->
      prefix_scan_outcome_observation observe right_errors right outcome.
Proof.
intros T A peer observe left_errors right_errors left right
  Hcontract Hpermutation Herrors [output|error]; cbn.
- pose proof
    (@prefix_scan_observation_peer_transport
      T A peer observe [] left right Hcontract Hpermutation) as Hrows.
  split; intro Houtput.
  + eapply tuple_list_semantic_rel_trans; eassumption.
  + eapply tuple_list_semantic_rel_trans; [exact Houtput|].
    now apply tuple_list_semantic_rel_sym.
- apply Herrors.
Qed.

Definition partitioned_prefix_scan_outcome_observation
    {T : Tuple.Rcd} {A : Type}
    (observe : A -> list A -> option (tuple T))
    (errors : sql_runtime_error -> Prop)
    (blocks : list (list A))
    (outcome : sql_outcome (list (tuple T))) : Prop :=
  match outcome with
  | SqlSuccess output =>
      tuple_list_semantic_rel T output
        (partitioned_prefix_scan_observation observe blocks)
  | SqlError error => errors error
  end.

Theorem partitioned_prefix_scan_outcome_peer_transport_iff :
  forall (T : Tuple.Rcd) (A : Type)
      (peer : A -> A -> Prop)
      (observe : A -> list A -> option (tuple T))
      (left_errors right_errors : sql_runtime_error -> Prop)
      left_blocks right_blocks,
    prefix_scan_adjacent_peer_contract peer observe ->
    Forall2 (peer_order_permutation peer) left_blocks right_blocks ->
    (forall error, left_errors error <-> right_errors error) ->
    forall outcome,
      partitioned_prefix_scan_outcome_observation
        observe left_errors left_blocks outcome <->
      partitioned_prefix_scan_outcome_observation
        observe right_errors right_blocks outcome.
Proof.
intros T A peer observe left_errors right_errors left_blocks right_blocks
  Hcontract Hblocks Herrors [output|error]; cbn.
- pose proof
    (partitioned_prefix_scan_observation_peer_transport
      Hcontract Hblocks) as Hrows.
  split; intro Houtput.
  + eapply tuple_list_semantic_rel_trans; eassumption.
  + eapply tuple_list_semantic_rel_trans; [exact Houtput|].
    now apply tuple_list_semantic_rel_sym.
- apply Herrors.
Qed.

(******************************************************************************)
(** Total semantic maps through every legal ORDER BY and FETCH observation. **)
(******************************************************************************)

Definition semantic_row_map_proper (T : Tuple.Rcd)
    (mapping : tuple T -> tuple T) : Prop :=
  forall first second,
    Oeset.compare (OTuple T) first second = Eq ->
    Oeset.compare (OTuple T) (mapping first) (mapping second) = Eq.

(** The key premise is representation-aware in the reverse direction: an
    ordered mapped-bag representative may contain tuples merely equivalent to
    [mapping row], not the same Rocq term. *)
Definition order_key_map_exact
    {T : Tuple.Rcd}
    (value_is_null : value T -> bool)
    (mapping : tuple T -> tuple T)
    (left_keys right_keys : list (sort_key T)) : Prop :=
  semantic_row_map_proper T mapping /\
  forall first second mapped_first mapped_second,
    Oeset.compare (OTuple T) mapped_first (mapping first) = Eq ->
    Oeset.compare (OTuple T) mapped_second (mapping second) = Eq ->
    compare_order_keys value_is_null right_keys mapped_first mapped_second =
    compare_order_keys value_is_null left_keys first second.

Theorem ordered_rows_total_map :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (rows : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    ordered_rows value_is_null left_keys rows ->
    ordered_rows value_is_null right_keys (map mapping rows).
Proof.
intros T value_is_null mapping left_keys right_keys rows Hcontract.
destruct Hcontract as [_ Hkeys].
induction rows as [|first rows IH]; intro Hordered.
- exact I.
- destruct rows as [|second rest].
  + exact I.
  + cbn [map ordered_rows] in Hordered |- *.
    destruct Hordered as [Hpair Htail].
    split.
    * unfold ordered_pair in *.
      rewrite (Hkeys first second (mapping first) (mapping second));
        [exact Hpair|apply Oeset.compare_eq_refl|apply Oeset.compare_eq_refl].
    * now apply IH.
Qed.

Lemma ordered_rows_total_map_reflect :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (input output : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    tuple_list_semantic_rel T output (map mapping input) ->
    ordered_rows value_is_null right_keys output ->
    ordered_rows value_is_null left_keys input.
Proof.
intros T value_is_null mapping left_keys right_keys input.
induction input as [|first input IH];
  intros output Hcontract Hrows Hordered.
- inversion Hrows; exact I.
- inversion Hrows as
    [|mapped_first expected_first mapped_tail expected_tail
      Hfirst Htail]; subst.
  destruct input as [|second rest].
  + exact I.
  + inversion Htail as
      [|mapped_second expected_second mapped_rest expected_rest
        Hsecond Hrest]; subst.
    cbn [map ordered_rows] in Hordered |- *.
    destruct Hordered as [Hpair Hordered_tail].
    destruct Hcontract as [Hproper Hkeys].
    split.
    * unfold ordered_pair in *.
      rewrite <- (Hkeys first second mapped_first mapped_second
        Hfirst Hsecond).
      exact Hpair.
    * eapply IH; [split; eassumption|exact Htail|exact Hordered_tail].
Qed.

(** A total semantic map sends each legal source ordering to a legal mapped
    ordering, with exact occurrence multiplicity in the mapped bag. *)
Theorem order_by_rows_total_map :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (input ordered : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    order_by_rows value_is_null left_keys input ordered ->
    order_by_rows value_is_null right_keys
      (map mapping input) (map mapping ordered).
Proof.
intros T value_is_null mapping left_keys right_keys input ordered
  Hcontract [Hbag Hordered].
destruct Hcontract as [Hproper Hkeys].
split.
- assert (Hself :
    query_same_rows_as_bag input (@query_rows_bag T input)).
  { apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl. }
  pose proof
    (@RelationalAlgebraFacts.query_same_rows_as_bag_map
      T mapping ordered (@query_rows_bag T input) Hproper Hbag)
    as Hmapped_ordered.
  pose proof
    (@RelationalAlgebraFacts.query_same_rows_as_bag_map
      T mapping input (@query_rows_bag T input) Hproper Hself)
    as Hmapped_input.
  apply query_same_rows_as_bag_iff_bag_eq in Hmapped_ordered, Hmapped_input.
  apply query_same_rows_as_bag_iff_bag_eq.
  eapply bag_eq_trans; [exact Hmapped_ordered|].
  now apply bag_eq_sym.
- eapply ordered_rows_total_map with
    (mapping := mapping) (left_keys := left_keys) (right_keys := right_keys).
  + now split.
  + exact Hordered.
Qed.

(** Conversely, every legal ordered representative of the mapped bag has a
    source ordering preimage.  Non-injective maps are supported: occurrences,
    rather than distinct values, are pulled back. *)
Theorem order_by_rows_total_map_preimage :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (input output : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    order_by_rows value_is_null right_keys (map mapping input) output ->
    exists ordered,
      order_by_rows value_is_null left_keys input ordered /\
      ordered_rows_equiv T output (map mapping ordered).
Proof.
intros T value_is_null mapping left_keys right_keys input output
  Hcontract [Hbag Hordered].
assert (Hself :
  query_same_rows_as_bag (map mapping input)
    (@query_rows_bag T (map mapping input))).
{ apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl. }
pose proof
  (@query_same_rows_as_bag_permut_between T
    output (map mapping input)
    (@query_rows_bag T (map mapping input)) Hbag Hself) as Hpermutation.
destruct
  (@relational_permutation_map_inv
    (tuple T) (tuple T)
    (fun first second =>
      Oeset.compare (OTuple T) first second = Eq)
    mapping output input Hpermutation)
  as [ordered [Hinput Hrows]].
exists ordered; split.
- split.
  + now apply permutation_same_rows_as_bag.
  + eapply ordered_rows_total_map_reflect; eassumption.
- now apply ordered_rows_equiv_of_Forall2.
Qed.

Lemma map_firstn_exact :
  forall (A B : Type) (mapping : A -> B) count rows,
    map mapping (firstn count rows) = firstn count (map mapping rows).
Proof.
intros A B mapping count.
induction count as [|count IH]; intros [|row rows];
  cbn; [reflexivity|reflexivity|reflexivity|].
now rewrite IH.
Qed.

Definition map_after_order_fetch_observation
    {T : Tuple.Rcd}
    (value_is_null : value T -> bool)
    (mapping : tuple T -> tuple T)
    (keys : list (sort_key T)) count input output : Prop :=
  exists ordered,
    order_by_rows value_is_null keys input ordered /\
    ordered_rows_equiv T output
      (map mapping (firstn count ordered)).

Definition order_fetch_after_map_observation
    {T : Tuple.Rcd}
    (value_is_null : value T -> bool)
    (mapping : tuple T -> tuple T)
    (keys : list (sort_key T)) count input output : Prop :=
  exists ordered,
    order_by_rows value_is_null keys (map mapping input) ordered /\
    ordered_rows_equiv T output (firstn count ordered).

(** Every legal ORDER BY/FETCH observation commutes with a total map whose
    key comparison is preserved and reflected.  The theorem relates complete
    observation sets in both directions; it never turns bag equality into one
    chosen exact order. *)
Theorem total_map_order_fetch_observation_iff :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (count : nat) (input output : list (tuple T)),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    map_after_order_fetch_observation
      value_is_null mapping left_keys count input output <->
    order_fetch_after_map_observation
      value_is_null mapping right_keys count input output.
Proof.
intros T value_is_null mapping left_keys right_keys count input output
  Hcontract; split.
- intros [ordered [Hordered Houtput]].
  exists (map mapping ordered); split.
  + now apply order_by_rows_total_map with (left_keys := left_keys).
  + rewrite <- map_firstn_exact.
    exact Houtput.
- intros [mapped_ordered [Hordered Houtput]].
  destruct
    (@order_by_rows_total_map_preimage
      T value_is_null mapping left_keys right_keys input mapped_ordered
      Hcontract Hordered)
    as [ordered [Hleft Hrows]].
  exists ordered; split; [exact Hleft|].
  eapply ordered_rows_equiv_trans; [exact Houtput|].
  pose proof (ordered_rows_equiv_firstn count Hrows) as Hprefix.
  rewrite <- map_firstn_exact in Hprefix.
  exact Hprefix.
Qed.

Definition map_after_order_fetch_outcome_observation
    {T : Tuple.Rcd}
    (value_is_null : value T -> bool)
    (mapping : tuple T -> tuple T)
    (keys : list (sort_key T)) count input
    (errors : sql_runtime_error -> Prop)
    (outcome : sql_outcome (list (tuple T))) : Prop :=
  match outcome with
  | SqlSuccess output =>
      map_after_order_fetch_observation
        value_is_null mapping keys count input output
  | SqlError error => errors error
  end.

Definition order_fetch_after_map_outcome_observation
    {T : Tuple.Rcd}
    (value_is_null : value T -> bool)
    (mapping : tuple T -> tuple T)
    (keys : list (sort_key T)) count input
    (errors : sql_runtime_error -> Prop)
    (outcome : sql_outcome (list (tuple T))) : Prop :=
  match outcome with
  | SqlSuccess output =>
      order_fetch_after_map_observation
        value_is_null mapping keys count input output
  | SqlError error => errors error
  end.

(** Outcome transport is fail-closed on SQL errors.  Total mapping and key
    preservation settle all successful legal observations, while callers
    still must prove exact error-category equivalence for the concrete child,
    join, projection, and ordering schedules. *)
Theorem total_map_order_fetch_outcome_observation_iff :
  forall (T : Tuple.Rcd) (value_is_null : value T -> bool)
      (mapping : tuple T -> tuple T)
      (left_keys right_keys : list (sort_key T))
      (count : nat) (input : list (tuple T))
      (left_errors right_errors : sql_runtime_error -> Prop),
    order_key_map_exact value_is_null mapping left_keys right_keys ->
    (forall error, left_errors error <-> right_errors error) ->
    forall outcome,
      map_after_order_fetch_outcome_observation
        value_is_null mapping left_keys count input left_errors outcome <->
      order_fetch_after_map_outcome_observation
        value_is_null mapping right_keys count input right_errors outcome.
Proof.
intros T value_is_null mapping left_keys right_keys count input
  left_errors right_errors Hcontract Herrors [output|error]; cbn.
- now apply total_map_order_fetch_observation_iff.
- apply Herrors.
Qed.
