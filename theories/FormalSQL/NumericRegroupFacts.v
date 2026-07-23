(************************************************************************************)
(** Exact NUMERIC regrouping and duplicate-free UNION facts for SQL rewrites.      **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Lia List NArith QArith Qcanon Sorting.Permutation
  ZArith.
From SQLFS Require Import FiniteBag FiniteCollection FiniteSet FTuples
  OrderedSet SqlBagAbstraction SqlQuerySemantics Values ValueNumeric.
From Logos.FormalSQL Require Import NumericDerivedFacts NumericFacts
  RelationalAlgebraFacts.

Import ListNotations.
Import NullValues.
Import Tuple.

(** [numeric_add] is the exact binary operation induced by PostgreSQL's
    [sum(numeric)] finalizer, including NaN and both infinities. *)
Lemma numeric_add_associative : forall first second third,
  numeric_add (numeric_add first second) third =
  numeric_add first (numeric_add second third).
Proof.
intros [|first| |] [|second| |] [|third| |];
  cbn [numeric_add]; try reflexivity.
- f_equal; symmetry; apply Qcplus_assoc.
Qed.

Definition numeric_sum_state_reachable_invariant
    (state : numeric_sum_state) : Prop :=
  0 <= numeric_sum_finite_count state /\
  0 <= numeric_sum_nan_count state /\
  0 <= numeric_sum_pos_inf_count state /\
  0 <= numeric_sum_neg_inf_count state /\
  (numeric_sum_total_count state = 0 ->
   numeric_sum_finite_accumulator state = Q2Qc (inject_Z 0)).

Lemma numeric_sum_initial_reachable_invariant :
  numeric_sum_state_reachable_invariant numeric_sum_initial.
Proof.
unfold numeric_sum_state_reachable_invariant, numeric_sum_initial,
  numeric_sum_total_count, numeric_agg_total_count; cbn.
repeat split; try lia; reflexivity.
Qed.

Lemma numeric_sum_transition_preserves_reachable_invariant :
  forall state next,
    numeric_sum_state_reachable_invariant state ->
    numeric_sum_state_reachable_invariant
      (numeric_sum_transition state next).
Proof.
intros [finite_count nan_count pos_inf_count neg_inf_count accumulator]
  [|finite| |] Hvalid;
  cbv [numeric_sum_state_reachable_invariant numeric_sum_transition
    numeric_sum_total_count numeric_agg_total_count
    numeric_sum_finite_count numeric_sum_nan_count
    numeric_sum_pos_inf_count numeric_sum_neg_inf_count
    numeric_sum_finite_accumulator] in *;
  destruct Hvalid as
    [Hfinite [Hnan [Hpos [Hneg Hzero]]]];
  repeat split; try lia.
all: intros Hcount; exfalso; lia.
Qed.

Definition numeric_sum_option_add
    (current : option numeric) (next : numeric) : option numeric :=
  match current with
  | None => Some next
  | Some total => Some (numeric_add total next)
  end.

Lemma numeric_sum_from_state_transition : forall state next,
  numeric_sum_state_reachable_invariant state ->
  numeric_sum_from_state (numeric_sum_transition state next) =
  numeric_sum_option_add (numeric_sum_from_state state) next.
Proof.
intros [finite_count nan_count pos_inf_count neg_inf_count accumulator]
  [|finite| |] Hvalid;
  cbv [numeric_sum_state_reachable_invariant
    numeric_sum_option_add numeric_sum_transition numeric_sum_from_state
    numeric_sum_total_count numeric_agg_total_count
    numeric_agg_special_result numeric_add
    numeric_sum_finite_count numeric_sum_nan_count
    numeric_sum_pos_inf_count numeric_sum_neg_inf_count
    numeric_sum_finite_accumulator] in *;
  destruct Hvalid as
    [Hfinite [Hnan [Hpos [Hneg Hzero]]]].
all: repeat match goal with
  | |- context [Z.eqb ?left ?right] =>
      destruct (Z.eqb left right) eqn:?; cbn
  | |- context [Z.ltb ?left ?right] =>
      destruct (Z.ltb left right) eqn:?; cbn
  end.
all: repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end.
all: repeat match goal with
  | Hzero : ?total = 0 -> _, Htotal : ?total = 0 |- _ =>
      specialize (Hzero Htotal)
  end.
all: try reflexivity; try lia; try (f_equal; ring).
all: assert (accumulator = Q2Qc (inject_Z 0)) as Haccumulator.
{ apply Hzero; lia. }
all: rewrite Haccumulator; f_equal; f_equal; cbn [inject_Z];
  apply Qcplus_0_l.
Qed.

Lemma numeric_sum_fold_option_add : forall numbers state,
  numeric_sum_state_reachable_invariant state ->
  numeric_sum_from_state
    (fold_left numeric_sum_transition numbers state) =
  fold_left numeric_sum_option_add numbers
    (numeric_sum_from_state state).
Proof.
induction numbers as [|number numbers IH]; intros state Hvalid; cbn.
- reflexivity.
- rewrite IH.
  + now rewrite numeric_sum_from_state_transition.
  + now apply numeric_sum_transition_preserves_reachable_invariant.
Qed.

Corollary numeric_sum_fold_from_initial : forall numbers,
  numeric_sum_from_state
    (fold_left numeric_sum_transition numbers numeric_sum_initial) =
  fold_left numeric_sum_option_add numbers None.
Proof.
intro numbers.
rewrite numeric_sum_fold_option_add.
- reflexivity.
- apply numeric_sum_initial_reachable_invariant.
Qed.

Lemma interp_sum_numeric_option_fold : forall observations,
  forallb is_numeric_value observations = true ->
  interp_sum_numeric observations =
  Value_numeric
    (fold_left numeric_sum_option_add (numeric_values observations) None).
Proof.
intros observations Hnumeric.
unfold interp_sum_numeric; rewrite Hnumeric, numeric_sum_fold_from_initial.
reflexivity.
Qed.

(** A finite NUMERIC observation is an exact canonical rational.  These
    helpers make the common DECIMAL rollup proof independent of generated
    attributes and select-list names. *)
Definition finite_numeric_observation (number : Qc) : NullValues.value :=
  Value_numeric (Some (NumericFinite number)).

Definition finite_numeric_total (numbers : list Qc) : Qc :=
  fold_left Qcplus numbers (Q2Qc 0).

Fixpoint nonempty_finite_group_totals
    (groups : list (list Qc)) : list Qc :=
  match groups with
  | [] => []
  | [] :: rest => nonempty_finite_group_totals rest
  | group :: rest =>
      finite_numeric_total group :: nonempty_finite_group_totals rest
  end.

Lemma numeric_values_finite_observations : forall numbers,
  numeric_values (map finite_numeric_observation numbers) =
  map NumericFinite numbers.
Proof.
induction numbers as [|number numbers IH]; cbn; now rewrite ?IH.
Qed.

Lemma finite_observations_all_numeric : forall numbers,
  forallb is_numeric_value (map finite_numeric_observation numbers) = true.
Proof.
induction numbers as [|number numbers IH]; cbn; now rewrite ?IH.
Qed.

Lemma numeric_sum_finite_fold_state :
  forall numbers finite_count nan_count pos_inf_count neg_inf_count accumulator,
    fold_left numeric_sum_transition (map NumericFinite numbers)
      (NumericSumState finite_count nan_count pos_inf_count neg_inf_count
        accumulator) =
    NumericSumState
      (finite_count + Z.of_nat (length numbers))
      nan_count pos_inf_count neg_inf_count
      (fold_left Qcplus numbers accumulator).
Proof.
induction numbers as [|number numbers IH];
  intros finite_count nan_count pos_inf_count neg_inf_count accumulator; cbn.
- f_equal; lia.
- rewrite IH; f_equal; lia.
Qed.

Lemma interp_sum_finite_observations : forall numbers,
  interp_sum_numeric (map finite_numeric_observation numbers) =
  match numbers with
  | [] => Value_numeric None
  | _ => Value_numeric (Some (NumericFinite (finite_numeric_total numbers)))
  end.
Proof.
intro numbers.
unfold interp_sum_numeric.
rewrite finite_observations_all_numeric, numeric_values_finite_observations.
unfold numeric_sum_initial.
rewrite numeric_sum_finite_fold_state.
destruct numbers as [|number numbers]; cbn [numeric_sum_initial
  numeric_sum_from_state numeric_sum_total_count numeric_agg_total_count
  numeric_agg_special_result finite_numeric_total].
- reflexivity.
- cbn [length].
  unfold numeric_sum_from_state, numeric_sum_total_count,
    numeric_agg_total_count, numeric_agg_special_result.
  cbn.
  f_equal; apply f_equal; ring.
Qed.

Lemma interp_sum_numeric_values_extensional : forall left right,
  forallb is_numeric_value left = true ->
  forallb is_numeric_value right = true ->
  numeric_values left = numeric_values right ->
  interp_sum_numeric left = interp_sum_numeric right.
Proof.
intros left right Hleft Hright Hvalues.
unfold interp_sum_numeric; now rewrite Hleft, Hright, Hvalues.
Qed.

Lemma finite_numeric_total_from_accumulator : forall numbers accumulator,
  fold_left Qcplus numbers accumulator =
  Qcplus accumulator (finite_numeric_total numbers).
Proof.
unfold finite_numeric_total.
induction numbers as [|number numbers IH]; intro accumulator.
- cbn; symmetry; apply Qcplus_0_r.
- cbn.
  rewrite (IH (Qcplus accumulator number)), (IH (Qcplus (Q2Qc 0) number)).
  ring.
Qed.

Lemma nonempty_group_totals_flatten : forall groups,
  finite_numeric_total (nonempty_finite_group_totals groups) =
  finite_numeric_total (concat groups).
Proof.
induction groups as [|group groups IH]; [reflexivity|].
destruct group as [|number numbers]; cbn [nonempty_finite_group_totals];
  [exact IH|].
unfold finite_numeric_total at 1 3.
cbn [concat].
rewrite fold_left_app.
cbn.
rewrite
  (finite_numeric_total_from_accumulator
    (nonempty_finite_group_totals groups)
    (Qcplus (Q2Qc 0)
      (fold_left Qcplus numbers (Qcplus (Q2Qc 0) number)))),
  (finite_numeric_total_from_accumulator
    (concat groups)
    (fold_left Qcplus numbers (Qcplus (Q2Qc 0) number))).
rewrite IH; ring.
Qed.

Lemma grouped_finite_sums_all_numeric : forall groups,
  forallb is_numeric_value
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) = true.
Proof.
induction groups as [|group groups IH]; cbn; [reflexivity|].
rewrite interp_sum_finite_observations.
destruct group; cbn; exact IH.
Qed.

Lemma numeric_values_grouped_finite_sums : forall groups,
  numeric_values
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) =
  map NumericFinite (nonempty_finite_group_totals groups).
Proof.
induction groups as [|group groups IH]; cbn; [reflexivity|].
rewrite interp_sum_finite_observations.
destruct group; cbn; now rewrite IH.
Qed.

Lemma nonempty_group_totals_nil_iff : forall groups,
  nonempty_finite_group_totals groups = [] <-> concat groups = [].
Proof.
induction groups as [|group groups IH]; [cbn; tauto|].
destruct group as [|number numbers].
- cbn [nonempty_finite_group_totals]; exact IH.
- cbn [nonempty_finite_group_totals]; split; discriminate.
Qed.

(** Pure mathematical-value equality: SUM over nonempty finite group totals
    equals SUM over the flattened input. Empty and all-empty partitions retain
    SQL NULL behavior: inner NULL sums are ignored, and an entirely empty
    partition still produces NULL. This theorem does not establish equivalence
    of intermediate SQL evaluation. In particular, it supplies no runtime
    overflow/range-error or typmod preservation, no grouping or ordering
    equivalence, and no license to reassociate operations whose intermediate
    representability can differ; callers must prove those obligations at the
    appropriate outcome boundary. *)
Theorem interp_sum_numeric_finite_regroup : forall groups,
  interp_sum_numeric
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) =
  interp_sum_numeric
    (map finite_numeric_observation (concat groups)).
Proof.
intro groups.
transitivity
  (interp_sum_numeric
    (map finite_numeric_observation
      (nonempty_finite_group_totals groups))).
- apply interp_sum_numeric_values_extensional.
  + apply grouped_finite_sums_all_numeric.
  + apply finite_observations_all_numeric.
  + rewrite numeric_values_grouped_finite_sums,
      numeric_values_finite_observations; reflexivity.
- rewrite !interp_sum_finite_observations.
  pose proof (nonempty_group_totals_flatten groups) as Htotals.
  destruct (concat groups) as [|number numbers] eqn:Hconcat.
  + assert (nonempty_finite_group_totals groups = []) as Hempty.
    { apply (proj2 (nonempty_group_totals_nil_iff groups)); exact Hconcat. }
    now rewrite Hempty.
  + destruct (nonempty_finite_group_totals groups) as [|total totals]
      eqn:Hgroups.
    * exfalso.
      apply (proj1 (nonempty_group_totals_nil_iff groups)) in Hgroups.
      rewrite Hgroups in Hconcat; discriminate.
    * now rewrite Htotals.
Qed.

(** Bag-side hypotheses used to prove that a SQL DISTINCT node is inert.
    They are stated using FormalSQL's semantic tuple comparison, not Rocq's
    structural equality. *)
Section DuplicateFreeUnion.

Context {T : Tuple.Rcd}.

Local Definition bagT := Febag.bag (SqlQuerySemantics.BTupleT T).

Definition query_bag_duplicate_free (bag : bagT) : Prop :=
  forall row,
    (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row bag <= 1)%N.

Definition query_bags_disjoint (left right : bagT) : Prop :=
  forall row,
    Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left = 0%N \/
    Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right = 0%N.

Lemma query_bags_disjoint_sym : forall left right,
  query_bags_disjoint left right -> query_bags_disjoint right left.
Proof.
intros left right Hdisjoint row.
destruct (Hdisjoint row) as [Hleft | Hright]; [right | left]; assumption.
Qed.

Lemma query_set_union_duplicate_free : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  query_bag_duplicate_free (query_set_bag Union left right).
Proof.
intros left right Hleft Hright Hdisjoint row.
unfold query_bag_duplicate_free in Hleft, Hright.
unfold query_bags_disjoint in Hdisjoint.
unfold query_set_bag; cbn.
rewrite Febag.nb_occ_union.
change
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right <= 1)%N.
destruct (Hdisjoint row) as [Hzero | Hzero]; rewrite Hzero.
- rewrite N.add_0_l; apply Hright.
- rewrite N.add_0_r; apply Hleft.
Qed.

Lemma query_set_union_disjoint_right : forall first second third,
  query_bags_disjoint first third ->
  query_bags_disjoint second third ->
  query_bags_disjoint (query_set_bag Union first second) third.
Proof.
intros first second third Hfirst Hsecond row.
unfold query_bags_disjoint in Hfirst, Hsecond.
destruct (Hfirst row) as [Hfirst_zero | Hthird_zero];
  [|right; exact Hthird_zero].
destruct (Hsecond row) as [Hsecond_zero | Hthird_zero];
  [left | right; exact Hthird_zero].
unfold query_set_bag; cbn; rewrite Febag.nb_occ_union.
change
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row first +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row second = 0)%N.
now rewrite Hfirst_zero, Hsecond_zero.
Qed.

Lemma query_distinct_bag_inert : forall bag,
  query_bag_duplicate_free bag ->
  bag_eq T (query_distinct_bag bag) bag.
Proof.
intros bag Hunique.
apply bag_eq_iff_occurrences; intro row.
unfold query_distinct_bag.
rewrite Febag.nb_occ_mk_bag.
change
  (Feset.nb_occ (Fecol.CSet (CTuple T)) row
    (Feset.mk_set (Fecol.CSet (CTuple T))
      (Febag.elements (SqlQuerySemantics.BTupleT T) bag)) =
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row bag).
rewrite Feset.nb_occ_alt, Feset.mem_mk_set.
rewrite <- Febag.mem_unfold, Febag.mem_nb_occ.
specialize (Hunique row).
destruct (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row bag) as [|count];
  cbn in Hunique |- *; [reflexivity|].
assert (N.pos count = 1%N) by lia.
now rewrite H.
Qed.

Corollary query_distinct_union_inert : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  bag_eq T
    (query_distinct_bag (query_set_bag Union left right))
    (query_set_bag Union left right).
Proof.
intros left right Hleft Hright Hdisjoint.
apply query_distinct_bag_inert.
now apply query_set_union_duplicate_free.
Qed.

Corollary query_distinct_three_way_union_inert :
  forall first second third,
    query_bag_duplicate_free first ->
    query_bag_duplicate_free second ->
    query_bag_duplicate_free third ->
    query_bags_disjoint first second ->
    query_bags_disjoint first third ->
    query_bags_disjoint second third ->
    bag_eq T
      (query_distinct_bag
        (query_set_bag Union (query_set_bag Union first second) third))
      (query_set_bag Union (query_set_bag Union first second) third).
Proof.
intros first second third Hfirst Hsecond Hthird
  Hfirst_second Hfirst_third Hsecond_third.
apply query_distinct_bag_inert.
apply query_set_union_duplicate_free.
- now apply query_set_union_duplicate_free.
- exact Hthird.
- now apply query_set_union_disjoint_right.
Qed.

End DuplicateFreeUnion.
