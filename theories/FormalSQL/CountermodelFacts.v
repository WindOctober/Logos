(******************************************************************************)
(** Generic observation-separation interfaces for FormalSQL countermodels.  **)
(******************************************************************************)

Set Implicit Arguments.

From SQLFS Require Import
  SqlSyntax FTuples FiniteBag FiniteCollection SqlOutcome SqlBagAbstraction
  SqlQuerySyntax SqlQuerySemantics SqlQueryFacts.
From Logos.FormalSQL Require Import
  QueryCardinality OrderedQueryFacts RelationalAlgebraFacts ProofAgentFacade.
From Stdlib Require Import List NArith.

Import ListNotations.
Import Tuple.

(** This module is the neutral countermodel entry point.  Operator-level
    success/cardinality contracts remain organized by semantic layer in
    [QueryCardinality], [OrderedQueryFacts], and [RelationalAlgebraFacts]; the
    theorems below only connect those contracts to observation separation.
    No query-shape dispatcher or benchmark-specific route is encoded here. *)

(** Successful observation functionality composes through any deterministic
    observation map that respects the source and target observation
    equivalences.  Operator-specific exact-success inversion theorems provide
    the [output_success] premise; this theorem itself does not inspect query
    syntax or assume absence of errors. *)
Theorem successful_relation_functional_map
    {A B : Type} (source_equiv : A -> A -> Prop)
    (target_equiv : B -> B -> Prop)
    (source : sql_outcome A -> Prop) (target : sql_outcome B -> Prop)
    (transform : A -> B) :
  (forall output,
    target (SqlSuccess output) ->
    exists input,
      source (SqlSuccess input) /\ output = transform input) ->
  (forall left right,
    source_equiv left right ->
    target_equiv (transform left) (transform right)) ->
  successful_relation_functional source_equiv source ->
  successful_relation_functional target_equiv target.
Proof.
intros Htarget Hproper Hsource left right Hleft Hright.
destruct (Htarget left Hleft) as [left_input [Hleft_input ->]].
destruct (Htarget right Hright) as [right_input [Hright_input ->]].
apply Hproper, Hsource; assumption.
Qed.

(** Functionality may be transported across an exact equivalence of possible
    bags.  Together with the generic unary/binary lift theorems in
    [SqlBagAbstraction], this is the uniform composition boundary for reset
    operators; no operator-shape dispatch is needed. *)
Theorem possible_bag_functional_rel_equiv
    (T : Tuple.Rcd) (left right : SqlBagAbstraction.bagT T -> Prop) :
  rel_equiv left right ->
  @possible_bag_functional T left ->
  @possible_bag_functional T right.
Proof.
intros Hequivalent Hleft first second Hfirst Hsecond.
apply Hleft.
- now apply (proj2 (Hequivalent first)).
- now apply (proj2 (Hequivalent second)).
Qed.

(** Query reset points share the same two composition principles.  Their
    exact success-bag characterizations remain operator-specific in
    [SqlQueryFacts], while these lemmas package the quotient and
    functionality plumbing once. *)
Theorem query_success_bags_functional_of_unary_reset
    (T : Tuple.Rcd) (parent_bags input_bags : SqlBagAbstraction.bagT T -> Prop)
    (operation : unary_bag_relation T) :
  rel_equiv parent_bags (lift_possible_bag_unary operation input_bags) ->
  unary_bag_relation_extensional operation ->
  @unary_bag_relation_functional T operation ->
  @possible_bag_functional T input_bags ->
  @possible_bag_functional T parent_bags.
Proof.
intros Hcharacterization Hext Hoperation Hinput.
eapply possible_bag_functional_rel_equiv.
- now apply rel_equiv_sym.
- now eapply lift_possible_bag_unary_functional.
Qed.

Theorem query_success_bags_functional_of_binary_reset
    (T : Tuple.Rcd)
    (parent_bags left_bags right_bags : SqlBagAbstraction.bagT T -> Prop)
    (operation : binary_bag_relation T) :
  rel_equiv parent_bags
    (lift_possible_bag_binary operation left_bags right_bags) ->
  binary_bag_relation_extensional operation ->
  @binary_bag_relation_functional T operation ->
  @possible_bag_functional T left_bags ->
  @possible_bag_functional T right_bags ->
  @possible_bag_functional T parent_bags.
Proof.
intros Hcharacterization Hext Hoperation Hleft Hright.
eapply possible_bag_functional_rel_equiv.
- now apply rel_equiv_sym.
- now eapply lift_possible_bag_binary_functional.
Qed.

(** A property used to distinguish successful observations must respect the
    observation equality of the enclosing semantics.  This contract is kept
    independent of SQL rows so it can also be reused for smaller relational
    evaluators and aggregate outcomes. *)
Definition observation_property_invariant {A : Type}
    (value_equiv : A -> A -> Prop) (property : A -> Prop) : Prop :=
  forall left right,
    value_equiv left right ->
    (property left <-> property right).

(** One legal success on the left separates two outcome relations whenever it
    has an observation-invariant property that no legal right success has.
    Errors remain present in both relations and are not assumed away. *)
Theorem outcome_relation_separation_of_left_success_property
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) (property : A -> Prop) :
  observation_property_invariant value_equiv property ->
  forall left_value,
    left (SqlSuccess left_value) ->
    property left_value ->
    (forall right_value,
      right (SqlSuccess right_value) ->
      ~ property right_value) ->
    outcome_relation_separation value_equiv left right.
Proof.
intros Hproper left_value Hleft Hproperty Hright.
eapply OutcomeSeparationLeftSuccess; [exact Hleft |].
intros right_value Hright_value Hequivalent.
apply (Hright right_value Hright_value).
now apply (proj1 (Hproper left_value right_value Hequivalent)).
Qed.

(** Symmetric success-property separation with the witnessed success on the
    right.  The equivalence argument still follows the left-to-right
    orientation used by [outcome_relation_separation]. *)
Theorem outcome_relation_separation_of_right_success_property
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) (property : A -> Prop) :
  observation_property_invariant value_equiv property ->
  forall right_value,
    right (SqlSuccess right_value) ->
    property right_value ->
    (forall left_value,
      left (SqlSuccess left_value) ->
      ~ property left_value) ->
    outcome_relation_separation value_equiv left right.
Proof.
intros Hproper right_value Hright Hproperty Hleft.
eapply OutcomeSeparationRightSuccess; [exact Hright |].
intros left_value Hleft_value Hequivalent.
apply (Hleft left_value Hleft_value).
now apply (proj2 (Hproper left_value right_value Hequivalent)).
Qed.

(** An exact SQL error is itself an observable countermodel witness when the
    opposite relation cannot expose the same error category.  These theorems
    intentionally require absence of that exact error, rather than confusing
    one differently observed error with determinism of the whole relation. *)
Theorem outcome_relation_separation_of_left_error_absent
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) :
  forall error,
    left (SqlError error) ->
    ~ right (SqlError error) ->
    outcome_relation_separation value_equiv left right.
Proof.
intros error Hleft Hright.
now apply OutcomeSeparationLeftError with error.
Qed.

Theorem outcome_relation_separation_of_right_error_absent
    {A : Type} (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) :
  forall error,
    right (SqlError error) ->
    ~ left (SqlError error) ->
    outcome_relation_separation value_equiv left right.
Proof.
intros error Hright Hleft.
now apply OutcomeSeparationRightError with error.
Qed.

(** Exact ordered-row observation equivalence preserves the occurrence count
    of every semantic row.  This is the small bridge from list observation to
    multiplicity-based countermodel arguments. *)
Lemma ordered_rows_equiv_nb_occ :
  forall (T : Tuple.Rcd) (row : tuple T) left right,
    ordered_rows_equiv T left right ->
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T left) =
    Febag.nb_occ (Fecol.CBag (CTuple T)) row (rows_bag T right).
Proof.
intros T row left right Hequivalent.
pose proof (ordered_rows_equiv_implies_bag_eq Hequivalent) as Hbags.
unfold bag_eq in Hbags.
rewrite Febag.nb_occ_equal in Hbags.
exact (Hbags row).
Qed.

(** One differing multiplicity is sufficient to refute semantic bag
    equality.  The direction is intentionally an implication rather than a
    decision procedure, so callers choose only the row relevant to their
    witness. *)
Lemma bag_not_eq_of_occurrence_difference :
  forall (T : Tuple.Rcd)
      (left right : SqlBagAbstraction.bagT T) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row left <>
      Febag.nb_occ (Fecol.CBag (CTuple T)) row right ->
    ~ bag_eq T left right.
Proof.
intros T left right row Hdifferent Hequivalent.
apply Hdifferent.
unfold bag_eq in Hequivalent.
rewrite Febag.nb_occ_equal in Hequivalent.
exact (Hequivalent row).
Qed.

(** A successful row bag can distinguish one side without any functionality
    assumption when it differs from every successful bag on the opposite
    side.  This is stronger than comparing two arbitrarily selected database
    executions and weaker than requiring the opposite evaluator to be wholly
    deterministic. *)
Theorem ordered_outcome_separation_of_left_success_bag_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall left_rows,
    left (SqlSuccess left_rows) ->
    (forall right_rows,
      right (SqlSuccess right_rows) ->
      ~ bag_eq T (rows_bag T left_rows) (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
intros left_rows Hleft Hdifferent.
eapply OutcomeSeparationLeftSuccess; [exact Hleft |].
intros right_rows Hright Hequivalent.
apply (Hdifferent right_rows Hright).
now apply ordered_rows_equiv_implies_bag_eq.
Qed.

Theorem ordered_outcome_separation_of_right_success_bag_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall right_rows,
    right (SqlSuccess right_rows) ->
    (forall left_rows,
      left (SqlSuccess left_rows) ->
      ~ bag_eq T (rows_bag T left_rows) (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
intros right_rows Hright Hdifferent.
eapply OutcomeSeparationRightSuccess; [exact Hright |].
intros left_rows Hleft Hequivalent.
apply (Hdifferent left_rows Hleft).
now apply ordered_rows_equiv_implies_bag_eq.
Qed.

(** A row whose occurrence count differs from every opposite success is a
    compact specialization of bag discrimination.  Duplicate multiplicities
    are preserved; the theorem does not silently switch to set semantics. *)
Theorem ordered_outcome_separation_of_left_success_occurrence_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall witness_row left_rows,
    left (SqlSuccess left_rows) ->
    (forall right_rows,
      right (SqlSuccess right_rows) ->
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T left_rows) <>
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
intros witness_row left_rows Hleft Hdifferent.
eapply OutcomeSeparationLeftSuccess; [exact Hleft |].
intros right_rows Hright Hequivalent.
apply (Hdifferent right_rows Hright).
now apply ordered_rows_equiv_nb_occ.
Qed.

Theorem ordered_outcome_separation_of_right_success_occurrence_difference
    (T : Tuple.Rcd)
    (left right : sql_outcome (list (tuple T)) -> Prop) :
  forall witness_row right_rows,
    right (SqlSuccess right_rows) ->
    (forall left_rows,
      left (SqlSuccess left_rows) ->
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T left_rows) <>
      Febag.nb_occ (Fecol.CBag (CTuple T)) witness_row
        (rows_bag T right_rows)) ->
    outcome_relation_separation (ordered_rows_equiv T) left right.
Proof.
intros witness_row right_rows Hright Hdifferent.
eapply OutcomeSeparationRightSuccess; [exact Hright |].
intros left_rows Hleft Hequivalent.
apply (Hdifferent left_rows Hleft).
now apply ordered_rows_equiv_nb_occ.
Qed.

(** Statement-indexed program lifting reuses the ordinary pointwise program
    semantics.  It lets a countermodel identify one separated statement
    without first manufacturing explicit prefix and suffix decompositions. *)
Theorem tnull_query_program_nth_separation_sound :
  forall db env index left_program right_program left_query right_query,
    nth_error left_program index = Some left_query ->
    nth_error right_program index = Some right_query ->
    TNullQueryExprOutcomeSeparation db env left_query right_query ->
    ~ TNullQueryProgramOutcomeEq db env left_program right_program.
Proof.
intros db env index.
induction index as [|index IH];
  intros [|left_head left_tail] [|right_head right_tail]
    left_query right_query Hleft Hright Hseparation Hprogram;
  cbn in Hleft, Hright; try discriminate.
- injection Hleft as Hleft; injection Hright as Hright.
  subst left_head right_head.
  apply (tnull_query_expr_outcome_separation_sound
    db env left_query right_query Hseparation).
  exact (proj1 Hprogram).
- eapply IH; [exact Hleft | exact Hright | exact Hseparation |].
  exact (proj2 Hprogram).
Qed.
