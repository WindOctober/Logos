(******************************************************************************)
(** Outcome-exact grouped-key HAVING-conjunct pushdown facts.                 **)
(******************************************************************************)

From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula
  ListPermut OrderedSet Partition SqlErrorSemantics SqlOutcome SqlQueryFacts
  SqlBagAbstraction SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import
  CardinalityCombinators GroupingRewriteFacts QueryCardinality
  RelationalAlgebraFacts.
From Stdlib Require Import Bool Lia List NArith SetoidList.

Import ListNotations.
Import Tuple.

(** Exact support coverage for ordinary, nonempty-key grouping.  Empty global
    grouping is excluded because it has a distinct empty-input correction. *)
Section GroupSupportRelations.

Context {T : Tuple.Rcd}.

Lemma query_make_groups_support_exact :
  forall env rows group_terms row,
    group_terms <> nil ->
    In row rows <->
    exists group,
      In group (@query_make_groups T env rows group_terms) /\
      In row group.
Proof.
intros env rows [|term terms] row Hterms; [contradiction|].
unfold query_make_groups, FlatData.make_groups; cbn.
set (key_of := query_grouping_key env (term :: terms)).
split.
- intro Hrow.
  match goal with
  | |- exists group,
      In group (map snd (@Partition.partition _ _ ?order ?key ?input)) /\
      In row group =>
      pose proof
        (@Partition.partition_permut _ _ order key input) as Hpartition
  end.
  pose proof
    (proj1 (ListPermut.in_permut_in Hpartition row) Hrow) as Hflat.
  apply in_flat_map in Hflat.
  destruct Hflat as [[key group] [Hpair Hingroup]].
  exists group; split; [|exact Hingroup].
  apply in_map_iff.
  exists (key, group); split; [reflexivity|exact Hpair].
- intros [group [Hgroup Hrow]].
  eapply Partition.in_map_snd_partition; eassumption.
Qed.

(** Mapping one representative per group has exactly the support of the input
    whenever every group member is related to that group's emitted row.  The
    relation may compare rows with different visible schemas. *)
Theorem query_make_groups_support_rel :
  forall (R : tuple T -> tuple T -> Prop) env rows group_terms
      (emit : list (tuple T) -> tuple T),
    group_terms <> nil ->
    (forall group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      R row (emit group)) ->
    list_support_rel R rows
      (map emit (@query_make_groups T env rows group_terms)).
Proof.
intros R env rows group_terms emit Hterms Hemit.
split.
- intros row Hrow.
  apply (proj1
    (query_make_groups_support_exact env rows group_terms row Hterms))
    in Hrow.
  destruct Hrow as [group [Hgroup Hrow]].
  exists (emit group); split.
  + now apply in_map.
  + now apply Hemit.
- intros output Houtput.
  apply in_map_iff in Houtput.
  destruct Houtput as [group [Houtput Hgroup]]; subst output.
  assert (Hnonempty : group <> nil).
  {
    unfold query_make_groups in Hgroup.
    destruct group_terms as [|term terms]; [contradiction|].
    cbn [FlatData.make_groups] in Hgroup.
    eapply Partition.in_map_snd_partition_diff_nil; exact Hgroup.
  }
  destruct group as [|row rest]; [contradiction|].
  exists row; split.
  + apply (proj2
      (query_make_groups_support_exact
        env rows group_terms row Hterms)).
    exists (row :: rest); split; [exact Hgroup|now left].
  + exact (Hemit (row :: rest) row Hgroup (or_introl eq_refl)).
Qed.

(** Emitting one row per ordinary group is duplicate-free whenever equality
    of two emitted rows reflects equality of the complete grouping keys of
    their source groups.  This is the operator-level fact: it does not assume
    any particular SELECT list, schema, or grouping-key arity. *)
Theorem query_make_groups_emit_NoDupA_of_key_reflection :
  forall env rows group_terms
      (emit : list (tuple T) -> tuple T),
    group_terms <> nil ->
    (forall left_group left_row right_group right_row,
      In left_group (@query_make_groups T env rows group_terms) ->
      In left_row left_group ->
      In right_group (@query_make_groups T env rows group_terms) ->
      In right_row right_group ->
      Oeset.compare (OTuple T) (emit left_group) (emit right_group) = Eq ->
      query_grouping_key env group_terms left_row =
      query_grouping_key env group_terms right_row) ->
    SetoidList.NoDupA
      (fun left right => Oeset.compare (OTuple T) left right = Eq)
      (map emit (@query_make_groups T env rows group_terms)).
Proof.
intros env rows [|term terms] emit Hterms Hreflect; [contradiction|].
unfold query_make_groups, FlatData.make_groups; cbn.
rewrite map_map.
eapply NoDupA_map_of_reflection with
  (source_relation := fun left right => fst left = fst right).
- apply all_diff_map_key_NoDupA.
  apply Partition.partition_all_diff_values.
- intros [left_key left_group] [right_key right_group]
    Hleft_pair Hright_pair Houtputs; cbn in Houtputs |- *.
  assert (Hleft_nonempty : left_group <> nil).
  { eapply Partition.in_partition_diff_nil; exact Hleft_pair. }
  assert (Hright_nonempty : right_group <> nil).
  { eapply Partition.in_partition_diff_nil; exact Hright_pair. }
  destruct left_group as [|left_row left_rest]; [contradiction|].
  destruct right_group as [|right_row right_rest]; [contradiction|].
  assert (Hleft_group :
    In (left_row :: left_rest)
      (@query_make_groups T env rows (term :: terms))).
  {
    unfold query_make_groups, FlatData.make_groups; cbn.
    apply in_map_iff.
    exists (left_key, left_row :: left_rest).
    split; [reflexivity|exact Hleft_pair].
  }
  assert (Hright_group :
    In (right_row :: right_rest)
      (@query_make_groups T env rows (term :: terms))).
  {
    unfold query_make_groups, FlatData.make_groups; cbn.
    apply in_map_iff.
    exists (right_key, right_row :: right_rest).
    split; [reflexivity|exact Hright_pair].
  }
  pose proof
    (Hreflect (left_row :: left_rest) left_row
      (right_row :: right_rest) right_row
      Hleft_group (or_introl eq_refl)
      Hright_group (or_introl eq_refl) Houtputs) as Hkeys.
  pose proof
    (@Partition.partition_homogeneous_values
      (tuple T) (list (value T))
      (OrderedSet.mk_olists (OVal T))
      (fun row => query_grouping_key env (term :: terms) row)
      rows left_key (left_row :: left_rest) Hleft_pair
      left_row (or_introl eq_refl)) as Hleft_key.
  pose proof
    (@Partition.partition_homogeneous_values
      (tuple T) (list (value T))
      (OrderedSet.mk_olists (OVal T))
      (fun row => query_grouping_key env (term :: terms) row)
      rows right_key (right_row :: right_rest) Hright_pair
      right_row (or_introl eq_refl)) as Hright_key.
  now rewrite Hleft_key, Hright_key in Hkeys.
Qed.

(** A projection-oriented corollary of
    [query_make_groups_emit_NoDupA_of_key_reflection]. *)
Local Lemma query_make_groups_projected_NoDupA :
  forall env rows group_terms
      (project : tuple T -> tuple T)
      (emit : list (tuple T) -> tuple T),
    group_terms <> nil ->
    (forall group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (emit group) = Eq) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env group_terms left =
      query_grouping_key env group_terms right) ->
    SetoidList.NoDupA
      (fun left right => Oeset.compare (OTuple T) left right = Eq)
      (map emit (@query_make_groups T env rows group_terms)).
Proof.
intros env rows group_terms project emit Hterms Hmember Hreflect.
eapply query_make_groups_emit_NoDupA_of_key_reflection; [exact Hterms|].
intros left_group left_row right_group right_row
  Hleft_group Hleft_row Hright_group Hright_row Houtputs.
apply Hreflect.
eapply Oeset.compare_eq_trans.
- exact (Hmember left_group left_row Hleft_group Hleft_row).
- eapply Oeset.compare_eq_trans; [exact Houtputs|].
  apply Oeset.compare_eq_sym.
  exact (Hmember right_group right_row Hright_group Hright_row).
Qed.

(** A nonempty GROUP BY that emits a key-complete projected view is a bag
    reset: projected support equality of its inputs determines exact equality
    of the emitted bags.  The theorem is intentionally independent of any
    concrete schema, table, column, or generated SELECT-list constant. *)
Theorem query_make_groups_projected_bag_eq_of_support_rel :
  forall env group_terms
      (project : tuple T -> tuple T)
      (emit : list (tuple T) -> tuple T)
      left_rows right_rows,
    group_terms <> nil ->
    (forall rows group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (emit group) = Eq) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env group_terms left =
      query_grouping_key env group_terms right) ->
    list_support_rel
      (fun left right =>
        Oeset.compare (OTuple T) (project left) (project right) = Eq)
      left_rows right_rows ->
    bag_eq T
      (rows_bag T
        (map emit (@query_make_groups T env left_rows group_terms)))
      (rows_bag T
        (map emit (@query_make_groups T env right_rows group_terms))).
Proof.
intros env group_terms project emit left_rows right_rows
  Hterms Hmember Hreflect Hinput.
assert (Hleft_support :
  list_support_rel
    (fun row output =>
      Oeset.compare (OTuple T) (project row) output = Eq)
    left_rows
    (map emit (@query_make_groups T env left_rows group_terms))).
{
  eapply query_make_groups_support_rel; [exact Hterms|].
  intros group row Hgroup Hrow.
  exact (Hmember left_rows group row Hgroup Hrow).
}
assert (Hright_support :
  list_support_rel
    (fun row output =>
      Oeset.compare (OTuple T) (project row) output = Eq)
    right_rows
    (map emit (@query_make_groups T env right_rows group_terms))).
{
  eapply query_make_groups_support_rel; [exact Hterms|].
  intros group row Hgroup Hrow.
  exact (Hmember right_rows group row Hgroup Hrow).
}
apply rows_bag_eq_of_nodup_support_rel.
- split.
  + intros left_output Hleft_output.
    destruct (proj2 Hleft_support left_output Hleft_output)
      as [left_row [Hleft_row Hleft_rel]].
    destruct (proj1 Hinput left_row Hleft_row)
      as [right_row [Hright_row Hinput_rel]].
    destruct (proj1 Hright_support right_row Hright_row)
      as [right_output [Hright_output Hright_rel]].
    exists right_output; split; [exact Hright_output|].
    eapply Oeset.compare_eq_trans.
    * apply Oeset.compare_eq_sym; exact Hleft_rel.
    * eapply Oeset.compare_eq_trans;
        [exact Hinput_rel|exact Hright_rel].
  + intros right_output Hright_output.
    destruct (proj2 Hright_support right_output Hright_output)
      as [right_row [Hright_row Hright_rel]].
    destruct (proj2 Hinput right_row Hright_row)
      as [left_row [Hleft_row Hinput_rel]].
    destruct (proj1 Hleft_support left_row Hleft_row)
      as [left_output [Hleft_output Hleft_rel]].
    exists left_output; split; [exact Hleft_output|].
    eapply Oeset.compare_eq_trans.
    * apply Oeset.compare_eq_sym; exact Hleft_rel.
    * eapply Oeset.compare_eq_trans;
        [exact Hinput_rel|exact Hright_rel].
- eapply query_make_groups_projected_NoDupA;
    [exact Hterms|intros; eapply Hmember; eassumption|exact Hreflect].
- eapply query_make_groups_projected_NoDupA;
    [exact Hterms|intros; eapply Hmember; eassumption|exact Hreflect].
Qed.

(** Two nonempty GROUP BY operators over the same input may use different
    grouping-key representations and different output constructors while
    still denote the same duplicate-free projected support.  Each emitted row
    must represent a member of its own group, and projected-row equality must
    reflect each side's own grouping key.  These premises are deliberately
    local to one GROUP operator: the theorem does not prescribe a surrounding
    join, filter, aggregate predicate, or query rewrite. *)
Theorem query_make_groups_heterogeneous_projected_bag_eq :
  forall env left_terms right_terms
      (project : tuple T -> tuple T)
      (left_emit right_emit : list (tuple T) -> tuple T) rows,
    left_terms <> nil ->
    right_terms <> nil ->
    (forall group row,
      In group (@query_make_groups T env rows left_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (left_emit group) = Eq) ->
    (forall group row,
      In group (@query_make_groups T env rows right_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row) (right_emit group) = Eq) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env left_terms left =
      query_grouping_key env left_terms right) ->
    (forall left right,
      Oeset.compare (OTuple T) (project left) (project right) = Eq ->
      query_grouping_key env right_terms left =
      query_grouping_key env right_terms right) ->
    bag_eq T
      (rows_bag T
        (map left_emit (@query_make_groups T env rows left_terms)))
      (rows_bag T
        (map right_emit (@query_make_groups T env rows right_terms))).
Proof.
intros env left_terms right_terms project left_emit right_emit rows
  Hleft_terms Hright_terms Hleft_member Hright_member
  Hleft_reflect Hright_reflect.
assert (Hleft_support : list_support_rel
  (fun row output =>
    Oeset.compare (OTuple T) (project row) output = Eq)
  rows (map left_emit (@query_make_groups T env rows left_terms))).
{
  eapply query_make_groups_support_rel; [exact Hleft_terms|].
  intros group row Hgroup Hrow.
  exact (Hleft_member group row Hgroup Hrow).
}
assert (Hright_support : list_support_rel
  (fun row output =>
    Oeset.compare (OTuple T) (project row) output = Eq)
  rows (map right_emit (@query_make_groups T env rows right_terms))).
{
  eapply query_make_groups_support_rel; [exact Hright_terms|].
  intros group row Hgroup Hrow.
  exact (Hright_member group row Hgroup Hrow).
}
apply rows_bag_eq_of_nodup_support_rel.
- split.
  + intros left_output Hleft_output.
    destruct (proj2 Hleft_support left_output Hleft_output)
      as [row [Hrow Hleft]].
    destruct (proj1 Hright_support row Hrow)
      as [right_output [Hright_output Hright]].
    exists right_output; split; [exact Hright_output|].
    eapply Oeset.compare_eq_trans.
    * apply Oeset.compare_eq_sym; exact Hleft.
    * exact Hright.
  + intros right_output Hright_output.
    destruct (proj2 Hright_support right_output Hright_output)
      as [row [Hrow Hright]].
    destruct (proj1 Hleft_support row Hrow)
      as [left_output [Hleft_output Hleft]].
    exists left_output; split; [exact Hleft_output|].
    eapply Oeset.compare_eq_trans.
    * apply Oeset.compare_eq_sym; exact Hleft.
    * exact Hright.
- eapply query_make_groups_emit_NoDupA_of_key_reflection;
    [exact Hleft_terms|].
  intros left_group left_row right_group right_row
    Hleft_group Hleft_row Hright_group Hright_row Houtputs.
  apply Hleft_reflect.
  eapply Oeset.compare_eq_trans.
  + exact (Hleft_member left_group left_row Hleft_group Hleft_row).
  + eapply Oeset.compare_eq_trans; [exact Houtputs|].
    apply Oeset.compare_eq_sym.
    exact (Hleft_member right_group right_row Hright_group Hright_row).
- eapply query_make_groups_emit_NoDupA_of_key_reflection;
    [exact Hright_terms|].
  intros left_group left_row right_group right_row
    Hleft_group Hleft_row Hright_group Hright_row Houtputs.
  apply Hright_reflect.
  eapply Oeset.compare_eq_trans.
  + exact (Hright_member left_group left_row Hleft_group Hleft_row).
  + eapply Oeset.compare_eq_trans; [exact Houtputs|].
    apply Oeset.compare_eq_sym.
    exact (Hright_member right_group right_row Hright_group Hright_row).
Qed.

End GroupSupportRelations.

(** Semantic permutation has the expected support projection.  This bridge
    intentionally forgets multiplicity; its only later consumer is a GROUP
    reset which reconstructs duplicate-free output multiplicities. *)
Lemma oeset_permut_support_rel :
  forall (A : Type) (ordered : Oeset.Rcd A) left right,
    Oeset.permut ordered left right ->
    list_support_rel
      (fun first second => Oeset.compare ordered first second = Eq)
      left right.
Proof.
intros A ordered left right Hpermut.
induction Hpermut as [|first second rest prefix suffix Hequal Hrest IH].
- split; intros value Hvalue; contradiction.
- destruct IH as [IHforward IHbackward].
  split.
  + intros value [Hvalue | Hvalue].
    * subst value. exists second; split.
      -- apply in_or_app; right; now left.
      -- exact Hequal.
    * destruct (IHforward value Hvalue) as [other [Hother Hrelated]].
      exists other; split; [|exact Hrelated].
      apply in_app_or in Hother; apply in_or_app.
      destruct Hother as [Hother | Hother].
      -- now left.
      -- right; now right.
  + intros value Hvalue.
    apply in_app_or in Hvalue.
    destruct Hvalue as [Hvalue | [Hvalue | Hvalue]].
    * destruct (IHbackward value) as [other [Hother Hrelated]].
      -- apply in_or_app; now left.
      -- exists other; split; [now right|exact Hrelated].
    * subst value. exists first; split; [now left|exact Hequal].
    * destruct (IHbackward value) as [other [Hother Hrelated]].
      -- apply in_or_app; now right.
      -- exists other; split; [now right|exact Hrelated].
Qed.

(** Equality of row bags is exactly semantic list permutation.  The forward
    direction complements the commonly used permutation-to-bag bridge and
    avoids reopening occurrence arithmetic at reset boundaries. *)
Lemma rows_bag_eq_implies_permut :
  forall (T : Tuple.Rcd) left right,
    bag_eq T (rows_bag T left) (rows_bag T right) ->
    Oeset.permut (OTuple T) left right.
Proof.
intros T left right Hbags.
apply Oeset.nb_occ_permut; intro row.
unfold bag_eq, rows_bag in Hbags.
rewrite Febag.nb_occ_equal in Hbags.
specialize (Hbags row).
now rewrite 2 Febag.nb_occ_mk_bag in Hbags.
Qed.

(** Semantic row permutation and equality of the corresponding finite bags
    are two presentations of the same multiplicity fact.  Keeping this
    direction next to [rows_bag_eq_implies_permut] lets reset-boundary proofs
    move between list representatives and bags without reopening occurrence
    arithmetic. *)
Lemma rows_permut_implies_bag_eq :
  forall (T : Tuple.Rcd) left right,
    Oeset.permut (OTuple T) left right ->
    bag_eq T (rows_bag T left) (rows_bag T right).
Proof.
intros T left right Hpermut.
unfold bag_eq, rows_bag.
rewrite Febag.nb_occ_equal; intro row.
rewrite 2 Febag.nb_occ_mk_bag.
now apply Oeset.permut_nb_occ.
Qed.

(** Reversing both representatives preserves semantic permutation.  This is
    useful at grouping boundaries because the partition implementation stores
    group members in accumulator order, while SQL exposes only their bag. *)
Lemma rows_reverse_permut_congr :
  forall (T : Tuple.Rcd) left right,
    Oeset.permut (OTuple T) left right ->
    Oeset.permut (OTuple T) (rev left) (rev right).
Proof.
intros T left right Hpermut.
eapply ListPermut._permut_trans with (l2 := left).
- intros first second third _ _ _ Hfirst Hsecond.
  eapply Oeset.compare_eq_trans; eassumption.
- apply Oeset.permut_sym.
  apply ListPermut._permut_rev.
  intros row _; apply Oeset.compare_eq_refl.
- eapply ListPermut._permut_trans with (l2 := right).
  + intros first second third _ _ _ Hfirst Hsecond.
    eapply Oeset.compare_eq_trans; eassumption.
  + exact Hpermut.
  + apply ListPermut._permut_rev.
    intros row _; apply Oeset.compare_eq_refl.
Qed.

Lemma query_same_rows_as_bag_permut_between :
  forall (T : Tuple.Rcd) first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    Oeset.permut (OTuple T) first second.
Proof.
intros T first second bag Hfirst Hsecond.
apply rows_bag_eq_implies_permut.
apply query_same_rows_as_bag_iff_bag_eq in Hfirst, Hsecond.
eapply bag_eq_trans; [exact Hfirst|].
now apply bag_eq_sym.
Qed.

(** These contracts expose the two facts about a relational formula outcome
    which an outcome-preserving filter rewrite actually needs.  Existence is
    separate from exclusion of other observations because formula evaluation
    is relational (subqueries can have several legal outcomes). *)
Section FormulaContracts.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Definition formula_total_success_at
    (env : Env.env T) (formula : formula_expr T relname) : Prop :=
  (exists truth, eval_formula env formula (SqlSuccess truth)) /\
  (forall error, ~ eval_formula env formula (SqlError error)).

Definition formula_acceptance_exact_at
    (env : Env.env T) (formula : formula_expr T relname)
    (accepted : bool) : Prop :=
  (exists truth,
    eval_formula env formula (SqlSuccess truth) /\
    Bool.is_true (B T) truth = accepted) /\
  (forall truth,
    eval_formula env formula (SqlSuccess truth) ->
    Bool.is_true (B T) truth = accepted) /\
  (forall error, ~ eval_formula env formula (SqlError error)).

Lemma formula_acceptance_exact_total_success :
  forall env formula accepted,
    formula_acceptance_exact_at env formula accepted ->
    formula_total_success_at env formula.
Proof.
  intros env formula accepted
    [[truth [Htruth Haccepted]] [Hsuccess Herror]].
  split; [now exists truth|exact Herror].
Qed.

Lemma formula_true_acceptance_exact :
  forall env,
    formula_acceptance_exact_at env FExpr_True true.
Proof.
intro env; unfold formula_acceptance_exact_at.
split.
- exists (Bool.true (B T)); split.
  + constructor.
  + apply Bool.true_is_true_alt.
- split.
  + intros truth Htruth; inversion Htruth; subst.
    apply Bool.true_is_true_alt.
  + intros error Herror; inversion Herror.
Qed.

(** A scalar predicate formula is acceptance-exact whenever evaluation of all
    of its arguments is explicitly runtime-safe.  The retained decision is
    [Bool.is_true] of the authoritative Bool3 predicate result: SQL FALSE and
    UNKNOWN are not identified as Bool3 values, but both correctly reject a
    row at the filter boundary. *)
Lemma formula_pred_acceptance_exact_safe :
  forall env predicate arguments,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    formula_acceptance_exact_at env (FExpr_Pred predicate arguments)
      (Bool.is_true (B T)
        (interp_predicate T predicate
          (map (@interp_aggterm T env) arguments))).
Proof.
  intros env predicate arguments Hsafe.
  unfold formula_acceptance_exact_at.
  split.
  - eexists; split.
    + now apply EFormula_PredSuccess.
    + reflexivity.
  - split.
    + intros truth Htruth.
      inversion Htruth; subst; reflexivity.
    + intros error Herror.
      inversion Herror; subst; congruence.
Qed.

(** Formula conjunction is eager for both SQL AND and SQL OR.  At a filter or
    HAVING boundary only the two [Bool.is_true] decisions are combined; this
    does not identify the underlying SQL FALSE and UNKNOWN values. *)
Definition acceptance_interp_conj
    (operation : and_or) (left right : bool) : bool :=
  match operation with
  | And_F => Datatypes.andb left right
  | Or_F => Datatypes.orb left right
  end.

Local Lemma is_true_orb :
  forall left right,
    Bool.is_true (B T) (Bool.orb (B T) left right) =
    Datatypes.orb
      (Bool.is_true (B T) left) (Bool.is_true (B T) right).
Proof.
  intros left right.
  rewrite BasicFacts.eq_bool_iff, !Bool.Bool.orb_true_iff,
    !Bool.true_is_true, Bool.orb_true_iff.
  intuition.
Qed.

Lemma acceptance_interp_conj_is_true :
  forall operation left right,
    Bool.is_true (B T) (interp_conj (B T) operation left right) =
    acceptance_interp_conj operation
      (Bool.is_true (B T) left) (Bool.is_true (B T) right).
Proof.
  intros [] left right; cbn [interp_conj acceptance_interp_conj].
  - apply Bool.is_true_andb.
  - apply is_true_orb.
Qed.

(** Exact child contracts compose through either eager conjunction operator.
    Both contracts are mandatory: the right formula is evaluated after every
    successful left observation, even for [AND FALSE] and [OR TRUE]. *)
Theorem formula_conj_acceptance_exact :
  forall env operation left right left_accepted right_accepted,
    formula_acceptance_exact_at env left left_accepted ->
    formula_acceptance_exact_at env right right_accepted ->
    formula_acceptance_exact_at env
      (FExpr_Conj operation left right)
      (acceptance_interp_conj operation left_accepted right_accepted).
Proof.
  intros env operation left right left_accepted right_accepted
    [[left_truth [Hleft Hleft_accepted]]
      [Hleft_success Hleft_error]]
    [[right_truth [Hright Hright_accepted]]
      [Hright_success Hright_error]].
  unfold formula_acceptance_exact_at.
  split.
  - exists (interp_conj (B T) operation left_truth right_truth).
    split.
    + now eapply EFormula_ConjSuccess.
    + rewrite acceptance_interp_conj_is_true,
        Hleft_accepted, Hright_accepted.
      reflexivity.
  - split.
    + intros truth Heval.
      inversion Heval; subst.
      rewrite acceptance_interp_conj_is_true.
      match goal with
      | Hleft_observed : eval_formula _ left (SqlSuccess ?observed_left),
        Hright_observed : eval_formula _ right (SqlSuccess ?observed_right)
        |- _ =>
          rewrite (Hleft_success observed_left Hleft_observed),
            (Hright_success observed_right Hright_observed);
          reflexivity
      end.
    + intros error Heval.
      inversion Heval; subst.
      * eapply Hleft_error; eassumption.
      * eapply Hright_error; eassumption.
Qed.

(** An eager right conjunct is acceptance-redundant when it is exact and
    error-free on every reached evaluation, and is accepting whenever the
    left guard accepts.  When the left guard rejects, SQL AND rejects
    regardless of the right Bool3 acceptance, but the right totality premise
    remains essential because FormalSQL still evaluates it. *)
Theorem formula_and_redundant_right_acceptance_exact :
  forall env left right left_accepted right_accepted,
    formula_acceptance_exact_at env left left_accepted ->
    formula_acceptance_exact_at env right right_accepted ->
    (left_accepted = true -> right_accepted = true) ->
    formula_acceptance_exact_at env
      (FExpr_Conj And_F left right) left_accepted.
Proof.
  intros env left right left_accepted right_accepted
    Hleft Hright Himplied.
  pose proof
    (formula_conj_acceptance_exact
      env And_F left right left_accepted right_accepted Hleft Hright)
    as Hexact.
  cbn [acceptance_interp_conj] in Hexact.
  destruct left_accepted; [|exact Hexact].
  rewrite (Himplied eq_refl) in Hexact.
  exact Hexact.
Qed.

(** [FExpr_Conj And_F] is eager in FormalSQL: the right formula is evaluated
    after every successful left observation, even when the left observation
    is SQL-nontrue.  These lemmas retain that evaluation order explicitly. *)
Lemma formula_and_success_intro :
  forall env left right left_truth right_truth,
    eval_formula env left (SqlSuccess left_truth) ->
    eval_formula env right (SqlSuccess right_truth) ->
    eval_formula env (FExpr_Conj And_F left right)
      (SqlSuccess (Bool.andb (B T) left_truth right_truth)).
Proof.
  intros; now apply EFormula_ConjSuccess.
Qed.

Lemma formula_and_right_error_intro :
  forall env left right left_truth error,
    eval_formula env left (SqlSuccess left_truth) ->
    eval_formula env right (SqlError error) ->
    eval_formula env (FExpr_Conj And_F left right) (SqlError error).
Proof.
  intros env left right left_truth error Hleft Hright.
  eapply EFormula_ConjRightError with (left_truth := left_truth);
    eassumption.
Qed.

Lemma formula_and_true_left_outcome_exact :
  forall env left right,
    formula_acceptance_exact_at env left true ->
    forall outcome,
      eval_formula env (FExpr_Conj And_F left right) outcome <->
      eval_formula env right outcome.
Proof.
  intros env left right
    [[left_truth [Hleft Hleft_accept]] [Hleft_success Hleft_error]]
    outcome.
  assert (Hleft_true : left_truth = Bool.true (B T)).
  { apply (proj1 (Bool.true_is_true (B T) left_truth));
      exact Hleft_accept. }
  split; intro Heval.
  - inversion Heval; subst.
    + exfalso; eapply Hleft_error; eassumption.
    + assumption.
    + assert (Hobserved_true : left_truth0 = Bool.true (B T)).
      { apply (proj1 (Bool.true_is_true (B T) left_truth0));
          now apply Hleft_success. }
      subst left_truth0.
      cbn [interp_conj].
      rewrite Bool.andb_true_l; assumption.
  - destruct outcome as [right_truth|error].
    + replace right_truth with
        (Bool.andb (B T) left_truth right_truth).
      * eapply formula_and_success_intro; eassumption.
      * subst left_truth; now rewrite Bool.andb_true_l.
    + eapply formula_and_right_error_intro; eassumption.
Qed.

Lemma formula_and_total_success_at_intro :
  forall env left right,
    formula_total_success_at env left ->
    formula_total_success_at env right ->
    formula_total_success_at env (FExpr_Conj And_F left right).
Proof.
  intros env left right
    [[left_truth Hleft] Hleft_error]
    [[right_truth Hright] Hright_error].
  split.
  - exists (Bool.andb (B T) left_truth right_truth).
    now eapply formula_and_success_intro.
  - intros error Heval; inversion Heval; subst.
    + eapply Hleft_error; eassumption.
    + eapply Hright_error; eassumption.
Qed.

Lemma formula_and_left_nontrue_success_rejected :
  forall env left right truth,
    formula_acceptance_exact_at env left false ->
    eval_formula env (FExpr_Conj And_F left right) (SqlSuccess truth) ->
    Bool.is_true (B T) truth = false.
Proof.
  intros env left right truth
    [[left_truth [Hleft Hleft_accept]] [Hleft_success Hleft_error]] Heval.
  inversion Heval; subst.
  assert (Hobserved : Bool.is_true (B T) left_truth0 = false).
  { apply Hleft_success; eassumption. }
  cbn [interp_conj].
  rewrite Bool.is_true_andb, Hobserved; reflexivity.
Qed.

End FormulaContracts.

Arguments formula_total_success_at
  {T relname} basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null env formula.
Arguments formula_acceptance_exact_at
  {T relname} basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null env formula accepted.

(** Exact row-filter execution from per-row acceptance contracts.  Requiring
    [formula_acceptance_exact_at] for every reached row rules out runtime-error
    observations explicitly.  [List.filter] retains the input order and every
    accepted occurrence, including duplicates. *)
Section ExactFilterBridge.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Theorem eval_filter_rows_acceptance_exact :
  forall env formula rows keep,
    (forall row,
      In row rows ->
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    forall outcome,
      eval_filter_rows env formula rows outcome <->
      outcome = SqlSuccess (List.filter keep rows).
Proof.
  intros env formula rows.
  induction rows as [|row rows IH]; intros keep Hexact outcome.
  - split; intro Heval.
    + inversion Heval; reflexivity.
    + subst; constructor.
  - pose proof (Hexact row (or_introl eq_refl)) as Hhead.
    destruct Hhead as [[truth [Htruth Hkeep]] [Hall Herror]].
    assert (Htail : forall other,
      In other rows ->
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env other) formula (keep other)).
    { intros other Hin; apply Hexact; now right. }
    split; intro Heval.
    + inversion Heval; subst.
      * exfalso; eapply Herror; eassumption.
      * match goal with
        | Hformula_eval :
            @eval_formula_expr_outcome _ _ _ _ _ _ _ _ _ _
              (SqlSuccess ?observed),
          Htail_eval :
            @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _
              rows ?tail |- _ =>
            specialize (IH keep Htail tail);
            apply (proj1 IH) in Htail_eval;
            subst tail;
            unfold filter_cons_outcome;
            rewrite (Hall observed Hformula_eval);
            destruct (keep row) eqn:Hrow;
              cbn [List.filter]; rewrite Hrow; reflexivity
        end.
    + subst outcome.
      replace (SqlSuccess (List.filter keep (row :: rows))) with
        (@filter_cons_outcome T truth row
          (SqlSuccess (List.filter keep rows))).
      * eapply EFilterRows_Cons.
        -- exact Htruth.
        -- apply (proj2
          (IH keep Htail (SqlSuccess (List.filter keep rows)))).
          reflexivity.
      * unfold filter_cons_outcome.
        rewrite Hkeep.
        destruct (keep row) eqn:Hrow;
          cbn [List.filter]; rewrite Hrow; reflexivity.
Qed.

End ExactFilterBridge.

(** Extensional, error-preserving interfaces for an ordinary WHERE boundary.
    Unlike [formula_expr_global_filter_outcome_equiv], the formula observation
    below is local to two possibly different row environments.  This is the
    useful boundary for transporting a filter across semantically equal rows:
    FALSE and UNKNOWN may differ, but TRUE acceptance and every runtime-error
    category must agree. *)
Section ExtensionalFilterOutcomeBridge.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Definition filter_formula_observation_equiv_at
    (left_env : Env.env T) (left_formula : formula_expr T relname)
    (right_env : Env.env T) (right_formula : formula_expr T relname) : Prop :=
  (forall left_truth,
    eval_formula left_env left_formula (SqlSuccess left_truth) ->
    exists right_truth,
      eval_formula right_env right_formula (SqlSuccess right_truth) /\
      Bool.is_true (B T) left_truth = Bool.is_true (B T) right_truth) /\
  (forall right_truth,
    eval_formula right_env right_formula (SqlSuccess right_truth) ->
    exists left_truth,
      eval_formula left_env left_formula (SqlSuccess left_truth) /\
      Bool.is_true (B T) left_truth = Bool.is_true (B T) right_truth) /\
  forall error,
    eval_formula left_env left_formula (SqlError error) <->
    eval_formula right_env right_formula (SqlError error).

Lemma filter_formula_observation_equiv_at_sym :
  forall left_env left_formula right_env right_formula,
    filter_formula_observation_equiv_at
      left_env left_formula right_env right_formula ->
    filter_formula_observation_equiv_at
      right_env right_formula left_env left_formula.
Proof.
intros left_env left_formula right_env right_formula
  [Hforward [Hbackward Herrors]].
split.
- intros right_truth Hright.
  destruct (Hbackward right_truth Hright) as
    [left_truth [Hleft Haccept]].
  exists left_truth; split; [exact Hleft|now symmetry].
- split.
  + intros left_truth Hleft.
    destruct (Hforward left_truth Hleft) as
      [right_truth [Hright Haccept]].
    exists right_truth; split; [exact Hright|now symmetry].
  + intro error; symmetry; apply Herrors.
Qed.

Local Lemma ordered_rows_equiv_cons_iff_filter :
  forall left_row left_rows right_row right_rows,
    ordered_rows_equiv T
      (left_row :: left_rows) (right_row :: right_rows) <->
    Oeset.compare (OTuple T) left_row right_row = Eq /\
    ordered_rows_equiv T left_rows right_rows.
Proof.
intros left_row left_rows right_row right_rows.
unfold ordered_rows_equiv, mk_oelists; cbn.
destruct (Oeset.compare (OTuple T) left_row right_row);
  split; try discriminate; intuition.
Qed.

(** Forward transport through the ordered filter scheduler.  [Forall2] is not
    hidden behind a permutation: the input correspondence remains positional,
    so the first formula error is preserved exactly. *)
Lemma eval_filter_rows_ordered_outcome_congr_forward :
  forall left_env left_formula left_rows left_outcome,
    eval_filter_rows left_env left_formula left_rows left_outcome ->
    forall right_env right_formula right_rows,
      ordered_rows_equiv T left_rows right_rows ->
      (forall left_row right_row,
        Oeset.compare (OTuple T) left_row right_row = Eq ->
        filter_formula_observation_equiv_at
          (env_t T left_env left_row) left_formula
          (env_t T right_env right_row) right_formula) ->
      exists right_outcome,
        eval_filter_rows right_env right_formula right_rows right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
Proof.
intros left_env left_formula left_rows left_outcome Heval.
induction Heval as
  [left_env left_formula
  |left_env left_formula left_row left_rows error Hleft_formula
  |left_env left_formula left_row left_rows left_truth left_tail
      Hleft_formula Hleft_tail IHtail];
  intros right_env right_formula right_rows Hrows Hformula.
- destruct right_rows as [|right_row right_rows].
  + exists (SqlSuccess nil); split; [constructor|apply ordered_rows_equiv_refl].
  + exfalso.
    pose proof (ordered_rows_equiv_length Hrows); discriminate.
- destruct right_rows as [|right_row right_rows].
  + exfalso.
    pose proof (ordered_rows_equiv_length Hrows); discriminate.
  + apply ordered_rows_equiv_cons_iff_filter in Hrows.
    destruct Hrows as [Hrow Hrows].
    destruct (Hformula left_row right_row Hrow) as [_ [_ Herrors]].
    exists (SqlError error); split.
    * apply EFilterRows_HeadError.
      exact (proj1 (Herrors error) Hleft_formula).
    * reflexivity.
- destruct right_rows as [|right_row right_rows].
  + exfalso.
    pose proof (ordered_rows_equiv_length Hrows); discriminate.
  + apply ordered_rows_equiv_cons_iff_filter in Hrows.
    destruct Hrows as [Hrow Hrows].
    destruct (Hformula left_row right_row Hrow) as
      [Hsuccess _].
    destruct (Hsuccess left_truth Hleft_formula) as
      [right_truth [Hright_formula Haccept]].
    destruct (IHtail right_env right_formula right_rows Hrows Hformula) as
      [right_tail [Hright_tail Htail_equiv]].
    exists (@filter_cons_outcome T right_truth right_row right_tail); split.
    * eapply EFilterRows_Cons; eassumption.
    * destruct left_tail as [left_tail_rows|left_error];
        destruct right_tail as [right_tail_rows|right_error];
        cbn in Htail_equiv |- *; try contradiction.
      -- unfold filter_cons_outcome.
         destruct (Bool.is_true (B T) left_truth) eqn:Hleft;
         destruct (Bool.is_true (B T) right_truth) eqn:Hright;
           try discriminate Haccept; cbn.
         ++ apply (proj2 (ordered_rows_equiv_cons_iff_filter
              left_row left_tail_rows right_row right_tail_rows)).
            now split.
         ++ exact Htail_equiv.
      -- now subst right_error.
Qed.

Local Lemma filter_rows_pointwise_observation_sym :
  forall left_env left_formula right_env right_formula,
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    forall right_row left_row,
      Oeset.compare (OTuple T) right_row left_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T right_env right_row) right_formula
        (env_t T left_env left_row) left_formula.
Proof.
intros left_env left_formula right_env right_formula
  Hformula right_row left_row Hrow.
apply filter_formula_observation_equiv_at_sym.
apply Hformula.
now apply Oeset.compare_eq_sym.
Qed.

(** Complete error-preserving congruence for two ordered filter schedulers.
    One inhabitation premise suffices: forward transport constructs a right
    outcome, and symmetry of the row/formula observations handles the reverse
    success and error clauses. *)
Theorem eval_filter_rows_ordered_outcome_congr :
  forall left_env left_formula left_rows
      right_env right_formula right_rows,
    ordered_rows_equiv T left_rows right_rows ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    (exists left_outcome,
      eval_filter_rows left_env left_formula left_rows left_outcome) ->
    outcome_relation_equiv (ordered_rows_equiv T)
      (eval_filter_rows left_env left_formula left_rows)
      (eval_filter_rows right_env right_formula right_rows).
Proof.
intros left_env left_formula left_rows right_env right_formula right_rows
  Hrows Hformula [left_outcome Hleft_outcome].
assert (Hrows_sym : ordered_rows_equiv T right_rows left_rows).
{ now apply ordered_rows_equiv_sym. }
assert (Hformula_sym : forall right_row left_row,
  Oeset.compare (OTuple T) right_row left_row = Eq ->
  filter_formula_observation_equiv_at
    (env_t T right_env right_row) right_formula
    (env_t T left_env left_row) left_formula).
{
  now apply (filter_rows_pointwise_observation_sym
    left_env left_formula right_env right_formula).
}
destruct (eval_filter_rows_ordered_outcome_congr_forward
  left_env left_formula left_rows left_outcome Hleft_outcome
  right_env right_formula right_rows Hrows Hformula) as
  [right_outcome [Hright_outcome Hrelated_outcome]].
apply outcome_relation_equiv_intro.
- now exists left_outcome.
- now exists right_outcome.
- intros left_rows' Hleft.
  destruct (eval_filter_rows_ordered_outcome_congr_forward
    left_env left_formula left_rows (SqlSuccess left_rows') Hleft
    right_env right_formula right_rows Hrows Hformula) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_rows'|right_error]; cbn in Hrelated.
  + exists right_rows'; now split.
  + contradiction.
- intros right_rows' Hright.
  destruct (eval_filter_rows_ordered_outcome_congr_forward
    right_env right_formula right_rows (SqlSuccess right_rows') Hright
    left_env left_formula left_rows Hrows_sym Hformula_sym) as
    [observed [Hobserved Hrelated]].
  destruct observed as [left_rows'|left_error]; cbn in Hrelated.
  + exists left_rows'; split; [exact Hobserved|].
    now apply ordered_rows_equiv_sym.
  + contradiction.
- intro error; split; intro Herror.
  + destruct (eval_filter_rows_ordered_outcome_congr_forward
      left_env left_formula left_rows (SqlError error) Herror
      right_env right_formula right_rows Hrows Hformula) as
      [observed [Hobserved Hrelated]].
    destruct observed as [right_rows'|right_error]; cbn in Hrelated.
    * contradiction.
    * now subst right_error.
  + destruct (eval_filter_rows_ordered_outcome_congr_forward
      right_env right_formula right_rows (SqlError error) Herror
      left_env left_formula left_rows Hrows_sym Hformula_sym) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_rows'|left_error]; cbn in Hrelated.
    * contradiction.
    * now subst left_error.
Qed.

(** Forward outcome transport for a complete [QExpr_Filter] boundary.  Child
    rows are related extensionally rather than required to be Leibniz-equal;
    the scheduler theorem above then preserves accepted rows and first-error
    behavior. *)
Lemma query_expr_filter_outcome_congr_extensional_forward :
  forall env left_formula right_formula left_input right_input,
    @query_expr_outcome_observation_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    forall left_outcome,
      eval_query env (QExpr_Filter left_formula left_input) left_outcome ->
      exists right_outcome,
        eval_query env (QExpr_Filter right_formula right_input) right_outcome /\
        outcome_equiv (ordered_rows_equiv T)
          left_outcome right_outcome.
Proof.
intros env left_formula right_formula left_input right_input
  [Hleft_input [Hright_input [Hforward [Hbackward Herrors]]]]
  Hformula [left_output|error] Heval.
- inversion Heval; subst.
  match goal with
  | H : eval_query env left_input (SqlSuccess _) |- _ =>
      rename H into Hleft
  end.
  match goal with
  | H : eval_filter_rows env left_formula _
      (SqlSuccess left_output) |- _ => rename H into Hfilter
  end.
  destruct (Hforward _ Hleft) as
    [right_rows [Hright Hrows]].
  destruct (eval_filter_rows_ordered_outcome_congr_forward
    env left_formula _ (SqlSuccess left_output) Hfilter
    env right_formula right_rows Hrows Hformula) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists (SqlSuccess right_output); split; [|exact Hrelated].
    eapply EQuery_FilterRows; eassumption.
  + contradiction.
- inversion Heval; subst.
  + exists (SqlError error); split; [|reflexivity].
    apply EQuery_FilterChildError.
    match goal with
    | Hchild : eval_query env left_input (SqlError error) |- _ =>
        exact (proj1 (Herrors error) Hchild)
    end.
  + match goal with
    | H : eval_query env left_input (SqlSuccess _) |- _ =>
        rename H into Hleft
    end.
    match goal with
    | H : eval_filter_rows env left_formula _ (SqlError error) |- _ =>
        rename H into Hfilter
    end.
    destruct (Hforward _ Hleft) as
      [right_rows [Hright Hrows]].
    destruct (eval_filter_rows_ordered_outcome_congr_forward
      env left_formula _ (SqlError error) Hfilter
      env right_formula right_rows Hrows Hformula) as
      [observed [Hobserved Hrelated]].
    destruct observed as [right_output|right_error]; cbn in Hrelated.
    * contradiction.
    * subst right_error.
      exists (SqlError error); split; [|reflexivity].
      eapply EQuery_FilterRows; eassumption.
Qed.

(** Query-level extensional congruence for two ordinary filters.  This is not
    a rewrite-pattern theorem: the child equivalence, formulas, environments,
    schemas, and rows remain abstract, and the only filter-specific premise is
    the SQL-observable TRUE/non-TRUE/error contract above. *)
Theorem query_expr_filter_outcome_congr_extensional :
  forall env left_formula right_formula left_input right_input,
    query_outcome_equiv env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_formula_observation_equiv_at
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    (exists left_outcome,
      eval_query env (QExpr_Filter left_formula left_input) left_outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_formula left_input)
      (QExpr_Filter right_formula right_input).
Proof.
intros env left_formula right_formula left_input right_input
  [Houtputs Hinput] Hformula [left_outcome Hleft_outcome].
assert (Hformula_sym : forall right_row left_row,
  Oeset.compare (OTuple T) right_row left_row = Eq ->
  filter_formula_observation_equiv_at
    (env_t T env right_row) right_formula
    (env_t T env left_row) left_formula).
{
  intros right_row left_row Hrow.
  apply filter_formula_observation_equiv_at_sym, Hformula.
  now apply Oeset.compare_eq_sym.
}
destruct Hinput as
  [Hleft_input [Hright_input [Hforward [Hbackward Herrors]]]].
assert (Hinput_sym :
  @query_expr_outcome_observation_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env right_input left_input).
{
  unfold query_expr_outcome_observation_equiv.
  apply outcome_relation_equiv_intro.
  - exact Hright_input.
  - exact Hleft_input.
  - intros right_rows Hright.
    destruct (Hbackward right_rows Hright) as
      [left_rows [Hleft Hrows]].
    exists left_rows; split; [exact Hleft|].
    now apply ordered_rows_equiv_sym.
  - intros left_rows Hleft.
    destruct (Hforward left_rows Hleft) as
      [right_rows [Hright Hrows]].
    exists right_rows; split; [exact Hright|].
    now apply ordered_rows_equiv_sym.
  - intro error; symmetry; apply Herrors.
}
assert (Hinput :
  @query_expr_outcome_observation_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env left_input right_input).
{
  unfold query_expr_outcome_observation_equiv.
  apply outcome_relation_equiv_intro.
  - exact Hleft_input.
  - exact Hright_input.
  - exact Hforward.
  - exact Hbackward.
  - exact Herrors.
}
destruct (query_expr_filter_outcome_congr_extensional_forward
  env left_formula right_formula left_input right_input
  Hinput Hformula left_outcome Hleft_outcome) as
  [right_outcome [Hright_outcome Hrelated_outcome]].
apply query_expr_outcome_equiv_of_observations.
- cbn; exact Houtputs.
- now exists left_outcome.
- now exists right_outcome.
- intros left_rows Hleft.
  destruct (query_expr_filter_outcome_congr_extensional_forward
    env left_formula right_formula left_input right_input
    Hinput Hformula (SqlSuccess left_rows) Hleft) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_rows|right_error]; cbn in Hrelated.
  + exists right_rows; now split.
  + contradiction.
- intros right_rows Hright.
  destruct (query_expr_filter_outcome_congr_extensional_forward
    env right_formula left_formula right_input left_input
    Hinput_sym Hformula_sym (SqlSuccess right_rows) Hright) as
    [observed [Hobserved Hrelated]].
  destruct observed as [left_rows|left_error]; cbn in Hrelated.
  + exists left_rows; split; [exact Hobserved|].
    now apply ordered_rows_equiv_sym.
  + contradiction.
- intro error; split; intro Herror.
  + destruct (query_expr_filter_outcome_congr_extensional_forward
      env left_formula right_formula left_input right_input
      Hinput Hformula (SqlError error) Herror) as
      [observed [Hobserved Hrelated]].
    destruct observed as [right_rows|right_error]; cbn in Hrelated.
    * contradiction.
    * now subst right_error.
  + destruct (query_expr_filter_outcome_congr_extensional_forward
      env right_formula left_formula right_input left_input
      Hinput_sym Hformula_sym (SqlError error) Herror) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_rows|left_error]; cbn in Hrelated.
    * contradiction.
    * now subst left_error.
Qed.

End ExtensionalFilterOutcomeBridge.

(** The exact list-level bridge.  [keep] is the group-key decision computed
    by the lower filter.  [key_formula] is its HAVING-level FormulaExpr view.
    On groups rejected by [keep], the source still performs SELECT aggregate
    finalization and eagerly evaluates all of HAVING; the explicit safety
    premise is therefore essential.  Scalar SELECT runtime evaluation is not
    a premise: the operational semantics correctly skips it once HAVING is
    SQL-nontrue. *)
Section GroupedHavingBridge.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_formula_aggregates :=
  (@eval_formula_expr_aggregate_runtime_error T relname
    symbol_runtime_error aggregate_runtime_error).
Local Abbreviation eval_select_aggregates :=
  (@eval_select_list_aggregate_runtime_error T
    symbol_runtime_error aggregate_runtime_error).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Definition group_env
    (env : Env.env T) (group_terms : list (@aggterm T))
    (group : list (tuple T)) : Env.env T :=
  env_g T env (@Group_By T group_terms) group.

Definition group_projection
    (env : Env.env T) (select_list : _select_list T)
    (group_terms : list (@aggterm T)) (group : list (tuple T)) : tuple T :=
  projection T (group_env env group_terms group) (@Select_List T select_list).

(** A property established for every logical group projection is preserved by
    every successful [eval_groups] result.  Rejected HAVING groups contribute
    no row; accepted groups contribute exactly their projection.  The theorem
    deliberately says nothing about failures and therefore cannot turn an
    erroneous execution into a success. *)
Theorem eval_groups_success_Forall_projection :
  forall env select_list group_terms having groups output
      (P : tuple T -> Prop),
    (forall group,
      In group groups ->
      P (group_projection env select_list group_terms group)) ->
    eval_groups env select_list group_terms having groups
      (SqlSuccess output) ->
    Forall P output.
Proof.
intros env select_list group_terms having groups.
induction groups as [|group groups IH]; intros output P Hproperty Heval.
- inversion Heval; constructor.
- inversion Heval; subst.
  + apply IH with (P := P); [|eassumption].
    intros other Hother; apply Hproperty; now right.
  + destruct tail as [tail_rows|tail_error].
    * unfold group_cons_outcome in H1.
      injection H1 as Houtput; subst output.
      constructor.
      -- apply Hproperty; now left.
      -- apply IH with (P := P); [|eassumption].
         intros other Hother; apply Hproperty; now right.
    * unfold group_cons_outcome in H1; discriminate.
Qed.

(** A successful global aggregate emits at most one row because SQL global
    grouping forms exactly one logical group, even on empty input. *)
Theorem eval_groups_global_success_length_le_one :
  forall env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    (length output <= 1)%nat.
Proof.
intros env select_list having rows output Heval.
pose proof
  (@eval_groups_success_length_le T
    symbol_runtime_error aggregate_runtime_error relname
    basesort instance unknown value_is_null env select_list [] having
    (@query_make_groups T env rows []) output Heval) as Hlength.
now rewrite query_make_groups_global_length_one in Hlength.
Qed.

(** Consequently every successful global-group row list is duplicate-free for
    any row relation.  This shape fact is independent of SELECT semantics. *)
Theorem eval_groups_global_success_NoDupA :
  forall (R : tuple T -> tuple T -> Prop)
      env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    SetoidList.NoDupA R output.
Proof.
intros R env select_list having rows output Heval.
pose proof
  (eval_groups_global_success_length_le_one
    env select_list having rows output Heval) as Hlength.
destruct output as [|first [|second rest]].
- constructor.
- constructor; [intro Hin; inversion Hin|constructor].
- cbn in Hlength; lia.
Qed.

(** Lift a projection property through the bag-consuming GROUP reset.  Since a
    group-bag success may choose any representative of the input bag, the
    premise is stated for every legal representative.  [P] must be proper for
    semantic tuple equality because the successful output bag need not retain
    the evaluator's literal list representatives. *)
Theorem eval_group_bag_success_occurrence_property :
  forall env select_list group_terms having input_bag output_bag
      (P : tuple T -> Prop),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      P left -> P right) ->
    (forall representative,
      query_same_rows_as_bag representative input_bag ->
      forall group,
        In group
          (@query_make_groups T env
            representative group_terms) ->
        P (group_projection env select_list group_terms group)) ->
    eval_group_bag env select_list group_terms having input_bag
      (SqlSuccess output_bag) ->
    forall row,
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row output_bag <> 0%N ->
      P row.
Proof.
intros env select_list group_terms having input_bag output_bag P
  Hproper Hprojection Heval.
remember (SqlSuccess output_bag) as observed eqn:Hobserved in Heval.
induction Heval; try discriminate.
injection Hobserved as Hbag; subst output_bag.
pose proof
  (eval_groups_success_Forall_projection
    env select_list group_terms having
    (query_make_groups env
      representative group_terms)
    grouped_rows P
    (Hprojection representative H)
    H1) as Hproperties.
pose proof
  (proj1
    (query_same_rows_as_bag_iff_occurrences
      T grouped_rows output_bag0) H2) as Hoccurrences.
intros row Hrow.
assert (Hlist_occurrence :
  Oeset.nb_occ (OTuple T) row grouped_rows <> 0%N).
{ rewrite Hoccurrences; exact Hrow. }
pose proof
  (Oeset.nb_occ_mem (OTuple T) row grouped_rows
    Hlist_occurrence) as Hmember.
apply Oeset.mem_bool_true_iff in Hmember.
destruct Hmember as [member [Hequal Hin]].
apply Forall_forall with (x := member) in Hproperties; [|exact Hin].
eapply Hproper; [|exact Hproperties].
apply Oeset.compare_eq_sym; exact Hequal.
Qed.

(** Pointwise execution observations needed to transport [eval_groups] across
    two ordered group lists.  The relation is intentionally below the query
    rewrite level: it records only the four scheduler decisions, exact HAVING
    outcomes, and semantic equality of the emitted rows. *)
Definition group_execution_observation_equiv
    (left_env : Env.env T) (left_select : _select_list T)
    (left_group_terms : list (@aggterm T))
    (left_having : formula_expr T relname)
    (right_env : Env.env T) (right_select : _select_list T)
    (right_group_terms : list (@aggterm T))
    (right_having : formula_expr T relname)
    (left_group right_group : list (tuple T)) : Prop :=
  eval_select_aggregates
    (group_env left_env left_group_terms left_group) left_select =
  eval_select_aggregates
    (group_env right_env right_group_terms right_group) right_select /\
  eval_formula_aggregates
    (group_env left_env left_group_terms left_group) left_having =
  eval_formula_aggregates
    (group_env right_env right_group_terms right_group) right_having /\
  (forall outcome,
    eval_formula
      (group_env left_env left_group_terms left_group)
      left_having outcome <->
    eval_formula
      (group_env right_env right_group_terms right_group)
      right_having outcome) /\
  @eval_select_list_runtime_error T
    symbol_runtime_error aggregate_runtime_error
    (group_env left_env left_group_terms left_group) left_select =
  @eval_select_list_runtime_error T
    symbol_runtime_error aggregate_runtime_error
    (group_env right_env right_group_terms right_group) right_select /\
  Oeset.compare (OTuple T)
    (group_projection left_env left_select left_group_terms left_group)
    (group_projection right_env right_select right_group_terms right_group) =
    Eq.

Lemma group_execution_observation_equiv_sym :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_group right_group,
    group_execution_observation_equiv
      left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_group right_group ->
    group_execution_observation_equiv
      right_env right_select right_group_terms right_having
      left_env left_select left_group_terms left_having
      right_group left_group.
Proof.
intros left_env left_select left_group_terms left_having
  right_env right_select right_group_terms right_having
  left_group right_group
  [Hselect [Hhaving [Hformula [Hruntime Hprojection]]]].
unfold group_execution_observation_equiv in *.
split; [now symmetry|].
split; [now symmetry|].
split.
- intro observed; exact (iff_sym (Hformula observed)).
- split; [now symmetry|].
  now apply Oeset.compare_eq_sym.
Qed.

(** Forward, error-preserving congruence for the ordered group scheduler.
    The theorem keeps first-error order explicit through [Forall2]; a mere
    permutation of groups would be insufficient for this statement. *)
Lemma eval_groups_outcome_Forall2_congr_forward :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_groups right_groups,
    Forall2
      (group_execution_observation_equiv
        left_env left_select left_group_terms left_having
        right_env right_select right_group_terms right_having)
      left_groups right_groups ->
    forall left_outcome,
      eval_groups left_env left_select left_group_terms left_having
        left_groups left_outcome ->
      exists right_outcome,
        eval_groups right_env right_select right_group_terms right_having
          right_groups right_outcome /\
        outcome_equiv (Oeset.permut (OTuple T))
          left_outcome right_outcome.
Proof.
intros left_env left_select left_group_terms left_having
  right_env right_select right_group_terms right_having
  left_groups right_groups Hgroups.
induction Hgroups as
  [|left_group right_group left_groups right_groups
    Hhead Hgroups IH]; intros left_outcome Heval.
- inversion Heval; subst.
  exists (SqlSuccess nil); split; [constructor|].
  apply Oeset.permut_refl.
  - destruct Hhead as
    [Hselect_aggregates
      [Hhaving_aggregates
        [Hformula [Hselect_runtime Hprojection]]]].
  unfold group_env in Hselect_aggregates, Hhaving_aggregates,
    Hformula, Hselect_runtime.
  inversion Heval; subst.
  + exists (SqlError error); split.
    * eapply EGroups_AggregateError.
      rewrite <- Hselect_aggregates; eassumption.
    * reflexivity.
  + exists (SqlError error); split.
    * eapply EGroups_HavingAggregateError.
      -- rewrite <- Hselect_aggregates; eassumption.
      -- rewrite <- Hhaving_aggregates; eassumption.
    * reflexivity.
  + exists (SqlError error); split.
    * eapply EGroups_HavingError.
      -- rewrite <- Hselect_aggregates; eassumption.
      -- rewrite <- Hhaving_aggregates; eassumption.
      -- apply (proj1 (Hformula (SqlError error))); assumption.
    * reflexivity.
  + match goal with
    | Htail_eval :
        eval_groups left_env left_select left_group_terms left_having
          left_groups ?left_tail |- _ =>
        destruct (IH left_tail Htail_eval)
          as [right_outcome [Hright Houtcome]]
    end.
    exists right_outcome; split.
    * eapply EGroups_HavingFalse with (truth := truth).
      -- rewrite <- Hselect_aggregates; eassumption.
      -- rewrite <- Hhaving_aggregates; eassumption.
      -- apply (proj1 (Hformula (SqlSuccess truth))); assumption.
      -- assumption.
      -- exact Hright.
    * exact Houtcome.
  + exists (SqlError error); split.
    * eapply EGroups_SelectError with (truth := truth).
      -- rewrite <- Hselect_aggregates; eassumption.
      -- rewrite <- Hhaving_aggregates; eassumption.
      -- apply (proj1 (Hformula (SqlSuccess truth))); assumption.
      -- assumption.
      -- rewrite <- Hselect_runtime; eassumption.
    * reflexivity.
  + match goal with
    | Htail_eval :
        eval_groups left_env left_select left_group_terms left_having
          left_groups ?left_tail |- _ =>
        destruct (IH left_tail Htail_eval)
          as [right_tail [Hright Htail]]
    end.
    exists (@group_cons_outcome T
      (group_projection right_env right_select right_group_terms right_group)
      right_tail); split.
    * unfold group_projection.
      eapply EGroups_SelectSuccess with (truth := truth).
      -- rewrite <- Hselect_aggregates; eassumption.
      -- rewrite <- Hhaving_aggregates; eassumption.
      -- apply (proj1 (Hformula (SqlSuccess truth))); assumption.
      -- assumption.
      -- rewrite <- Hselect_runtime; eassumption.
      -- exact Hright.
    * destruct tail as [left_rows|left_error];
        destruct right_tail as [right_rows|right_error];
        cbn [group_cons_outcome] in *; try contradiction.
      -- apply Oeset.permut_cons; assumption.
      -- exact Htail.
Qed.

Local Lemma group_execution_observation_Forall2_sym :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_groups right_groups,
    Forall2
      (group_execution_observation_equiv
        left_env left_select left_group_terms left_having
        right_env right_select right_group_terms right_having)
      left_groups right_groups ->
    Forall2
      (group_execution_observation_equiv
        right_env right_select right_group_terms right_having
        left_env left_select left_group_terms left_having)
      right_groups left_groups.
Proof.
intros left_env left_select left_group_terms left_having
  right_env right_select right_group_terms right_having
  left_groups right_groups Hgroups.
induction Hgroups; constructor; [|exact IHHgroups].
now apply group_execution_observation_equiv_sym.
Qed.

(** Complete relational congruence for two ordered group schedulers.  The one
    inhabitation premise is enough: forward transport constructs a right-hand
    outcome, while the symmetric pointwise relation transports every success
    and every error in both directions. *)
Theorem eval_groups_outcome_Forall2_congr :
  forall left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_groups right_groups,
    Forall2
      (group_execution_observation_equiv
        left_env left_select left_group_terms left_having
        right_env right_select right_group_terms right_having)
      left_groups right_groups ->
    (exists outcome,
      eval_groups left_env left_select left_group_terms left_having
        left_groups outcome) ->
    outcome_relation_equiv (Oeset.permut (OTuple T))
      (eval_groups left_env left_select left_group_terms left_having
        left_groups)
      (eval_groups right_env right_select right_group_terms right_having
        right_groups).
Proof.
intros left_env left_select left_group_terms left_having
  right_env right_select right_group_terms right_having
  left_groups right_groups Hgroups Hleft.
pose proof
  (group_execution_observation_Forall2_sym
    left_env left_select left_group_terms left_having
    right_env right_select right_group_terms right_having
    left_groups right_groups Hgroups) as Hgroups_sym.
destruct Hleft as [left_outcome Hleft_outcome].
destruct
  (eval_groups_outcome_Forall2_congr_forward
    left_env left_select left_group_terms left_having
    right_env right_select right_group_terms right_having
    left_groups right_groups Hgroups left_outcome Hleft_outcome)
  as [right_outcome [Hright_outcome Hrelated_outcome]].
eapply outcome_relation_equiv_intro.
- now exists left_outcome.
- now exists right_outcome.
- intros left_rows Hleft_rows.
  destruct
    (eval_groups_outcome_Forall2_congr_forward
      left_env left_select left_group_terms left_having
      right_env right_select right_group_terms right_having
      left_groups right_groups Hgroups (SqlSuccess left_rows) Hleft_rows)
    as [observed [Hobserved Hrelated]].
  destruct observed as [right_rows|right_error]; cbn in Hrelated.
  + exists right_rows; now split.
  + contradiction.
- intros right_rows Hright_rows.
  destruct
    (eval_groups_outcome_Forall2_congr_forward
      right_env right_select right_group_terms right_having
      left_env left_select left_group_terms left_having
      right_groups left_groups Hgroups_sym
      (SqlSuccess right_rows) Hright_rows)
    as [observed [Hobserved Hrelated]].
  destruct observed as [left_rows|left_error]; cbn in Hrelated.
  + exists left_rows; split; [exact Hobserved|].
    now apply Oeset.permut_sym.
  + contradiction.
- intro error; split; intro Heval.
  + destruct
      (eval_groups_outcome_Forall2_congr_forward
        left_env left_select left_group_terms left_having
        right_env right_select right_group_terms right_having
        left_groups right_groups Hgroups (SqlError error) Heval)
      as [observed [Hobserved Hrelated]].
    destruct observed as [right_rows|right_error]; cbn in Hrelated.
    * contradiction.
    * now subst right_error.
  + destruct
      (eval_groups_outcome_Forall2_congr_forward
        right_env right_select right_group_terms right_having
        left_env left_select left_group_terms left_having
        right_groups left_groups Hgroups_sym (SqlError error) Heval)
      as [observed [Hobserved Hrelated]].
    destruct observed as [left_rows|left_error]; cbn in Hrelated.
    * contradiction.
    * now subst left_error.
Qed.

(** If HAVING is acceptance-exact TRUE for every reached group and all four
    operational runtime checks are safe, group evaluation has exactly the
    ordered projection map shown below.  The list result retains duplicate
    group occurrences; this theorem does not construct the groups or cross the
    enclosing grouping operator's bag reset. *)
Theorem eval_groups_true_outcome_exact :
  forall env select_list group_terms having groups,
    (forall group,
      In group groups ->
      eval_select_aggregates
        (group_env env group_terms group) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms group) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms group) having true /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (group_env env group_terms group) select_list = None) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess
        (map (group_projection env select_list group_terms) groups).
Proof.
  intros env select_list group_terms having groups.
  induction groups as [|group groups IH]; intros Hsafe outcome.
  - split; intro Heval.
    + inversion Heval; reflexivity.
    + subst outcome; constructor.
  - destruct (Hsafe group (or_introl eq_refl)) as
      [Hselect_aggregates
        [Hhaving_aggregates
          [Hexact Hselect_runtime]]].
    destruct Hexact as
      [[truth [Htruth Htruth_true]] [Hsuccess Hformula_error]].
    assert (Htail : forall other,
      In other groups ->
      eval_select_aggregates
        (group_env env group_terms other) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms other) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms other) having true /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (group_env env group_terms other) select_list = None).
    { intros other Hin; apply Hsafe; now right. }
    unfold group_env in Hselect_aggregates, Hhaving_aggregates,
      Htruth, Htruth_true, Hsuccess, Hformula_error, Hselect_runtime.
    split; intro Heval.
    + inversion Heval; subst.
      * congruence.
      * congruence.
      * exfalso; eapply Hformula_error; eassumption.
      * match goal with
        | Hhaving : eval_formula _ having (SqlSuccess ?observed),
          Hfalse : Bool.is_true (B T) ?observed = false |- _ =>
            specialize (Hsuccess observed Hhaving); congruence
        end.
      * congruence.
      * match goal with
        | Hgroups : eval_groups _ select_list group_terms having groups ?tail
            |- _ =>
            apply (proj1 (IH Htail tail)) in Hgroups;
            subst tail;
            reflexivity
        end.
    + subst outcome.
      change (eval_groups env select_list group_terms having (group :: groups)
        (@group_cons_outcome T
          (group_projection env select_list group_terms group)
          (SqlSuccess
            (map (group_projection env select_list group_terms) groups)))).
      unfold group_projection at 1.
      eapply EGroups_SelectSuccess with (truth := truth).
      * exact Hselect_aggregates.
      * exact Hhaving_aggregates.
      * exact Htruth.
      * exact Htruth_true.
      * exact Hselect_runtime.
      * apply (proj2
          (IH Htail
            (SqlSuccess
              (map (group_projection env select_list group_terms) groups)))).
        reflexivity.
Qed.

(** SQL global aggregation forms one group even when [rows] is empty.  This
    specialization packages that global-group rule with exact TRUE-HAVING
    execution, so clients do not have to unfold the partition scheduler or
    rebuild the singleton group by hand. *)
Theorem eval_groups_global_true_outcome_exact :
  forall env select_list rows,
    eval_select_aggregates
      (group_env env [] (rev rows)) select_list = None ->
    @eval_select_list_runtime_error T
      symbol_runtime_error aggregate_runtime_error
      (group_env env [] (rev rows)) select_list = None ->
    forall outcome,
      eval_groups env select_list [] FExpr_True
        (query_make_groups env rows []) outcome <->
      outcome = SqlSuccess
        [group_projection env select_list [] (rev rows)].
Proof.
intros env select_list rows Haggregates Hruntime outcome.
rewrite query_make_groups_global_exact.
apply eval_groups_true_outcome_exact.
intros group Hgroup.
destruct Hgroup as [Hgroup | Hgroup]; [subst group|contradiction].
split; [exact Haggregates|].
split; [reflexivity|].
split; [apply formula_true_acceptance_exact|exact Hruntime].
Qed.

(** Exact group execution for an arbitrary acceptance decision.  SELECT and
    HAVING aggregate finalization still run for every reached group, and the
    HAVING formula must have one exact acceptance decision and no error
    observation.  Scalar SELECT evaluation is required safe only for accepted
    groups because the operational semantics skips projection after a
    SQL-nontrue HAVING result.  The result retains group order and duplicate
    occurrences exactly. *)
Theorem eval_groups_acceptance_outcome_exact :
  forall env select_list group_terms having groups keep,
    (forall group,
      In group groups ->
      eval_select_aggregates
        (group_env env group_terms group) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms group) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms group) having (keep group) /\
      (keep group = true ->
        @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (group_env env group_terms group) select_list = None)) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess
        (map (group_projection env select_list group_terms)
          (filter keep groups)).
Proof.
  intros env select_list group_terms having groups.
  induction groups as [|group groups IH]; intros keep Hsafe outcome.
  - split; intro Heval.
    + inversion Heval; reflexivity.
    + subst outcome; constructor.
  - destruct (Hsafe group (or_introl eq_refl)) as
      [Hselect_aggregates
        [Hhaving_aggregates
          [Hexact Hselect_runtime]]].
    destruct Hexact as
      [[truth [Htruth Htruth_keep]] [Hsuccess Hformula_error]].
    assert (Htail : forall other,
      In other groups ->
      eval_select_aggregates
        (group_env env group_terms other) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms other) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms other) having (keep other) /\
      (keep other = true ->
        @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (group_env env group_terms other) select_list = None)).
    { intros other Hin; apply Hsafe; now right. }
    unfold group_env in Hselect_aggregates, Hhaving_aggregates,
      Htruth, Htruth_keep, Hsuccess, Hformula_error, Hselect_runtime.
    destruct (keep group) eqn:Hkeep.
    + specialize (Hselect_runtime eq_refl).
      split; intro Heval.
      * inversion Heval; subst.
        -- congruence.
        -- congruence.
        -- exfalso; eapply Hformula_error; eassumption.
        -- match goal with
           | Hhaving : eval_formula _ having (SqlSuccess ?observed),
             Hfalse : Bool.is_true (B T) ?observed = false |- _ =>
               specialize (Hsuccess observed Hhaving); congruence
           end.
        -- congruence.
        -- match goal with
           | Hgroups : eval_groups _ select_list group_terms having groups ?tail
               |- _ =>
               apply (proj1 (IH keep Htail tail)) in Hgroups;
               subst tail;
               cbn [filter]; rewrite Hkeep; reflexivity
           end.
      * subst outcome.
        cbn [filter]; rewrite Hkeep; cbn.
        change (eval_groups env select_list group_terms having (group :: groups)
          (@group_cons_outcome T
            (group_projection env select_list group_terms group)
            (SqlSuccess
              (map (group_projection env select_list group_terms)
                (filter keep groups))))).
        unfold group_projection at 1.
        eapply EGroups_SelectSuccess with (truth := truth).
        -- exact Hselect_aggregates.
        -- exact Hhaving_aggregates.
        -- exact Htruth.
        -- exact Htruth_keep.
        -- exact Hselect_runtime.
        -- apply (proj2
             (IH keep Htail
               (SqlSuccess
                 (map (group_projection env select_list group_terms)
                   (filter keep groups))))).
           reflexivity.
    + split; intro Heval.
      * inversion Heval; subst.
        -- congruence.
        -- congruence.
        -- exfalso; eapply Hformula_error; eassumption.
        -- match goal with
           | Hgroups : eval_groups _ select_list group_terms having groups ?tail
               |- _ =>
               apply (proj1 (IH keep Htail tail)) in Hgroups;
               subst tail;
               cbn [filter]; rewrite Hkeep; reflexivity
           end.
        -- match goal with
           | Hhaving : eval_formula _ having (SqlSuccess ?observed),
             Htrue : Bool.is_true (B T) ?observed = true |- _ =>
               specialize (Hsuccess observed Hhaving); congruence
           end.
        -- match goal with
           | Hhaving : eval_formula _ having (SqlSuccess ?observed),
             Htrue : Bool.is_true (B T) ?observed = true |- _ =>
               specialize (Hsuccess observed Hhaving); congruence
           end.
      * subst outcome.
        cbn [filter]; rewrite Hkeep; cbn.
        eapply EGroups_HavingFalse with (truth := truth).
        -- exact Hselect_aggregates.
        -- exact Hhaving_aggregates.
        -- exact Htruth.
        -- exact Htruth_keep.
        -- apply (proj2
             (IH keep Htail
               (SqlSuccess
                 (map (group_projection env select_list group_terms)
                   (filter keep groups))))).
           reflexivity.
Qed.

(** When every reached HAVING predicate has one exact SQL-nontrue decision,
    group execution succeeds with the empty bag.  Aggregate finalization for
    both SELECT and HAVING remains required because the scheduler reaches
    those phases before testing HAVING.  Scalar SELECT runtime safety is not
    required: projection is unreachable for a rejected group. *)
Theorem eval_groups_all_rejected_outcome_exact :
  forall env select_list group_terms having groups,
    (forall group,
      In group groups ->
      eval_select_aggregates
        (group_env env group_terms group) select_list = None /\
      eval_formula_aggregates
        (group_env env group_terms group) having = None /\
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (group_env env group_terms group) having false) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess [].
Proof.
  intros env select_list group_terms having groups Hsafe outcome.
  assert (Hconstant : filter (fun _ : list (tuple T) => false) groups = []).
  { apply ListFacts.filter_false; intros; reflexivity. }
  pose proof
    (eval_groups_acceptance_outcome_exact
      env select_list group_terms having groups
      (fun _ : list (tuple T) => false)) as Hexact.
  rewrite Hconstant in Hexact.
  cbn [map] in Hexact.
  apply Hexact.
  intros group Hgroup.
  destruct (Hsafe group Hgroup) as
    [Hselect_aggregates [Hhaving_aggregates Hacceptance]].
  split; [exact Hselect_aggregates|].
  split; [exact Hhaving_aggregates|].
  split; [exact Hacceptance|].
  intro Htrue; discriminate Htrue.
Qed.

Definition grouped_key_formula_contract
    (env : Env.env T) (group_terms : list (@aggterm T))
    (key_formula : formula_expr T relname)
    (groups : list (list (tuple T)))
    (keep : list (tuple T) -> bool) : Prop :=
  forall group,
    In group groups ->
    eval_formula_aggregates (group_env env group_terms group) key_formula =
      None /\
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null
      (group_env env group_terms group) key_formula (keep group).

Definition skipped_group_runtime_safe
    (env : Env.env T) (select_list : _select_list T)
    (group_terms : list (@aggterm T))
    (rest_having : formula_expr T relname)
    (groups : list (list (tuple T)))
    (keep : list (tuple T) -> bool) : Prop :=
  forall group,
    In group groups ->
    keep group = false ->
    eval_select_aggregates (group_env env group_terms group) select_list = None /\
    eval_formula_aggregates (group_env env group_terms group) rest_having = None /\
    formula_total_success_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null
      (group_env env group_terms group) rest_having.

Lemma grouped_key_formula_contract_tail :
  forall env group_terms key_formula group groups keep,
    grouped_key_formula_contract env group_terms key_formula
      (group :: groups) keep ->
    grouped_key_formula_contract env group_terms key_formula groups keep.
Proof.
  intros env group_terms key_formula group groups keep Hcontract other Hin.
  apply Hcontract; now right.
Qed.

Lemma skipped_group_runtime_safe_tail :
  forall env select_list group_terms rest_having group groups keep,
    skipped_group_runtime_safe env select_list group_terms rest_having
      (group :: groups) keep ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      groups keep.
Proof.
  intros env select_list group_terms rest_having group groups keep
    Hsafe other Hin.
  apply Hsafe; now right.
Qed.

Theorem eval_groups_having_key_conj_filter_exact :
  forall env select_list group_terms key_formula rest_having groups keep,
    grouped_key_formula_contract env group_terms key_formula groups keep ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      groups keep ->
    forall outcome,
      eval_groups env select_list group_terms
        (FExpr_Conj And_F key_formula rest_having) groups outcome <->
      eval_groups env select_list group_terms rest_having
        (filter keep groups) outcome.
Proof.
  intros env select_list group_terms key_formula rest_having groups.
  induction groups as [|group groups IH]; intros keep Hkey Hskip outcome.
  - cbn; split; intro Heval; inversion Heval; constructor.
  - assert (Hkey_head := Hkey group (or_introl eq_refl)).
    destruct Hkey_head as [Hkey_aggregates Hkey_exact].
    assert (Hkey_tail := grouped_key_formula_contract_tail
      env group_terms key_formula group groups keep Hkey).
    assert (Hskip_tail := skipped_group_runtime_safe_tail
      env select_list group_terms rest_having group groups keep Hskip).
    specialize (IH keep Hkey_tail Hskip_tail).
    destruct (keep group) eqn:Hkeep; cbn [filter]; rewrite Hkeep; cbn.
    + assert (Hformula : forall observed,
        eval_formula (group_env env group_terms group)
          (FExpr_Conj And_F key_formula rest_having) observed <->
        eval_formula (group_env env group_terms group)
          rest_having observed).
      {
        intro observed.
        now apply formula_and_true_left_outcome_exact.
      }
      assert (Haggregates :
        eval_formula_aggregates (group_env env group_terms group)
          (FExpr_Conj And_F key_formula rest_having) =
        eval_formula_aggregates (group_env env group_terms group)
          rest_having).
      {
        cbn [eval_formula_expr_aggregate_runtime_error].
        now rewrite Hkey_aggregates.
      }
      unfold group_env in Haggregates.
      split; intro Heval; inversion Heval; subst.
      * eapply EGroups_AggregateError; eassumption.
      * eapply EGroups_HavingAggregateError.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
      * eapply EGroups_HavingError.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
      * eapply EGroups_HavingFalse.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
        -- eassumption.
        -- apply (proj1 (IH _)); eassumption.
      * eapply EGroups_SelectError.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
      * eapply EGroups_SelectSuccess.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
        -- apply (proj1 (IH _)); eassumption.
      * eapply EGroups_AggregateError; eassumption.
      * eapply EGroups_HavingAggregateError.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
      * eapply EGroups_HavingError.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
      * eapply EGroups_HavingFalse.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
        -- eassumption.
        -- apply (proj2 (IH _)); eassumption.
      * eapply EGroups_SelectError.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
      * eapply EGroups_SelectSuccess.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
        -- apply (proj2 (IH _)); eassumption.
    + destruct (Hskip group (or_introl eq_refl) Hkeep) as
      [Hselect_aggregates
          [Hrest_aggregates
            Hrest_total]].
      pose proof (formula_acceptance_exact_total_success
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null _ _ _ Hkey_exact)
        as Hkey_total.
      pose proof (formula_and_total_success_at_intro
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null _ _ _
        Hkey_total Hrest_total)
        as Hconj_total.
      destruct Hconj_total as
        [[conj_truth Hconj_truth] Hconj_error].
      assert (Hconj_rejected :
        Bool.is_true (B T) conj_truth = false).
      {
        eapply formula_and_left_nontrue_success_rejected; eassumption.
      }
      assert (Haggregates :
        eval_formula_aggregates (group_env env group_terms group)
          (FExpr_Conj And_F key_formula rest_having) = None).
      {
        cbn [eval_formula_expr_aggregate_runtime_error].
        now rewrite Hkey_aggregates, Hrest_aggregates.
      }
      unfold group_env in Hselect_aggregates, Haggregates.
      split; intro Heval.
      * inversion Heval; subst.
        -- congruence.
        -- congruence.
        -- exfalso; eapply Hconj_error; eassumption.
        -- apply (proj1 (IH _)); eassumption.
        -- assert (Hrejected : Bool.is_true (B T) truth = false).
           { eapply formula_and_left_nontrue_success_rejected; eassumption. }
           congruence.
        -- assert (Hrejected : Bool.is_true (B T) truth = false).
           { eapply formula_and_left_nontrue_success_rejected; eassumption. }
           congruence.
      * eapply EGroups_HavingFalse.
        -- exact Hselect_aggregates.
        -- exact Haggregates.
        -- exact Hconj_truth.
        -- exact Hconj_rejected.
        -- apply (proj2 (IH _)); eassumption.
Qed.


End GroupedHavingBridge.

(** Lift exact group-list contracts across the grouping bag reset.  The input
    bags may be unrelated and each reset may choose an arbitrary list
    representative.  All representation dependence is therefore exposed by
    the final permutation premise; key and group-processing errors remain
    observable unless the representative-specific exactness contracts rule
    them out. *)
Section ExactGroupBagReset.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** A semantic permutation changes only the list representative of a bag. *)
Local Lemma query_same_rows_as_bag_permut_transport :
  forall (left right : list (tuple T)) bag,
    Oeset.permut (OTuple T) left right ->
    query_same_rows_as_bag left bag ->
    query_same_rows_as_bag right bag.
Proof.
  intros left right bag Hpermut Hleft.
  unfold query_same_rows_as_bag, query_rows_bag in *.
  rewrite Febag.nb_occ_equal in Hleft |- *.
  intro row.
  specialize (Hleft row).
  rewrite Febag.nb_occ_mk_bag in Hleft |- *.
  rewrite <- (Oeset.permut_nb_occ (OA := OTuple T) row Hpermut).
  exact Hleft.
Qed.

(** A projection is permutation-stable when changing only the representative
    order of one logical group cannot change its emitted tuple.  This property
    is deliberately explicit: exact/numeric aggregates generally satisfy it,
    whereas floating-point SUM and AVG do not. *)
Definition group_projection_permutation_stable
    (env : Env.env T) (select_list : _select_list T)
    (group_terms : list (@aggterm T)) : Prop :=
  forall left right,
    Oeset.permut (OTuple T) left right ->
    Oeset.compare (OTuple T)
      (group_projection env select_list group_terms left)
      (group_projection env select_list group_terms right) = Eq.

(** Exact successful list semantics on every legal representative, together
    with semantic permutation of the emitted rows, is sufficient to equate
    the complete grouping-reset outcome relations.  In particular, this does
    not assume a preferred representative or literal output-list equality. *)
Theorem eval_group_bag_exact_rows_permut_equiv :
  forall env select_list group_terms left_having right_having
      (left_bag right_bag :
        Febag.bag (Fecol.CBag (Tuple.CTuple T)))
      (left_rows right_rows :
        list (list (tuple T)) -> list (tuple T)),
    (forall representative,
      query_same_rows_as_bag representative left_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        eval_groups env select_list group_terms left_having groups outcome <->
        outcome = SqlSuccess (left_rows groups)) ->
    (forall representative,
      query_same_rows_as_bag representative right_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        eval_groups env select_list group_terms right_having groups outcome <->
        outcome = SqlSuccess (right_rows groups)) ->
    (forall left_representative right_representative,
      query_same_rows_as_bag left_representative left_bag ->
      query_same_rows_as_bag right_representative right_bag ->
      Oeset.permut (OTuple T)
        (left_rows
          (query_make_groups env left_representative group_terms))
        (right_rows
          (query_make_groups env right_representative group_terms))) ->
    forall outcome,
      eval_group_bag env select_list group_terms left_having left_bag outcome <->
      eval_group_bag env select_list group_terms right_having right_bag outcome.
Proof.
  intros env select_list group_terms left_having right_having
    left_bag right_bag left_rows right_rows
    Hleft_exact Hright_exact Hrows_permut outcome.
  split; intro Heval.
  - inversion Heval; subst.
    + pose proof (Hleft_exact representative H) as Hcontract.
      cbn in Hcontract.
      destruct Hcontract as [Hnone _].
      congruence.
    + pose proof (Hleft_exact representative H) as Hcontract.
      cbn in Hcontract.
      destruct Hcontract as [_ Hexact].
      apply (proj1 (Hexact (SqlError error))) in H1.
      discriminate.
    + pose proof (Hleft_exact representative H) as Hleft_contract.
      cbn in Hleft_contract.
      destruct Hleft_contract as [_ Hleft_groups].
      apply (proj1 (Hleft_groups (SqlSuccess grouped_rows))) in H1.
      inversion H1; subst grouped_rows.
      pose proof (query_elements_same_rows_as_bag T right_bag)
        as Hright_representative.
      pose proof (Hright_exact
        (Febag.elements (Fecol.CBag (Tuple.CTuple T)) right_bag)
        Hright_representative) as Hright_contract.
      cbn in Hright_contract.
      destruct Hright_contract as [Hright_keys Hright_groups].
      eapply EGroupBag_Success with
        (representative :=
          Febag.elements (Fecol.CBag (Tuple.CTuple T)) right_bag)
        (grouped_rows :=
          right_rows
            (query_make_groups env
              (Febag.elements (Fecol.CBag (Tuple.CTuple T)) right_bag)
              group_terms)).
      * exact Hright_representative.
      * exact Hright_keys.
      * apply (proj2 (Hright_groups _)); reflexivity.
      * eapply query_same_rows_as_bag_permut_transport.
        -- eapply Hrows_permut; eassumption.
        -- exact H2.
  - inversion Heval; subst.
    + pose proof (Hright_exact representative H) as Hcontract.
      cbn in Hcontract.
      destruct Hcontract as [Hnone _].
      congruence.
    + pose proof (Hright_exact representative H) as Hcontract.
      cbn in Hcontract.
      destruct Hcontract as [_ Hexact].
      apply (proj1 (Hexact (SqlError error))) in H1.
      discriminate.
    + pose proof (Hright_exact representative H) as Hright_contract.
      cbn in Hright_contract.
      destruct Hright_contract as [_ Hright_groups].
      apply (proj1 (Hright_groups (SqlSuccess grouped_rows))) in H1.
      inversion H1; subst grouped_rows.
      pose proof (query_elements_same_rows_as_bag T left_bag)
        as Hleft_representative.
      pose proof (Hleft_exact
        (Febag.elements (Fecol.CBag (Tuple.CTuple T)) left_bag)
        Hleft_representative) as Hleft_contract.
      cbn in Hleft_contract.
      destruct Hleft_contract as [Hleft_keys Hleft_groups].
      eapply EGroupBag_Success with
        (representative :=
          Febag.elements (Fecol.CBag (Tuple.CTuple T)) left_bag)
        (grouped_rows :=
          left_rows
            (query_make_groups env
              (Febag.elements (Fecol.CBag (Tuple.CTuple T)) left_bag)
              group_terms)).
      * exact Hleft_representative.
      * exact Hleft_keys.
      * apply (proj2 (Hleft_groups _)); reflexivity.
      * eapply query_same_rows_as_bag_permut_transport.
        -- apply Oeset.permut_sym.
           eapply Hrows_permut; eassumption.
        -- exact H2.
Qed.

(** Every legal representative of a global input bag induces its own exact
    successful aggregate outcome when that representative is runtime-safe.
    For permutation-stable aggregates these outcomes coincide; for REAL/DOUBLE
    SUM and AVG this theorem exposes the distinct legal fold-order results. *)
Theorem eval_group_bag_global_true_success_for_representative :
  forall env select_list input_bag representative,
    query_same_rows_as_bag representative input_bag ->
    @eval_select_list_aggregate_runtime_error T
      symbol_runtime_error aggregate_runtime_error
      (Env.env_g T env (@Env.Group_By T []) (rev representative))
      select_list = None ->
    @eval_select_list_runtime_error T
      symbol_runtime_error aggregate_runtime_error
      (Env.env_g T env (@Env.Group_By T []) (rev representative))
      select_list = None ->
    eval_group_bag env select_list [] FExpr_True input_bag
      (SqlSuccess
        (rows_bag T
          [group_projection env select_list [] (rev representative)])).
Proof.
intros env select_list input_bag representative
  Hrepresentative Haggregate Hruntime.
eapply EGroupBag_Success with
  (representative := representative)
  (grouped_rows :=
    [group_projection env select_list [] (rev representative)]).
- exact Hrepresentative.
- unfold group_keys_runtime_error.
  clear Hrepresentative Haggregate Hruntime.
  induction representative as [|row rows IH]; [reflexivity|cbn; exact IH].
- apply (proj2
    (eval_groups_global_true_outcome_exact
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env select_list representative Haggregate Hruntime
      (SqlSuccess
        [group_projection env select_list [] (rev representative)]))).
  reflexivity.
- apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl.
Qed.

(** Runtime-safe global aggregation always has a successful bag outcome.  The
    premise is intentionally about every possible group representative: bag
    reset may choose any representative, and this theorem must not hide an
    aggregate or scalar projection error for one such choice. *)
Theorem eval_group_bag_global_true_success_exists :
  forall env select_list input_bag,
    (forall group,
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_g T env (@Env.Group_By T []) group) select_list = None /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_g T env (@Env.Group_By T []) group) select_list = None) ->
    exists output_bag,
      eval_group_bag env select_list [] FExpr_True input_bag
        (SqlSuccess output_bag).
Proof.
intros env select_list input_bag Hsafe.
set (representative :=
  Febag.elements (Fecol.CBag (Tuple.CTuple T)) input_bag).
exists (rows_bag T
  [group_projection env select_list [] (rev representative)]).
destruct (Hsafe (rev representative)) as [Haggregate Hruntime].
apply eval_group_bag_global_true_success_for_representative; try assumption.
unfold representative; apply query_elements_same_rows_as_bag.
Qed.

(** A successful global aggregation has one representative-independent output
    row only when its projection is permutation-stable.  The explicit premise
    excludes floating-point SUM/AVG, whose legal results can depend on the
    order chosen for the input bag representative. *)
Theorem eval_group_bag_global_true_success_bag_unique_if_stable :
  forall env select_list input_bag chosen output_bag,
    query_same_rows_as_bag chosen input_bag ->
    group_projection_permutation_stable env select_list [] ->
    (forall group,
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_g T env (@Env.Group_By T []) group) select_list = None /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_g T env (@Env.Group_By T []) group) select_list = None) ->
    eval_group_bag env select_list [] FExpr_True input_bag
      (SqlSuccess output_bag) ->
    bag_eq T output_bag
      (rows_bag T
        [group_projection env select_list []
          (rev chosen)]).
Proof.
intros env select_list input_bag chosen output_bag
  Hchosen Hstable Hselect Heval.
inversion Heval; subst.
destruct (Hselect (rev representative))
  as [Haggregates Hruntime].
pose proof (proj1
  (eval_groups_global_true_outcome_exact
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env select_list representative
    Haggregates Hruntime (SqlSuccess grouped_rows)) H2) as Hgrouped.
injection Hgrouped as Hgrouped; subst grouped_rows.
apply query_same_rows_as_bag_iff_bag_eq in H7.
eapply bag_eq_trans; [exact (bag_eq_sym H7)|].
apply rows_permut_implies_bag_eq.
apply Oeset.permut_cons.
- apply Hstable.
  apply rows_reverse_permut_congr.
  eapply query_same_rows_as_bag_permut_between; eassumption.
- apply Oeset.permut_refl.
Qed.

End ExactGroupBagReset.

(** A TRUE-HAVING GROUP reset can consume projected support directly.  The
    theorem is generic in the projection and keeps all runtime checks as
    explicit premises.  Its direct-column TNull specialization can discharge
    those checks by computation, while aggregate/scalar callers must prove
    them honestly. *)
Section TrueGroupProjectedSupport.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Theorem eval_group_bag_true_projected_support_equiv :
  forall env select_list group_terms
      (project : tuple T -> tuple T) left_rows right_rows,
    group_terms <> nil ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (project first) (project second) = Eq) ->
    (forall rows group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      Oeset.compare (OTuple T) (project row)
        (group_projection env select_list group_terms group) = Eq) ->
    (forall first second,
      Oeset.compare (OTuple T) (project first) (project second) = Eq ->
      query_grouping_key env group_terms first =
      query_grouping_key env group_terms second) ->
    (forall rows,
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms rows = None) ->
    (forall rows group,
      In group (@query_make_groups T env rows group_terms) ->
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (env_g T env (@Group_By T group_terms) group) select_list = None /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (env_g T env (@Group_By T group_terms) group) select_list = None) ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) (project first) (project second) = Eq)
      left_rows right_rows ->
    forall outcome,
      eval_group_bag env select_list group_terms FExpr_True
        (rows_bag T left_rows) outcome <->
      eval_group_bag env select_list group_terms FExpr_True
        (rows_bag T right_rows) outcome.
Proof.
intros env select_list group_terms project left_rows right_rows
  Hterms Hproject Hmember Hreflect Hkeys Hselect Hsupport outcome.
eapply eval_group_bag_exact_rows_permut_equiv with
  (left_rows := fun groups =>
    map (group_projection env select_list group_terms) groups)
  (right_rows := fun groups =>
    map (group_projection env select_list group_terms) groups).
- intros representative Hrepresentative; cbn.
  split; [apply Hkeys|].
  apply eval_groups_true_outcome_exact.
  intros group Hgroup.
  destruct (Hselect representative group Hgroup)
    as [Haggregate Hruntime].
  split; [exact Haggregate|].
  split; [reflexivity|].
  split; [apply formula_true_acceptance_exact|exact Hruntime].
- intros representative Hrepresentative; cbn.
  split; [apply Hkeys|].
  apply eval_groups_true_outcome_exact.
  intros group Hgroup.
  destruct (Hselect representative group Hgroup)
    as [Haggregate Hruntime].
  split; [exact Haggregate|].
  split; [reflexivity|].
  split; [apply formula_true_acceptance_exact|exact Hruntime].
- intros left_representative right_representative
    Hleft_representative Hright_representative.
  apply rows_bag_eq_implies_permut.
  eapply query_make_groups_projected_bag_eq_of_support_rel
    with (project := project).
  + exact Hterms.
  + exact Hmember.
  + exact Hreflect.
  + assert (Hleft_original :
      @query_same_rows_as_bag T left_rows (rows_bag T left_rows)).
    { apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl. }
    assert (Hright_original :
      @query_same_rows_as_bag T right_rows (rows_bag T right_rows)).
    { apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl. }
    pose proof
      (@query_same_rows_as_bag_permut_between T
        _ _ _ Hleft_representative Hleft_original) as Hleft_permut.
    pose proof
      (@query_same_rows_as_bag_permut_between T
        _ _ _ Hright_original Hright_representative) as Hright_permut.
    pose proof
      (@oeset_permut_support_rel (tuple T) (OTuple T)
        _ _ Hleft_permut)
      as Hleft_rows.
    pose proof
      (@oeset_permut_support_rel (tuple T) (OTuple T)
        _ _ Hright_permut)
      as Hright_rows.
    assert (Hleft_projected :
      list_support_rel
        (fun first second =>
          Oeset.compare (OTuple T) (project first) (project second) = Eq)
        left_representative left_rows).
    {
      destruct Hleft_rows as [Hforward Hbackward]; split.
      - intros first Hfirst.
        destruct (Hforward first Hfirst) as [second [Hsecond Hequal]].
        exists second; split; [exact Hsecond|now apply Hproject].
      - intros second Hsecond.
        destruct (Hbackward second Hsecond) as [first [Hfirst Hequal]].
        exists first; split; [exact Hfirst|now apply Hproject].
    }
    assert (Hright_projected :
      list_support_rel
        (fun first second =>
          Oeset.compare (OTuple T) (project first) (project second) = Eq)
        right_rows right_representative).
    {
      destruct Hright_rows as [Hforward Hbackward]; split.
      - intros first Hfirst.
        destruct (Hforward first Hfirst) as [second [Hsecond Hequal]].
        exists second; split; [exact Hsecond|now apply Hproject].
      - intros second Hsecond.
        destruct (Hbackward second Hsecond) as [first [Hfirst Hequal]].
        exists first; split; [exact Hfirst|now apply Hproject].
    }
    eapply list_support_rel_compose with
      (middle := right_rows)
      (R := fun first second =>
        Oeset.compare (OTuple T) (project first) (project second) = Eq)
      (S := fun first second =>
        Oeset.compare (OTuple T) (project first) (project second) = Eq).
    * eapply list_support_rel_compose with
        (middle := left_rows)
        (R := fun first second =>
          Oeset.compare (OTuple T) (project first) (project second) = Eq)
        (S := fun first second =>
          Oeset.compare (OTuple T) (project first) (project second) = Eq).
      -- exact Hleft_projected.
      -- exact Hsupport.
      -- intros first middle last Hfirst Hlast.
         exact
           (@Oeset.compare_eq_trans (tuple T) (OTuple T)
             (project first) (project middle) (project last)
             Hfirst Hlast).
    * exact Hright_projected.
    * intros first middle last Hfirst Hlast.
      exact
        (@Oeset.compare_eq_trans (tuple T) (OTuple T)
          (project first) (project middle) (project last)
          Hfirst Hlast).
Qed.

(** Query-level scheduler lift for a GROUP node.  [supported] is deliberately
    abstract: a caller may instantiate it with exact bag equality, projected
    support, or another relation, but must prove that the complete group-bag
    outcome relation (including every runtime error) is preserved. *)
Theorem query_expr_group_outcome_equiv_of_supported_child_outcomes :
  forall env select_list group_terms having left right
      (supported : list (tuple T) -> list (tuple T) -> Prop),
    query_expr_outputs
      (QExpr_Group select_list group_terms having left) =
    query_expr_outputs
      (QExpr_Group select_list group_terms having right) ->
    (exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group select_list group_terms having left) outcome) ->
    (forall left_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null env right
          (SqlSuccess right_rows) /\
        supported left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null env left
          (SqlSuccess left_rows) /\
        supported left_rows right_rows) ->
    (forall error,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlError error) <->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlError error)) ->
    (forall left_rows right_rows,
      supported left_rows right_rows ->
      forall outcome,
        eval_group_bag env select_list group_terms having
          (rows_bag T left_rows) outcome <->
        eval_group_bag env select_list group_terms having
          (rows_bag T right_rows) outcome) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
Proof.
intros env select_list group_terms having left right supported
  Houtputs Hleft_outcome Hforward Hbackward Hchild_errors Hgroups.
assert (Heval : forall outcome,
  @eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null env
    (QExpr_Group select_list group_terms having left) outcome <->
  @eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null env
    (QExpr_Group select_list group_terms having right) outcome).
{
  intros [output | error].
  - rewrite !eval_query_expr_group_success_iff.
    split.
    + intros [left_rows [output_bag
        [Hleft [Hgroup Houtput]]]].
      destruct (Hforward left_rows Hleft)
        as [right_rows [Hright Hsupported]].
      exists right_rows, output_bag; repeat split; try assumption.
      now apply (proj1 (Hgroups left_rows right_rows Hsupported
        (SqlSuccess output_bag))).
    + intros [right_rows [output_bag
        [Hright [Hgroup Houtput]]]].
      destruct (Hbackward right_rows Hright)
        as [left_rows [Hleft Hsupported]].
      exists left_rows, output_bag; repeat split; try assumption.
      now apply (proj2 (Hgroups left_rows right_rows Hsupported
        (SqlSuccess output_bag))).
  - rewrite !eval_query_expr_group_error_iff.
    split.
    + intros [Hchild | [left_rows [Hleft Hgroup]]].
      * left; now apply (proj1 (Hchild_errors error)).
      * right.
        destruct (Hforward left_rows Hleft)
          as [right_rows [Hright Hsupported]].
        exists right_rows; split; [exact Hright|].
        now apply (proj1 (Hgroups left_rows right_rows Hsupported
          (SqlError error))).
    + intros [Hchild | [right_rows [Hright Hgroup]]].
      * left; now apply (proj2 (Hchild_errors error)).
      * right.
        destruct (Hbackward right_rows Hright)
          as [left_rows [Hleft Hsupported]].
        exists left_rows; split; [exact Hleft|].
        now apply (proj2 (Hgroups left_rows right_rows Hsupported
          (SqlError error))).
}
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- exact Hleft_outcome.
- destruct Hleft_outcome as [outcome Houtcome].
  exists outcome; now apply (proj1 (Heval outcome)).
- intros rows Hrows. exists rows; split.
  + now apply (proj1 (Heval (SqlSuccess rows))).
  + apply ordered_rows_equiv_refl.
- intros rows Hrows. exists rows; split.
  + now apply (proj2 (Heval (SqlSuccess rows))).
  + apply ordered_rows_equiv_refl.
- intro error; apply Heval.
Qed.

End TrueGroupProjectedSupport.
