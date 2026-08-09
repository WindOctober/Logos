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
From Stdlib Require Import Bool Lia List NArith SetoidList Sorting.Permutation.

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


(** Exact observations for the canonical Boolean scalar language.  These
    contracts expose both successful acceptance and every SQL runtime error:
    FALSE and UNKNOWN are identified only at the final [Bool.is_true] filter
    boundary, never inside scalar evaluation. *)
Section ScalarContracts.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_operands :=
  (@eval_scalar_boolean_operands_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Definition scalar_expr_total_success_at
    (env : Env.env T)
    (expression : scalar_expr T relname ScalarResultBoolean) : Prop :=
  (exists truth,
    eval_scalar_boolean env expression (SqlSuccess truth)) /\
  (forall error,
    ~ eval_scalar_boolean env expression (SqlError error)).

Definition scalar_expr_acceptance_exact_at
    (env : Env.env T)
    (expression : scalar_expr T relname ScalarResultBoolean)
    (accepted : bool) : Prop :=
  (exists truth,
    eval_scalar_boolean env expression (SqlSuccess truth) /\
    Bool.is_true (B T) truth = accepted) /\
  (forall truth,
    eval_scalar_boolean env expression (SqlSuccess truth) ->
    Bool.is_true (B T) truth = accepted) /\
  (forall error,
    ~ eval_scalar_boolean env expression (SqlError error)).

Definition scalar_value_list_exact_at
    (env : Env.env T)
    (expressions : list (scalar_expr T relname ScalarResultValue))
    (expected : list (Tuple.value T)) : Prop :=
  eval_scalar_values env expressions (SqlSuccess expected) /\
  (forall values,
    eval_scalar_values env expressions (SqlSuccess values) ->
    values = expected) /\
  (forall error,
    ~ eval_scalar_values env expressions (SqlError error)).

Lemma scalar_expr_acceptance_exact_total_success :
  forall env expression accepted,
    scalar_expr_acceptance_exact_at env expression accepted ->
    scalar_expr_total_success_at env expression.
Proof.
intros env expression accepted
  [[truth [Htruth Haccepted]] [Hsuccess Herror]].
split; [now exists truth|exact Herror].
Qed.

Lemma scalar_expr_true_acceptance_exact :
  forall env,
    scalar_expr_acceptance_exact_at env SExpr_True true.
Proof.
intro env; unfold scalar_expr_acceptance_exact_at.
split.
- exists (Bool.true (B T)); split.
  + constructor.
  + apply Bool.true_is_true_alt.
- split.
  + intros truth Htruth; inversion Htruth; subst.
    apply Bool.true_is_true_alt.
  + intros error Herror; inversion Herror.
Qed.

(** Typed predicate arguments may contain lazy CASE expressions or scalar
    subqueries.  The premise therefore records the whole relational argument
    observation instead of falling back to flat terms. *)
Lemma scalar_expr_pred_acceptance_exact_safe :
  forall env predicate arguments values,
    scalar_value_list_exact_at env arguments values ->
    scalar_expr_acceptance_exact_at env (SExpr_Pred predicate arguments)
      (Bool.is_true (B T) (interp_predicate T predicate values)).
Proof.
intros env predicate arguments values [Hexists [Hsuccess Herror]].
unfold scalar_expr_acceptance_exact_at.
split.
- exists (interp_predicate T predicate values); split.
  + now apply EScalar_PredSuccess.
  + reflexivity.
- split.
  + intros truth Heval; inversion Heval; subst.
    match goal with
    | Hvalues : eval_scalar_values _ arguments (SqlSuccess ?observed) |- _ =>
        now rewrite (Hsuccess observed Hvalues)
    end.
  + intros error Heval; inversion Heval; subst.
    eapply Herror; eassumption.
Qed.

Definition scalar_acceptance_combine
    (operation : and_or) (left right : bool) : bool :=
  match operation with
  | And_F => andb left right
  | Or_F => orb left right
  end.

Definition scalar_acceptance_identity (operation : and_or) : bool :=
  match operation with
  | And_F => true
  | Or_F => false
  end.

Definition scalar_acceptance_fold
    (operation : and_or) (accepted : list bool) : bool :=
  fold_right (scalar_acceptance_combine operation)
    (scalar_acceptance_identity operation) accepted.

Local Lemma scalar_is_true_orb :
  forall left right,
    Bool.is_true (B T) (Bool.orb (B T) left right) =
    orb (Bool.is_true (B T) left) (Bool.is_true (B T) right).
Proof.
intros left right.
rewrite BasicFacts.eq_bool_iff, !Bool.Bool.orb_true_iff,
  !Bool.true_is_true, Bool.orb_true_iff.
intuition.
Qed.

Lemma scalar_acceptance_interp_conj :
  forall operation left right,
    Bool.is_true (B T) (interp_conj (B T) operation left right) =
    scalar_acceptance_combine operation
      (Bool.is_true (B T) left) (Bool.is_true (B T) right).
Proof.
intros [] left right; cbn [interp_conj scalar_acceptance_combine].
- apply Bool.is_true_andb.
- apply scalar_is_true_orb.
Qed.

Local Lemma scalar_is_true_false :
  Bool.is_true (B T) (Bool.false (B T)) = false.
Proof.
destruct (Bool.is_true (B T) (Bool.false (B T))) eqn:Htruth;
  [|reflexivity].
apply (proj1 (Bool.true_is_true (B T) (Bool.false (B T)))) in Htruth.
exfalso; now apply (Bool.true_diff_false (B T)).
Qed.

Local Lemma scalar_decisive_acceptance :
  forall operation truth other,
    scalar_conj_operand_decides T operation truth = true ->
    Bool.is_true (B T) (scalar_conj_decisive_result T operation) =
    scalar_acceptance_combine operation
      (Bool.is_true (B T) truth) other.
Proof.
intros [|] truth other Hdecides.
- cbn [scalar_conj_operand_decides] in Hdecides.
  apply (proj1
    (Bool.true_is_true (B T) (Bool.negb (B T) truth))) in Hdecides.
  assert (Hfalse : truth = Bool.false (B T)).
  { rewrite <- (Bool.negb_negb (B T) truth), Hdecides.
    apply Bool.negb_true. }
  subst truth.
  cbn [scalar_conj_decisive_result scalar_acceptance_combine].
  now rewrite scalar_is_true_false.
- cbn [scalar_conj_operand_decides] in Hdecides.
  cbn [scalar_conj_decisive_result scalar_acceptance_combine].
  now rewrite Hdecides, Bool.true_is_true_alt.
Qed.

Definition scalar_boolean_operands_acceptance_exact_at
    (env : Env.env T) (operation : and_or)
    (expressions : list (scalar_expr T relname ScalarResultBoolean))
    (accepted : bool) : Prop :=
  (exists truth,
    eval_scalar_operands env operation expressions (SqlSuccess truth) /\
    Bool.is_true (B T) truth = accepted) /\
  (forall truth,
    eval_scalar_operands env operation expressions (SqlSuccess truth) ->
    Bool.is_true (B T) truth = accepted) /\
  (forall error,
    ~ eval_scalar_operands env operation expressions (SqlError error)).

Lemma eval_scalar_boolean_operands_acceptance_exact :
  forall env operation expressions accepted,
    Forall2
      (fun expression decision =>
        scalar_expr_acceptance_exact_at env expression decision)
      expressions accepted ->
    scalar_boolean_operands_acceptance_exact_at env operation expressions
      (scalar_acceptance_fold operation accepted).
Proof.
intros env operation expressions accepted Hcontracts.
induction Hcontracts as
  [|expression decision expressions accepted Hhead Htail IH].
- unfold scalar_boolean_operands_acceptance_exact_at,
    scalar_acceptance_fold, scalar_acceptance_identity.
  split.
  + exists (scalar_conj_identity T operation); split.
    * constructor.
    * destruct operation; cbn [scalar_conj_identity].
      -- apply Bool.true_is_true_alt.
      -- apply scalar_is_true_false.
  + split.
    * intros truth Heval; inversion Heval; subst.
      destruct operation; cbn [scalar_conj_identity].
      -- apply Bool.true_is_true_alt.
      -- apply scalar_is_true_false.
    * intros error Heval; inversion Heval.
- destruct Hhead as
    [[head_truth [Hhead_eval Hhead_accept]]
      [Hhead_success Hhead_error]].
  destruct IH as
    [[tail_truth [Htail_eval Htail_accept]]
      [Htail_success Htail_error]].
  unfold scalar_boolean_operands_acceptance_exact_at.
  split.
  + destruct (scalar_conj_operand_decides T operation head_truth)
      eqn:Hdecides.
    * exists (scalar_conj_decisive_result T operation); split.
      -- eapply EScalarBooleanOperands_HeadDecides;
           [exact Hhead_eval|exact Hdecides].
      -- rewrite (scalar_decisive_acceptance operation head_truth
          (scalar_acceptance_fold operation accepted) Hdecides),
          Hhead_accept.
         reflexivity.
    * exists (interp_conj (B T) operation head_truth tail_truth); split.
      -- change (eval_scalar_operands env operation
           (expression :: expressions)
           (scalar_conj_cons_outcome T operation head_truth
             (SqlSuccess tail_truth))).
         eapply EScalarBooleanOperands_Continue;
           [exact Hhead_eval|exact Hdecides|exact Htail_eval].
      -- rewrite scalar_acceptance_interp_conj,
           Hhead_accept, Htail_accept.
         reflexivity.
  + split.
    * intros truth Heval; inversion Heval; subst.
      -- match goal with
         | Hexpression : eval_scalar_boolean env expression
             (SqlSuccess ?observed),
           Hdecides : scalar_conj_operand_decides T operation ?observed = true
             |- _ =>
             rewrite (scalar_decisive_acceptance operation observed
               (scalar_acceptance_fold operation accepted) Hdecides),
               (Hhead_success observed Hexpression);
             reflexivity
         end.
      -- match goal with
         | Hexpression : eval_scalar_boolean env expression
             (SqlSuccess ?observed),
           Htail_observed : eval_scalar_operands env operation expressions
             ?tail_outcome,
           Houtcome : scalar_conj_cons_outcome T operation ?observed
             ?tail_outcome = SqlSuccess truth |- _ =>
             destruct tail_outcome as [tail_truth0|tail_error];
               cbn [scalar_conj_cons_outcome] in Houtcome;
               try discriminate;
             injection Houtcome as Htruth; subst truth;
             rewrite scalar_acceptance_interp_conj,
               (Hhead_success observed Hexpression),
               (Htail_success tail_truth0 Htail_observed);
             reflexivity
         end.
    * intros error Heval; inversion Heval; subst.
      -- match goal with
         | Hexpression : eval_scalar_boolean env expression
             (SqlError ?observed) |- _ =>
             exact (Hhead_error observed Hexpression)
         end.
      -- match goal with
         | Htail_observed : eval_scalar_operands env operation expressions
             ?tail_outcome,
           Houtcome : scalar_conj_cons_outcome T operation ?observed
             ?tail_outcome = SqlError error |- _ =>
             destruct tail_outcome as [tail_truth0|tail_error];
               cbn [scalar_conj_cons_outcome] in Houtcome;
               try discriminate;
             injection Houtcome as Herror; subst tail_error;
             exact (Htail_error error Htail_observed)
         end.
Qed.

Local Lemma scalar_acceptance_fold_permutation :
  forall operation left right,
    Permutation left right ->
    scalar_acceptance_fold operation left =
    scalar_acceptance_fold operation right.
Proof.
intros operation left right Hpermutation.
unfold scalar_acceptance_fold.
induction Hpermutation; cbn.
- reflexivity.
- now rewrite IHHpermutation.
- destruct operation.
  + destruct x, y,
      (fold_right (scalar_acceptance_combine And_F)
        (scalar_acceptance_identity And_F) l); reflexivity.
  + destruct x, y,
      (fold_right (scalar_acceptance_combine Or_F)
        (scalar_acceptance_identity Or_F) l); reflexivity.
- now rewrite IHHpermutation1, IHHpermutation2.
Qed.

Local Lemma scalar_acceptance_fold_append :
  forall operation left right,
    scalar_acceptance_fold operation (left ++ right) =
    scalar_acceptance_combine operation
      (scalar_acceptance_fold operation left)
      (scalar_acceptance_fold operation right).
Proof.
intros operation left right.
unfold scalar_acceptance_fold.
revert right; induction left as [|head left IH]; intro right.
- destruct operation; reflexivity.
- cbn.
  rewrite IH.
  destruct operation.
  + destruct head,
      (fold_right (scalar_acceptance_combine And_F)
        (scalar_acceptance_identity And_F) left),
      (fold_right (scalar_acceptance_combine And_F)
        (scalar_acceptance_identity And_F) right); reflexivity.
  + destruct head,
      (fold_right (scalar_acceptance_combine Or_F)
        (scalar_acceptance_identity Or_F) left),
      (fold_right (scalar_acceptance_combine Or_F)
        (scalar_acceptance_identity Or_F) right); reflexivity.
Qed.

Local Lemma scalar_acceptance_contracts_map :
  forall env expressions decide,
    (forall expression,
      In expression expressions ->
      scalar_expr_acceptance_exact_at env expression (decide expression)) ->
    Forall2
      (fun expression accepted =>
        scalar_expr_acceptance_exact_at env expression accepted)
      expressions (map decide expressions).
Proof.
intros env expressions; induction expressions as [|expression expressions IH];
  intros decide Hcontracts; cbn.
- constructor.
- constructor.
  + apply Hcontracts; now left.
  + apply IH; intros other Hin; apply Hcontracts; now right.
Qed.

(** The compiled site matrix may choose any operand permutation.  The theorem
    derives one schedule-independent acceptance result from exact contracts
    for every original operand, while retaining all scalar error categories. *)
Theorem scalar_expr_conj_list_acceptance_exact :
  forall site_rows env operation expressions decide,
    (forall expression,
      In expression expressions ->
      scalar_expr_acceptance_exact_at env expression (decide expression)) ->
    scalar_expr_acceptance_exact_at env
      (SExpr_ConjList site_rows operation expressions)
      (scalar_acceptance_fold operation (map decide expressions)).
Proof.
intros site_rows env operation expressions decide Hcontracts.
pose proof
  (schedule_boolean_operands_permutation boolean_schedule
    site_rows expressions) as Hschedule.
set (scheduled :=
  schedule_boolean_operands boolean_schedule site_rows expressions)
  in Hschedule |- *.
assert (Hscheduled : Forall2
  (fun expression accepted =>
    scalar_expr_acceptance_exact_at env expression accepted)
  scheduled (map decide scheduled)).
{
  apply scalar_acceptance_contracts_map.
  intros expression Hin; apply Hcontracts.
  eapply Permutation_in; [apply Permutation_sym; exact Hschedule|exact Hin].
}
pose proof
  (eval_scalar_boolean_operands_acceptance_exact
    env operation scheduled (map decide scheduled) Hscheduled) as Hexact.
assert (Hacceptance :
  scalar_acceptance_fold operation (map decide scheduled) =
  scalar_acceptance_fold operation (map decide expressions)).
{
  apply scalar_acceptance_fold_permutation.
  apply Permutation_sym, Permutation_map, Hschedule.
}
destruct Hexact as
  [[truth [Htruth Htruth_accept]] [Hsuccess Herror]].
unfold scalar_expr_acceptance_exact_at.
split.
- exists truth; split.
  + constructor; exact Htruth.
  + now rewrite Htruth_accept, Hacceptance.
- split.
  + intros observed Heval; inversion Heval; subst.
    match goal with
    | Hoperands :
        @eval_scalar_boolean_operands_outcome _ _ _ _ _ _ _ _ _ _ _ _
          (SqlSuccess observed) |- _ =>
        rewrite (Hsuccess observed Hoperands), Hacceptance; reflexivity
    end.
  + intros error Heval; inversion Heval; subst.
    eapply Herror; eassumption.
Qed.

(** Adding one exact, error-free AND operand is acceptance-redundant when it
    accepts whenever the original conjunction accepts.  The operand remains
    part of the schedule, so this is not a short-circuit or error-erasure
    lemma. *)
Theorem scalar_expr_conj_list_redundant_operand_acceptance_exact :
  forall site_rows env expressions redundant decide,
    (forall expression,
      In expression expressions ->
      scalar_expr_acceptance_exact_at env expression (decide expression)) ->
    scalar_expr_acceptance_exact_at env redundant (decide redundant) ->
    (scalar_acceptance_fold And_F (map decide expressions) = true ->
      decide redundant = true) ->
    scalar_expr_acceptance_exact_at env
      (SExpr_ConjList site_rows And_F (expressions ++ [redundant]))
      (scalar_acceptance_fold And_F (map decide expressions)).
Proof.
intros site_rows env expressions redundant decide
  Hexpressions Hredundant Himplied.
pose proof (scalar_expr_conj_list_acceptance_exact
  site_rows env And_F (expressions ++ [redundant]) decide) as Hexact.
assert (Hcontracts : forall expression,
  In expression (expressions ++ [redundant]) ->
  scalar_expr_acceptance_exact_at env expression (decide expression)).
{
  intros expression Hin.
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - now apply Hexpressions.
  - destruct Hin as [Hin|Hin]; [now subst expression|contradiction].
}
specialize (Hexact Hcontracts).
replace (scalar_acceptance_fold And_F
  (map decide (expressions ++ [redundant]))) with
  (scalar_acceptance_fold And_F (map decide expressions)) in Hexact.
- exact Hexact.
- rewrite map_app, scalar_acceptance_fold_append.
  cbn [scalar_acceptance_fold scalar_acceptance_combine
    scalar_acceptance_identity].
  destruct (scalar_acceptance_fold And_F (map decide expressions))
    eqn:Hleft; cbn; [now rewrite (Himplied eq_refl)|reflexivity].
Qed.

End ScalarContracts.

Arguments scalar_expr_total_success_at
  {T relname} basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null boolean_schedule env expression.
Arguments scalar_expr_acceptance_exact_at
  {T relname} basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null boolean_schedule env expression accepted.
Arguments scalar_value_list_exact_at
  {T relname} basesort instance unknown symbol_runtime_error
  aggregate_runtime_error value_is_null boolean_schedule env expressions
  expected.

(** Exact row-filter execution from per-row acceptance contracts.  Requiring
    [scalar_expr_acceptance_exact_at] for every reached row rules out runtime-error
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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Theorem eval_filter_rows_acceptance_exact :
  forall env formula rows keep,
    (forall row,
      In row rows ->
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
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
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env other) formula (keep other)).
    { intros other Hin; apply Hexact; now right. }
    split; intro Heval.
    + inversion Heval; subst.
      * exfalso; eapply Herror; eassumption.
      * match goal with
        | Hformula_eval :
            @eval_scalar_boolean_expr_outcome _ _ _ _ _ _ _ _ _ _ _
              (SqlSuccess ?observed),
          Htail_eval :
            @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _
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
    Unlike the global scalar-context relation, the observation below is local
    to two possibly different row environments.  This is the
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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Definition filter_scalar_observation_equiv_at
    (left_env : Env.env T) (left_formula : scalar_expr T relname ScalarResultBoolean)
    (right_env : Env.env T) (right_formula : scalar_expr T relname ScalarResultBoolean) : Prop :=
  (forall left_truth,
    eval_scalar_boolean left_env left_formula (SqlSuccess left_truth) ->
    exists right_truth,
      eval_scalar_boolean right_env right_formula (SqlSuccess right_truth) /\
      Bool.is_true (B T) left_truth = Bool.is_true (B T) right_truth) /\
  (forall right_truth,
    eval_scalar_boolean right_env right_formula (SqlSuccess right_truth) ->
    exists left_truth,
      eval_scalar_boolean left_env left_formula (SqlSuccess left_truth) /\
      Bool.is_true (B T) left_truth = Bool.is_true (B T) right_truth) /\
  forall error,
    eval_scalar_boolean left_env left_formula (SqlError error) <->
    eval_scalar_boolean right_env right_formula (SqlError error).

(** Two exact contracts for the same TRUE/non-TRUE decision induce the local
    observation relation needed by ordered filter transport.  The contracts
    rule out every scalar runtime error on both sides; successful Bool3 values
    may still differ as long as their SQL filter acceptance agrees. *)
Lemma filter_scalar_observation_equiv_at_of_acceptance_exact :
  forall left_env left_formula right_env right_formula accepted,
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule left_env left_formula accepted ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule right_env right_formula accepted ->
    filter_scalar_observation_equiv_at
      left_env left_formula right_env right_formula.
Proof.
intros left_env left_formula right_env right_formula accepted
  [[left_truth [Hleft_truth Hleft_accept]]
    [Hleft_success Hleft_error]]
  [[right_truth [Hright_truth Hright_accept]]
    [Hright_success Hright_error]].
split.
- intros observed Hobserved.
  exists right_truth; split; [exact Hright_truth|].
  now rewrite (Hleft_success observed Hobserved), Hright_accept.
- split.
  + intros observed Hobserved.
    exists left_truth; split; [exact Hleft_truth|].
    now rewrite Hleft_accept, (Hright_success observed Hobserved).
  + intro error; split; intro Herror.
    * exfalso; exact (Hleft_error error Herror).
    * exfalso; exact (Hright_error error Herror).
Qed.

Lemma filter_scalar_observation_equiv_at_sym :
  forall left_env left_formula right_env right_formula,
    filter_scalar_observation_equiv_at
      left_env left_formula right_env right_formula ->
    filter_scalar_observation_equiv_at
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
        filter_scalar_observation_equiv_at
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
      filter_scalar_observation_equiv_at
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    forall right_row left_row,
      Oeset.compare (OTuple T) right_row left_row = Eq ->
      filter_scalar_observation_equiv_at
        (env_t T right_env right_row) right_formula
        (env_t T left_env left_row) left_formula.
Proof.
intros left_env left_formula right_env right_formula
  Hformula right_row left_row Hrow.
apply filter_scalar_observation_equiv_at_sym.
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
      filter_scalar_observation_equiv_at
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
  filter_scalar_observation_equiv_at
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
      boolean_schedule env left_input right_input ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      filter_scalar_observation_equiv_at
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
      filter_scalar_observation_equiv_at
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
  filter_scalar_observation_equiv_at
    (env_t T env right_row) right_formula
    (env_t T env left_row) left_formula).
{
  intros right_row left_row Hrow.
  apply filter_scalar_observation_equiv_at_sym, Hformula.
  now apply Oeset.compare_eq_sym.
}
destruct Hinput as
  [Hleft_input [Hright_input [Hforward [Hbackward Herrors]]]].
assert (Hinput_sym :
  @query_expr_outcome_observation_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule env right_input left_input).
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
    boolean_schedule env left_input right_input).
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

(** Grouped evaluation remains list-ordered internally and crosses to bags
    only at [eval_group_bag_outcome].  These shape facts do not assume a
    deterministic SELECT projection and therefore apply unchanged to typed
    scalar subqueries and schedule-dependent scalar observations. *)
Section TypedGroupShapeFacts.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Theorem eval_groups_global_success_length_le_one :
  forall env select_list having rows output,
    eval_groups env select_list [] having
      (@query_make_groups T env rows []) (SqlSuccess output) ->
    (length output <= 1)%nat.
Proof.
intros env select_list having rows output Heval.
pose proof
  (@eval_groups_success_length_le T
    relname basesort instance unknown symbol_runtime_error
    aggregate_runtime_error value_is_null boolean_schedule
    env select_list [] having
    (@query_make_groups T env rows []) output Heval) as Hlength.
now rewrite query_make_groups_global_length_one in Hlength.
Qed.

(** A successful global group emits at most one row, hence is duplicate-free
    for every semantic row relation.  This is independent of how its typed
    projection was observed. *)
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

End TypedGroupShapeFacts.

(** Complete grouping-reset transport.  The exact group-list contracts are
    stated over typed SELECT expressions and typed grouping keys.  No output
    projection function is selected by this theorem: callers supply whatever
    exact row list their relational scalar evaluation proves. *)
Section TypedGroupBagReset.

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

Theorem eval_group_bag_exact_rows_permut_equiv :
  forall left_schedule right_schedule env select_list group_keys group_terms
      left_having right_having
      (left_bag right_bag :
        Febag.bag (Fecol.CBag (Tuple.CTuple T)))
      (left_rows right_rows :
        list (list (tuple T)) -> list (tuple T)),
    scalar_group_key_terms group_keys = Some group_terms ->
    (forall representative,
      query_same_rows_as_bag representative left_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        @eval_groups_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env select_list group_terms left_having groups outcome <->
        outcome = SqlSuccess (left_rows groups)) ->
    (forall representative,
      query_same_rows_as_bag representative right_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        @eval_groups_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env select_list group_terms right_having groups outcome <->
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
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env select_list group_keys left_having left_bag outcome <->
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env select_list group_keys right_having right_bag outcome.
Proof.
intros left_schedule right_schedule env select_list group_keys group_terms
  left_having right_having left_bag right_bag left_rows right_rows
  Hgroup_terms Hleft_exact Hright_exact Hrows_permut outcome.
split; intro Heval.
- inversion Heval; subst.
  + match goal with
    | Hrepresentative :
        @query_same_rows_as_bag T ?representative left_bag |- _ =>
        destruct (Hleft_exact representative Hrepresentative)
          as [Hnone _];
        congruence
    end.
  + match goal with
    | Hterms : scalar_group_key_terms group_keys = Some ?observed_terms,
      Hrepresentative : query_same_rows_as_bag ?representative left_bag,
      Hgroups : @eval_groups_outcome _ _ _ _ _ _ _ _ left_schedule
        env select_list ?observed_terms left_having _ (SqlError ?error) |- _ =>
        assert (Hobserved : observed_terms = group_terms) by congruence;
        subst observed_terms;
        destruct (Hleft_exact representative Hrepresentative)
          as [_ Hexact];
        apply (proj1 (Hexact (SqlError error))) in Hgroups;
        discriminate
    end.
  + match goal with
    | Hterms : scalar_group_key_terms group_keys = Some ?observed_terms,
      Hrepresentative : query_same_rows_as_bag ?representative left_bag,
      Hgroups : @eval_groups_outcome _ _ _ _ _ _ _ _ left_schedule
        env select_list ?observed_terms left_having _
          (SqlSuccess ?grouped_rows),
      Houtput : query_same_rows_as_bag ?grouped_rows ?output_bag |- _ =>
        assert (Hobserved : observed_terms = group_terms) by congruence;
        subst observed_terms;
        destruct (Hleft_exact representative Hrepresentative)
          as [_ Hleft_groups];
        apply (proj1 (Hleft_groups (SqlSuccess grouped_rows))) in Hgroups;
        inversion Hgroups; subst grouped_rows;
        pose proof (query_elements_same_rows_as_bag T right_bag)
          as Hright_representative;
        pose proof (Hright_exact
          (Febag.elements (Fecol.CBag (Tuple.CTuple T)) right_bag)
          Hright_representative) as Hright_contract;
        cbn in Hright_contract;
        destruct Hright_contract as [Hright_keys Hright_groups];
        eapply EGroupBag_Success with
          (group_terms := group_terms)
          (representative :=
            Febag.elements (Fecol.CBag (Tuple.CTuple T)) right_bag)
          (grouped_rows :=
            right_rows
              (query_make_groups env
                (Febag.elements (Fecol.CBag (Tuple.CTuple T)) right_bag)
                group_terms));
        [ exact Hgroup_terms
        | exact Hright_representative
        | exact Hright_keys
        | apply (proj2 (Hright_groups _)); reflexivity
        | eapply query_same_rows_as_bag_permut_transport;
          [eapply Hrows_permut; eassumption|exact Houtput] ]
    end.
- inversion Heval; subst.
  + match goal with
    | Hrepresentative :
        @query_same_rows_as_bag T ?representative right_bag |- _ =>
        destruct (Hright_exact representative Hrepresentative)
          as [Hnone _];
        congruence
    end.
  + match goal with
    | Hterms : scalar_group_key_terms group_keys = Some ?observed_terms,
      Hrepresentative : query_same_rows_as_bag ?representative right_bag,
      Hgroups : @eval_groups_outcome _ _ _ _ _ _ _ _ right_schedule
        env select_list ?observed_terms right_having _ (SqlError ?error) |- _ =>
        assert (Hobserved : observed_terms = group_terms) by congruence;
        subst observed_terms;
        destruct (Hright_exact representative Hrepresentative)
          as [_ Hexact];
        apply (proj1 (Hexact (SqlError error))) in Hgroups;
        discriminate
    end.
  + match goal with
    | Hterms : scalar_group_key_terms group_keys = Some ?observed_terms,
      Hrepresentative : query_same_rows_as_bag ?representative right_bag,
      Hgroups : @eval_groups_outcome _ _ _ _ _ _ _ _ right_schedule
        env select_list ?observed_terms right_having _
          (SqlSuccess ?grouped_rows),
      Houtput : query_same_rows_as_bag ?grouped_rows ?output_bag |- _ =>
        assert (Hobserved : observed_terms = group_terms) by congruence;
        subst observed_terms;
        destruct (Hright_exact representative Hrepresentative)
          as [_ Hright_groups];
        apply (proj1 (Hright_groups (SqlSuccess grouped_rows))) in Hgroups;
        inversion Hgroups; subst grouped_rows;
        pose proof (query_elements_same_rows_as_bag T left_bag)
          as Hleft_representative;
        pose proof (Hleft_exact
          (Febag.elements (Fecol.CBag (Tuple.CTuple T)) left_bag)
          Hleft_representative) as Hleft_contract;
        cbn in Hleft_contract;
        destruct Hleft_contract as [Hleft_keys Hleft_groups];
        eapply EGroupBag_Success with
          (group_terms := group_terms)
          (representative :=
            Febag.elements (Fecol.CBag (Tuple.CTuple T)) left_bag)
          (grouped_rows :=
            left_rows
              (query_make_groups env
                (Febag.elements (Fecol.CBag (Tuple.CTuple T)) left_bag)
                group_terms));
        [ exact Hgroup_terms
        | exact Hleft_representative
        | exact Hleft_keys
        | apply (proj2 (Hleft_groups _)); reflexivity
        | eapply query_same_rows_as_bag_permut_transport;
          [apply Oeset.permut_sym; eapply Hrows_permut; eassumption
          |exact Houtput] ]
    end.
Qed.

End TypedGroupBagReset.

(** Query-level lift for a canonical typed GROUP node.  [supported] may be
    exact bag equality, projected support, or another reviewed relation, but
    its premise must preserve the complete group-bag relation including exact
    runtime-error categories. *)
Section TypedGroupQueryLift.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Theorem query_expr_group_outcome_equiv_of_supported_child_outcomes :
  forall env select_list group_keys having left right
      (supported : list (tuple T) -> list (tuple T) -> Prop),
    query_expr_outputs
      (QExpr_Group select_list group_keys having left) =
    query_expr_outputs
      (QExpr_Group select_list group_keys having right) ->
    (exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env
        (QExpr_Group select_list group_keys having left) outcome) ->
    (forall left_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule env right (SqlSuccess right_rows) /\
        supported left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          boolean_schedule env left (SqlSuccess left_rows) /\
        supported left_rows right_rows) ->
    (forall error,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left (SqlError error) <->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right (SqlError error)) ->
    (forall left_rows right_rows,
      supported left_rows right_rows ->
      forall outcome,
        eval_group_bag env select_list group_keys having
          (rows_bag T left_rows) outcome <->
        eval_group_bag env select_list group_keys having
          (rows_bag T right_rows) outcome) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env
      (QExpr_Group select_list group_keys having left)
      (QExpr_Group select_list group_keys having right).
Proof.
intros env select_list group_keys having left right supported
  Houtputs Hleft_outcome Hforward Hbackward Hchild_errors Hgroups.
assert (Heval : forall outcome,
  @eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule env
    (QExpr_Group select_list group_keys having left) outcome <->
  @eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule env
    (QExpr_Group select_list group_keys having right) outcome).
{
  intros [output | error].
  - rewrite !eval_query_expr_group_success_iff.
    split.
    + intros [left_rows [output_bag [Hleft [Hgroup Houtput]]]].
      destruct (Hforward left_rows Hleft)
        as [right_rows [Hright Hsupported]].
      exists right_rows, output_bag; repeat split; try assumption.
      now apply (proj1 (Hgroups left_rows right_rows Hsupported
        (SqlSuccess output_bag))).
    + intros [right_rows [output_bag [Hright [Hgroup Houtput]]]].
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

End TypedGroupQueryLift.
