(** Correlation-preserving SQL [NOT IN] case and outcome interfaces. *)

Set Implicit Arguments.

From Stdlib Require Import List NArith.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula
  FTuples GenericInstance OrderedSet Projection SqlBagAbstraction
  SqlErrorSemantics SqlOutcome SqlQueryFacts SqlQuerySemantics SqlQuerySyntax
  Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts RelationalAlgebraFacts ScalarPredicateFacts
  SubqueryFacts TNullSyntax.

Import ListNotations.
Import Tuple.

(** Complete row-level classification for the concrete PostgreSQL Bool3
    instance.  Duplicate candidate occurrences stay in the canonical bag
    representative; the theorem observes them only through SQL existential
    truth, never through Rocq equality. *)
Section TNullMembershipCases.

Lemma tnull_in_rows_unknown_iff :
  forall env select_items rows,
    @in_rows_truth TNull unknown3 NullValues.is_null_value
      env select_items rows = unknown3 <->
    Exists
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = unknown3)
      (@query_canonical_rows TNull rows) /\
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row <> true3)
      (@query_canonical_rows TNull rows).
Proof.
intros env select_items rows.
unfold in_rows_truth.
apply interp_exists_quant_unknown_iff.
Qed.

Theorem tnull_in_rows_semantic_cases :
  forall env select_items rows,
    ((@query_canonical_rows TNull rows = nil) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = false3) \/
    ((exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = true3) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = true3) \/
    ((Exists
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row <> true3)
        (@query_canonical_rows TNull rows)) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = unknown3) \/
    ((@query_canonical_rows TNull rows <> nil) /\
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = false3)
        (@query_canonical_rows TNull rows) /\
      @in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows = false3).
Proof.
intros env select_items rows.
remember
  (@in_rows_truth TNull unknown3 NullValues.is_null_value
    env select_items rows) as truth eqn:Htruth.
destruct truth.
- right; left; split; [|now symmetry].
  apply (@in_rows_true_iff TNull unknown3 NullValues.is_null_value).
  now symmetry.
- destruct (@query_canonical_rows TNull rows) as [|row tail] eqn:Hrows.
  + left; now split.
  + right; right; right.
    split; [discriminate|].
    split.
    * rewrite Forall_forall.
      intros candidate Hin.
      apply (@in_rows_false_iff TNull unknown3
        NullValues.is_null_value env select_items rows).
      -- now symmetry.
      -- rewrite Hrows; exact Hin.
    * now symmetry.
- right; right; left; split; [|now symmetry].
  apply tnull_in_rows_unknown_iff.
  now symmetry.
Qed.

(** [NOT IN] accepts exactly when every candidate comparison is FALSE.
    Empty candidate input is included by the vacuous [Forall]. *)
Theorem tnull_not_in_rows_acceptance_iff_all_false :
  forall env select_items rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull unknown3 NullValues.is_null_value
          env select_items rows)) = true <->
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = false3)
      (@query_canonical_rows TNull rows).
Proof.
intros env select_items rows.
rewrite Bool.true_is_true, negb3_true_iff.
rewrite (@in_rows_false_iff TNull unknown3 NullValues.is_null_value
  env select_items rows).
symmetry; apply Forall_forall.
Qed.

(** Marker form used by anti-existence/count decorrelations: acceptance means
    that neither a TRUE match nor an UNKNOWN comparison exists.  This is the
    NULL-aware condition that a plain anti-semijoin must not omit. *)
Theorem tnull_not_in_rows_acceptance_iff_no_true_or_unknown :
  forall env select_items rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull unknown3 NullValues.is_null_value
          env select_items rows)) = true <->
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items row = true3) /\
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items row = unknown3).
Proof.
intros env select_items rows.
rewrite tnull_not_in_rows_acceptance_iff_all_false.
split.
- intro Hall; rewrite Forall_forall in Hall.
  split; intros [row [Hin Htruth]].
  + specialize (Hall row Hin); congruence.
  + specialize (Hall row Hin); congruence.
- intros [Htrue Hunknown].
  rewrite Forall_forall.
  intros row Hin.
  destruct (@in_row_truth TNull unknown3 NullValues.is_null_value
    env select_items row) eqn:Htruth.
  + exfalso; apply Htrue; exists row; now split.
  + reflexivity.
  + exfalso; apply Hunknown; exists row; now split.
Qed.

End TNullMembershipCases.

(** Safe query-level distribution of [IN] acceptance over UNION ALL.  The
    result is deliberately a filter-acceptance theorem, not equality of the
    complete Bool3 truth: a branch may contribute UNKNOWN without making the
    disjunction accepted.  Child evaluation remains left-to-right, and the
    explicit no-error premises justify the corresponding eager branch form. *)
Section UnionAllMembershipAcceptance.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Lemma query_rows_bag_occ_local : forall rows row,
  Febag.nb_occ (Fecol.CBag (CTuple T)) row (query_rows_bag rows) =
  Oeset.nb_occ (OTuple T) row rows.
Proof.
intros rows row.
unfold query_rows_bag, SqlQuerySemantics.BTupleT.
apply Febag.nb_occ_mk_bag.
Qed.

Local Lemma query_distinct_bag_occurrence_nonzero_iff :
  forall bag row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row
      (query_distinct_bag bag) <> 0%N <->
    Febag.nb_occ (Fecol.CBag (CTuple T)) row bag <> 0%N.
Proof.
intros bag row.
assert (Hdistinct :
  Febag.nb_occ (Fecol.CBag (CTuple T)) row
    (query_distinct_bag bag) =
  if Febag.mem (Fecol.CBag (CTuple T)) row bag then 1%N else 0%N).
{
  unfold query_distinct_bag.
  rewrite Febag.nb_occ_mk_bag.
  change
    (Feset.nb_occ (Fecol.CSet (CTuple T)) row
      (Feset.mk_set (Fecol.CSet (CTuple T))
        (Febag.elements (Fecol.CBag (CTuple T)) bag)) =
     if Febag.mem (Fecol.CBag (CTuple T)) row bag then 1%N else 0%N).
  rewrite Feset.nb_occ_alt, Feset.mem_mk_set.
  rewrite <- Febag.mem_unfold.
  reflexivity.
}
rewrite Hdistinct.
destruct (Febag.mem (Fecol.CBag (CTuple T)) row bag) eqn:Hmem.
- split; [|intros _ Hzero; discriminate Hzero].
  intros _ Hzero.
  rewrite Febag.mem_nb_occ, Hzero in Hmem.
  discriminate Hmem.
- split.
  + intros Hfalse; exfalso; apply Hfalse; reflexivity.
  + intros Hnonzero.
    exfalso.
    apply Hnonzero.
    now apply Febag.not_mem_nb_occ.
Qed.

(** DISTINCT changes multiplicity but not semantic row support. *)
Theorem query_distinct_rows_support_rel :
  forall input output,
    query_same_rows_as_bag output
      (query_distinct_bag (query_rows_bag input)) ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      output input.
Proof.
intros input output Houtput.
pose proof
  ((proj1
    (@query_same_rows_as_bag_iff_occurrences T output
      (query_distinct_bag (query_rows_bag input)))) Houtput) as Hoccurrences.
clear Houtput; rename Hoccurrences into Houtput.
split.
- intros row Hrow.
  assert (Houtput_occ : Oeset.nb_occ (OTuple T) row output <> 0%N).
  { now apply Oeset.In_nb_occ. }
  rewrite Houtput in Houtput_occ.
  apply (proj1
    (@query_distinct_bag_occurrence_nonzero_iff
      (query_rows_bag input) row)) in Houtput_occ.
  rewrite query_rows_bag_occ_local in Houtput_occ.
  apply Oeset.nb_occ_mem in Houtput_occ.
  apply Oeset.mem_bool_true_iff in Houtput_occ.
  destruct Houtput_occ as [other [Hequal Hother]].
  exists other; now split.
- intros row Hrow.
  assert (Hinput_occ : Oeset.nb_occ (OTuple T) row input <> 0%N).
  { now apply Oeset.In_nb_occ. }
  rewrite <- query_rows_bag_occ_local in Hinput_occ.
  rename Hinput_occ into Hinput_bag_occ.
  apply (proj2
    (@query_distinct_bag_occurrence_nonzero_iff
      (query_rows_bag input) row)) in Hinput_bag_occ.
  rewrite <- Houtput in Hinput_bag_occ.
  apply Oeset.nb_occ_mem in Hinput_bag_occ.
  apply Oeset.mem_bool_true_iff in Hinput_bag_occ.
  destruct Hinput_bag_occ as [other [Hequal Hother]].
  exists other; split; [exact Hother|].
  now apply Oeset.compare_eq_sym.
Qed.

(** Membership acceptance is insensitive to DISTINCT, while the underlying
    row bag and its duplicate multiplicities are not identified. *)
Theorem in_rows_acceptance_distinct :
  forall env select_items input output,
    query_same_rows_as_bag output
      (query_distinct_bag (query_rows_bag input)) ->
    Bool.is_true (B T)
      (@in_rows_truth T unknown value_is_null env select_items output) =
    Bool.is_true (B T)
      (@in_rows_truth T unknown value_is_null env select_items input).
Proof.
intros env select_items input output Houtput.
apply in_rows_acceptance_support_rel.
now apply query_distinct_rows_support_rel.
Qed.

Theorem formula_in_union_all_acceptance_exact :
  forall env select_items left right (accept : tuple T -> bool)
      left_accepted right_accepted,
    query_expr_sort left =S= query_expr_sort right ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env left (SqlSuccess rows)) ->
    (exists rows, eval_query env right (SqlSuccess rows)) ->
    (forall row,
      Bool.is_true (B T)
        (@in_row_truth T unknown value_is_null env select_items row) =
      accept row) ->
    (forall rows,
      eval_query env left (SqlSuccess rows) ->
      existsb accept rows = left_accepted) ->
    (forall rows,
      eval_query env right (SqlSuccess rows) ->
      existsb accept rows = right_accepted) ->
    (forall error, ~ eval_query env left (SqlError error)) ->
    (forall error, ~ eval_query env right (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_In select_items (QExpr_Set Union left right))
      (orb left_accepted right_accepted).
Proof.
intros env select_items left right accept left_accepted right_accepted
  Hsort Harguments [left_rows0 Hleft0] [right_rows0 Hright0]
  Haccept Hleft_fixed Hright_fixed Hleft_errors Hright_errors.
eapply formula_in_acceptance_exact
  with (accept := accept).
- exact Harguments.
- exists
    (Febag.elements (Fecol.CBag (CTuple T))
      (query_set_bag_function Union left right
        (query_rows_bag left_rows0) (query_rows_bag right_rows0))).
  apply eval_query_expr_set_success_iff.
  exists left_rows0, right_rows0.
  repeat split; try assumption.
  apply query_elements_same_rows_as_bag.
- exact Haccept.
- intros output Houtput.
  apply eval_query_expr_set_success_iff in Houtput.
  destruct Houtput as
    [left_rows [right_rows [Hleft [Hright Houtput]]]].
  assert (Happend :
    query_same_rows_as_bag (left_rows ++ right_rows)
      (query_set_bag_function Union left right
        (query_rows_bag left_rows) (query_rows_bag right_rows))).
  {
    unfold query_set_bag_function; rewrite Hsort.
    apply query_same_rows_as_bag_iff_occurrences; intro row.
    rewrite Oeset.nb_occ_app.
    unfold query_set_bag, Febag.interp_set_op; cbn.
    rewrite Febag.nb_occ_union, 2 rows_bag_occ; reflexivity.
  }
  assert (Hpermut : Oeset.permut (OTuple T) output
    (left_rows ++ right_rows)).
  {
    eapply query_same_rows_as_bag_permut_between;
      [exact Houtput|exact Happend].
  }
  assert (Hproper : forall first second,
    Oeset.compare (OTuple T) first second = Eq ->
    accept first = accept second).
  {
    intros first second Hequal.
    rewrite <- (Haccept first), <- (Haccept second).
    apply f_equal.
    unfold in_row_truth.
    apply query_tuple_equal_congr.
    + apply Oeset.compare_eq_refl.
    + exact Hequal.
  }
  assert (Hexists : existsb accept output =
    existsb accept (left_rows ++ right_rows)).
  {
    eapply existsb_rel_permut; [|exact Hpermut].
    intros first second Hequal; now apply Hproper.
  }
  rewrite Hexists.
  transitivity
    (Datatypes.orb
      (existsb accept left_rows) (existsb accept right_rows)).
  + apply List.existsb_app.
  + rewrite (Hleft_fixed left_rows Hleft),
      (Hright_fixed right_rows Hright).
    reflexivity.
- intros error Herror.
  inversion Herror; subst.
  + eapply Hleft_errors; eassumption.
  + eapply Hright_errors; eassumption.
Qed.

End UnionAllMembershipAcceptance.

(** Exact formula-level lifts.  The fixed correlated environment is retained
    throughout; argument failures and child query errors remain observable.
    The row predicates below establish, rather than assume, the Bool3 result
    used by the generic [NOT IN] outcome theorem. *)
Section TNullNotInOutcomes.

Context {relname : Type}.

Variable basesort : relname -> Fset.set (A TNull).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple TNull)).
Variable symbol_runtime_error :
  scalar_operator TNull ->
  list (option sql_runtime_error * value TNull) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate TNull ->
  list (option sql_runtime_error * value TNull) ->
  option sql_runtime_error.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error
    NullValues.is_null_value).

Theorem tnull_formula_not_in_accepts_exact_of_all_false :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error TNull
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = false3)
        (@query_canonical_rows TNull rows)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value env
      (FExpr_Not (FExpr_In select_items subquery)) true.
Proof.
intros env select_items subquery Harguments Hsuccess Hall Herrors.
pose proof
  (@formula_not_in_acceptance_exact_of_fixed_truth
    TNull relname basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value
    env select_items subquery false3 Harguments Hsuccess) as Hlift.
assert (Hfixed : forall rows,
  eval_query env subquery (SqlSuccess rows) ->
  @in_rows_truth TNull unknown3 NullValues.is_null_value
    env select_items rows = false3).
{
  intros rows Hrows.
  apply (@in_rows_false_iff TNull unknown3 NullValues.is_null_value
    env select_items rows).
  rewrite <- Forall_forall.
  exact (Hall rows Hrows).
}
specialize (Hlift Hfixed Herrors).
cbn [negb3] in Hlift.
exact Hlift.
Qed.

Theorem tnull_formula_not_in_rejects_exact_of_true_match :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error TNull
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = true3) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value env
      (FExpr_Not (FExpr_In select_items subquery)) false.
Proof.
intros env select_items subquery Harguments Hsuccess Hmatch Herrors.
pose proof
  (@formula_not_in_acceptance_exact_of_fixed_truth
    TNull relname basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value
    env select_items subquery true3 Harguments Hsuccess) as Hlift.
specialize (Hlift (fun rows Hrows =>
  (proj2 (@in_rows_true_iff TNull unknown3 NullValues.is_null_value
    env select_items rows)) (Hmatch rows Hrows)) Herrors).
cbn [negb3] in Hlift.
exact Hlift.
Qed.

Theorem tnull_formula_not_in_rejects_exact_of_unknown_without_match :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error TNull
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Exists
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull unknown3 NullValues.is_null_value
            env select_items row <> true3)
        (@query_canonical_rows TNull rows)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value env
      (FExpr_Not (FExpr_In select_items subquery)) false.
Proof.
intros env select_items subquery Harguments Hsuccess Hunknown Herrors.
pose proof
  (@formula_not_in_acceptance_exact_of_fixed_truth
    TNull relname basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value
    env select_items subquery unknown3 Harguments Hsuccess) as Hlift.
specialize (Hlift (fun rows Hrows =>
  (proj2 (tnull_in_rows_unknown_iff env select_items rows))
    (Hunknown rows Hrows)) Herrors).
cbn [negb3] in Hlift.
exact Hlift.
Qed.

End TNullNotInOutcomes.
