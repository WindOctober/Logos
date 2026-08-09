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

Context {relname : Type}.

Lemma tnull_in_rows_unknown_iff :
  forall values (subquery : query_expr TNull relname) rows,
    @in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery rows = unknown3 <->
    Exists
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = unknown3)
      (@query_canonical_rows TNull rows) /\
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row <> true3)
      (@query_canonical_rows TNull rows).
Proof.
intros values subquery rows.
unfold in_rows_truth.
apply interp_exists_quant_unknown_iff.
Qed.

Theorem tnull_in_rows_semantic_cases :
  forall values (subquery : query_expr TNull relname) rows,
    ((@query_canonical_rows TNull rows = nil) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = false3) \/
    ((exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = true3) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = true3) \/
    ((Exists
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row <> true3)
        (@query_canonical_rows TNull rows)) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = unknown3) \/
    ((@query_canonical_rows TNull rows <> nil) /\
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = false3)
        (@query_canonical_rows TNull rows) /\
      @in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows = false3).
Proof.
intros values subquery rows.
remember
  (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
    values subquery rows) as truth eqn:Htruth.
destruct truth.
- right; left; split; [|now symmetry].
  apply (@in_rows_true_iff TNull relname unknown3
    NullValues.is_null_value).
  now symmetry.
- destruct (@query_canonical_rows TNull rows) as [|row tail] eqn:Hrows.
  + left; now split.
  + right; right; right.
    split; [discriminate|].
    split.
    * rewrite Forall_forall.
      intros candidate Hin.
      apply (@in_rows_false_iff TNull relname unknown3
        NullValues.is_null_value values subquery rows).
      -- now symmetry.
      -- rewrite Hrows; exact Hin.
    * now symmetry.
- right; right; left; split; [|now symmetry].
  apply (tnull_in_rows_unknown_iff values subquery rows).
  now symmetry.
Qed.

(** [NOT IN] accepts exactly when every candidate comparison is FALSE.
    Empty candidate input is included by the vacuous [Forall]. *)
Theorem tnull_not_in_rows_acceptance_iff_all_false :
  forall values (subquery : query_expr TNull relname) rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
          values subquery rows)) = true <->
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = false3)
      (@query_canonical_rows TNull rows).
Proof.
intros values subquery rows.
rewrite Bool.true_is_true, negb3_true_iff.
rewrite (@in_rows_false_iff TNull relname unknown3
  NullValues.is_null_value values subquery rows).
symmetry; apply Forall_forall.
Qed.

(** Marker form used by anti-existence/count decorrelations: acceptance means
    that neither a TRUE match nor an UNKNOWN comparison exists.  This is the
    NULL-aware condition that a plain anti-semijoin must not omit. *)
Theorem tnull_not_in_rows_acceptance_iff_no_true_or_unknown :
  forall values (subquery : query_expr TNull relname) rows,
    Bool.is_true Bool3
      (negb3
        (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
          values subquery rows)) = true <->
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery row = true3) /\
    (~ exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery row = unknown3).
Proof.
intros values subquery rows.
rewrite (tnull_not_in_rows_acceptance_iff_all_false
  values subquery rows).
split.
- intro Hall; rewrite Forall_forall in Hall.
  split; intros [row [Hin Htruth]].
  + specialize (Hall row Hin); congruence.
  + specialize (Hall row Hin); congruence.
- intros [Htrue Hunknown].
  rewrite Forall_forall.
  intros row Hin.
  destruct (@in_row_truth TNull relname unknown3 NullValues.is_null_value
    values subquery row) eqn:Htruth.
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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

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
  forall values (subquery : query_expr T relname) input output,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) input ->
    query_same_rows_as_bag output
      (query_distinct_bag (query_rows_bag input)) ->
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null
        values subquery output) =
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null
        values subquery input).
Proof.
intros values subquery input output Hinput Houtput.
pose proof
  (@query_distinct_rows_support_rel input output Houtput) as Hsupport.
assert (Houtput_rows :
  Forall (query_row_has_outputs (query_expr_outputs subquery)) output).
{
  rewrite Forall_forall in Hinput |- *.
  intros row Hrow.
  destruct (proj1 Hsupport row Hrow) as
    [input_row [Hinput_row Hequal]].
  eapply (query_row_has_outputs_congr
    (outputs := query_expr_outputs subquery)
    (left := input_row) row).
  - apply Oeset.compare_eq_sym; exact Hequal.
  - exact (Hinput input_row Hinput_row).
}
eapply in_rows_acceptance_support_rel;
  [exact Houtput_rows|exact Hinput|exact Hsupport].
Qed.

Theorem scalar_expr_in_union_all_acceptance_exact :
  forall env arguments left right
      (accept : list (value T) -> tuple T -> bool)
      left_accepted right_accepted,
    query_expr_sort left =S= query_expr_sort right ->
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env left (SqlSuccess rows)) ->
    (exists rows, eval_query env right (SqlSuccess rows)) ->
    (forall rows,
      eval_query env (QExpr_Set Union left right) (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs
          (query_expr_outputs (QExpr_Set Union left right))) rows) ->
    (forall values,
      eval_scalar_values env arguments (SqlSuccess values) ->
      forall row,
      Bool.is_true (B T)
        (@in_row_truth T relname unknown value_is_null
          values (QExpr_Set Union left right) row) =
      accept values row) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env left (SqlSuccess rows) ->
      existsb (accept values) rows = left_accepted) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env right (SqlSuccess rows) ->
      existsb (accept values) rows = right_accepted) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env left (SqlError error)) ->
    (forall error, ~ eval_query env right (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_In arguments (QExpr_Set Union left right))
      (orb left_accepted right_accepted).
Proof.
intros env arguments left right accept left_accepted right_accepted
  Hsort Harguments [left_rows0 Hleft0] [right_rows0 Hright0]
  Houtputs Haccept Hleft_fixed Hright_fixed Hargument_errors
  Hleft_errors Hright_errors.
eapply scalar_expr_in_acceptance_exact
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
- exact Houtputs.
- exact Haccept.
- intros values output Hvalues Houtput.
  pose proof (Houtputs output Houtput) as Houtput_rows.
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
    query_row_has_outputs
      (query_expr_outputs (QExpr_Set Union left right)) first ->
    accept values first = accept values second).
  {
    intros first second Hequal Hfirst_outputs.
    rewrite <- (Haccept values Hvalues first),
      <- (Haccept values Hvalues second).
    apply f_equal.
    eapply in_row_truth_congr; eassumption.
  }
  assert (Hexists : existsb (accept values) output =
    existsb (accept values) (left_rows ++ right_rows)).
  {
    eapply existsb_rel_permut_with_left_property;
      [|exact Hpermut|exact Houtput_rows].
    exact Hproper.
  }
  rewrite Hexists.
  transitivity
    (Datatypes.orb
      (existsb (accept values) left_rows)
      (existsb (accept values) right_rows)).
  + apply List.existsb_app.
  + rewrite (Hleft_fixed values left_rows Hvalues Hleft),
      (Hright_fixed values right_rows Hvalues Hright).
    reflexivity.
- exact Hargument_errors.
- intros error Herror.
  inversion Herror; subst.
  + eapply Hleft_errors; eassumption.
  + eapply Hright_errors; eassumption.
Qed.

End UnionAllMembershipAcceptance.

(** Exact typed-scalar lifts.  The fixed correlated environment is retained
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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error
    NullValues.is_null_value boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error
    NullValues.is_null_value boolean_schedule).

Theorem tnull_scalar_expr_not_in_accepts_exact_of_all_false :
  forall env arguments subquery,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = false3)
        (@query_canonical_rows TNull rows)) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery)) true.
Proof.
intros env arguments subquery Harguments Hsuccess Hall
  Hargument_errors Herrors.
pose proof
  (@scalar_expr_not_in_acceptance_exact_of_fixed_truth
    TNull relname basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value
    boolean_schedule env arguments subquery false3 Harguments Hsuccess)
    as Hlift.
assert (Hfixed : forall values rows,
  eval_scalar_values env arguments (SqlSuccess values) ->
  eval_query env subquery (SqlSuccess rows) ->
  @in_rows_truth TNull relname unknown3 NullValues.is_null_value
    values subquery rows = false3).
{
  intros values rows Hvalues Hrows.
  apply (@in_rows_false_iff TNull relname unknown3
    NullValues.is_null_value values subquery rows).
  rewrite <- Forall_forall.
  exact (Hall values rows Hvalues Hrows).
}
specialize (Hlift Hfixed Hargument_errors Herrors).
cbn [negb3] in Hlift.
exact Hlift.
Qed.

Theorem tnull_scalar_expr_not_in_rejects_exact_of_true_match :
  forall env arguments subquery,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = true3) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery)) false.
Proof.
intros env arguments subquery Harguments Hsuccess Hmatch
  Hargument_errors Herrors.
pose proof
  (@scalar_expr_not_in_acceptance_exact_of_fixed_truth
    TNull relname basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value
    boolean_schedule env arguments subquery true3 Harguments Hsuccess)
    as Hlift.
specialize (Hlift (fun values rows Hvalues Hrows =>
  (proj2 (@in_rows_true_iff TNull relname unknown3
    NullValues.is_null_value values subquery rows))
    (Hmatch values rows Hvalues Hrows)) Hargument_errors Herrors).
cbn [negb3] in Hlift.
exact Hlift.
Qed.

Theorem tnull_scalar_expr_not_in_rejects_exact_of_unknown_without_match :
  forall env arguments subquery,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      Exists
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = unknown3)
        (@query_canonical_rows TNull rows) /\
      Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row <> true3)
        (@query_canonical_rows TNull rows)) ->
    (forall error,
      ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery)) false.
Proof.
intros env arguments subquery Harguments Hsuccess Hunknown
  Hargument_errors Herrors.
pose proof
  (@scalar_expr_not_in_acceptance_exact_of_fixed_truth
    TNull relname basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value
    boolean_schedule env arguments subquery unknown3 Harguments Hsuccess)
    as Hlift.
specialize (Hlift (fun values rows Hvalues Hrows =>
  (proj2 (tnull_in_rows_unknown_iff values subquery rows))
    (Hunknown values rows Hvalues Hrows)) Hargument_errors Herrors).
cbn [negb3] in Hlift.
exact Hlift.
Qed.

End TNullNotInOutcomes.
