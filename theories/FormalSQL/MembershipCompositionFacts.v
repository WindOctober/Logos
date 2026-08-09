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

(** DISTINCT support and membership-acceptance laws. *)
Section DistinctMembershipAcceptance.

Context {T : Tuple.Rcd} {relname : Type}.

Variable unknown : Bool.b (B T).
Variable value_is_null : value T -> bool.

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

End DistinctMembershipAcceptance.

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
