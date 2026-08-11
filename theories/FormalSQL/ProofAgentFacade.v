(******************************************************************************)
(** Stable, compact TNull proof surface for generated FormalSQL developments. **)
(******************************************************************************)

From SQLFS Require Export SqlQuerySyntax SqlQuerySemantics SqlQueryContexts.
From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Join Env Bool3 Formula Projection SqlOutcome
  SqlQueryWellFormed SqlBagAbstraction SqlQueryFacts SqlErrorSemantics
  SchemaConstraints.
From Logos.FormalSQL Require Import
  TNullSyntax SchemaCardinality QueryCardinality
  CardinalityCombinators
  (* OrderedQueryFacts is re-exported below for facade clients. *)
  AggregateRuntimeFacts GroupingRewriteFacts RelationalAlgebraFacts
  GroupedFilterOutcomeFacts NumericRegroupFacts RenameTransportFacts.
From Logos.FormalSQL Require Export
  QueryTNullSyntax OrderedQueryFacts PossibleOutcomeFacts.
From Stdlib Require Import
  List Lia NArith SetoidList SetoidPermutation Sorting.Permutation.

Import ListNotations.
Import Tuple.

(** These aliases deliberately hide the module paths of FormalSQL's tuple and
    finite-collection implementation.  They add no equality or quotienting. *)
Definition TNullAttribute : Type := attribute TNull.
Definition TNullRow : Type := tuple TNull.
Definition TNullValue : Type := value TNull.
Definition TNullAttributeSet : Type := Fset.set (A TNull).
Definition TNullEnvironment : Type := Env.env TNull.
Definition TNullScalarValueExpr : Type :=
  @scalar_expr TNull relname ScalarResultValue.
Definition TNullScalarBooleanExpr : Type :=
  @scalar_expr TNull relname ScalarResultBoolean.
Definition TNullQuerySelectItem : Type :=
  (TNullScalarValueExpr * attribute TNull)%type.
Definition TNullQuerySelectList : Type := list TNullQuerySelectItem.
Definition TNullQueryGroupingSet : Type :=
  (TNullQuerySelectList * list TNullScalarValueExpr)%type.
Definition TNullQueryExpr : Type := QueryExpr.
Definition TNullQueryProgram : Type := QueryProgram.
Definition TNullDatabase : Type := db_state.
Definition TNullRowsOutcome : Type := sql_outcome (list TNullRow).

Definition TNullRowOrder : Oeset.Rcd TNullRow := OTuple TNull.
Definition TNullAttributeOrder : Oset.Rcd TNullAttribute := OAtt TNull.
Definition TNullRowCollection : Fecol.Rcd TNullRowOrder := CTuple TNull.
Definition TNullRowBagRecord : Febag.Rcd TNullRowOrder :=
  Fecol.CBag TNullRowCollection.
Definition TNullRowBag : Type := Febag.bag TNullRowBagRecord.

Definition TNullRowEq (left right : TNullRow) : Prop :=
  Oeset.compare TNullRowOrder left right = Eq.

(** Stable equivalence-law names for the semantic tuple equality used by the
    facade.  These avoid repeatedly exposing the ordered-set implementation
    when generated proofs compose local row correspondences. *)
Lemma tnull_row_eq_refl :
  forall row, TNullRowEq row row.
Proof.
intro row; unfold TNullRowEq.
apply Oeset.compare_eq_refl.
Qed.

Lemma tnull_row_eq_sym :
  forall left right,
    TNullRowEq left right ->
    TNullRowEq right left.
Proof.
intros left right Hequal; unfold TNullRowEq in *.
now apply Oeset.compare_eq_sym.
Qed.

Lemma tnull_row_eq_trans :
  forall first second third,
    TNullRowEq first second ->
    TNullRowEq second third ->
    TNullRowEq first third.
Proof.
intros first second third Hfirst Hsecond; unfold TNullRowEq in *.
eapply Oeset.compare_eq_trans; eassumption.
Qed.

Definition TNullRowPermut (left right : list TNullRow) : Prop :=
  Oeset.permut TNullRowOrder left right.

Definition TNullAttributeSetEq
    (left right : TNullAttributeSet) : Prop :=
  left =S= right.

Definition TNullBagEq (left right : TNullRowBag) : Prop :=
  bag_eq TNull left right.

Definition TNullRowsBag (rows : list TNullRow) : TNullRowBag :=
  rows_bag TNull rows.

(** Semantic row permutation induces equality of the represented bags. *)
Lemma tnull_row_permut_implies_rows_bag_eq :
  forall left right,
    TNullRowPermut left right ->
    TNullBagEq (TNullRowsBag left) (TNullRowsBag right).
Proof.
intros left right Hpermut.
unfold TNullRowPermut, TNullBagEq, TNullRowsBag, bag_eq, rows_bag in *.
rewrite Febag.nb_occ_equal; intro row.
rewrite 2 Febag.nb_occ_mk_bag.
now apply Oeset.permut_nb_occ.
Qed.

(** The facade intentionally leaves typed Project, Filter, Group, Join, and
    GroupingSets side conditions visible.  Their canonical theorem families
    are re-exported from [PossibleOutcomeFacts]; no structural tactic guesses
    predicate acceptance, scalar safety, grouping, or shared-child evidence. *)
(** Stable names for proof boundaries that generated developments must keep
    separate.  These are transparent aliases of the authoritative FormalSQL
    predicates, not alternate semantics. *)
Definition TNullQueryExprOutcome
    (db : TNullDatabase) (env : TNullEnvironment)
    (query : TNullQueryExpr) (outcome : TNullRowsOutcome) : Prop :=
  eval_query_expr_outcome_in_env db env query outcome.

Definition TNullQueryExprOutcomeEq
    (db : TNullDatabase) (env : TNullEnvironment)
    (left right : TNullQueryExpr) : Prop :=
  query_expr_outcome_equiv_in_env db env left right.

(** The complete possible query-outcome relation with successful ordered rows
    abstracted to bags.  Runtime-error categories and the quantification over
    all legal Boolean schedules remain part of the authoritative semantics. *)
Definition TNullQueryPossibleBagOutcomes
    (db : TNullDatabase) (env : TNullEnvironment)
    (query : TNullQueryExpr) : sql_outcome TNullRowBag -> Prop :=
  @query_possible_bag_outcomes TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env query.

(** Stable TNull name for typed possible-bag/outcome equivalence.  This is a
    transparent alias: recovering ordered possible outcomes still requires
    [BagClosed] for both sides through the exported FormalSQL bridge. *)
Definition TNullQueryExprPossibleBagOutcomeEq
    (db : TNullDatabase) (env : TNullEnvironment)
    (left right : TNullQueryExpr) : Prop :=
  @query_expr_possible_bag_outcome_equiv TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env left right.

(** Conservative structural automation for operators that only forward or
    transparently reshape an already proved exact outcome equivalence.  Typed
    Project, Filter, Group, Join, GroupingSets, RowMap, and Window remain
    explicit semantic boundaries. *)
Ltac logos :=
  repeat first
    [ assumption
    | apply query_expr_distinct_possible_outcome_equiv_congr
    | apply query_expr_order_by_possible_outcome_equiv_congr
    | apply query_expr_offset_possible_outcome_equiv_congr
    | apply query_expr_fetch_possible_outcome_equiv_congr
    | apply query_expr_rank_possible_outcome_equiv_congr
    | apply query_expr_distinct_outcome_equiv_congr
    | apply query_expr_order_by_outcome_equiv_congr
    | apply query_expr_offset_outcome_equiv_congr
    | apply query_expr_fetch_outcome_equiv_congr
    | apply query_expr_rank_outcome_equiv_congr ].

(** Compact observation-certificate vocabulary shared by equivalence and
    counterexample proofs.  These are transparent aliases of the exact
    ordered-row relation and the authoritative query evaluator. *)
Definition TNullRowsObservationEq
    (left right : list TNullRow) : Prop :=
  @ordered_rows_equiv TNull left right.

Definition TNullQueryExprObservationFunctional
    (db : TNullDatabase) (env : TNullEnvironment)
    (query : TNullQueryExpr) : Prop :=
  successful_relation_functional TNullRowsObservationEq
    (TNullQueryExprOutcome db env query).

Definition TNullQuerySuccessBag
    (db : TNullDatabase) (env : TNullEnvironment)
    (query : TNullQueryExpr) (bag : TNullRowBag) : Prop :=
  exists boolean_schedule : boolean_site -> boolean_evaluation_order,
    @query_success_bags TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      boolean_schedule env query bag.

Lemma tnull_query_success_outcome_is_success_bag :
  forall db env query rows,
    TNullQueryExprOutcome db env query (SqlSuccess rows) ->
    TNullQuerySuccessBag db env query (TNullRowsBag rows).
Proof.
intros db env query rows [boolean_schedule Hrows].
exists boolean_schedule, rows; split; [exact Hrows|apply bag_eq_refl].
Qed.

Definition TNullQuerySuccessBagFunctional
    (db : TNullDatabase) (env : TNullEnvironment)
    (query : TNullQueryExpr) : Prop :=
  forall first second,
    TNullQuerySuccessBag db env query first ->
    TNullQuerySuccessBag db env query second ->
    TNullBagEq first second.

Definition TNullQueryExprOutcomeSeparation
    (db : TNullDatabase) (env : TNullEnvironment)
    (left right : TNullQueryExpr) : Prop :=
  outcome_relation_separation TNullRowsObservationEq
    (TNullQueryExprOutcome db env left)
    (TNullQueryExprOutcome db env right).

(** A directional FormalSQL countermodel refutes query outcome equivalence;
    no choice of a single representative execution is trusted. *)
Lemma tnull_query_expr_outcome_separation_sound :
  forall db env left right,
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryExprOutcomeEq db env left right.
Proof.
intros db env left right Hseparation Hequivalent.
destruct Hequivalent as [_ Hobservations].
apply
  (@outcome_relation_separation_sound
    (list TNullRow) TNullRowsObservationEq
    (TNullQueryExprOutcome db env left)
    (TNullQueryExprOutcome db env right) Hseparation).
exact Hobservations.
Qed.

(** One successful observation separates two relational query evaluators when
    every successful observation on the opposite side has a different row
    count.  Ordered-row equivalence preserves length, so no opposite success
    can match the witness.  Error outcomes remain in both relations and are
    neither discarded nor assumed absent. *)
Lemma tnull_query_expr_outcome_separation_of_left_success_length_difference :
  forall db env left right left_rows,
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    (forall right_rows,
      TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
      List.length left_rows <> List.length right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
Proof.
intros db env left right left_rows Hleft Hdifferent.
eapply OutcomeSeparationLeftSuccess; [exact Hleft |].
intros right_rows Hright Hequivalent.
apply (Hdifferent right_rows Hright).
unfold TNullRowsObservationEq in Hequivalent.
now apply ordered_rows_equiv_length in Hequivalent.
Qed.

Lemma tnull_query_expr_outcome_separation_of_right_success_length_difference :
  forall db env left right right_rows,
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    (forall left_rows,
      TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
      List.length left_rows <> List.length right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
Proof.
intros db env left right right_rows Hright Hdifferent.
eapply OutcomeSeparationRightSuccess; [exact Hright |].
intros left_rows Hleft Hequivalent.
apply (Hdifferent left_rows Hleft).
unfold TNullRowsObservationEq in Hequivalent.
now apply ordered_rows_equiv_length in Hequivalent.
Qed.

Lemma tnull_query_expr_outcome_separation_of_right_functional_observation_difference :
  forall db env left right left_rows right_rows,
    TNullQueryExprObservationFunctional db env right ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullRowsObservationEq left_rows right_rows ->
    TNullQueryExprOutcomeSeparation db env left right.
Proof.
intros db env left right left_rows right_rows
  Hfunctional Hleft Hright Hdifferent.
eapply OutcomeSeparationLeftSuccess; [exact Hleft |].
intros candidate Hcandidate Hequivalent.
apply Hdifferent.
eapply ordered_rows_equiv_trans; [exact Hequivalent |].
exact (Hfunctional candidate right_rows Hcandidate Hright).
Qed.

Lemma tnull_query_expr_outcome_separation_of_left_functional_observation_difference :
  forall db env left right left_rows right_rows,
    TNullQueryExprObservationFunctional db env left ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullRowsObservationEq left_rows right_rows ->
    TNullQueryExprOutcomeSeparation db env left right.
Proof.
intros db env left right left_rows right_rows
  Hfunctional Hleft Hright Hdifferent.
eapply OutcomeSeparationRightSuccess; [exact Hright |].
intros candidate Hcandidate Hequivalent.
apply Hdifferent.
eapply ordered_rows_equiv_trans.
- apply ordered_rows_equiv_sym.
  exact (Hfunctional candidate left_rows Hcandidate Hleft).
- exact Hequivalent.
Qed.

(** A concrete bag difference is a relational countermodel only when the
    opposite success-bag relation is functional.  This bridge packages that
    universal argument while retaining errors as separate outcomes. *)
Lemma tnull_query_expr_outcome_separation_of_right_functional_bag_difference :
  forall db env left right left_rows right_rows,
    TNullQuerySuccessBagFunctional db env right ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullBagEq (TNullRowsBag left_rows) (TNullRowsBag right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
Proof.
intros db env left right left_rows right_rows
  Hfunctional Hleft Hright Hdifferent.
eapply OutcomeSeparationLeftSuccess; [exact Hleft |].
intros candidate Hcandidate Hequivalent.
unfold TNullBagEq, TNullRowsBag in Hdifferent.
apply Hdifferent.
eapply bag_eq_trans.
- apply (@ordered_rows_equiv_implies_bag_eq TNull left_rows candidate).
  exact Hequivalent.
- apply Hfunctional.
  + now apply tnull_query_success_outcome_is_success_bag.
  + now apply tnull_query_success_outcome_is_success_bag.
Qed.

Lemma tnull_query_expr_outcome_separation_of_left_functional_bag_difference :
  forall db env left right left_rows right_rows,
    TNullQuerySuccessBagFunctional db env left ->
    TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
    TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
    ~ TNullBagEq (TNullRowsBag left_rows) (TNullRowsBag right_rows) ->
    TNullQueryExprOutcomeSeparation db env left right.
Proof.
intros db env left right left_rows right_rows
  Hfunctional Hleft Hright Hdifferent.
eapply OutcomeSeparationRightSuccess; [exact Hright |].
intros candidate Hcandidate Hequivalent.
unfold TNullBagEq, TNullRowsBag in Hdifferent.
apply Hdifferent.
eapply bag_eq_trans.
- apply bag_eq_sym, Hfunctional.
  + exact (tnull_query_success_outcome_is_success_bag
      db env left candidate Hcandidate).
  + exact (tnull_query_success_outcome_is_success_bag
      db env left left_rows Hleft).
- apply (@ordered_rows_equiv_implies_bag_eq TNull candidate right_rows).
  exact Hequivalent.
Qed.

Definition TNullQueryProgramOutcomeEq
    (db : TNullDatabase) (env : TNullEnvironment)
    (left right : TNullQueryProgram) : Prop :=
  query_program_outcome_equiv_in_env db env left right.

(** A separated statement refutes any program equivalence whose head contains
    that statement.  This is the minimal program lift needed by generated
    countermodels; it does not inspect or constrain the remaining statements. *)
Lemma tnull_query_program_head_separation_sound :
  forall db env left right left_tail right_tail,
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryProgramOutcomeEq db env
        (left :: left_tail) (right :: right_tail).
Proof.
intros db env left right left_tail right_tail Hseparation Hprogram.
apply (tnull_query_expr_outcome_separation_sound
  db env left right Hseparation).
exact (proj1 Hprogram).
Qed.

(** The same statement-local certificate may occur after any equally long
    pair of program prefixes.  No property of those prefixes is required:
    pointwise program equivalence would itself expose equivalence at the
    separated statement. *)
Lemma tnull_query_program_prefix_separation_sound :
  forall db env left_prefix right_prefix left right left_tail right_tail,
    length left_prefix = length right_prefix ->
    TNullQueryExprOutcomeSeparation db env left right ->
    ~ TNullQueryProgramOutcomeEq db env
        (left_prefix ++ left :: left_tail)
        (right_prefix ++ right :: right_tail).
Proof.
intros db env left_prefix.
induction left_prefix as [| left_head left_prefix IH];
  intros [| right_head right_prefix] left right left_tail right_tail
    Hlength Hseparation Hprogram;
  cbn in Hlength; try discriminate.
- cbn in Hprogram.
  apply (tnull_query_expr_outcome_separation_sound
    db env left right Hseparation).
  exact (proj1 Hprogram).
- injection Hlength as Hlength.
  cbn in Hprogram.
  destruct Hprogram as [_ Hprogram].
  eapply IH; eassumption.
Qed.

Definition TNullRowLabels (row : TNullRow) : TNullAttributeSet :=
  labels TNull row.

Definition TNullRowValue
    (row : TNullRow) (attribute : TNullAttribute) : TNullValue :=
  dot TNull row attribute.

(** Stable list-level names for the two join expansions used by the existing
    total-functional combinators. *)
Definition TNullThetaJoinRows
    (join : TNullRow -> TNullRow -> TNullRow)
    (accept : TNullRow -> TNullRow -> bool)
    (left right : list TNullRow) : list TNullRow :=
  theta_join_list TNullRow join accept left right.

Definition TNullLeftJoinRows
    (join : TNullRow -> TNullRow -> TNullRow)
    (accept : TNullRow -> TNullRow -> bool)
    (pad : TNullRow -> TNullRow)
    (left right : list TNullRow) : list TNullRow :=
  TNullThetaJoinRows join accept left right ++
  map pad
    (filter
      (fun left_row => negb (existsb (accept left_row) right)) left).

(** Structural-equality wrapper for the existing theta-join combinator. *)
Lemma tnull_map_theta_join_total_functional :
  forall (B : Type)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> B) left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (TNullThetaJoinRows join accept left right) =
    map emit left.
Proof.
intros B join accept project emit left right Hproject Htotal Hfunctional.
unfold TNullThetaJoinRows.
now apply map_theta_join_total_functional.
Qed.

(** Structural-equality wrapper for the existing left-join combinator. *)
Lemma tnull_map_left_join_total_functional :
  forall (B : Type)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> B) (pad : TNullRow -> TNullRow)
      left right,
    (forall left_row right_row,
      project (join left_row right_row) = emit left_row) ->
    (forall left_row,
      In left_row left -> project (pad left_row) = emit left_row) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    map project (TNullLeftJoinRows join accept pad left right) =
    map emit left.
Proof.
intros B join accept project emit pad left right
  Hproject Hpad Htotal Hfunctional.
unfold TNullLeftJoinRows, TNullThetaJoinRows.
rewrite map_app.
now apply map_left_join_total_functional.
Qed.

(** Extensional counterpart of the structural theta-join law.  This is the
    appropriate boundary for FormalSQL rows: it preserves multiplicity while
    quotienting only the hidden tuple representation. *)
Lemma tnull_map_theta_join_total_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit left).
Proof.
intros join accept project emit left right Hproject Htotal Hfunctional.
unfold TNullThetaJoinRows, theta_join_list.
induction left as [|left_row left_rows IH]; cbn.
- unfold TNullRowPermut; apply Oeset.permut_refl.
- destruct
    (filter_singleton_of_nonempty_length_le_one
      TNullRow (accept left_row) right)
    as [right_row Hright].
  + apply Htotal; now left.
  + apply Hfunctional; now left.
  + change
      (TNullRowPermut
        (map project
          (map (join left_row) (filter (accept left_row) right) ++
           flat_map
             (fun row => d_join_list TNullRow join accept row right)
             left_rows))
        (emit left_row :: map emit left_rows)).
    rewrite Hright; cbn.
    unfold TNullRowPermut in *.
    apply
      (proj1
        (Oeset.permut_cons TNullRowOrder
          (project (join left_row right_row)) (emit left_row)
          (map project
            (flat_map
              (fun row => d_join_list TNullRow join accept row right)
              left_rows))
          (map emit left_rows)
          (Hproject left_row right_row))).
    apply IH.
    * intros row Hrow; apply Htotal; now right.
    * intros row Hrow; apply Hfunctional; now right.
Qed.

(** The projection law for a theta join is needed only for pairs that are
    actually selected from the two input lists.  This membership-aware form
    is strictly easier to use with schema-derived row facts: malformed or
    unreachable tuples impose no projection obligation. *)
Lemma tnull_map_theta_join_total_functional_permut_accepted :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit left).
Proof.
intros join accept project emit left right Hproject Htotal Hfunctional.
unfold TNullThetaJoinRows, theta_join_list.
induction left as [|left_row left_rows IH]; cbn.
- unfold TNullRowPermut; apply Oeset.permut_refl.
- destruct
    (filter_singleton_of_nonempty_length_le_one
      TNullRow (accept left_row) right)
    as [right_row Hright].
  + apply Htotal; now left.
  + apply Hfunctional; now left.
  + assert (Hselected : In right_row (filter (accept left_row) right)).
    { rewrite Hright; now left. }
    apply filter_In in Hselected.
    destruct Hselected as [Hright_in Haccepted].
    change
      (TNullRowPermut
        (map project
          (map (join left_row) (filter (accept left_row) right) ++
           flat_map
             (fun row => d_join_list TNullRow join accept row right)
             left_rows))
        (emit left_row :: map emit left_rows)).
    rewrite Hright; cbn.
    unfold TNullRowPermut in *.
    apply
      (proj1
        (Oeset.permut_cons TNullRowOrder
          (project (join left_row right_row)) (emit left_row)
          (map project
            (flat_map
              (fun row => d_join_list TNullRow join accept row right)
              left_rows))
          (map emit left_rows)
          (Hproject left_row right_row
            (or_introl eq_refl) Hright_in Haccepted))).
    apply IH.
    * intros row other Hrow Hother Haccept.
      apply Hproject; [now right | exact Hother | exact Haccept].
    * intros row Hrow; apply Htotal; now right.
    * intros row Hrow; apply Hfunctional; now right.
Qed.

(** Partial-functional theta join as an occurrence-preserving semijoin.  The
    right payload is erased only for accepted pairs; unmatched left rows are
    omitted rather than forcing a totality witness. *)
Lemma tnull_map_theta_join_functional_permut_filter_exists :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (map emit
        (filter
          (fun left_row => existsb (accept left_row) right) left)).
Proof.
intros join accept project emit left right Hproject Hfunctional.
unfold TNullRowEq, TNullRowPermut, TNullThetaJoinRows in *.
now apply map_theta_join_functional_permut_filter_exists.
Qed.

(** Extensional left-join corollary.  Totality makes the padded branch empty;
    the padding premise is retained to mirror the structural API. *)
Lemma tnull_map_left_join_total_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (pad : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      TNullRowEq (project (pad left_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullLeftJoinRows join accept pad left right))
      (map emit left).
Proof.
intros join accept project emit pad left right
  Hproject _Hpad Htotal Hfunctional.
unfold TNullLeftJoinRows.
rewrite (anti_filter_empty_of_total_match
  TNullRow TNullRow accept left right Htotal).
cbn [map]; rewrite app_nil_r.
now apply tnull_map_theta_join_total_functional_permut.
Qed.

(** Extensional partial-functional LEFT JOIN law.  A left occurrence may have
    no match; in that case the padded branch supplies its one projected output.
    Duplicate left occurrences remain duplicate occurrences. *)
Lemma tnull_map_left_join_functional_permut :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (pad : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      TNullRowEq (project (pad left_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    TNullRowPermut
      (map project (TNullLeftJoinRows join accept pad left right))
      (map emit left).
Proof.
intros join accept project emit pad left right Hproject Hpad Hfunctional.
unfold TNullRowEq, TNullRowPermut,
  TNullLeftJoinRows, TNullThetaJoinRows in *.
now apply map_left_join_functional_permut.
Qed.

(** Stable extensional introduction rule for FormalSQL rows. *)
Lemma tnull_row_eq_of_labels_and_values :
  forall left right,
    TNullAttributeSetEq (TNullRowLabels left) (TNullRowLabels right) ->
    (forall attribute,
      attribute inS TNullRowLabels left ->
      TNullRowValue left attribute = TNullRowValue right attribute) ->
    TNullRowEq left right.
Proof.
intros left right Hlabels Hvalues.
unfold TNullRowEq, TNullRowOrder.
apply (proj2 (@tuple_eq TNull left right)); split.
- exact Hlabels.
- exact Hvalues.
Qed.

(** Select exactly the groups whose representative key is accepted when all
    accepted rows have one nonempty grouping key.  Empty input remains empty;
    a nonempty accepted slice forms one group in FormalSQL's accumulator
    order. *)
Lemma tnull_query_groups_matching_one_key :
  forall env group_terms rows
      (keep : list TNullValue -> bool) key,
    group_terms <> nil ->
    (forall row,
      In row
        (filter
          (fun item =>
            keep (query_grouping_key env group_terms item)) rows) ->
      query_grouping_key env group_terms row = key) ->
    filter
      (fun members =>
        match members with
        | nil => false
        | row :: _ => keep (query_grouping_key env group_terms row)
        end)
      (@query_make_groups TNull env rows group_terms) =
    match
      filter
        (fun item =>
          keep (query_grouping_key env group_terms item)) rows
    with
    | nil => nil
    | _ :: _ =>
        [rev
          (filter
            (fun item =>
              keep (query_grouping_key env group_terms item)) rows)]
    end.
Proof.
intros env group_terms rows keep key Hterms Hconstant.
rewrite <-
  (query_make_groups_filter_by_key_exact
    TNull env group_terms rows keep Hterms).
exact
  (@query_make_groups_constant_nonempty_key TNull env
    (filter
      (fun item =>
        keep (query_grouping_key env group_terms item)) rows)
    group_terms key Hterms Hconstant).
Qed.

(** A total-functional theta join emits one left observation when [witness]
    is true and nothing when it is false.  The false branch requires exact
    absence of accepted pairs; the true branch preserves every duplicate left
    occurrence. *)
Lemma tnull_theta_join_by_witness :
  forall (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow)
      (left right : list TNullRow) (witness : bool),
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (witness = true ->
      forall left_row,
        In left_row left ->
        exists right_row,
          In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (length (filter (accept left_row) right) <= 1)%nat) ->
    (witness = false ->
      forall left_row right_row,
        In left_row left ->
        In right_row right ->
        accept left_row right_row = false) ->
    TNullRowPermut
      (map project (TNullThetaJoinRows join accept left right))
      (if witness then map emit left else nil).
Proof.
intros join accept project emit left right witness
  Hproject Htotal Hfunctional Hnone.
destruct witness eqn:Hwitness.
- cbn.
  apply tnull_map_theta_join_total_functional_permut.
  + exact Hproject.
  + now apply Htotal.
  + exact Hfunctional.
- cbn.
  unfold TNullThetaJoinRows.
  induction left as [|left_row left_rows IH]; cbn.
  + unfold TNullRowPermut; constructor.
  + assert (Hempty : filter (accept left_row) right = nil).
    {
      apply (@ListFacts.filter_false TNullRow (accept left_row) right).
      intros right_row Hright.
      apply Hnone; [reflexivity | now left | exact Hright].
    }
    change
      (TNullRowPermut
        (map project
          (map (join left_row) (filter (accept left_row) right) ++
           flat_map
             (fun row => d_join_list TNullRow join accept row right)
             left_rows))
        nil).
    rewrite Hempty; cbn.
    apply IH.
    * intro Himpossible; discriminate.
    * intros row Hrow; apply Hfunctional; now right.
    * intros _ row other Hrow Hother.
      apply Hnone; [reflexivity | now right | exact Hother].
Qed.

(** Duplicate-freedom transports across the existing total-functional theta
    join permutation.  This is the list-level bridge needed before proving a
    projected successful bag is fixed by SQL DISTINCT. *)
Lemma tnull_total_functional_theta_project_nodup :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    NoDupA TNullRowEq (map emit left) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
Proof.
intros join accept project emit left right
  Hproject Htotal Hfunctional Hnodup.
pose proof
  (tnull_map_theta_join_total_functional_permut
    join accept project emit left right Hproject Htotal Hfunctional)
  as Hpermut.
unfold TNullRowPermut, TNullRowEq, TNullRowOrder in Hpermut, Hnodup |- *.
eapply PermutationA_preserves_NoDupA.
- apply oeset_compare_Equivalence.
- apply related_permut_PermutationA.
  + apply oeset_compare_Equivalence.
  + apply Oeset.permut_sym; exact Hpermut.
- exact Hnodup.
Qed.

(** Duplicate-freedom needs the projection law only on accepted input pairs,
    matching the membership-aware theta-join permutation above. *)
Lemma tnull_total_functional_theta_project_nodup_accepted :
  forall
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project emit : TNullRow -> TNullRow) left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      TNullRowEq (project (join left_row right_row)) (emit left_row)) ->
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    NoDupA TNullRowEq (map emit left) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
Proof.
intros join accept project emit left right
  Hproject Htotal Hfunctional Hnodup.
pose proof
  (tnull_map_theta_join_total_functional_permut_accepted
    join accept project emit left right Hproject Htotal Hfunctional)
  as Hpermut.
unfold TNullRowPermut, TNullRowEq, TNullRowOrder in Hpermut, Hnodup |- *.
eapply PermutationA_preserves_NoDupA.
- apply oeset_compare_Equivalence.
- apply related_permut_PermutationA.
  + apply oeset_compare_Equivalence.
  + apply Oeset.permut_sym; exact Hpermut.
- exact Hnodup.
Qed.

(** A partial-functional theta join preserves output duplicate-freedom when a
    source key is duplicate-free and equality of accepted projected outputs
    reflects equality of that key.  The premise consumes primary-key-style
    [NoDupA] evidence directly and does not require every left row to match. *)
Lemma tnull_functional_theta_project_nodup_of_key_reflection :
  forall (Key : Type) (key_relation : Key -> Key -> Prop)
      (key : TNullRow -> Key)
      (join : TNullRow -> TNullRow -> TNullRow)
      (accept : TNullRow -> TNullRow -> bool)
      (project : TNullRow -> TNullRow) left right,
    NoDupA key_relation (map key left) ->
    (forall left_row,
      In left_row left ->
      (List.length (filter (accept left_row) right) <= 1)%nat) ->
    (forall left_first left_second right_first right_second,
      In left_first left -> In left_second left ->
      In right_first right -> In right_second right ->
      accept left_first right_first = true ->
      accept left_second right_second = true ->
      TNullRowEq
        (project (join left_first right_first))
        (project (join left_second right_second)) ->
      key_relation (key left_first) (key left_second)) ->
    NoDupA TNullRowEq
      (map project (TNullThetaJoinRows join accept left right)).
Proof.
intros Key key_relation key join accept project left right
  Hkeys Hfunctional Hreflect.
unfold TNullThetaJoinRows, theta_join_list, d_join_list.
eapply NoDupA_map_of_reflection
  with
    (source_relation :=
      fun left_output right_output =>
        TNullRowEq (project left_output) (project right_output)).
- eapply NoDupA_flat_map_filter_map_functional_reflection
    with
      (source_relation :=
        fun left_row right_row =>
          key_relation (key left_row) (key right_row)).
  + now apply NoDupA_map_preimage.
  + exact Hfunctional.
  + intros l1 l2 r1 r2 Hl1 Hl2 Hr1 Hr2 Ha1 Ha2 Hout.
    exact
      (Hreflect l1 l2 r1 r2
        Hl1 Hl2 Hr1 Hr2 Ha1 Ha2 Hout).
- intros left_output right_output _ _ Hout.
  exact Hout.
Qed.

(** Semantic [NoDupA] bounds every tuple occurrence by one. *)
Lemma tnull_nodup_occ_le_one :
  forall rows,
    NoDupA TNullRowEq rows ->
    forall row,
      (Oeset.nb_occ TNullRowOrder row rows <= 1)%N.
Proof.
intros rows Hnodup row.
pose proof (oeset_nb_occ_of_NoDupA TNullRowOrder Hnodup row) as Hocc.
destruct (Oeset.nb_occ TNullRowOrder row rows) as [|count] eqn:Hcount.
- apply N.le_0_l.
- destruct (Oeset.mem_bool TNullRowOrder row rows) eqn:Hmember;
    cbn in Hocc.
  + assert (N.pos count = 1%N) by congruence.
    rewrite H; reflexivity.
  + discriminate Hocc.
Qed.

(** * Outcome-progress admission

    This structural contract records only the boundaries at which the exact
    evaluator can otherwise be uninhabited.  It is not a runtime-safety
    predicate: every scalar computation may still produce [SqlError].  GROUP
    keys must decode to the aggregate-term kernel, and FETCH 0 retains the
    analysis-error placement check required by the specialized EXISTS
    evaluator. *)
Fixpoint query_expr_progress_ready
    {T : Tuple.Rcd} {generic_relname : Type}
    (value_is_null : value T -> bool)
    (query : @query_expr T generic_relname) {struct query} : Prop :=
  match query with
  | QExpr_Error _ _ | QExpr_Values _ _ | QExpr_Table _ _ => True
  | QExpr_Set _ left_query right_query
  | QExpr_NaturalJoin left_query right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_progress_ready value_is_null left_query /\
      query_expr_progress_ready value_is_null right_query
  | QExpr_Join kind predicate matched_select left_select right_select
      left_query right_query =>
      query_expr_progress_ready value_is_null left_query /\
      query_expr_progress_ready value_is_null right_query /\
      scalar_expr_progress_ready value_is_null predicate /\
      match kind with
      | QueryJoinInner =>
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            matched_select
      | QueryJoinLeft =>
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            matched_select /\
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            left_select
      | QueryJoinRight =>
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            matched_select /\
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            right_select
      | QueryJoinFull =>
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            matched_select /\
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            left_select /\
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            right_select
      | QueryJoinSemi | QueryJoinAnti =>
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            left_select
      end
  | QExpr_Project select_list input =>
      query_expr_progress_ready value_is_null input /\
      prop_forall
        (fun item => scalar_expr_progress_ready value_is_null (fst item))
        select_list
  | QExpr_RowMap _ _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input =>
      query_expr_progress_ready value_is_null input
  | QExpr_Fetch count input =>
      query_expr_progress_ready value_is_null input /\
      match count with
      | O => query_expr_contains_analysis_error input = false
      | S _ => True
      end
  | QExpr_Filter expression input =>
      query_expr_progress_ready value_is_null input /\
      scalar_expr_progress_ready value_is_null expression
  | QExpr_Group select_list group_keys having input =>
      query_expr_progress_ready value_is_null input /\
      prop_forall
        (fun item => scalar_expr_progress_ready value_is_null (fst item))
        select_list /\
      scalar_expr_progress_ready value_is_null having /\
      exists group_terms,
        scalar_group_key_terms group_keys = Some group_terms
  | QExpr_GroupingSets grouping_sets input =>
      query_expr_progress_ready value_is_null input /\
      prop_forall
        (fun grouping_set =>
          prop_forall
            (fun item => scalar_expr_progress_ready value_is_null (fst item))
            (fst grouping_set) /\
          exists group_terms,
            scalar_group_key_terms (snd grouping_set) = Some group_terms)
        grouping_sets
  | QExpr_Rank _ _ _ _ input
  | QExpr_Window _ _ _ input =>
      query_expr_progress_ready value_is_null input
  end
with scalar_expr_progress_ready
    {T : Tuple.Rcd} {generic_relname : Type}
    (value_is_null : value T -> bool)
    {kind : scalar_result_kind}
    (expression : @scalar_expr T generic_relname kind)
    {struct expression} : Prop :=
  match expression with
  | SExpr_Leaf _ _ | SExpr_True => True
  | SExpr_Call _ _ arguments
  | SExpr_Pred _ arguments =>
      prop_forall (scalar_expr_progress_ready value_is_null) arguments
  | SExpr_Case _ condition then_expression else_expression =>
      scalar_expr_progress_ready value_is_null condition /\
      scalar_expr_progress_ready value_is_null then_expression /\
      scalar_expr_progress_ready value_is_null else_expression
  | SExpr_BoolValue _ _ inner
  | SExpr_ValueBool _ inner
  | SExpr_Not inner =>
      scalar_expr_progress_ready value_is_null inner
  | SExpr_ConjList _ _ expressions =>
      prop_forall (scalar_expr_progress_ready value_is_null) expressions
  | SExpr_Quant _ _ arguments subquery
  | SExpr_In arguments subquery =>
      prop_forall (scalar_expr_progress_ready value_is_null) arguments /\
      query_expr_progress_ready value_is_null subquery
  | SExpr_Exists subquery =>
      query_expr_progress_ready value_is_null subquery
  | SExpr_Subquery _ null_value subquery =>
      value_is_null null_value = true /\
      query_expr_progress_ready value_is_null subquery
  end.

Section ProgressReadinessFromWellPlacedTyping.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variable basesort : generic_relname -> Fset.set (A T).
Variable leaf_has_type : type T -> @aggterm T -> Prop.
Variable call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Variable predicate_has_types : predicate T -> list (type T) -> Prop.
Variables rank_type boolean_type : type T.
Variable generic_value_is_null : value T -> bool.

Local Definition QueryAccepted (query : @query_expr T generic_relname) : Prop :=
  @query_expr_admissible T generic_relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type generic_value_is_null query.

Local Definition ScalarAccepted
    (phase : scalar_phase) (kind : scalar_result_kind)
    (expression : @scalar_expr T generic_relname kind) : Prop :=
  @scalar_expr_admissible T generic_relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type generic_value_is_null phase kind expression.

Local Definition QueryContainsAnalysisError
    (query : @query_expr T generic_relname) : bool :=
  query_expr_contains_analysis_error query.

Local Definition ScalarContainsAnalysisError
    (kind : scalar_result_kind)
    (expression : @scalar_expr T generic_relname kind) : bool :=
  scalar_expr_contains_analysis_error expression.

Local Definition QueryProgressReady
    (query : @query_expr T generic_relname) : Prop :=
  query_expr_progress_ready generic_value_is_null query.

Local Definition ScalarProgressReady
    (kind : scalar_result_kind)
    (expression : @scalar_expr T generic_relname kind) : Prop :=
  scalar_expr_progress_ready generic_value_is_null expression.

Local Lemma scalar_list_all_progress_ready :
  forall kind (expressions : list (@scalar_expr T generic_relname kind)),
    list_all _
      (fun expression => forall phase,
        ScalarAccepted phase kind expression ->
        ScalarContainsAnalysisError kind expression = false ->
        ScalarProgressReady kind expression)
      expressions ->
    forall phase,
      prop_forall (ScalarAccepted phase kind) expressions ->
      existsb (ScalarContainsAnalysisError kind) expressions = false ->
      prop_forall (ScalarProgressReady kind) expressions.
Proof.
intros kind expressions Hall.
induction Hall as [|expression Hexpression expressions Hexpressions IH];
  intros phase Haccepted Hcontains;
  cbn [prop_forall] in Haccepted;
  cbn in Hcontains |- *.
- constructor.
- destruct Haccepted as [Hhead Htail].
  apply Bool.Bool.orb_false_iff in Hcontains as
    [Hhead_contains Htail_contains].
  constructor.
  + exact (Hexpression phase Hhead Hhead_contains).
  + exact (IH phase Htail Htail_contains).
Qed.

Local Lemma scalar_select_list_all_progress_ready :
  forall select_list : list
      (@scalar_expr T generic_relname ScalarResultValue * attribute T),
    list_all _
      (prod_all _
        (fun expression => forall phase,
          ScalarAccepted phase ScalarResultValue expression ->
          ScalarContainsAnalysisError ScalarResultValue expression = false ->
          ScalarProgressReady ScalarResultValue expression)
        _ (fun _ => unit)) select_list ->
    forall phase,
      prop_forall
        (fun item =>
          ScalarAccepted phase ScalarResultValue (fst item) /\
          scalar_expr_type (fst item) = type_of_attribute T (snd item))
        select_list ->
      existsb
        (fun item =>
          ScalarContainsAnalysisError ScalarResultValue (fst item))
        select_list = false ->
      prop_forall
        (fun item => ScalarProgressReady ScalarResultValue (fst item))
        select_list.
Proof.
intros select_list Hall.
induction Hall as [|item Hitem rest Hrest IH];
  intros phase Haccepted Hcontains;
  cbn [prop_forall] in Haccepted;
  cbn in Hcontains |- *.
- constructor.
- inversion Hitem as [expression Hexpression attribute Hunit]; subst.
  destruct Haccepted as [[Hhead _] Htail].
  apply Bool.Bool.orb_false_iff in Hcontains as
    [Hhead_contains Htail_contains].
  constructor.
  + exact (Hexpression phase Hhead Hhead_contains).
  + exact (IH phase Htail Htail_contains).
Qed.

Local Lemma scalar_grouping_sets_all_progress_ready :
  forall grouping_sets : list
      (list (@scalar_expr T generic_relname ScalarResultValue * attribute T) *
       list (@scalar_expr T generic_relname ScalarResultValue)),
    list_all _
      (prod_all _
        (list_all _
          (prod_all _
            (fun expression => forall phase,
              ScalarAccepted phase ScalarResultValue expression ->
              ScalarContainsAnalysisError ScalarResultValue expression =
                false ->
              ScalarProgressReady ScalarResultValue expression)
            _ (fun _ => unit)))
        _
        (list_all _
          (fun expression => forall phase,
            ScalarAccepted phase ScalarResultValue expression ->
            ScalarContainsAnalysisError ScalarResultValue expression = false ->
            ScalarProgressReady ScalarResultValue expression)))
      grouping_sets ->
    prop_forall
      (fun grouping_set =>
        prop_forall
          (fun item =>
            ScalarAccepted ScalarPhaseSelect ScalarResultValue (fst item) /\
            scalar_expr_type (fst item) =
              type_of_attribute T (snd item))
          (fst grouping_set) /\
        prop_forall
          (ScalarAccepted ScalarPhaseGroupBy ScalarResultValue)
          (snd grouping_set) /\
        exists group_terms,
          scalar_group_key_terms (snd grouping_set) = Some group_terms)
      grouping_sets ->
    existsb
      (fun grouping_set =>
        (existsb
          (fun item =>
            ScalarContainsAnalysisError ScalarResultValue (fst item))
          (fst grouping_set) ||
         existsb (ScalarContainsAnalysisError ScalarResultValue)
           (snd grouping_set))%bool)
      grouping_sets = false ->
    prop_forall
      (fun grouping_set =>
        prop_forall
          (fun item => ScalarProgressReady ScalarResultValue (fst item))
          (fst grouping_set) /\
        exists group_terms,
          scalar_group_key_terms (snd grouping_set) = Some group_terms)
      grouping_sets.
Proof.
intros grouping_sets Hall.
induction Hall as [|grouping_set Hgroup rest Hrest IH];
  intros Haccepted Hcontains;
  cbn [prop_forall] in Haccepted;
  cbn in Hcontains |- *.
- constructor.
- inversion Hgroup as [select_list Hselect group_keys Hkeys]; subst.
  destruct Haccepted as
    [[Hselect_accepted [Hkeys_accepted Hdecode]] Htail_accepted].
  apply Bool.Bool.orb_false_iff in Hcontains as
    [Hhead_contains Htail_contains].
  apply Bool.Bool.orb_false_iff in Hhead_contains as
    [Hselect_contains Hkeys_contains].
  constructor.
  + split.
    * eapply scalar_select_list_all_progress_ready;
        [exact Hselect | exact Hselect_accepted | exact Hselect_contains].
    * exact Hdecode.
  + exact (IH Htail_accepted Htail_contains).
Qed.

(** Generic typing plus containment-false is sufficient for the structural
    progress contract.  The containment premise is intentionally separate:
    generic typing alone permits a nested analysis-error leaf, while FETCH 0
    must not erase such an observation. *)
Lemma query_scalar_expr_well_placed_progress_ready :
  (forall query,
    QueryAccepted query ->
    QueryContainsAnalysisError query = false ->
    QueryProgressReady query) /\
  (forall kind (expression : @scalar_expr T generic_relname kind) phase,
    ScalarAccepted phase kind expression ->
    ScalarContainsAnalysisError kind expression = false ->
    ScalarProgressReady kind expression).
Proof.
apply query_scalar_expr_admissibility_mutind;
  intros;
  unfold QueryAccepted, ScalarAccepted,
    QueryContainsAnalysisError, ScalarContainsAnalysisError,
    QueryProgressReady, ScalarProgressReady in *;
  cbn [query_expr_admissible scalar_expr_admissible
    query_expr_contains_analysis_error scalar_expr_contains_analysis_error
    query_expr_progress_ready scalar_expr_progress_ready] in *.
all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
all: repeat match goal with
  | H : orb _ _ = false |- _ =>
      apply Bool.Bool.orb_false_iff in H; destruct H
  end.
all: try exact I.
all: try match goal with
  | kind : query_join_kind |- _ => destruct kind; cbn in *
  end.
all: repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
all: repeat split; try assumption; try eauto.
all: try match goal with
  | Hrecursive : QueryAccepted ?query ->
        QueryContainsAnalysisError ?query = false ->
        QueryProgressReady ?query,
    Haccepted : QueryAccepted ?query,
    Hcontains : QueryContainsAnalysisError ?query = false
      |- QueryProgressReady ?query =>
      exact (Hrecursive Haccepted Hcontains)
  end.
all: try match goal with
  | Hrecursive : forall phase,
        ScalarAccepted phase ?kind ?expression ->
        ScalarContainsAnalysisError ?kind ?expression = false ->
        ScalarProgressReady ?kind ?expression,
    Haccepted : ScalarAccepted ?phase ?kind ?expression,
    Hcontains : ScalarContainsAnalysisError ?kind ?expression = false
      |- ScalarProgressReady ?kind ?expression =>
      exact (Hrecursive _ Haccepted Hcontains)
  end.
all: try (eapply scalar_list_all_progress_ready; eassumption).
all: try (eapply scalar_select_list_all_progress_ready; eassumption).
all: try (eapply scalar_grouping_sets_all_progress_ready; eassumption).
all: try (destruct n; cbn; auto).
all: eauto.
all: eapply scalar_select_list_all_progress_ready
  with (phase := ScalarPhaseRowSelect).
all: unfold ScalarAccepted, ScalarContainsAnalysisError,
  ScalarProgressReady; assumption.
Qed.

Theorem query_expr_well_placed_progress_ready :
  forall query,
    QueryAccepted query ->
    query_expr_analysis_error_well_placed query ->
    QueryProgressReady query.
Proof.
intros query Haccepted Hplaced.
destruct query; cbn [query_expr_analysis_error_well_placed] in Hplaced |- *;
  try exact I;
  eapply (proj1 query_scalar_expr_well_placed_progress_ready);
  eassumption.
Qed.

End ProgressReadinessFromWellPlacedTyping.

(** The TNull admission boundary contains generic typing, analysis-error
    placement, and Boolean-site uniqueness.  Only the first two components
    are needed for inhabitation; site uniqueness constrains legal generated
    syntax but does not strengthen this result into runtime safety. *)
Theorem tnull_query_expr_well_placed_progress_ready :
  forall basesort query,
    TNullQueryExprAdmissible basesort query ->
    @query_expr_progress_ready TNull relname
      NullValues.is_null_value query.
Proof.
intros basesort query [Haccepted [Hplaced Hsites]].
eapply (@query_expr_well_placed_progress_ready TNull relname basesort
  TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
  type_int64 type_bool NullValues.is_null_value);
  eassumption.
Qed.

(** * Scheduled outcome progress

    Query rows, cardinality demand, EXISTS demand, and scalar evaluation form
    one recursive progress problem.  Keeping them in one induction is what
    prevents a scalar subquery or an EXISTS target-elision path from hiding
    the same inhabitation obligation under a different evaluator. *)
Section ScheduledOutcomeProgress.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variable basesort : generic_relname -> Fset.set (A T).
Variable instance :
  generic_relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable generic_value_is_null : value T -> bool.

Local Definition EvalQuery schedule env query outcome : Prop :=
  @eval_query_expr_outcome T generic_relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error generic_value_is_null
    schedule env query outcome.

Local Definition EvalQueryCardinality schedule env query outcome : Prop :=
  @eval_query_cardinality_outcome T generic_relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error generic_value_is_null
    schedule env query outcome.

Local Definition EvalQueryExists schedule env query outcome : Prop :=
  @eval_query_exists_outcome T generic_relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error generic_value_is_null
    schedule env query outcome.

Local Definition EvalScalarValue schedule env expression outcome : Prop :=
  @eval_scalar_value_expr_outcome T generic_relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error generic_value_is_null
    schedule env expression outcome.

Local Definition EvalScalarBoolean schedule env expression outcome : Prop :=
  @eval_scalar_boolean_expr_outcome T generic_relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error generic_value_is_null
    schedule env expression outcome.

Local Definition QueryScheduledOutcomeProgress
    (query : @query_expr T generic_relname) : Prop :=
  forall schedule env,
    @query_expr_progress_ready T generic_relname
      generic_value_is_null query ->
    (exists outcome, EvalQuery schedule env query outcome) /\
    (exists outcome, EvalQueryCardinality schedule env query outcome) /\
    (exists outcome, EvalQueryExists schedule env query outcome).

Local Definition ScalarScheduledOutcomeProgress
    (kind : scalar_result_kind)
    (expression : @scalar_expr T generic_relname kind) : Prop :=
  match kind as result_kind return
      @scalar_expr T generic_relname result_kind -> Prop with
  | ScalarResultValue =>
      fun value_expression => forall schedule env,
        @scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultValue value_expression ->
        exists outcome,
          EvalScalarValue schedule env value_expression outcome
  | ScalarResultBoolean =>
      fun boolean_expression => forall schedule env,
        @scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultBoolean boolean_expression ->
        exists outcome,
          EvalScalarBoolean schedule env boolean_expression outcome
  end expression.

Local Lemma list_all_member :
  forall (A : Type) (property : A -> Prop) values value,
    list_all A property values ->
    In value values ->
    property value.
Proof.
intros A property values value Hall.
induction Hall as [|head Hhead tail Htail IH]; cbn; intro Hin.
- contradiction.
- destruct Hin as [-> | Hin]; [exact Hhead | now apply IH].
Qed.

Local Lemma grouping_set_select_list_progress_member :
  forall grouping_sets : list
      (list (@scalar_expr T generic_relname ScalarResultValue * attribute T) *
       list (@scalar_expr T generic_relname ScalarResultValue)),
    list_all _
      (prod_all _
        (list_all _
          (prod_all _
            (ScalarScheduledOutcomeProgress ScalarResultValue)
            _ (fun _ => unit)))
        _
        (list_all _
          (ScalarScheduledOutcomeProgress ScalarResultValue)))
      grouping_sets ->
    forall select_list group_keys,
      In (select_list, group_keys) grouping_sets ->
      exists Hselect :
        list_all _
          (prod_all _
            (ScalarScheduledOutcomeProgress ScalarResultValue)
            _ (fun _ => unit)) select_list,
        True.
Proof.
intros grouping_sets Hall.
induction Hall as [|grouping_set Hgroup rest Hrest IH];
  intros select_list group_keys Hin; cbn in Hin.
- contradiction.
- inversion Hgroup as
    [head_select Hselect_progress head_keys Hkeys_progress]; subst.
  destruct Hin as [Hequal | Hin].
  + inversion Hequal; subst.
    exists Hselect_progress; exact I.
  + exact (IH select_list group_keys Hin).
Qed.

Local Lemma scalar_value_list_all_has_outcome :
  forall expressions,
    list_all _
      (ScalarScheduledOutcomeProgress ScalarResultValue) expressions ->
    forall schedule env,
      prop_forall
        (@scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultValue) expressions ->
      forall expression,
        In expression expressions ->
        exists outcome,
          EvalScalarValue schedule env expression outcome.
Proof.
intros expressions Hall.
induction Hall as [|expression Hexpression expressions Hexpressions IH];
  intros schedule env Hready other Hin;
  cbn [prop_forall] in Hready, Hin.
- contradiction.
- destruct Hready as [Hhead Htail].
  destruct Hin as [<- | Hin].
  + exact (Hexpression schedule env Hhead).
  + exact (IH schedule env Htail other Hin).
Qed.

Local Lemma scalar_boolean_list_all_has_outcome :
  forall expressions,
    list_all _
      (ScalarScheduledOutcomeProgress ScalarResultBoolean) expressions ->
    forall schedule env,
      prop_forall
        (@scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultBoolean) expressions ->
      forall expression,
        In expression expressions ->
        exists outcome,
          EvalScalarBoolean schedule env expression outcome.
Proof.
intros expressions Hall.
induction Hall as [|expression Hexpression expressions Hexpressions IH];
  intros schedule env Hready other Hin;
  cbn [prop_forall] in Hready, Hin.
- contradiction.
- destruct Hready as [Hhead Htail].
  destruct Hin as [<- | Hin].
  + exact (Hexpression schedule env Hhead).
  + exact (IH schedule env Htail other Hin).
Qed.

Local Lemma scalar_select_list_all_has_outcome :
  forall select_list : list
      (@scalar_expr T generic_relname ScalarResultValue * attribute T),
    list_all _
      (prod_all _
        (ScalarScheduledOutcomeProgress ScalarResultValue)
        _ (fun _ => unit)) select_list ->
    forall schedule env,
      prop_forall
        (fun item =>
          @scalar_expr_progress_ready T generic_relname
            generic_value_is_null ScalarResultValue (fst item))
        select_list ->
      forall expression,
        In expression (map fst select_list) ->
        exists outcome,
          EvalScalarValue schedule env expression outcome.
Proof.
intros select_list Hall.
induction Hall as [|item Hitem rest Hrest IH];
  intros schedule env Hready expression Hin;
  cbn [prop_forall] in Hready;
  cbn in Hin.
- contradiction.
- inversion Hitem as [head Hhead attribute Hunit]; subst.
  destruct Hready as [Hhead_ready Htail_ready].
  destruct Hin as [<- | Hin].
  + exact (Hhead schedule env Hhead_ready).
  + exact (IH schedule env Htail_ready expression Hin).
Qed.

Local Arguments JoinSourceMatched {T} _.
Local Arguments JoinSourceLeft {T} _.
Local Arguments JoinSourceRight {T} _.

Local Definition query_join_source_allowed
    (kind : query_join_kind) (source : query_join_source T) : Prop :=
  match kind, source with
  | QueryJoinInner, JoinSourceMatched _ => True
  | QueryJoinLeft, JoinSourceMatched _
  | QueryJoinLeft, JoinSourceLeft _ => True
  | QueryJoinRight, JoinSourceMatched _
  | QueryJoinRight, JoinSourceRight _ => True
  | QueryJoinFull, _ => True
  | QueryJoinSemi, JoinSourceLeft _
  | QueryJoinAnti, JoinSourceLeft _ => True
  | _, _ => False
  end.

Local Lemma query_join_matched_sources_are_matched :
  forall left rights flags source,
    In source (@query_join_matched_sources T left rights flags) ->
    exists row, source = JoinSourceMatched row.
Proof.
intros left rights; induction rights as [|right rights IH];
  intros [|flag flags] source Hin; cbn in Hin; try contradiction.
destruct flag; cbn in Hin.
- destruct Hin as [Hequal | Hin].
  + subst source; eauto.
  + now apply IH in Hin.
- now apply IH in Hin.
Qed.

Local Lemma query_join_left_sources_are_allowed :
  forall kind lefts rights matrix source,
    In source (@query_join_left_sources T kind lefts rights matrix) ->
    query_join_source_allowed kind source.
Proof.
intros kind lefts; induction lefts as [|left lefts IH];
  intros rights [|flags matrix] source Hin; cbn in Hin; try contradiction.
destruct kind; cbn in Hin |- *.
- apply in_app_or in Hin as [Hin | Hin].
  + apply query_join_matched_sources_are_matched in Hin as [row ->]; exact I.
  + exact (IH rights matrix source Hin).
- destruct (query_join_row_has_match flags); cbn in Hin.
  + apply in_app_or in Hin as [Hin | Hin].
    * apply query_join_matched_sources_are_matched in Hin as [row ->]; exact I.
    * exact (IH rights matrix source Hin).
  + destruct Hin as [Hequal | Hin].
    * subst source; exact I.
    * exact (IH rights matrix source Hin).
- apply in_app_or in Hin as [Hin | Hin].
  + apply query_join_matched_sources_are_matched in Hin as [row ->]; exact I.
  + exact (IH rights matrix source Hin).
- destruct (query_join_row_has_match flags); cbn in Hin.
  + apply in_app_or in Hin as [Hin | Hin].
    * apply query_join_matched_sources_are_matched in Hin as [row ->]; exact I.
    * exact (IH rights matrix source Hin).
  + destruct Hin as [Hequal | Hin].
    * subst source; exact I.
    * exact (IH rights matrix source Hin).
- destruct (query_join_row_has_match flags); cbn in Hin.
  + destruct Hin as [Hequal | Hin].
    * subst source; exact I.
    * exact (IH rights matrix source Hin).
  + exact (IH rights matrix source Hin).
- destruct (query_join_row_has_match flags); cbn in Hin.
  + exact (IH rights matrix source Hin).
  + destruct Hin as [Hequal | Hin].
    * subst source; exact I.
    * exact (IH rights matrix source Hin).
Qed.

Local Lemma query_join_unmatched_right_sources_are_right :
  forall index rights matrix source,
    In source
      (@query_join_unmatched_right_sources_from T index rights matrix) ->
    exists row, source = JoinSourceRight row.
Proof.
intros index rights; revert index.
induction rights as [|right rights IH]; intros index matrix source Hin;
  cbn in Hin; try contradiction.
destruct (query_join_column_has_match index matrix); cbn in Hin.
- now apply IH in Hin.
- destruct Hin as [Hequal | Hin].
  + subst source; eauto.
  + now apply IH in Hin.
Qed.

Local Lemma query_join_sources_are_allowed :
  forall kind lefts rights matrix source,
    In source (@query_join_sources T kind lefts rights matrix) ->
    query_join_source_allowed kind source.
Proof.
intros kind lefts rights matrix source Hin.
unfold query_join_sources in Hin.
apply in_app_or in Hin as [Hin | Hin].
- now apply query_join_left_sources_are_allowed in Hin.
- destruct kind; cbn in Hin |- *; try contradiction;
    apply query_join_unmatched_right_sources_are_right in Hin as [row ->];
    exact I.
Qed.

Local Lemma query_join_source_select_progress_ready :
  forall kind matched_select left_select right_select source,
    query_join_source_allowed kind source ->
    (match kind with
     | QueryJoinInner =>
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           matched_select
     | QueryJoinLeft =>
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           left_select
     | QueryJoinRight =>
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           right_select
     | QueryJoinFull =>
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           matched_select /\
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           left_select /\
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           right_select
     | QueryJoinSemi | QueryJoinAnti =>
         prop_forall
           (fun item =>
             @scalar_expr_progress_ready T generic_relname
               generic_value_is_null ScalarResultValue (fst item))
           left_select
     end) ->
    prop_forall
      (fun item =>
        @scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultValue (fst item))
      (query_join_source_select
        matched_select left_select right_select source).
Proof.
intros kind matched_select left_select right_select source Hallowed Hready.
destruct kind, source; cbn in Hallowed, Hready |- *; tauto.
Qed.

Local Lemma eval_scalar_select_list_has_outcome_of_progress :
  forall schedule env
      (select_list : list
        (@scalar_expr T generic_relname ScalarResultValue * attribute T)),
    list_all _
      (prod_all _
        (ScalarScheduledOutcomeProgress ScalarResultValue)
        _ (fun _ => unit)) select_list ->
    prop_forall
      (fun item =>
        @scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultValue (fst item))
      select_list ->
    exists outcome,
      @eval_scalar_values_outcome T generic_relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error generic_value_is_null
        schedule env (map fst select_list) outcome.
Proof.
intros schedule env select_list Hall Hready.
eapply eval_scalar_values_has_outcome.
intros expression Hin.
eapply scalar_select_list_all_has_outcome; eassumption.
Qed.

Local Lemma eval_groups_has_outcome_of_progress :
  forall schedule env select_list group_terms having groups,
    list_all _
      (prod_all _
        (ScalarScheduledOutcomeProgress ScalarResultValue)
        _ (fun _ => unit)) select_list ->
    ScalarScheduledOutcomeProgress ScalarResultBoolean having ->
    prop_forall
      (fun item =>
        @scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultValue (fst item))
      select_list ->
    @scalar_expr_progress_ready T generic_relname
      generic_value_is_null ScalarResultBoolean having ->
    exists outcome,
      @eval_groups_outcome T generic_relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error generic_value_is_null
        schedule env select_list group_terms having groups outcome.
Proof.
intros schedule env select_list group_terms having groups
  Hselect Hhaving Hselect_ready Hhaving_ready.
eapply eval_groups_has_outcome.
- intros group Hgroup.
  exact (Hhaving schedule
    (env_g T env (@Group_By T group_terms) group) Hhaving_ready).
- intros group truth Hgroup Htruth Haccepted.
  eapply eval_scalar_select_list_has_outcome_of_progress;
    eassumption.
Qed.

Local Lemma eval_groups_cardinality_has_outcome_of_progress :
  forall schedule env select_list group_terms having groups,
    ScalarScheduledOutcomeProgress ScalarResultBoolean having ->
    @scalar_expr_progress_ready T generic_relname
      generic_value_is_null ScalarResultBoolean having ->
    exists outcome,
      @eval_groups_cardinality_outcome T generic_relname
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error generic_value_is_null schedule
        env select_list group_terms having groups outcome.
Proof.
intros schedule env select_list group_terms having groups
  Hhaving Hhaving_ready.
eapply eval_groups_cardinality_has_outcome.
intros group Hgroup.
exact (Hhaving schedule
  (env_g T env (@Group_By T group_terms) group) Hhaving_ready).
Qed.

Local Lemma eval_group_bag_has_outcome_of_progress :
  forall schedule env select_list group_keys group_terms having input_bag,
    scalar_group_key_terms group_keys = Some group_terms ->
    list_all _
      (prod_all _
        (ScalarScheduledOutcomeProgress ScalarResultValue)
        _ (fun _ => unit)) select_list ->
    ScalarScheduledOutcomeProgress ScalarResultBoolean having ->
    prop_forall
      (fun item =>
        @scalar_expr_progress_ready T generic_relname
          generic_value_is_null ScalarResultValue (fst item))
      select_list ->
    @scalar_expr_progress_ready T generic_relname
      generic_value_is_null ScalarResultBoolean having ->
    exists outcome,
      @eval_group_bag_outcome T generic_relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error generic_value_is_null
        schedule env select_list group_keys having input_bag outcome.
Proof.
intros schedule env select_list group_keys group_terms having input_bag
  Hdecode Hselect Hhaving Hselect_ready Hhaving_ready.
eapply eval_group_bag_has_outcome; [exact Hdecode |].
intros representative Hrepresentative Hkeys.
eapply eval_groups_has_outcome_of_progress; eassumption.
Qed.

Local Lemma eval_group_cardinality_has_outcome_of_progress :
  forall schedule env select_list group_terms having input_bag,
    ScalarScheduledOutcomeProgress ScalarResultBoolean having ->
    @scalar_expr_progress_ready T generic_relname
      generic_value_is_null ScalarResultBoolean having ->
    exists outcome,
      @eval_group_cardinality_outcome T generic_relname
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error generic_value_is_null schedule
        env select_list group_terms having input_bag outcome.
Proof.
intros schedule env select_list group_terms having input_bag
  Hhaving Hhaving_ready.
eapply eval_group_cardinality_has_outcome.
intros representative Hrepresentative Hkeys.
eapply eval_groups_cardinality_has_outcome_of_progress; eassumption.
Qed.

Local Lemma scalar_true_scheduled_outcome_progress :
  ScalarScheduledOutcomeProgress ScalarResultBoolean SExpr_True.
Proof.
intros schedule env Hready.
exists (SqlSuccess (Bool.true (B T))); constructor.
Qed.

(** The simultaneous core theorem.  Each query component contains ordinary
    rows, cardinality-only demand, and EXISTS-only demand for one fixed
    schedule; the scalar component contains the matching typed outcome. *)
Lemma query_scalar_expr_progress_ready_has_outcomes :
  (forall query, QueryScheduledOutcomeProgress query) /\
  (forall kind (expression : @scalar_expr T generic_relname kind),
    ScalarScheduledOutcomeProgress kind expression).
Proof.
apply query_scalar_expr_admissibility_mutind.
- intros outputs error.
  unfold QueryScheduledOutcomeProgress.
  intros schedule env Hready.
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Error outputs error) outcome).
  { apply query_expr_error_has_outcome. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros outputs values.
  unfold QueryScheduledOutcomeProgress.
  intros schedule env Hready.
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Values outputs values) outcome).
  { apply query_expr_values_has_outcome. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros outputs table.
  unfold QueryScheduledOutcomeProgress.
  intros schedule env Hready.
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Table outputs table) outcome).
  { apply query_expr_table_has_outcome. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros operation left_query Hleft right_query Hright.
  unfold QueryScheduledOutcomeProgress in *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hleft_ready Hright_ready].
  destruct (Hleft schedule env Hleft_ready) as
    [Hleft_full [Hleft_cardinality Hleft_exists]].
  destruct (Hright schedule env Hright_ready) as
    [Hright_full [Hright_cardinality Hright_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_Set operation left_query right_query) outcome).
  { eapply query_expr_set_has_outcome; eassumption. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros left_query Hleft right_query Hright.
  unfold QueryScheduledOutcomeProgress in *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hleft_ready Hright_ready].
  destruct (Hleft schedule env Hleft_ready) as
    [Hleft_full [Hleft_cardinality Hleft_exists]].
  destruct (Hright schedule env Hright_ready) as
    [Hright_full [Hright_cardinality Hright_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_NaturalJoin left_query right_query) outcome).
  { eapply query_expr_natural_join_has_outcome; eassumption. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros left_query Hleft right_query Hright.
  unfold QueryScheduledOutcomeProgress in *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hleft_ready Hright_ready].
  destruct (Hleft schedule env Hleft_ready) as
    [Hleft_full [Hleft_cardinality Hleft_exists]].
  destruct (Hright schedule env Hright_ready) as
    [Hright_full [Hright_cardinality Hright_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_CrossJoin left_query right_query) outcome).
  { eapply query_expr_cross_join_has_outcome; eassumption. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros kind predicate Hpredicate
    matched_select Hmatched left_select Hleft_select
    right_select Hright_select
    left_query Hleft right_query Hright.
  unfold QueryScheduledOutcomeProgress in Hleft, Hright |- *.
  unfold ScalarScheduledOutcomeProgress in Hpredicate.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as
    [Hleft_ready [Hright_ready [Hpredicate_ready Hselects_ready]]].
  destruct (Hleft schedule env Hleft_ready) as
    [Hleft_full [Hleft_cardinality Hleft_exists]].
  destruct (Hright schedule env Hright_ready) as
    [Hright_full [Hright_cardinality Hright_exists]].
  assert (Hconditions : forall left_rows right_rows,
    exists outcome,
      @eval_join_conditions_outcome T generic_relname
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error generic_value_is_null schedule
        env predicate left_rows right_rows outcome).
  {
    intros left_rows right_rows.
    eapply eval_join_conditions_has_outcome.
    intros left_row Hleft_row.
    eapply eval_join_row_conditions_has_outcome.
    intros right_row Hright_row.
    exact (Hpredicate schedule
      (env_t T env (join_tuple T left_row right_row)) Hpredicate_ready).
  }
  assert (Hjoin_bag : forall left_rows right_rows,
    EvalQuery schedule env left_query (SqlSuccess left_rows) ->
    EvalQuery schedule env right_query (SqlSuccess right_rows) ->
    exists outcome,
      @eval_join_bag_outcome T generic_relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error generic_value_is_null
        schedule env kind predicate matched_select left_select right_select
        (query_rows_bag left_rows) (query_rows_bag right_rows) outcome).
  {
    intros left_rows right_rows Hleft_rows Hright_rows.
    eapply eval_join_bag_has_outcome.
    - intros left_rep right_rep Hleft_rep Hright_rep.
      apply Hconditions.
    - intros left_rep right_rep matrix Hleft_rep Hright_rep Hmatrix.
      eapply eval_project_join_sources_has_outcome.
      intros source Hsource.
      eapply eval_scalar_values_has_outcome.
      intros expression Hexpression.
      pose proof
        (query_join_sources_are_allowed kind left_rep right_rep matrix
          source Hsource) as Hallowed.
      pose proof
        (query_join_source_select_progress_ready kind matched_select
          left_select right_select source Hallowed Hselects_ready)
        as Hsource_ready.
      destruct source; cbn in Hexpression, Hsource_ready |- *.
      + eapply scalar_select_list_all_has_outcome;
          [exact Hmatched | exact Hsource_ready | exact Hexpression].
      + eapply scalar_select_list_all_has_outcome;
          [exact Hleft_select | exact Hsource_ready | exact Hexpression].
      + eapply scalar_select_list_all_has_outcome;
          [exact Hright_select | exact Hsource_ready | exact Hexpression].
  }
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_Join kind predicate matched_select left_select right_select
        left_query right_query) outcome).
  {
    eapply query_expr_join_has_outcome;
      [exact Hleft_full | exact Hright_full | exact Hjoin_bag].
  }
  assert (Hcardinality : exists outcome,
    EvalQueryCardinality schedule env
      (QExpr_Join kind predicate matched_select left_select right_select
        left_query right_query) outcome).
  {
    eapply eval_query_cardinality_join_has_outcome;
      [exact Hleft_full | exact Hright_full |].
    intros left_rows right_rows Hleft_rows Hright_rows.
    eapply eval_join_cardinality_has_outcome.
    intros left_rep right_rep Hleft_rep Hright_rep.
    apply Hconditions.
  }
  split; [exact Hfull | split; [exact Hcardinality |]].
  eapply eval_query_exists_cardinality_has_outcome;
    [reflexivity | exact Hcardinality].
- intros select_list Hselect input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hinput_ready Hselect_ready].
  destruct (Hinput schedule env Hinput_ready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Project select_list input) outcome).
  {
    eapply query_expr_project_has_outcome; [|exact Hinput_full].
    intros input_rows Hinput_rows row Hrow.
    eapply eval_scalar_select_list_has_outcome_of_progress;
      eassumption.
  }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_project_has_outcome;
      exact Hinput_cardinality.
  + eapply eval_query_exists_project_has_outcome; exact Hinput_exists.
- intros outputs row_map input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct (Hinput schedule env Hready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_RowMap outputs row_map input) outcome).
  { eapply query_expr_row_map_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_row_map_has_outcome;
      exact Hinput_cardinality.
  + eapply eval_query_exists_row_map_has_outcome; exact Hinput_exists.
- intros formula Hformula input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  unfold ScalarScheduledOutcomeProgress in Hformula.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hinput_ready Hformula_ready].
  destruct (Hinput schedule env Hinput_ready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hscalar : forall input_rows,
    EvalQuery schedule env input (SqlSuccess input_rows) ->
    forall row, In row input_rows ->
    exists outcome,
      EvalScalarBoolean schedule (env_t T env row) formula outcome).
  {
    intros input_rows Hinput_rows row Hrow.
    exact (Hformula schedule (env_t T env row) Hformula_ready).
  }
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Filter formula input) outcome).
  {
    eapply query_expr_filter_has_outcome_of_scalar_total;
      [exact Hscalar | exact Hinput_full].
  }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_filter_has_outcome;
      [exact Hinput_full | exact Hscalar].
- intros select_list Hselect group_keys Hgroup_keys
    having Hhaving input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  unfold ScalarScheduledOutcomeProgress in Hhaving.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as
    [Hinput_ready [Hselect_ready [Hhaving_ready [group_terms Hdecode]]]].
  destruct (Hinput schedule env Hinput_ready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hgroup_bag : forall input_rows,
    EvalQuery schedule env input (SqlSuccess input_rows) ->
    exists outcome,
      @eval_group_bag_outcome T generic_relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error generic_value_is_null
        schedule env select_list group_keys having
        (query_rows_bag input_rows) outcome).
  {
    intros input_rows Hinput_rows.
    eapply eval_group_bag_has_outcome_of_progress
      with (group_terms := group_terms);
      eassumption.
  }
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_Group select_list group_keys having input) outcome).
  {
    eapply query_expr_group_has_outcome
      with (group_terms := group_terms);
      [exact Hdecode | exact Hgroup_bag | exact Hinput_full].
  }
  assert (Hcardinality : exists outcome,
    EvalQueryCardinality schedule env
      (QExpr_Group select_list group_keys having input) outcome).
  {
    eapply eval_query_cardinality_group_has_outcome
      with (group_terms := group_terms);
      [exact Hdecode | exact Hinput_full |].
    intros input_rows Hinput_rows.
    eapply eval_group_cardinality_has_outcome_of_progress;
      eassumption.
  }
  split; [exact Hfull | split; [exact Hcardinality |]].
  eapply eval_query_exists_cardinality_has_outcome;
    [reflexivity | exact Hcardinality].
- intros grouping_sets Hbranches input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hinput_ready Hbranches_ready].
  destruct (Hinput schedule env Hinput_ready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  pose proof Hbranches_ready as Hbranches_ready_forall.
  apply prop_forall_iff_Forall in Hbranches_ready_forall.
  rewrite Forall_forall in Hbranches_ready_forall.
  assert (Hgrouping_bag : forall input_rows,
    EvalQuery schedule env input (SqlSuccess input_rows) ->
    exists outcome,
      @eval_grouping_sets_bag_outcome T generic_relname
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error generic_value_is_null schedule
        env grouping_sets (query_rows_bag input_rows) outcome).
  {
    intros input_rows Hinput_rows.
    eapply eval_grouping_sets_bag_has_outcome.
    intros select_list group_keys Hin.
    destruct
      (grouping_set_select_list_progress_member
        grouping_sets Hbranches select_list group_keys Hin) as
      [Hselect_progress Hselect_witness].
    specialize (Hbranches_ready_forall _ Hin).
    destruct Hbranches_ready_forall as
      [Hselect_ready [group_terms Hdecode]].
    eapply eval_group_bag_has_outcome_of_progress
      with (group_terms := group_terms);
      [ exact Hdecode
      | exact Hselect_progress
      | exact scalar_true_scheduled_outcome_progress
      | exact Hselect_ready
      | exact I ].
  }
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_GroupingSets grouping_sets input) outcome).
  {
    eapply query_expr_grouping_sets_has_outcome;
      [exact Hgrouping_bag | exact Hinput_full].
  }
  assert (Hcardinality : exists outcome,
    EvalQueryCardinality schedule env
      (QExpr_GroupingSets grouping_sets input) outcome).
  {
    eapply eval_query_cardinality_grouping_sets_has_outcome;
      [exact Hinput_full |].
    intros input_rows Hinput_rows.
    eapply eval_grouping_sets_cardinality_has_outcome.
    intros select_list group_keys Hin.
    destruct
      (grouping_set_select_list_progress_member
        grouping_sets Hbranches select_list group_keys Hin) as
      [Hselect_progress Hselect_witness].
    specialize (Hbranches_ready_forall _ Hin).
    destruct Hbranches_ready_forall as
      [Hselect_ready [group_terms Hdecode]].
    exists group_terms; split; [exact Hdecode |].
    eapply eval_group_cardinality_has_outcome_of_progress;
      [exact scalar_true_scheduled_outcome_progress | exact I].
  }
  split; [exact Hfull | split; [exact Hcardinality |]].
  eapply eval_query_exists_cardinality_has_outcome;
    [reflexivity | exact Hcardinality].
- intros partition_keys order_keys rank_attribute rank_value input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct (Hinput schedule env Hready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      outcome).
  { eapply query_expr_rank_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros partition_keys order_keys items input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct (Hinput schedule env Hready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env
      (QExpr_Window partition_keys order_keys items input) outcome).
  { eapply query_expr_window_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct (Hinput schedule env Hready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Distinct input) outcome).
  { eapply query_expr_distinct_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_distinct_has_outcome; exact Hinput_exists.
- intros keys input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct (Hinput schedule env Hready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_OrderBy keys input) outcome).
  { eapply query_expr_order_by_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_order_by_has_outcome;
      exact Hinput_cardinality.
  + eapply eval_query_exists_order_by_has_outcome; exact Hinput_exists.
- intros count input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct (Hinput schedule env Hready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Offset count input) outcome).
  { eapply query_expr_offset_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_demanded_has_outcome;
      [reflexivity | exact Hfull].
  + eapply eval_query_exists_demanded_has_outcome;
      [reflexivity | exact Hfull].
- intros count input Hinput.
  unfold QueryScheduledOutcomeProgress in Hinput |- *.
  intros schedule env Hready.
  cbn [query_expr_progress_ready] in Hready.
  destruct Hready as [Hinput_ready Hzero].
  destruct (Hinput schedule env Hinput_ready) as
    [Hinput_full [Hinput_cardinality Hinput_exists]].
  assert (Hfull : exists outcome,
    EvalQuery schedule env (QExpr_Fetch count input) outcome).
  { eapply query_expr_fetch_has_outcome; exact Hinput_full. }
  split; [exact Hfull | split].
  + eapply eval_query_cardinality_fetch_has_outcome;
      exact Hinput_cardinality.
  + destruct count as [|count].
    * eapply eval_query_exists_fetch_zero_has_outcome; exact Hzero.
    * eapply eval_query_exists_fetch_positive_has_outcome;
        exact Hinput_exists.
- intros result_type term.
  unfold ScalarScheduledOutcomeProgress.
  intros schedule env Hready.
  exists (scalar_leaf_value_outcome
    symbol_runtime_error aggregate_runtime_error env term).
  constructor.
- intros result_type operator arguments Harguments.
  unfold ScalarScheduledOutcomeProgress.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (@eval_scalar_values_has_outcome T generic_relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    generic_value_is_null schedule env arguments) as
    [[values | error] Hvalues].
  {
    intros expression Hin.
    eapply scalar_value_list_all_has_outcome; eassumption.
  }
  + exists (scalar_call_value_outcome T
      symbol_runtime_error operator values).
    eapply EScalar_CallSuccess; exact Hvalues.
  + exists (SqlError error).
    eapply EScalar_CallArgumentsError; exact Hvalues.
- intros result_type condition Hcondition
    then_expression Hthen else_expression Helse.
  unfold ScalarScheduledOutcomeProgress in Hcondition, Hthen, Helse |- *.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct Hready as [Hcondition_ready [Hthen_ready Helse_ready]].
  destruct (Hcondition schedule env Hcondition_ready) as
    [[truth | error] Htruth].
  + destruct (Bool.is_true (B T) truth) eqn:Haccepted.
    * destruct (Hthen schedule env Hthen_ready) as [outcome Houtcome].
      exists outcome.
      eapply EScalar_CaseThen; eassumption.
    * destruct (Helse schedule env Helse_ready) as [outcome Houtcome].
      exists outcome.
      eapply EScalar_CaseElse; eassumption.
  + exists (SqlError error).
    eapply EScalar_CaseConditionError; exact Htruth.
- intros result_type embed expression Hexpression.
  unfold ScalarScheduledOutcomeProgress in Hexpression |- *.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (Hexpression schedule env Hready) as [outcome Houtcome].
  exists (scalar_bool_value_outcome T embed outcome).
  now apply EScalar_BoolValue.
- intros decode expression Hexpression.
  unfold ScalarScheduledOutcomeProgress in Hexpression |- *.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (Hexpression schedule env Hready) as [outcome Houtcome].
  exists (sql_outcome_map decode outcome).
  now apply EScalar_ValueBool.
- intros predicate arguments Harguments.
  unfold ScalarScheduledOutcomeProgress.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (@eval_scalar_values_has_outcome T generic_relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    generic_value_is_null schedule env arguments) as
    [[values | error] Hvalues].
  {
    intros expression Hin.
    eapply scalar_value_list_all_has_outcome; eassumption.
  }
  + exists (SqlSuccess (interp_predicate T predicate values)).
    eapply EScalar_PredSuccess; exact Hvalues.
  + exists (SqlError error).
    eapply EScalar_PredArgumentsError; exact Hvalues.
- intros site_rows operation expressions Hexpressions.
  unfold ScalarScheduledOutcomeProgress.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (@eval_scalar_boolean_operands_has_outcome T generic_relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    generic_value_is_null schedule env operation
    (schedule_boolean_operands schedule site_rows expressions)) as
    [outcome Houtcome].
  {
    intros expression Hin.
    eapply scalar_boolean_list_all_has_outcome;
      [exact Hexpressions | exact Hready |].
    eapply Permutation_in;
      [ apply Permutation_sym,
          schedule_boolean_operands_permutation
      | exact Hin ].
  }
  exists outcome; now apply EScalar_ConjList.
- intros expression Hexpression.
  unfold ScalarScheduledOutcomeProgress in Hexpression |- *.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (Hexpression schedule env Hready) as
    [[truth | error] Houtcome].
  + exists (SqlSuccess (Bool.negb (B T) truth)).
    now apply EScalar_NotSuccess.
  + exists (SqlError error); now apply EScalar_NotError.
- unfold ScalarScheduledOutcomeProgress.
  intros schedule env Hready.
  exists (SqlSuccess (Bool.true (B T))); constructor.
- intros quantifier predicate arguments Harguments subquery Hsubquery.
  unfold ScalarScheduledOutcomeProgress.
  unfold QueryScheduledOutcomeProgress in Hsubquery.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct Hready as [Harguments_ready Hsubquery_ready].
  destruct (@eval_scalar_values_has_outcome T generic_relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    generic_value_is_null schedule env arguments) as
    [[values | error] Hvalues].
  {
    intros expression Hin.
    eapply scalar_value_list_all_has_outcome; eassumption.
  }
  + destruct (Hsubquery schedule env Hsubquery_ready) as
      [Hquery [Hcardinality Hexists]].
    destruct Hquery as [[rows | error] Hrows].
    * exists
        (SqlSuccess
          (interp_quant (B T) quantifier
            (fun row =>
              interp_predicate T predicate
                (values ++ query_row_output_values T
                  (query_expr_outputs subquery) row))
            (query_canonical_rows rows))).
      eapply EScalar_QuantSuccess; eassumption.
    * exists (SqlError error).
      eapply EScalar_QuantSubqueryError; eassumption.
  + exists (SqlError error).
    eapply EScalar_QuantArgumentsError; exact Hvalues.
- intros arguments Harguments subquery Hsubquery.
  unfold ScalarScheduledOutcomeProgress.
  unfold QueryScheduledOutcomeProgress in Hsubquery.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct Hready as [Harguments_ready Hsubquery_ready].
  destruct (@eval_scalar_values_has_outcome T generic_relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    generic_value_is_null schedule env arguments) as
    [[values | error] Hvalues].
  {
    intros expression Hin.
    eapply scalar_value_list_all_has_outcome; eassumption.
  }
  + destruct (Hsubquery schedule env Hsubquery_ready) as
      [Hquery [Hcardinality Hexists]].
    destruct Hquery as [[rows | error] Hrows].
    * exists
        (SqlSuccess
          (interp_quant (B T) Exists_F
            (fun row =>
              query_value_lists_equal T unknown generic_value_is_null values
                (query_row_output_values T
                  (query_expr_outputs subquery) row))
            (query_canonical_rows rows))).
      eapply EScalar_InSuccess; eassumption.
    * exists (SqlError error).
      eapply EScalar_InSubqueryError; eassumption.
  + exists (SqlError error).
    eapply EScalar_InArgumentsError; exact Hvalues.
- intros subquery Hsubquery.
  unfold ScalarScheduledOutcomeProgress.
  unfold QueryScheduledOutcomeProgress in Hsubquery.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct (Hsubquery schedule env Hready) as
    [Hquery [Hcardinality Hexists]].
  destruct Hexists as [[truth | error] Houtcome].
  + exists (SqlSuccess truth); now apply EScalar_ExistsSuccess.
  + exists (SqlError error); now apply EScalar_ExistsError.
- intros result_type null_value subquery Hsubquery.
  unfold ScalarScheduledOutcomeProgress.
  unfold QueryScheduledOutcomeProgress in Hsubquery.
  intros schedule env Hready.
  cbn [scalar_expr_progress_ready] in Hready.
  destruct Hready as [Hnull Hsubquery_ready].
  destruct (Hsubquery schedule env Hsubquery_ready) as
    [Hquery [Hcardinality Hexists]].
  destruct Hquery as [outcome Houtcome].
  exists
    (scalar_subquery_value_outcome T null_value
      (query_expr_outputs subquery) outcome).
  eapply EScalar_Subquery; eassumption.
Qed.

End ScheduledOutcomeProgress.

(** Fixed-schedule TNull row progress.  The quantified schedule remains
    arbitrary, and the witness may be either successful rows or a SQL error. *)
Theorem tnull_query_expr_progress_ready_scheduled_progress :
  forall db env query,
    @query_expr_progress_ready TNull relname
      NullValues.is_null_value query ->
    forall schedule,
      exists outcome,
        @eval_query_expr_outcome TNull relname
          (@_basesort TNull db) (@_instance TNull db) unknown3
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          NullValues.is_null_value schedule env query outcome.
Proof.
intros db env query Hready schedule.
pose proof
  (proj1
    (@query_scalar_expr_progress_ready_has_outcomes TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value) query) as Hprogress.
unfold QueryScheduledOutcomeProgress in Hprogress.
destruct (Hprogress schedule env Hready) as [Hrows _].
exact Hrows.
Qed.

(** Cardinality demand is inhabited under the same structural contract; its
    outcome likewise preserves every reached SQL error. *)
Theorem tnull_query_expr_progress_ready_scheduled_cardinality_progress :
  forall db env query,
    @query_expr_progress_ready TNull relname
      NullValues.is_null_value query ->
    forall schedule,
      exists outcome,
        @eval_query_cardinality_outcome TNull relname
          (@_basesort TNull db) (@_instance TNull db) unknown3
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          NullValues.is_null_value schedule env query outcome.
Proof.
intros db env query Hready schedule.
pose proof
  (proj1
    (@query_scalar_expr_progress_ready_has_outcomes TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value) query) as Hprogress.
unfold QueryScheduledOutcomeProgress in Hprogress.
destruct (Hprogress schedule env Hready) as [_ [Hcardinality _]].
exact Hcardinality.
Qed.

(** EXISTS demand is separately inhabited, including FETCH 0's explicit
    analysis-error placement premise and GROUP/JOIN cardinality routing. *)
Theorem tnull_query_expr_progress_ready_scheduled_exists_progress :
  forall db env query,
    @query_expr_progress_ready TNull relname
      NullValues.is_null_value query ->
    forall schedule,
      exists outcome,
        @eval_query_exists_outcome TNull relname
          (@_basesort TNull db) (@_instance TNull db) unknown3
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          NullValues.is_null_value schedule env query outcome.
Proof.
intros db env query Hready schedule.
pose proof
  (proj1
    (@query_scalar_expr_progress_ready_has_outcomes TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value) query) as Hprogress.
unfold QueryScheduledOutcomeProgress in Hprogress.
destruct (Hprogress schedule env Hready) as [_ [_ Hexists]].
exact Hexists.
Qed.

(** Typed scalar progress is exposed without conflating value and Boolean
    outcomes.  Scalar EXISTS and scalar subqueries reuse the query demand
    progress proved above. *)
Theorem tnull_scalar_expr_progress_ready_scheduled_progress :
  forall db env kind (expression : @scalar_expr TNull relname kind),
    @scalar_expr_progress_ready TNull relname
      NullValues.is_null_value kind expression ->
    forall schedule,
      match kind as result_kind return
          @scalar_expr TNull relname result_kind -> Prop with
      | ScalarResultValue =>
          fun value_expression => exists outcome,
            @eval_scalar_value_expr_outcome TNull relname
              (@_basesort TNull db) (@_instance TNull db) unknown3
              NullValues.interp_scalar_operator_runtime_error
              NullValues.interp_aggregate_runtime_error
              NullValues.is_null_value schedule env value_expression outcome
      | ScalarResultBoolean =>
          fun boolean_expression => exists outcome,
            @eval_scalar_boolean_expr_outcome TNull relname
              (@_basesort TNull db) (@_instance TNull db) unknown3
              NullValues.interp_scalar_operator_runtime_error
              NullValues.interp_aggregate_runtime_error
              NullValues.is_null_value schedule env boolean_expression outcome
      end expression.
Proof.
intros db env kind expression Hready schedule.
pose proof
  (proj2
    (@query_scalar_expr_progress_ready_has_outcomes TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value) kind expression) as Hprogress.
unfold ScalarScheduledOutcomeProgress in Hprogress.
destruct kind; exact (Hprogress schedule env Hready).
Qed.

(** Public TNull admission gives scheduled progress for every legal Boolean
    schedule.  This remains an inhabitation theorem, not runtime safety. *)
Theorem tnull_query_expr_well_placed_scheduled_progress :
  forall db env query,
    TNullQueryExprAdmissible (@_basesort TNull db) query ->
    forall schedule,
      exists outcome,
        @eval_query_expr_outcome TNull relname
          (@_basesort TNull db) (@_instance TNull db) unknown3
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          NullValues.is_null_value schedule env query outcome.
Proof.
intros db env query Hwell_placed schedule.
eapply tnull_query_expr_progress_ready_scheduled_progress.
- exact
    (tnull_query_expr_well_placed_progress_ready
      (@_basesort TNull db) query Hwell_placed).
Qed.

(** The possible-outcome façade chooses one legal schedule only to witness
    existence.  It does not assert that schedule's outcome is unique, or
    remove the other outcomes from the nondeterministic relation. *)
Theorem tnull_query_expr_well_placed_possible_progress :
  forall db env query,
    TNullQueryExprAdmissible (@_basesort TNull db) query ->
    exists outcome, TNullQueryExprOutcome db env query outcome.
Proof.
intros db env query Hwell_placed.
unfold TNullQueryExprOutcome, eval_query_expr_outcome_in_env.
eapply (@query_expr_scheduled_progress_has_possible_outcome
  TNull relname (@_basesort TNull db) (@_instance TNull db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  env query).
unfold query_expr_scheduled_progress.
intro schedule.
now apply tnull_query_expr_well_placed_scheduled_progress.
Qed.
