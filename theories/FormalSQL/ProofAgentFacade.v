(******************************************************************************)
(** Stable, compact TNull proof surface for generated FormalSQL developments. **)
(******************************************************************************)

From SQLFS Require Export SqlQuerySyntax SqlQuerySemantics SqlQueryContexts.
From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Join Env Bool3 Projection SqlOutcome
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
From Stdlib Require Import List Lia NArith SetoidList SetoidPermutation.

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
