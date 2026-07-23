(******************************************************************************)
(** Stable, compact TNull proof surface for generated FormalSQL developments. **)
(******************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Join Env Formula Bool3 Projection SqlAlgebra SqlOutcome SqlQuerySyntax SqlQuerySemantics
  SqlQueryWellFormed SqlBagAbstraction SqlQueryFacts SqlErrorSemantics.
From Logos.FormalSQL Require Import
  TNullSyntax QueryTNullSyntax RewriteSpec CardinalityCombinators
  AggregateRuntimeFacts GroupingRewriteFacts RelationalAlgebraFacts
  GroupedFilterOutcomeFacts OccFacts.
From Stdlib Require Import List.

Import ListNotations.
Import Tuple.

(** These aliases deliberately hide the module paths of FormalSQL's tuple and
    finite-collection implementation.  They add no equality or quotienting. *)
Definition TNullAttribute : Type := attribute TNull.
Definition TNullRow : Type := tuple TNull.
Definition TNullValue : Type := value TNull.
Definition TNullAttributeSet : Type := Fset.set (A TNull).
Definition TNullEnvironment : Type := Env.env TNull.
Definition TNullSelectList : Type := SelectListT.
Definition TNullQuery : Type := Query.
Definition TNullQueryExpr : Type := QueryExpr.
Definition TNullQueryProgram : Type := QueryProgram.
Definition TNullFormulaExpr : Type := @formula_expr TNull relname.
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

Definition TNullRowPermut (left right : list TNullRow) : Prop :=
  Oeset.permut TNullRowOrder left right.

Definition TNullAttributeSetEq
    (left right : TNullAttributeSet) : Prop :=
  left =S= right.

Definition TNullBagEq (left right : TNullRowBag) : Prop :=
  bag_eq TNull left right.

Definition TNullRowsBag (rows : list TNullRow) : TNullRowBag :=
  rows_bag TNull rows.

(** Stable names for proof boundaries that generated developments must keep
    separate.  These are transparent aliases of the authoritative FormalSQL
    predicates, not alternate semantics. *)
Definition TNullBagQueryAdmissible
    (db : TNullDatabase) (query : TNullQuery) : Prop :=
  @bag_query_admissible TNull relname (@_basesort TNull db) query.

Definition TNullQueryExprAdmissible
    (db : TNullDatabase) (query : TNullQueryExpr) : Prop :=
  @query_expr_admissible TNull relname (@_basesort TNull db) query.

Definition TNullQueryExprOutcome
    (db : TNullDatabase) (env : TNullEnvironment)
    (query : TNullQueryExpr) (outcome : TNullRowsOutcome) : Prop :=
  eval_query_expr_outcome_in_env db env query outcome.

Definition TNullQueryExprOutcomeEq
    (db : TNullDatabase) (env : TNullEnvironment)
    (left right : TNullQueryExpr) : Prop :=
  query_expr_outcome_equiv_in_env db env left right.

Definition TNullQueryProgramOutcomeEq
    (db : TNullDatabase) (env : TNullEnvironment)
    (left right : TNullQueryProgram) : Prop :=
  query_program_outcome_equiv_in_env db env left right.

Definition TNullEvalGroupsOutcome
    (db : TNullDatabase) (env : TNullEnvironment)
    (select : TNullSelectList) (group_terms : list AggTerm)
    (having : TNullFormulaExpr) (groups : list (list TNullRow))
    (outcome : TNullRowsOutcome) : Prop :=
  @eval_groups_outcome TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms having groups outcome.

Definition TNullGroupedKeyFormulaContract
    (db : TNullDatabase) (env : TNullEnvironment)
    (group_terms : list AggTerm) (key_formula : TNullFormulaExpr)
    (groups : list (list TNullRow)) (keep : list TNullRow -> bool) : Prop :=
  @grouped_key_formula_contract TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env group_terms key_formula groups keep.

Definition TNullSkippedGroupRuntimeSafe
    (db : TNullDatabase) (env : TNullEnvironment)
    (select : TNullSelectList) (group_terms : list AggTerm)
    (rest_having : TNullFormulaExpr) (groups : list (list TNullRow))
    (keep : list TNullRow -> bool) : Prop :=
  @skipped_group_runtime_safe TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms rest_having groups keep.

Definition TNullBagFormulaGroupKeyLink
    (db : TNullDatabase) (env : TNullEnvironment)
    (group_terms : list AggTerm) (bag_formula : Formula)
    (key_formula : TNullFormulaExpr) (rows : list TNullRow)
    (keep_key : list TNullValue -> bool) : Prop :=
  @bag_formula_group_key_link TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env group_terms bag_formula key_formula rows keep_key.

Definition TNullGroupedKeyKeep
    (env : TNullEnvironment) (group_terms : list AggTerm)
    (keep_key : list TNullValue -> bool) : list TNullRow -> bool :=
  @grouped_key_keep TNull env group_terms keep_key.

Definition TNullBagFormulaRowKeep
    (db : TNullDatabase) (env : TNullEnvironment)
    (formula : Formula) : TNullRow -> bool :=
  @bag_formula_row_keep TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    env formula.

(** TNull specialization of the exact grouped-key HAVING bridge.  The two
    premises retain aggregate-finalization, formula-error, and skipped-group
    obligations instead of silently treating HAVING as a Boolean filter. *)
Lemma tnull_eval_groups_having_key_conj_filter_exact :
  forall db env select group_terms key_formula rest_having groups keep,
    TNullGroupedKeyFormulaContract
      db env group_terms key_formula groups keep ->
    TNullSkippedGroupRuntimeSafe
      db env select group_terms rest_having groups keep ->
    forall outcome,
      TNullEvalGroupsOutcome db env select group_terms
        (FExpr_Conj And_F key_formula rest_having) groups outcome <->
      TNullEvalGroupsOutcome db env select group_terms rest_having
        (filter keep groups) outcome.
Proof.
intros db env select group_terms key_formula rest_having groups keep
  Hkey Hsafe outcome.
exact
  (@eval_groups_having_key_conj_filter_exact TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms key_formula rest_having groups keep
    Hkey Hsafe outcome).
Qed.

(** Compositional specialization linking the compact bag [Formula] used by
    [Sigma] to the exact [FormulaExpr] used by HAVING. *)
Lemma tnull_eval_groups_having_key_conj_after_bag_filter_exact :
  forall db env select group_terms key_formula rest_having rows
      bag_formula keep_key,
    group_terms <> nil ->
    TNullBagFormulaGroupKeyLink
      db env group_terms bag_formula key_formula rows keep_key ->
    TNullSkippedGroupRuntimeSafe db env select group_terms rest_having
      (@query_make_groups TNull env rows group_terms)
      (TNullGroupedKeyKeep env group_terms keep_key) ->
    forall outcome,
      TNullEvalGroupsOutcome db env select group_terms
        (FExpr_Conj And_F key_formula rest_having)
        (@query_make_groups TNull env rows group_terms) outcome <->
      TNullEvalGroupsOutcome db env select group_terms rest_having
        (@query_make_groups TNull env
          (filter (TNullBagFormulaRowKeep db env bag_formula) rows)
          group_terms) outcome.
Proof.
intros db env select group_terms key_formula rest_having rows
  bag_formula keep_key Hnonempty Hlink Hsafe outcome.
exact
  (@eval_groups_having_key_conj_after_bag_formula_filter_exact
    TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms key_formula rest_having rows bag_formula keep_key
    Hnonempty Hlink Hsafe outcome).
Qed.

Definition TNullBagMap
    (mapping : TNullRow -> TNullRow) (bag : TNullRowBag) : TNullRowBag :=
  Febag.map TNullRowBagRecord TNullRowBagRecord mapping bag.

Definition TNullProjectRow
    (env : TNullEnvironment) (select : TNullSelectList) (row : TNullRow) :
    TNullRow :=
  projected_tuple env select row.

Definition TNullRowLabels (row : TNullRow) : TNullAttributeSet :=
  labels TNull row.

Definition TNullRowValue
    (row : TNullRow) (attribute : TNullAttribute) : TNullValue :=
  dot TNull row attribute.

(** Public row-level wrapper for a direct projection.  Attribute presence and
    output uniqueness remain explicit premises. *)
Lemma tnull_direct_projection_preserves_attribute :
  forall (env : TNullEnvironment) (select : TNullSelectList)
      (attribute : TNullAttribute) (row : TNullRow),
    select_list_directly_selects_attr select attribute ->
    select_list_has_unique_outputs select ->
    attribute inS TNullRowLabels row ->
    TNullRowValue (TNullProjectRow env select row) attribute =
    TNullRowValue row attribute.
Proof.
intros env select attribute row Hselect Hunique Hpresent.
exact
  (direct_projection_preserves_attr
    env select attribute Hselect Hunique row Hpresent).
Qed.

(** A direct projection is extensionally the original row when it selects
    every original attribute, has unique outputs, and has exactly the same
    labels.  These premises do not assume structural tuple equality. *)
Lemma tnull_direct_projection_row_eq :
  forall (env : TNullEnvironment) (select : TNullSelectList)
      (row : TNullRow),
    select_list_has_unique_outputs select ->
    (forall attribute,
      attribute inS TNullRowLabels row ->
      select_list_directly_selects_attr select attribute) ->
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select row))
      (TNullRowLabels row) ->
    TNullRowEq (TNullProjectRow env select row) row.
Proof.
intros env select row Hunique Hselect Hlabels.
unfold TNullRowEq, TNullRowOrder.
apply (proj2 (@tuple_eq TNull _ _)); split.
- exact Hlabels.
- intros attribute Hprojected.
  assert (Hrow : attribute inS TNullRowLabels row).
  {
    unfold TNullAttributeSetEq in Hlabels.
    rewrite <- (Fset.mem_eq_2 _ _ _ Hlabels).
    exact Hprojected.
  }
  apply tnull_direct_projection_preserves_attribute.
  + now apply Hselect.
  + exact Hunique.
  + exact Hrow.
Qed.

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

(** TNull specialization of the existing double-projection bag law. *)
Lemma tnull_double_projection_bag_eq :
  forall env outer_left inner_left outer_right inner_right bag,
    (forall row,
      TNullRowEq
        (TNullProjectRow env outer_left
          (TNullProjectRow env inner_left row))
        (TNullProjectRow env outer_right
          (TNullProjectRow env inner_right row))) ->
    TNullBagEq
      (TNullBagMap
        (fun row => TNullProjectRow env outer_left row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner_left row) bag))
      (TNullBagMap
        (fun row => TNullProjectRow env outer_right row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner_right row) bag)).
Proof.
intros env outer_left inner_left outer_right inner_right bag Hrows.
unfold TNullRowEq, TNullBagEq, TNullBagMap, TNullProjectRow in *.
now apply double_projection_bag_eq.
Qed.

(** Query-level specialization using the database's exact basesort and
    instance.  This proves only bag equality; runtime-error obligations remain
    separate. *)
Lemma tnull_double_projection_query_bag_eq :
  forall (db : TNullDatabase) (env : TNullEnvironment)
      (outer_left inner_left outer_right inner_right : TNullSelectList)
      (input : TNullQuery),
    (forall row,
      TNullRowEq
        (TNullProjectRow env outer_left
          (TNullProjectRow env inner_left row))
        (TNullProjectRow env outer_right
          (TNullProjectRow env inner_right row))) ->
    TNullBagEq
      (eval_query_in_env db env
        (Pi outer_left (Pi inner_left input)))
      (eval_query_in_env db env
        (Pi outer_right (Pi inner_right input))).
Proof.
intros db env outer_left inner_left outer_right inner_right input Hrows.
unfold TNullRowEq, TNullBagEq, TNullProjectRow,
  eval_query_in_env, Pi in *.
now apply double_projection_query_bag_eq.
Qed.

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

(******************************************************************************)
(** Error-preserving compact-query reset and projection composition surface. **)
(******************************************************************************)

(** Exact deterministic runtime-error observation for the compact bag algebra.
    This is a transparent name for the authoritative FormalSQL evaluator. *)
Definition TNullQueryRuntimeError
    (db : TNullDatabase) (env : TNullEnvironment) (query : TNullQuery) :=
  query_runtime_error_in_env db env query.

(** Per-row projection error observation. *)
Definition TNullSelectListRuntimeError
    (env : TNullEnvironment) (select : TNullSelectList) :=
  @eval_select_list_runtime_error TNull
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error env select.

(** Per-row compact WHERE/HAVING error observation, including correlated
    compact subqueries evaluated against the same database. *)
Definition TNullFormulaRuntimeError
    (db : TNullDatabase) (env : TNullEnvironment)
    (formula : Formula) :=
  @eval_formula_runtime_error TNull relname
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    (@eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error)
    env formula.

(** The exact local error scans owned by compact [Pi] and [Sigma].  Separate
    names make the first-error order visible rather than hiding it behind a
    blanket safety premise. *)
Definition TNullProjectionScanRuntimeError
    (db : TNullDatabase) (env : TNullEnvironment)
    (select : TNullSelectList) (input : TNullQuery) :=
  first_runtime_error
    (fun row => TNullSelectListRuntimeError (env_t TNull env row) select)
    (Febag.elements TNullRowBagRecord (eval_query_in_env db env input)).

Definition TNullFilterScanRuntimeError
    (db : TNullDatabase) (env : TNullEnvironment)
    (formula : Formula) (input : TNullQuery) :=
  first_runtime_error
    (fun row => TNullFormulaRuntimeError db (env_t TNull env row) formula)
    (Febag.elements TNullRowBagRecord (eval_query_in_env db env input)).

(** A [QExpr_Bag] reset preserves the complete outcome relation when the
    ordered output signatures are exactly equal, the deterministic error
    discriminator is equal, and successful compact results are equal as
    FormalSQL bags.  Bag equality deliberately quotients only semantic tuple
    representation; it retains every multiplicity. *)
Lemma tnull_qexpr_bag_outcome_eq_of_runtime_and_bag_eq :
  forall db env left_outputs right_outputs left right,
    left_outputs = right_outputs ->
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env right ->
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env right) ->
    TNullQueryExprOutcomeEq db env
      (QExpr_Bag left_outputs left)
      (QExpr_Bag right_outputs right).
Proof.
intros db env left_outputs right_outputs left right
  Houtputs Hruntime Hbags.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env.
apply query_expr_outcome_equiv_of_observations.
- cbn [query_expr_outputs]; exact Houtputs.
- unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hruntime.
  destruct
    (@eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env left)
    as [error |] eqn:Hleft.
  + exists (SqlError error).
    apply eval_query_expr_bag_error_iff.
    unfold eval_query_outcome; now rewrite Hleft.
  + exists
      (SqlSuccess
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env left))).
    apply eval_query_expr_bag_success_iff.
    exists (eval_query_in_env db env left); split.
    * unfold eval_query_outcome, eval_query_in_env; now rewrite Hleft.
    * unfold query_same_rows_as_bag, query_rows_bag.
      apply Febag.elements_mk_bag.
- unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hruntime.
  destruct
    (@eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env right)
    as [error |] eqn:Hright.
  + exists (SqlError error).
    apply eval_query_expr_bag_error_iff.
    unfold eval_query_outcome; now rewrite Hright.
  + exists
      (SqlSuccess
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env right))).
    apply eval_query_expr_bag_success_iff.
    exists (eval_query_in_env db env right); split.
    * unfold eval_query_outcome, eval_query_in_env; now rewrite Hright.
    * unfold query_same_rows_as_bag, query_rows_bag.
      apply Febag.elements_mk_bag.
- intros rows Hleft.
  apply eval_query_expr_bag_success_iff in Hleft.
  destruct Hleft as [left_bag [Hleft Hrows]].
  unfold eval_query_outcome in Hleft.
  unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hruntime.
  destruct
    (@eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env left)
    as [left_error |] eqn:Hleft_error; [discriminate |].
  inversion Hleft; subst left_bag.
  assert (Hright_error :
    @eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env right = None).
  { now rewrite <- Hruntime. }
  exists rows; split.
  + apply eval_query_expr_bag_success_iff.
    exists (eval_query_in_env db env right); split.
    * unfold eval_query_outcome, eval_query_in_env.
      now rewrite Hright_error.
    * eapply query_same_rows_as_bag_bag_transport; [exact Hrows |].
      exact Hbags.
  + apply ordered_rows_equiv_refl.
- intros rows Hright.
  apply eval_query_expr_bag_success_iff in Hright.
  destruct Hright as [right_bag [Hright Hrows]].
  unfold eval_query_outcome in Hright.
  unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hruntime.
  destruct
    (@eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env right)
    as [right_error |] eqn:Hright_error; [discriminate |].
  inversion Hright; subst right_bag.
  assert (Hleft_error :
    @eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env left = None).
  { now rewrite Hruntime. }
  exists rows; split.
  + apply eval_query_expr_bag_success_iff.
    exists (eval_query_in_env db env left); split.
    * unfold eval_query_outcome, eval_query_in_env.
      now rewrite Hleft_error.
    * eapply query_same_rows_as_bag_bag_transport; [exact Hrows |].
      now apply bag_eq_sym.
  + apply ordered_rows_equiv_refl.
- intro error.
  rewrite 2 eval_query_expr_bag_error_iff.
  unfold eval_query_outcome.
  unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hruntime.
  rewrite Hruntime.
  destruct
    (@eval_query_runtime_error TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error env right);
    simpl; [reflexivity | split; discriminate].
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

(** Direct projection against a separately named expected schema.  The two
    label equalities keep the empty/renamed-column cases explicit. *)
Lemma tnull_direct_projection_row_eq_on_expected_labels :
  forall env select expected row,
    select_list_has_unique_outputs select ->
    (forall attribute,
      attribute inS expected ->
      select_list_directly_selects_attr select attribute) ->
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select row)) expected ->
    TNullAttributeSetEq (TNullRowLabels row) expected ->
    TNullRowEq (TNullProjectRow env select row) row.
Proof.
intros env select expected row Hunique Hselect Hprojected Hrow.
apply tnull_direct_projection_row_eq; [exact Hunique | |].
- intros attribute Hpresent.
  apply Hselect.
  unfold TNullAttributeSetEq in Hrow.
  rewrite <- (Fset.mem_eq_2 _ _ _ Hrow).
  exact Hpresent.
- unfold TNullAttributeSetEq in *.
  rewrite Fset.equal_spec in Hprojected, Hrow |- *.
  intro attribute.
  now rewrite (Hprojected attribute), (Hrow attribute).
Qed.

(** Pointwise semantic row equality lifts through one bag map without
    collapsing duplicates. *)
Lemma tnull_bag_map_ext :
  forall left_map right_map bag,
    (forall row,
      In row (Febag.elements TNullRowBagRecord bag) ->
      TNullRowEq (left_map row) (right_map row)) ->
    TNullBagEq
      (TNullBagMap left_map bag)
      (TNullBagMap right_map bag).
Proof.
intros left_map right_map bag Hmaps.
unfold TNullBagEq, TNullBagMap, bag_eq.
rewrite Febag.nb_occ_equal; intro output.
rewrite 2 Febag.map_unfold, 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_alt TNullRowOrder).
intros row Hrow; apply Hmaps; exact Hrow.
Qed.

Lemma tnull_bag_map_identity :
  forall bag,
    TNullBagEq (TNullBagMap (fun row => row) bag) bag.
Proof.
intro bag.
unfold TNullBagEq, TNullBagMap, bag_eq, Febag.map.
rewrite List.map_id.
apply Febag.elements_mk_bag.
Qed.

(** Nested projection maps agree with their composed row map.  Projection is
    proper for semantic tuple equality, which is the exact side condition
    needed by finite-collection map composition. *)
Lemma tnull_projection_bag_map_compose :
  forall env outer inner bag,
    TNullBagEq
      (TNullBagMap
        (fun row => TNullProjectRow env outer row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner row) bag))
      (TNullBagMap
        (fun row =>
          TNullProjectRow env outer (TNullProjectRow env inner row)) bag).
Proof.
intros env outer inner bag.
unfold TNullBagEq, TNullBagMap, TNullProjectRow, bag_eq.
rewrite Febag.nb_occ_equal; intro output.
assert (Hmap :
  Fecol.nb_occ output
    (Fecol.map (CTuple TNull)
      (fun row => projection TNull (env_t TNull env row)
        (@Select_List TNull outer))
      (Fecol.map (CTuple TNull)
        (fun row => projection TNull (env_t TNull env row)
          (@Select_List TNull inner))
        (Fecol.Fbag bag))) =
  Fecol.nb_occ output
    (Fecol.map (CTuple TNull)
      (fun row =>
        projection TNull
          (env_t TNull env
            (projection TNull (env_t TNull env row)
              (@Select_List TNull inner)))
          (@Select_List TNull outer))
      (Fecol.Fbag bag))).
{
  apply Fecol.nb_occ_map_map.
  intros left right _ _ Hequal.
  apply projection_eq, env_t_eq_2; exact Hequal.
}
rewrite 2 Fecol.nb_occ_bag in Hmap.
cbn [Fecol.map Fecol.to_bag] in Hmap.
exact Hmap.
Qed.

(** One direct projection and a two-stage projection are bag-equal whenever
    their composed row functions are extensionally equal. *)
Lemma tnull_single_double_projection_bag_eq :
  forall env single outer inner bag,
    (forall row,
      In row (Febag.elements TNullRowBagRecord bag) ->
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row))) ->
    TNullBagEq
      (TNullBagMap (fun row => TNullProjectRow env single row) bag)
      (TNullBagMap
        (fun row => TNullProjectRow env outer row)
        (TNullBagMap
          (fun row => TNullProjectRow env inner row) bag)).
Proof.
intros env single outer inner bag Hrows.
eapply bag_eq_trans.
- apply tnull_bag_map_ext.
  intros row Hrow; now apply Hrows.
- apply bag_eq_sym, tnull_projection_bag_map_compose.
Qed.

Lemma tnull_single_double_projection_query_bag_eq :
  forall db env single outer inner input,
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullRowEq
        (TNullProjectRow env single row)
        (TNullProjectRow env outer (TNullProjectRow env inner row))) ->
    TNullBagEq
      (eval_query_in_env db env (Pi single input))
      (eval_query_in_env db env (Pi outer (Pi inner input))).
Proof.
intros db env single outer inner input Hrows.
unfold TNullBagEq, eval_query_in_env, Pi.
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Pi TNull relname single input)).
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Pi TNull relname outer (@Q_Pi TNull relname inner input))).
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_Pi TNull relname inner input)).
fold (TNullBagEq
  (TNullBagMap
    (fun row => TNullProjectRow env single row)
    (@eval_query TNull relname
      (@_basesort TNull db) (@_instance TNull db)
      unknown3 contains_nulls env input))
  (TNullBagMap
    (fun row => TNullProjectRow env outer row)
    (TNullBagMap
      (fun row => TNullProjectRow env inner row)
      (@eval_query TNull relname
        (@_basesort TNull db) (@_instance TNull db)
        unknown3 contains_nulls env input)))).
now apply tnull_single_double_projection_bag_eq.
Qed.

(** Eliminating a direct projection over an arbitrary compact input.  Row
    equality is required for every semantic input representative. *)
Lemma tnull_direct_projection_query_bag_eq :
  forall db env select input,
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullRowEq (TNullProjectRow env select row) row) ->
    TNullBagEq
      (eval_query_in_env db env (Pi select input))
      (eval_query_in_env db env input).
Proof.
intros db env select input Hrows.
eapply bag_eq_trans with
  (second :=
    TNullBagMap (fun row => row) (eval_query_in_env db env input)).
- unfold eval_query_in_env, Pi at 1.
  rewrite (@eval_query_unfold TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
    (@Q_Pi TNull relname select input)).
  apply tnull_bag_map_ext.
  intros row Hrow; apply Hrows; exact Hrow.
- apply tnull_bag_map_identity.
Qed.

Corollary tnull_direct_table_projection_query_bag_eq :
  forall db env relation select,
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord (@_instance TNull db relation)) ->
      TNullRowEq (TNullProjectRow env select row) row) ->
    TNullBagEq
      (eval_query_in_env db env
        (Pi select (@Q_Table TNull relname relation)))
      (eval_query_in_env db env (@Q_Table TNull relname relation)).
Proof.
intros db env relation select Hrows.
apply tnull_direct_projection_query_bag_eq.
exact Hrows.
Qed.

(** Compact bag-result congruence.  These lemmas transport only the pure bag
    result; the following runtime lemmas keep errors separate. *)
Lemma tnull_cross_join_eval_bag_congr :
  forall db env left left' right right',
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env left') ->
    TNullBagEq
      (eval_query_in_env db env right)
      (eval_query_in_env db env right') ->
    TNullBagEq
      (eval_query_in_env db env (CrossJoin left right))
      (eval_query_in_env db env (CrossJoin left' right')).
Proof.
intros db env left left' right right' Hleft Hright.
unfold TNullBagEq, eval_query_in_env, CrossJoin in *.
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_CrossJoin TNull relname left right)).
rewrite (@eval_query_unfold TNull relname
  (@_basesort TNull db) (@_instance TNull db) unknown3 contains_nulls env
  (@Q_CrossJoin TNull relname left' right')).
now apply query_cross_join_bag_congr.
Qed.

Lemma tnull_pi_eval_bag_congr :
  forall db env select left right,
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env right) ->
    TNullBagEq
      (eval_query_in_env db env (Pi select left))
      (eval_query_in_env db env (Pi select right)).
Proof.
intros db env select left right Hbag.
exact (pi_eval_bag_congr db env select left right Hbag).
Qed.

Lemma tnull_sigma_eval_bag_congr :
  forall db env formula left right,
    TNullBagEq
      (eval_query_in_env db env left)
      (eval_query_in_env db env right) ->
    TNullBagEq
      (eval_query_in_env db env (Sigma formula left))
      (eval_query_in_env db env (Sigma formula right)).
Proof.
intros db env formula left right Hbag.
exact (sigma_eval_bag_congr db env formula left right Hbag).
Qed.

(** Exact runtime-error congruence exposes both the child discriminator and
    the local first-error scan. *)
Lemma tnull_cross_join_runtime_error_congr :
  forall db env left left' right right',
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env left' ->
    TNullQueryRuntimeError db env right =
      TNullQueryRuntimeError db env right' ->
    TNullQueryRuntimeError db env (CrossJoin left right) =
      TNullQueryRuntimeError db env (CrossJoin left' right').
Proof.
intros db env left left' right right' Hleft Hright.
unfold TNullQueryRuntimeError, query_runtime_error_in_env, CrossJoin in *.
cbn [eval_query_runtime_error].
now rewrite Hleft, Hright.
Qed.

Lemma tnull_pi_runtime_error_congr :
  forall db env select left right,
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env right ->
    TNullProjectionScanRuntimeError db env select left =
      TNullProjectionScanRuntimeError db env select right ->
    TNullQueryRuntimeError db env (Pi select left) =
      TNullQueryRuntimeError db env (Pi select right).
Proof.
intros db env select left right Hchild Hscan.
unfold TNullQueryRuntimeError, TNullProjectionScanRuntimeError,
  query_runtime_error_in_env, TNullSelectListRuntimeError,
  eval_query_in_env, Pi in *.
cbn [eval_query_runtime_error].
unfold TNullRowBagRecord, TNullRowCollection in Hscan.
unfold SqlErrorSemantics.BTupleT.
apply f_equal2; assumption.
Qed.

Lemma tnull_sigma_runtime_error_congr :
  forall db env formula left right,
    TNullQueryRuntimeError db env left =
      TNullQueryRuntimeError db env right ->
    TNullFilterScanRuntimeError db env formula left =
      TNullFilterScanRuntimeError db env formula right ->
    TNullQueryRuntimeError db env (Sigma formula left) =
      TNullQueryRuntimeError db env (Sigma formula right).
Proof.
intros db env formula left right Hchild Hscan.
unfold TNullQueryRuntimeError, TNullFilterScanRuntimeError,
  query_runtime_error_in_env, TNullFormulaRuntimeError,
  eval_query_in_env, Sigma in *.
cbn [eval_query_runtime_error].
unfold TNullRowBagRecord, TNullRowCollection in Hscan.
unfold SqlErrorSemantics.BTupleT.
apply f_equal2; assumption.
Qed.

Corollary tnull_cross_join_runtime_error_none :
  forall db env left right,
    TNullQueryRuntimeError db env left = None ->
    TNullQueryRuntimeError db env right = None ->
    TNullQueryRuntimeError db env (CrossJoin left right) = None.
Proof.
intros db env left right Hleft Hright.
unfold TNullQueryRuntimeError, query_runtime_error_in_env, CrossJoin in *.
cbn [eval_query_runtime_error].
now rewrite Hleft, Hright.
Qed.

Lemma tnull_pi_runtime_error_none :
  forall db env select input,
    TNullQueryRuntimeError db env input = None ->
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullSelectListRuntimeError (env_t TNull env row) select = None) ->
    TNullQueryRuntimeError db env (Pi select input) = None.
Proof.
intros db env select input Hinput Hselect.
unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hinput |- *.
unfold Pi.
cbn [eval_query_runtime_error].
rewrite Hinput; cbn.
rewrite first_runtime_error_none_iff.
now apply Forall_forall.
Qed.

Lemma tnull_sigma_runtime_error_none :
  forall db env formula input,
    TNullQueryRuntimeError db env input = None ->
    (forall row,
      In row
        (Febag.elements TNullRowBagRecord
          (eval_query_in_env db env input)) ->
      TNullFormulaRuntimeError db (env_t TNull env row) formula = None) ->
    TNullQueryRuntimeError db env (Sigma formula input) = None.
Proof.
intros db env formula input Hinput Hformula.
unfold TNullQueryRuntimeError, query_runtime_error_in_env in Hinput |- *.
unfold Sigma.
cbn [eval_query_runtime_error].
rewrite Hinput; cbn.
rewrite first_runtime_error_none_iff.
now apply Forall_forall.
Qed.
