(******************************************************************************)
(** Stable, compact TNull proof surface for generated FormalSQL developments. **)
(******************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Join Env Formula Bool3 Projection SqlOutcome SqlQuerySyntax SqlQuerySemantics
  SqlQueryWellFormed SqlBagAbstraction SqlQueryFacts SqlErrorSemantics
  SchemaConstraints.
From Logos.FormalSQL Require Import
  TNullSyntax QueryTNullSyntax SchemaCardinality QueryCardinality
  CardinalityCombinators
  OrderedQueryFacts
  AggregateRuntimeFacts GroupingRewriteFacts RelationalAlgebraFacts
  GroupedFilterOutcomeFacts NumericRegroupFacts.
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
Definition TNullSelectList : Type := SelectListT.
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

(** A runtime-safe scalar predicate supplies the exact TRUE/non-TRUE
    acceptance contract required by the generic JOIN evaluator.  This bridge
    preserves the underlying Bool3 result: FALSE and UNKNOWN are identified
    only by [Bool.is_true] at the SQL join-condition boundary. *)
Lemma tnull_join_condition_pred_acceptance_exact_safe :
  forall db env predicate arguments left right,
    first_runtime_error
      (@eval_aggterm_runtime_error TNull
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error
        (env_t TNull env (join_tuple TNull left right)))
      arguments = None ->
    @join_condition_acceptance_exact_at TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (FExpr_Pred predicate arguments) left right
      (Bool.is_true (B TNull)
        (NullValues.interp_predicate predicate
          (map
            (@Interp.interp_aggterm TNull
              (env_t TNull env (join_tuple TNull left right)))
            arguments))).
Proof.
intros db env predicate arguments left right Hsafe.
unfold join_condition_acceptance_exact_at.
exact
  (@formula_pred_acceptance_exact_safe TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    (env_t TNull env (join_tuple TNull left right))
    predicate arguments Hsafe).
Qed.

(** Stable names for proof boundaries that generated developments must keep
    separate.  These are transparent aliases of the authoritative FormalSQL
    predicates, not alternate semantics. *)
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
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms having groups outcome.

Definition TNullGroupedKeyFormulaContract
    (db : TNullDatabase) (env : TNullEnvironment)
    (group_terms : list AggTerm) (key_formula : TNullFormulaExpr)
    (groups : list (list TNullRow)) (keep : list TNullRow -> bool) : Prop :=
  @grouped_key_formula_contract TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env group_terms key_formula groups keep.

Definition TNullSkippedGroupRuntimeSafe
    (db : TNullDatabase) (env : TNullEnvironment)
    (select : TNullSelectList) (group_terms : list AggTerm)
    (rest_having : TNullFormulaExpr) (groups : list (list TNullRow))
    (keep : list TNullRow -> bool) : Prop :=
  @skipped_group_runtime_safe TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms rest_having groups keep.

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
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env select group_terms key_formula rest_having groups keep
    Hkey Hsafe outcome).
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

(** Exact first-match lookup used by a TNull SELECT list.  This is the lookup
    performed by FormalSQL's [projection]: when output aliases repeat, the
    first matching item supplies the cell value.  Exposing that operation
    directly lets generated proofs state the local lookup fact they need
    without assuming that every output alias in the SELECT list is unique. *)
Definition TNullSelectLookup
    (select : TNullSelectList) (attribute : TNullAttribute) : option AggTerm :=
  Oset.find (OAtt TNull) attribute
    (@Projection.pairs_of_selects TNull select).

(** The first SELECT item always owns its own output alias. *)
Lemma tnull_select_lookup_head :
  forall items expression attribute,
    TNullSelectLookup
      (SelectList (SelectAs expression attribute :: items)) attribute =
    Some expression.
Proof.
intros items expression attribute.
unfold TNullSelectLookup, SelectList, SelectAs,
  Projection.pairs_of_selects, Projection.pair_of_select.
cbn.
now rewrite Oset.eq_bool_refl.
Qed.

(** Looking past a differently named head item preserves the exact lookup in
    the tail.  The Boolean inequality is intentionally explicit because it is
    the branch condition used by [Oset.find]. *)
Lemma tnull_select_lookup_cons_other :
  forall items head_expression head_attribute attribute,
    Oset.eq_bool (OAtt TNull) attribute head_attribute = false ->
    TNullSelectLookup
      (SelectList (SelectAs head_expression head_attribute :: items))
      attribute =
    TNullSelectLookup (SelectList items) attribute.
Proof.
intros items head_expression head_attribute attribute Hdifferent.
unfold TNullSelectLookup, SelectList, SelectAs,
  Projection.pairs_of_selects, Projection.pair_of_select.
change
  ((if Oset.eq_bool (OAtt TNull) attribute head_attribute
    then Some head_expression
    else Oset.find (OAtt TNull) attribute
      (map (@Projection.pair_of_select TNull) items)) =
   Oset.find (OAtt TNull) attribute
     (map (@Projection.pair_of_select TNull) items)).
now rewrite Hdifferent.
Qed.

(** A successful lookup both retains its output label and fixes the exact
    projected cell value.  No [all_diff] premise is needed: [lookup] already
    names the expression selected by first-match semantics. *)
Lemma tnull_select_lookup_retained :
  forall env select attribute expression row,
    TNullSelectLookup select attribute = Some expression ->
    attribute inS
      TNullRowLabels (TNullProjectRow env select row) /\
    TNullRowValue (TNullProjectRow env select row) attribute =
      Interp.interp_aggterm TNull (env_t TNull env row) expression.
Proof.
intros env [items] attribute expression row Hlookup.
assert (Hselected :
  In (attribute, expression)
    (map (@Projection.pair_of_select TNull) items)).
{
  unfold TNullSelectLookup, Projection.pairs_of_selects in Hlookup.
  exact (Oset.find_some _ _ _ Hlookup).
}
assert (Houtput :
  In attribute
    (map
      (fun item =>
        match item with
        | @Projection.Select_As _ _ output => output
        end)
      items)).
{
  rewrite in_map_iff in Hselected.
  destruct Hselected as [item [Hpair Hitem]].
  destruct item as [selected_expression output].
  cbn [Projection.pair_of_select] in Hpair.
  injection Hpair as Hattribute Hexpression.
  subst output selected_expression.
  rewrite in_map_iff.
  exists (@Projection.Select_As TNull expression attribute).
  split; [reflexivity | exact Hitem].
}
assert (Hsort :
  attribute inS
    (@Projection.select_list_sort TNull (@_Select_List TNull items))).
{
  unfold Projection.select_list_sort, Projection.select_list_outputs.
  rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff.
  exact Houtput.
}
split.
- unfold TNullRowLabels, TNullProjectRow, projected_tuple.
  rewrite (Fset.mem_eq_2 _ _ _
    (@Projection.labels_projection TNull (env_t TNull env row) items)).
  exact Hsort.
- unfold TNullRowValue, TNullProjectRow, projected_tuple,
    Projection.projection.
  unfold TNullSelectLookup, Projection.pairs_of_selects in Hlookup.
  rewrite Tuple.dot_mk_tuple.
  unfold TNullAttribute in Hsort.
  rewrite Hsort.
  cbn [Projection.pairs_of_selects].
  now rewrite Hlookup.
Qed.

(** A projected label is present exactly when first-match lookup finds an
    expression for it.  Repeated aliases remain sound: the existential does
    not choose a later occurrence, and its witness is the expression actually
    returned by [Oset.find]. *)
Lemma tnull_select_lookup_some_iff_projected_label :
  forall env select attribute row,
    (exists expression,
      TNullSelectLookup select attribute = Some expression) <->
    attribute inS TNullRowLabels (TNullProjectRow env select row).
Proof.
intros env [items] attribute row; split.
- intros [expression Hlookup].
  exact (proj1
    (tnull_select_lookup_retained
      env (SelectList items) attribute expression row Hlookup)).
- intro Hpresent.
  assert (Houtput : In attribute
    (map
      (fun item =>
        match item with
        | @Projection.Select_As _ _ output => output
        end)
      items)).
  {
    unfold TNullRowLabels, TNullProjectRow, projected_tuple in Hpresent.
    rewrite (Fset.mem_eq_2 _ _ _
      (@Projection.labels_projection TNull (env_t TNull env row) items))
      in Hpresent.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff in Hpresent.
    exact Hpresent.
  }
  destruct (TNullSelectLookup (SelectList items) attribute)
    as [expression|] eqn:Hlookup.
  + now exists expression.
  + exfalso.
    apply (Oset.find_none_alt (OAtt TNull) attribute
      (map (@Projection.pair_of_select TNull) items) Hlookup).
    rewrite in_map_iff in Houtput.
    destruct Houtput as [item [Hattribute Hitem]].
    destruct item as [expression output].
    cbn in Hattribute; subst output.
    rewrite in_map_iff.
    exists (attribute, expression); split; [reflexivity|].
    rewrite in_map_iff.
    exists (@Projection.Select_As TNull expression attribute).
    split; [reflexivity|exact Hitem].
Qed.

(** Exact absence bridge for concrete generated projection shapes.  It is
    intentionally phrased with the Boolean membership test so callers can
    rewrite it directly, without unfolding [labels_projection]. *)
Lemma tnull_select_lookup_none_iff_projected_label_absent :
  forall env select attribute row,
    TNullSelectLookup select attribute = None <->
    (attribute inS? TNullRowLabels (TNullProjectRow env select row)) = false.
Proof.
intros env select attribute row; split.
- intro Hnone.
  destruct (attribute inS?
    TNullRowLabels (TNullProjectRow env select row)) eqn:Hpresent;
    [|reflexivity].
  assert (Hexists : exists expression,
    TNullSelectLookup select attribute = Some expression).
  {
    apply (proj2
      (tnull_select_lookup_some_iff_projected_label
        env select attribute row)).
    exact Hpresent.
  }
  destruct Hexists as [expression Hsome].
  rewrite Hnone in Hsome; discriminate.
- intro Habsent.
  destruct (TNullSelectLookup select attribute)
    as [expression|] eqn:Hlookup; [|reflexivity].
  pose proof
    (proj1
      (tnull_select_lookup_some_iff_projected_label
        env select attribute row)
      (ex_intro _ expression Hlookup)) as Hpresent.
  rewrite Habsent in Hpresent; discriminate.
Qed.

(** A lookup-selected direct reference reads the source cell whenever that
    source label is present on the input row.  Source presence remains
    explicit because an absent reference is resolved through the outer
    environment by SQL's correlated-name semantics. *)
Lemma tnull_select_lookup_direct_value :
  forall env select source target row,
    TNullSelectLookup select target = Some (AExpr (Dot source)) ->
    source inS TNullRowLabels row ->
    TNullRowValue (TNullProjectRow env select row) target =
    TNullRowValue row source.
Proof.
intros env select source target row Hlookup Hsource.
pose proof
  (proj2
    (tnull_select_lookup_retained
      env select target (AExpr (Dot source)) row Hlookup)) as Hvalue.
unfold TNullRowLabels in Hsource.
unfold AExpr, Dot in Hvalue.
rewrite
  (@interp_direct_attribute_in_env_t TNull env row source Hsource)
  in Hvalue.
exact Hvalue.
Qed.

(** A lookup-selected scalar constant is independent of both the input row
    and the outer environment. *)
Lemma tnull_select_lookup_constant_value :
  forall env select target value row,
    TNullSelectLookup select target = Some (AExpr (Constant value)) ->
    TNullRowValue (TNullProjectRow env select row) target = value.
Proof.
intros env select target value row Hlookup.
pose proof
  (proj2
    (tnull_select_lookup_retained
      env select target (AExpr (Constant value)) row Hlookup)) as Hvalue.
exact Hvalue.
Qed.

(** Cell-level composition of two direct projections.  Each stage records its
    own first-match lookup; the first lookup also establishes that the middle
    alias is present, so the second stage cannot fall through to the outer
    environment. *)
Lemma tnull_select_lookup_direct_compose :
  forall env first second source middle target row,
    TNullSelectLookup first middle = Some (AExpr (Dot source)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    source inS TNullRowLabels row ->
    target inS
      TNullRowLabels
        (TNullProjectRow env second (TNullProjectRow env first row)) /\
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    TNullRowValue row source.
Proof.
intros env first second source middle target row
  Hfirst Hsecond Hsource.
pose proof
  (proj1
    (tnull_select_lookup_retained
      env first middle (AExpr (Dot source)) row Hfirst)) as Hmiddle.
pose proof
  (proj1
    (tnull_select_lookup_retained
      env second target (AExpr (Dot middle))
      (TNullProjectRow env first row) Hsecond)) as Htarget.
split; [exact Htarget |].
rewrite
  (tnull_select_lookup_direct_value
    env second middle target (TNullProjectRow env first row)
    Hsecond Hmiddle).
now apply tnull_select_lookup_direct_value.
Qed.

(** Constant-producing projections compose through a later direct reference
    without any input-label premise.  This is useful for outer-join padding:
    the first stage materializes the padding cell and thereby makes the middle
    alias present before the second stage reads it. *)
Lemma tnull_select_lookup_constant_direct_compose :
  forall env first second value middle target row,
    TNullSelectLookup first middle = Some (AExpr (Constant value)) ->
    TNullSelectLookup second target = Some (AExpr (Dot middle)) ->
    target inS
      TNullRowLabels
        (TNullProjectRow env second (TNullProjectRow env first row)) /\
    TNullRowValue
      (TNullProjectRow env second (TNullProjectRow env first row)) target =
    value.
Proof.
intros env first second value middle target row Hfirst Hsecond.
pose proof
  (proj1
    (tnull_select_lookup_retained
      env first middle (AExpr (Constant value)) row Hfirst)) as Hmiddle.
pose proof
  (proj1
    (tnull_select_lookup_retained
      env second target (AExpr (Dot middle))
      (TNullProjectRow env first row) Hsecond)) as Htarget.
split; [exact Htarget |].
rewrite
  (tnull_select_lookup_direct_value
    env second middle target (TNullProjectRow env first row)
    Hsecond Hmiddle).
now apply tnull_select_lookup_constant_value.
Qed.

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

(** A direct SELECT item may rename its source attribute.  Under unique output
    aliases, reading the target field of the projected row returns exactly the
    source field of the input row.  Source presence is essential because an
    absent direct reference falls through to the outer environment. *)
Lemma tnull_direct_projection_alias_value :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (row : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels row ->
    TNullRowValue
      (TNullProjectRow env (@_Select_List TNull items) row) target =
    TNullRowValue row source.
Proof.
intros env items source target row Hselect Hunique Hpresent.
unfold select_list_has_unique_outputs in Hunique.
unfold TNullRowLabels in Hpresent.
unfold TNullRowValue, TNullProjectRow, projected_tuple.
rewrite (@dot_projection TNull (env_t TNull env row) items target
  (@A_Expr TNull (@F_Dot TNull source)) Hselect Hunique).
unfold Interp.interp_aggterm, Interp.interp_funterm,
  Interp.interp_dot, env_t.
simpl.
change
  ((if source inS? labels TNull row
    then @dot TNull row source
    else Interp.interp_dot TNull env source) =
   @dot TNull row source).
now rewrite Hpresent.
Qed.

(** A direct renamed projection retains both the target label and the exact
    source cell value.  The statement deliberately does not infer target-type
    conformance from two arbitrary attribute constructors; generated callers
    retain that typing obligation separately. *)
Lemma tnull_direct_projection_alias_retained :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (row : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels row ->
    target inS
      TNullRowLabels
        (TNullProjectRow env (@_Select_List TNull items) row) /\
    TNullRowValue
      (TNullProjectRow env (@_Select_List TNull items) row) target =
    TNullRowValue row source.
Proof.
intros env items source target row Hselect Hunique Hpresent.
split.
- unfold TNullRowLabels, TNullProjectRow, projected_tuple.
  rewrite (Fset.mem_eq_2 _ _ _
    (@Projection.labels_projection TNull (env_t TNull env row) items)).
  rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  exists
    (@Select_As TNull
      (@A_Expr TNull (@F_Dot TNull source)) target).
  split; [reflexivity | exact Hselect].
- now apply tnull_direct_projection_alias_value.
Qed.

(** Equality of two rows after the same renamed direct projection reflects
    equality of the retained source cells.  No injectivity claim is made for
    any other projected expression or attribute. *)
Lemma tnull_direct_projection_alias_reflects_value :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      (source target : TNullAttribute) (left right : TNullRow),
    In
      (@Select_As TNull
        (@A_Expr TNull (@F_Dot TNull source)) target)
      items ->
    select_list_has_unique_outputs (@_Select_List TNull items) ->
    source inS TNullRowLabels left ->
    source inS TNullRowLabels right ->
    TNullRowEq
      (TNullProjectRow env (@_Select_List TNull items) left)
      (TNullProjectRow env (@_Select_List TNull items) right) ->
    TNullRowValue left source = TNullRowValue right source.
Proof.
intros env items source target left right
  Hselect Hunique Hleft Hright Hequal.
pose proof
  (tnull_direct_projection_alias_retained
    env items source target left Hselect Hunique Hleft)
  as [Htarget Hleft_value].
pose proof
  (tnull_direct_projection_alias_retained
    env items source target right Hselect Hunique Hright)
  as [_ Hright_value].
pose proof
  (FTuples.Tuple.tuple_eq_dot_alt TNull _ _ Hequal target Htarget)
  as Hvalue.
unfold TNullRowValue in Hleft_value, Hright_value |- *.
rewrite Hleft_value, Hright_value in Hvalue.
exact Hvalue.
Qed.

(** A singleton INTEGER primary key continues to bound equality matches after
    a direct aliasing projection, even when both the source rows and projected
    rows are arbitrary representatives of their bags.  The guarded predicate
    is used only while crossing the bag boundary; target-label presence then
    justifies the unguarded predicate exposed to generated proofs. *)
Lemma tnull_projected_alias_int32_primary_key_matches_at_most_one :
  forall (env : TNullEnvironment) (items : list SelectItemT)
      source_name target_name (fixed : TNullValue)
      (raw_rows projected_rows : list TNullRow) (raw_bag : TNullRowBag),
    Forall
      (row_attribute_present_conforms (Attr_int32 source_name)) raw_rows ->
    primary_key_conforms [Attr_int32 source_name] raw_rows ->
    In
      (SelectAs (DotInt32 source_name) (AttrInt32 target_name))
      items ->
    select_list_has_unique_outputs (SelectList items) ->
    value_conforms_attribute (Attr_int32 source_name) fixed ->
    @query_same_rows_as_bag TNull raw_rows raw_bag ->
    @query_same_rows_as_bag TNull projected_rows
      (@query_project_bag TNull env (SelectList items) raw_bag) ->
    (List.length
      (filter
        (fun row =>
          postgres_int32_equal_true fixed
            (TNullRowValue row (Attr_int32 target_name)))
        projected_rows) <= 1)%nat.
Proof.
intros env items source_name target_name fixed raw_rows projected_rows raw_bag
  Hraw_typed Hprimary Hselect Hunique Hfixed Hraw Hprojected.
set (project := fun row : TNullRow =>
  TNullProjectRow env (SelectList items) row).
set (source_keep := fun row : TNullRow =>
  postgres_int32_equal_true fixed
    (TNullRowValue row (Attr_int32 source_name))).
set (target_keep := fun row : TNullRow =>
  postgres_int32_equal_true fixed
    (TNullRowValue row (Attr_int32 target_name))).
set (guarded_target_keep := fun row : TNullRow =>
  if Attr_int32 target_name inS? TNullRowLabels row then
    target_keep row
  else false).
set (mapped := map project raw_rows).
change (List.length (filter target_keep projected_rows) <= 1)%nat.
assert (Hmapped :
  @query_same_rows_as_bag TNull mapped
    (@query_project_bag TNull env (SelectList items) raw_bag)).
{
  unfold mapped, project, query_project_bag, TNullProjectRow.
  now apply projected_rows_same_as_mapped_bag.
}
assert (Hmapped_typed :
  Forall
    (row_attribute_present_conforms (Attr_int32 target_name)) mapped).
{
  unfold mapped; rewrite Forall_forall.
  intros projected Hmapped_row.
  apply in_map_iff in Hmapped_row.
  destruct Hmapped_row as [raw [<- Hraw_row]].
  pose proof Hraw_typed as Hraw_typed_rows.
  rewrite Forall_forall in Hraw_typed_rows.
  destruct (Hraw_typed_rows raw Hraw_row)
    as [Hsource_present Hsource_typed].
  unfold project.
  pose proof
    (tnull_direct_projection_alias_retained env items
      (Attr_int32 source_name) (Attr_int32 target_name) raw
      Hselect Hunique Hsource_present)
    as [Htarget_present Halias].
  split; [exact Htarget_present |].
  unfold TNullRowValue in Halias, Hsource_typed |- *.
  rewrite <- Halias in Hsource_typed.
  exact Hsource_typed.
}
assert (Hprojected_typed :
  Forall
    (row_attribute_present_conforms (Attr_int32 target_name))
    projected_rows).
{
  eapply query_same_rows_as_bag_Forall_between
    with (first := mapped)
      (bag := @query_project_bag TNull env (SelectList items) raw_bag).
  - apply row_attribute_present_conforms_proper.
  - exact Hmapped.
  - exact Hprojected.
  - exact Hmapped_typed.
}
assert (Hprojected_guarded :
  filter guarded_target_keep projected_rows =
  filter target_keep projected_rows).
{
  apply ListFacts.filter_eq.
  rewrite Forall_forall in Hprojected_typed.
  intros row Hrow; unfold guarded_target_keep.
  destruct (Hprojected_typed row Hrow) as [Hpresent _].
  change
    ((Attr_int32 target_name inS? TNullRowLabels row) = true)
    in Hpresent.
  now rewrite Hpresent.
}
assert (Hguarded_proper : tuple_predicate_proper guarded_target_keep).
{
  intros first second Hequal.
  unfold guarded_target_keep, TNullRowLabels.
  pose proof (tuple_eq_labels TNull first second Hequal) as Hlabels.
  rewrite Fset.equal_spec in Hlabels.
  specialize (Hlabels (Attr_int32 target_name)).
  destruct (Attr_int32 target_name inS? labels TNull first)
    eqn:Hfirst.
  - assert (Hsecond :
      (Attr_int32 target_name inS? labels TNull second) = true).
    { exact (eq_trans (eq_sym Hlabels) Hfirst). }
    rewrite Hsecond; unfold target_keep, TNullRowValue; f_equal.
    now apply tuple_eq_dot_alt.
  - assert (Hsecond :
      (Attr_int32 target_name inS? labels TNull second) = false).
    { exact (eq_trans (eq_sym Hlabels) Hfirst). }
    now rewrite Hsecond.
}
pose proof
  (query_same_rows_as_bag_filter_length_between
    guarded_target_keep projected_rows mapped
    (@query_project_bag TNull env (SelectList items) raw_bag)
    Hguarded_proper Hprojected Hmapped)
  as Hcount.
assert (Halias_all : forall raw,
  In raw raw_rows ->
  guarded_target_keep (project raw) = source_keep raw).
{
  intros raw Hraw_row.
  pose proof Hraw_typed as Hraw_typed_rows.
  rewrite Forall_forall in Hraw_typed_rows.
  destruct (Hraw_typed_rows raw Hraw_row) as [Hsource_present _].
  pose proof
    (tnull_direct_projection_alias_retained env items
      (Attr_int32 source_name) (Attr_int32 target_name) raw
      Hselect Hunique Hsource_present)
    as [Htarget_present Halias].
  unfold guarded_target_keep, project.
  change
    ((Attr_int32 target_name inS?
      TNullRowLabels (TNullProjectRow env (SelectList items) raw)) = true)
    in Htarget_present.
  rewrite Htarget_present.
  unfold target_keep, source_keep, TNullRowValue in Halias |- *.
  f_equal.
  exact Halias.
}
assert (Hmapped_count :
  List.length (filter guarded_target_keep mapped) =
  List.length (filter source_keep raw_rows)).
{
  unfold mapped.
  assert (Hfilters :
    filter (fun raw => guarded_target_keep (project raw)) raw_rows =
    filter source_keep raw_rows).
  { now apply ListFacts.filter_eq. }
  now rewrite ListFacts.filter_map, length_map, Hfilters.
}
assert (Hsource_bound :
  (List.length (filter source_keep raw_rows) <= 1)%nat).
{
  unfold source_keep.
  eapply int32_primary_key_true_matches_at_most_one.
  - exact Hfixed.
  - unfold rows_attribute_conform.
    rewrite Forall_forall in Hraw_typed.
    intros row Hrow.
    exact (proj2 (Hraw_typed row Hrow)).
  - exact Hprimary.
}
pose proof
  (f_equal (@List.length TNullRow) Hprojected_guarded)
  as Hprojected_count.
assert (Htotal :
  List.length (filter target_keep projected_rows) =
  List.length (filter source_keep raw_rows)).
{
  exact
    (eq_trans (eq_sym Hprojected_count)
      (eq_trans Hcount Hmapped_count)).
}
exact
  (eq_ind_r (fun count => (count <= 1)%nat) Hsource_bound Htotal).
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

(** A fixed SELECT list is proper for semantic row equality.  This is the
    row-level companion of [ordered_rows_equiv_map_projection] and avoids
    rebuilding projection lookup facts at every support-transport boundary. *)
Lemma tnull_project_row_eq_congr :
  forall env select left right,
    TNullRowEq left right ->
    TNullRowEq
      (TNullProjectRow env select left)
      (TNullProjectRow env select right).
Proof.
intros env select left right Hequal.
unfold TNullRowEq, TNullRowOrder, TNullProjectRow, projected_tuple.
apply Projection.projection_eq, Env.env_t_eq_2.
exact Hequal.
Qed.

(** Equality of projected rows exposes equality of the interpretation of any
    selected expression whose output alias is unique.  Unlike the direct-dot
    convenience lemmas above, this statement deliberately reasons about the
    expression value itself, so it remains valid when a missing column is
    resolved through the outer environment. *)
Lemma tnull_projected_select_item_reflects_value :
  forall env items expression attribute left right,
    In (@Select_As TNull expression attribute) items ->
    select_list_has_unique_outputs (SelectList items) ->
    TNullRowEq
      (TNullProjectRow env (SelectList items) left)
      (TNullProjectRow env (SelectList items) right) ->
    Interp.interp_aggterm TNull (env_t TNull env left) expression =
    Interp.interp_aggterm TNull (env_t TNull env right) expression.
Proof.
intros env items expression attribute left right
  Hselect Hunique Hequal.
assert (Hattribute :
  attribute inS
    TNullRowLabels (TNullProjectRow env (SelectList items) left)).
{
  unfold TNullRowLabels, TNullProjectRow, projected_tuple.
  rewrite (Fset.mem_eq_2 _ _ _
    (@Projection.labels_projection TNull
      (env_t TNull env left) items)).
  rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  exists (@Select_As TNull expression attribute).
  split; [reflexivity | exact Hselect].
}
pose proof
  (@FTuples.Tuple.tuple_eq_dot_alt TNull
    (TNullProjectRow env (SelectList items) left)
    (TNullProjectRow env (SelectList items) right)
    Hequal attribute Hattribute) as Hvalue.
unfold TNullProjectRow, projected_tuple, SelectList in Hvalue.
unfold select_list_has_unique_outputs in Hunique.
rewrite
  (@Projection.dot_projection TNull
    (env_t TNull env left) items attribute expression Hselect Hunique),
  (@Projection.dot_projection TNull
    (env_t TNull env right) items attribute expression Hselect Hunique)
  in Hvalue.
exact Hvalue.
Qed.

(** For a nonempty direct-column GROUP BY, projecting one group and
    projecting any member of that group produce the same semantic row.  This
    is stated at expression level, so it needs no source-label side condition:
    both evaluations use the same outer-environment fallback. *)
Lemma tnull_direct_columns_group_projection_member_eq :
  forall env rows columns group row,
    In group
      (@query_make_groups TNull env rows (map DotColumn columns)) ->
    In row group ->
    TNullRowEq
      (TNullProjectRow env (SelectColumns columns) row)
      (group_projection env (SelectColumns columns)
        (map DotColumn columns) group).
Proof.
intros env rows columns group row Hgroup Hrow.
unfold TNullRowEq, TNullRowOrder, TNullProjectRow, projected_tuple,
  group_projection, Projection.projection.
apply FTuples.Tuple.mk_tuple_eq.
- apply Fset.equal_refl.
- intros attribute _ _.
  unfold SelectColumns, SelectList, Projection.pairs_of_selects.
  case_eq
    (Oset.find (OAtt TNull) attribute
      (map (@Projection.pair_of_select TNull)
        (map SelectColumn columns))).
  + intros expression Hfind.
    pose proof (Oset.find_some _ _ _ Hfind) as Hselected.
    rewrite map_map, in_map_iff in Hselected.
    destruct Hselected as [column [Hpair Hcolumn]].
    unfold SelectColumn in Hpair; cbn in Hpair.
    injection Hpair as Hattribute Hequation.
    subst attribute expression.
    symmetry.
    unfold GroupedFilterOutcomeFacts.group_env.
    assert (Hterm : In (DotColumn column) (map DotColumn columns))
      by now apply in_map.
    destruct column.
    all: cbn
      [DotColumn DotZ DotInt32 DotInt64 DotString DotBool DotFloat
       DotDouble DotNumeric DotDecimal DotDate DotTime DotTimestamp
       DotTimestamptz AExpr Dot] in Hterm |- *.
    all: eapply query_group_env_grouping_expression_member; eassumption.
  + reflexivity.
Qed.

(** Direct-column projection equality reflects equality of the complete
    grouping key when every output alias is unique.  The SELECT list contains
    every grouping expression by construction; no injectivity is claimed for
    arbitrary projections. *)
Lemma tnull_direct_columns_projection_reflects_grouping_key :
  forall env columns left right,
    select_list_has_unique_outputs (SelectColumns columns) ->
    TNullRowEq
      (TNullProjectRow env (SelectColumns columns) left)
      (TNullProjectRow env (SelectColumns columns) right) ->
    query_grouping_key env (map DotColumn columns) left =
    query_grouping_key env (map DotColumn columns) right.
Proof.
intros env columns left right Hunique Hequal.
unfold query_grouping_key.
rewrite !map_map.
apply map_ext_in.
intros column Hcolumn.
eapply tnull_projected_select_item_reflects_value
  with
    (items := map SelectColumn columns)
    (expression := DotColumn column)
    (attribute := ColumnAttribute column).
- change (In (SelectColumn column) (map SelectColumn columns)).
  now apply in_map.
- exact Hunique.
- exact Hequal.
Qed.

(** One direct projection representative per nonempty group has exactly the
    projected support of the input.  Multiplicity is intentionally absent;
    callers consume this interface at a later grouping or DISTINCT reset. *)
Lemma tnull_direct_columns_group_projection_support_rel :
  forall env rows columns,
    columns <> nil ->
    list_support_rel
      (fun row output =>
        TNullRowEq (TNullProjectRow env (SelectColumns columns) row) output)
      rows
      (map
        (group_projection env (SelectColumns columns)
          (map DotColumn columns))
        (@query_make_groups TNull env rows (map DotColumn columns))).
Proof.
intros env rows columns Hcolumns.
eapply query_make_groups_support_rel.
- destruct columns; [contradiction | discriminate].
- intros group row Hgroup Hrow.
  exact
    (tnull_direct_columns_group_projection_member_eq
      env rows columns group row Hgroup Hrow).
Qed.

(** A later GROUP BY over all directly selected keys forgets prior
    multiplicities.  Therefore projected input support, rather than input bag
    equality, is sufficient for equality of the two duplicate-free grouped
    result bags.  Nonempty grouping and unique aliases are essential. *)
Lemma tnull_direct_columns_group_rows_bag_eq_of_projection_support :
  forall env columns left_rows right_rows,
    columns <> nil ->
    select_list_has_unique_outputs (SelectColumns columns) ->
    list_support_rel
      (fun left right =>
        TNullRowEq
          (TNullProjectRow env (SelectColumns columns) left)
          (TNullProjectRow env (SelectColumns columns) right))
      left_rows right_rows ->
    TNullBagEq
      (TNullRowsBag
        (map
          (group_projection env (SelectColumns columns)
            (map DotColumn columns))
          (@query_make_groups TNull env left_rows
            (map DotColumn columns))))
      (TNullRowsBag
        (map
          (group_projection env (SelectColumns columns)
            (map DotColumn columns))
          (@query_make_groups TNull env right_rows
            (map DotColumn columns)))).
Proof.
intros env columns left_rows right_rows
  Hcolumns Hunique Hsupport.
eapply query_make_groups_projected_bag_eq_of_support_rel
  with
    (project := fun row =>
      TNullProjectRow env (SelectColumns columns) row)
    (emit := group_projection env (SelectColumns columns)
      (map DotColumn columns)).
- destruct columns; [contradiction | discriminate].
- intros rows group row Hgroup Hrow.
  exact
    (tnull_direct_columns_group_projection_member_eq
      env rows columns group row Hgroup Hrow).
- intros left right Hequal.
  now apply tnull_direct_columns_projection_reflects_grouping_key.
- exact Hsupport.
Qed.

(** Direct column references contain neither scalar operators nor aggregate
    applications, so evaluating them as GROUP keys is unconditionally safe.
    Missing labels may still resolve through an outer environment, but that
    lookup is total and therefore does not introduce a runtime error. *)
Lemma tnull_direct_columns_group_keys_runtime_safe :
  forall env rows columns,
    @group_keys_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (map DotColumn columns) rows = None.
Proof.
intros env rows columns.
unfold group_keys_runtime_error.
assert (Hterms : forall row,
  first_runtime_error
    (@eval_aggterm_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row))
    (map DotColumn columns) = None).
{
  intro row; induction columns as [|column columns IH]; [reflexivity|].
  destruct column;
    cbn
      [DotColumn DotZ DotInt32 DotInt64 DotString DotBool DotFloat
       DotDouble DotNumeric DotDecimal DotDate DotTime DotTimestamp
       DotTimestamptz AExpr Dot eval_aggterm_runtime_error
       eval_funterm_runtime_error first_runtime_error first_error];
    exact IH.
}
induction rows as [|row rows IH]; [reflexivity|].
cbn [first_runtime_error first_error].
now rewrite Hterms, IH.
Qed.

(** The SELECT list paired with a direct-column GROUP is safe both during
    aggregate finalization and during the post-HAVING scalar phase. *)
Lemma tnull_direct_columns_group_select_runtime_safe :
  forall env columns,
    @eval_select_list_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) = None /\
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) = None.
Proof.
intros env columns; split.
- induction columns as [|column columns IH]; [reflexivity|].
  destruct column;
    cbn
      [SelectColumns SelectColumn SelectList SelectAs DotColumn
       DotZ DotInt32 DotInt64 DotString DotBool DotFloat DotDouble
       DotNumeric DotDecimal DotDate DotTime DotTimestamp DotTimestamptz
       AExpr Dot eval_select_list_aggregate_runtime_error
       eval_select_aggregate_runtime_error
       eval_aggterm_aggregate_runtime_error first_runtime_error first_error];
    exact IH.
- induction columns as [|column columns IH]; [reflexivity|].
  destruct column;
    cbn
      [SelectColumns SelectColumn SelectList SelectAs DotColumn
       DotZ DotInt32 DotInt64 DotString DotBool DotFloat DotDouble
       DotNumeric DotDecimal DotDate DotTime DotTimestamp DotTimestamptz
       AExpr Dot eval_select_list_runtime_error eval_select_runtime_error
       eval_aggterm_runtime_error eval_funterm_runtime_error
       first_runtime_error first_error];
    exact IH.
Qed.

(** A direct-column SELECT is an exact, order-preserving pointwise map and
    cannot fail locally.  This specializes the generic projection evaluator
    without making any claim about errors produced by an enclosing child
    query. *)
Lemma tnull_project_rows_select_columns_success :
  forall env columns rows,
    @project_rows_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env (SelectColumns columns) rows =
    SqlSuccess
      (map
        (fun row => TNullProjectRow env (SelectColumns columns) row)
        rows).
Proof.
intros env columns rows.
apply project_rows_outcome_all_safe.
intro row.
exact (proj2
  (tnull_direct_columns_group_select_runtime_safe
    (env_t TNull env row) columns)).
Qed.

(** Consequently [QExpr_Project] with [SelectColumns] propagates exactly the
    child's error observations.  The iff deliberately keeps child errors
    visible; only projection-local errors are ruled out. *)
Lemma tnull_query_expr_project_select_columns_error_iff :
  forall db env columns input error,
    TNullQueryExprOutcome db env
      (QExpr_Project (SelectColumns columns) input) (SqlError error) <->
    TNullQueryExprOutcome db env input (SqlError error).
Proof.
intros db env columns input error.
unfold TNullQueryExprOutcome.
apply eval_query_expr_project_error_iff_safe.
intro row.
exact (proj2
  (tnull_direct_columns_group_select_runtime_safe
    (env_t TNull env row) columns)).
Qed.

(** Complete group-bag outcome equivalence for a direct-column GROUP BY with
    TRUE HAVING.  Projected support is sufficient because this operator emits
    one duplicate-free representative per complete key; all local runtime
    checks are discharged above, so the relation contains no hidden error
    premise. *)
Lemma tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support :
  forall db env columns left_rows right_rows,
    columns <> nil ->
    select_list_has_unique_outputs (SelectColumns columns) ->
    list_support_rel
      (fun left right =>
        TNullRowEq
          (TNullProjectRow env (SelectColumns columns) left)
          (TNullProjectRow env (SelectColumns columns) right))
      left_rows right_rows ->
    forall outcome,
      @eval_group_bag_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (TNullRowsBag left_rows) outcome <->
      @eval_group_bag_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (TNullRowsBag right_rows) outcome.
Proof.
intros db env columns left_rows right_rows Hcolumns Hunique Hsupport outcome.
eapply eval_group_bag_true_projected_support_equiv with
  (project := fun row => TNullProjectRow env (SelectColumns columns) row).
- destruct columns; [contradiction|discriminate].
- intros first second Hequal.
  now apply tnull_project_row_eq_congr.
- intros rows group row Hgroup Hrow.
  exact
    (tnull_direct_columns_group_projection_member_eq
      env rows columns group row Hgroup Hrow).
- intros first second Hequal.
  now apply tnull_direct_columns_projection_reflects_grouping_key.
- intro rows.
  exact (@tnull_direct_columns_group_keys_runtime_safe env rows columns).
- intros rows group Hgroup.
  apply tnull_direct_columns_group_select_runtime_safe.
- exact Hsupport.
Qed.

(** Every direct-column TRUE group over a concrete child row list has a
    successful group-bag observation.  This is used only to lift a child
    outcome witness to the enclosing GROUP; it does not choose a privileged
    result in the declarative relation. *)
Lemma tnull_direct_columns_group_bag_has_success :
  forall db env columns rows,
    exists output_bag,
      @eval_group_bag_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (TNullRowsBag rows) (SqlSuccess output_bag).
Proof.
intros db env columns rows.
set (groups :=
  @query_make_groups TNull env (query_canonical_rows rows)
    (map DotColumn columns)).
set (outputs :=
  map
    (group_projection env (SelectColumns columns) (map DotColumn columns))
    groups).
exists (TNullRowsBag outputs).
eapply EGroupBag_Success with
  (representative := rows) (grouped_rows := outputs).
- apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl.
- apply tnull_direct_columns_group_keys_runtime_safe.
- assert (Hsafe : forall group,
    In group groups ->
    @eval_select_list_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      (SelectColumns columns) = None /\
    @eval_formula_expr_aggregate_runtime_error TNull relname
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      FExpr_True = None /\
    @formula_acceptance_exact_at TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      FExpr_True true /\
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      (SelectColumns columns) = None).
  {
    intros group Hgroup.
    destruct
      (tnull_direct_columns_group_select_runtime_safe
        (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
        columns) as [Haggregate Hruntime].
    split; [exact Haggregate|].
    split; [reflexivity|].
    split; [apply formula_true_acceptance_exact|exact Hruntime].
  }
  apply (proj2
    (@eval_groups_true_outcome_exact TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (SelectColumns columns) (map DotColumn columns) FExpr_True
      groups Hsafe (SqlSuccess outputs))).
  unfold outputs; reflexivity.
- apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl.
Qed.

(** Direct-column grouping with TRUE HAVING has no local error outcome for
    any input bag or representative.  This does not erase child-query errors:
    it concerns only [eval_group_bag_outcome], after a successful child bag
    has already been supplied.  Empty grouping keys remain the ordinary
    global-group case; no bag-reset or nonemptiness theorem is used here. *)
Lemma tnull_eval_group_bag_direct_columns_true_no_error :
  forall db env columns input_bag error,
    ~ @eval_group_bag_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (SelectColumns columns) (map DotColumn columns) FExpr_True
      input_bag (SqlError error).
Proof.
intros db env columns input_bag error Herror.
inversion Herror; subst.
- match goal with
  | Hkeys :
      @group_keys_runtime_error TNull
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error
        env (map DotColumn columns) _ = Some _ |- _ =>
      pose proof
        (@tnull_direct_columns_group_keys_runtime_safe
          env (query_canonical_rows representative) columns) as Hnone;
      congruence
  end.
- assert (Hsafe : forall group,
    In group
      (@query_make_groups TNull env
        (query_canonical_rows representative) (map DotColumn columns)) ->
    @eval_select_list_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      (SelectColumns columns) = None /\
    @eval_formula_expr_aggregate_runtime_error TNull relname
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      FExpr_True = None /\
    @formula_acceptance_exact_at TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      FExpr_True true /\
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
      (SelectColumns columns) = None).
  {
    intros group Hgroup.
    destruct
      (tnull_direct_columns_group_select_runtime_safe
        (env_g TNull env (@Group_By TNull (map DotColumn columns)) group)
        columns) as [Haggregate Hruntime].
    split; [exact Haggregate|].
    split; [reflexivity|].
    split; [apply formula_true_acceptance_exact|exact Hruntime].
  }
  match goal with
  | Hgroups :
      @eval_groups_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env (SelectColumns columns) (map DotColumn columns) FExpr_True
        (@query_make_groups TNull env
          (query_canonical_rows representative) (map DotColumn columns))
        (SqlError error) |- _ =>
      pose proof
        (proj1
          (@eval_groups_true_outcome_exact TNull relname
            (@_basesort TNull db) (@_instance TNull db) unknown3
            NullValues.interp_scalar_operator_runtime_error
            NullValues.interp_aggregate_runtime_error NullValues.is_null_value
            env (SelectColumns columns) (map DotColumn columns) FExpr_True
            (@query_make_groups TNull env
              (query_canonical_rows representative) (map DotColumn columns))
            Hsafe (SqlError error)) Hgroups) as Hsuccess;
      discriminate
  end.
Qed.

(** High-level direct-column GROUP outcome bridge.  Successful children need
    only pair by projected support; all child error categories remain an
    explicit iff and are propagated unchanged by the GROUP scheduler. *)
Lemma tnull_direct_columns_group_outcome_equiv_of_projected_support :
  forall db env columns left right,
    columns <> nil ->
    select_list_has_unique_outputs (SelectColumns columns) ->
    (exists outcome, TNullQueryExprOutcome db env left outcome) ->
    (forall left_rows,
      TNullQueryExprOutcome db env left (SqlSuccess left_rows) ->
      exists right_rows,
        TNullQueryExprOutcome db env right (SqlSuccess right_rows) /\
        list_support_rel
          (fun left_row right_row =>
            TNullRowEq
              (TNullProjectRow env (SelectColumns columns) left_row)
              (TNullProjectRow env (SelectColumns columns) right_row))
          left_rows right_rows) ->
    (forall right_rows,
      TNullQueryExprOutcome db env right (SqlSuccess right_rows) ->
      exists left_rows,
        TNullQueryExprOutcome db env left (SqlSuccess left_rows) /\
        list_support_rel
          (fun left_row right_row =>
            TNullRowEq
              (TNullProjectRow env (SelectColumns columns) left_row)
              (TNullProjectRow env (SelectColumns columns) right_row))
          left_rows right_rows) ->
    (forall error,
      TNullQueryExprOutcome db env left (SqlError error) <->
      TNullQueryExprOutcome db env right (SqlError error)) ->
    TNullQueryExprOutcomeEq db env
      (QExpr_Group (SelectColumns columns) (map DotColumn columns)
        FExpr_True left)
      (QExpr_Group (SelectColumns columns) (map DotColumn columns)
        FExpr_True right).
Proof.
intros db env columns left right Hcolumns Hunique Hleft_outcome
  Hforward Hbackward Herrors.
assert (Hparent_outcome : exists outcome,
  TNullQueryExprOutcome db env
    (QExpr_Group (SelectColumns columns) (map DotColumn columns)
      FExpr_True left) outcome).
{
  destruct Hleft_outcome as [[rows | error] Houtcome].
  - destruct (tnull_direct_columns_group_bag_has_success
      db env columns rows) as [output_bag Hgroup].
    exists (SqlSuccess
      (Febag.elements TNullRowBagRecord output_bag)).
    unfold TNullQueryExprOutcome in *.
    eapply EQuery_GroupBagSuccess with
      (input_rows := rows) (output_bag := output_bag).
    + exact Houtcome.
    + exact Hgroup.
    + apply query_elements_same_rows_as_bag.
  - exists (SqlError error).
    unfold TNullQueryExprOutcome in *.
    now apply EQuery_GroupChildError.
}
unfold TNullQueryExprOutcomeEq, TNullQueryExprOutcome in *.
eapply query_expr_group_outcome_equiv_of_supported_child_outcomes
  with
    (supported := fun left_rows right_rows =>
      list_support_rel
        (fun left_row right_row =>
          TNullRowEq
            (TNullProjectRow env (SelectColumns columns) left_row)
            (TNullProjectRow env (SelectColumns columns) right_row))
        left_rows right_rows).
- reflexivity.
- exact Hparent_outcome.
- exact Hforward.
- exact Hbackward.
- exact Herrors.
- intros left_rows right_rows Hsupport outcome.
  now apply
    (tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support
      db env columns left_rows right_rows Hcolumns Hunique Hsupport outcome).
Qed.

(** Projections evaluated in independently chosen environments are
    extensionally equal when their SELECT items pair in order, expose the same
    aliases, and interpret to the same values.  The proof follows the two
    select lists linearly; it does not normalize the concrete tuple comparator.
    Runtime-error safety remains a separate evaluator obligation. *)
Lemma tnull_projection_envs_eq_of_select_items :
  forall (left_env right_env : Env.env TNull)
      (left_items right_items : list SelectItemT),
    Forall2
      (fun left right =>
        match left, right with
        | @Projection.Select_As _ left_expression left_attribute,
          @Projection.Select_As _ right_expression right_attribute =>
            left_attribute = right_attribute /\
            Interp.interp_aggterm TNull left_env left_expression =
            Interp.interp_aggterm TNull right_env right_expression
        end)
      left_items right_items ->
    TNullRowEq
      (Projection.projection TNull left_env
        (@Projection.Select_List TNull (SelectList left_items)))
      (Projection.projection TNull right_env
        (@Projection.Select_List TNull (SelectList right_items))).
Proof.
intros left_env right_env left_items right_items Hagree.
assert (Houtputs :
  map
    (fun item =>
      match item with
      | @Projection.Select_As _ _ attribute => attribute
      end)
    left_items =
  map
    (fun item =>
      match item with
      | @Projection.Select_As _ _ attribute => attribute
      end)
    right_items).
{
  induction Hagree as
    [|left right left_tail right_tail Hhead _ IH].
  - reflexivity.
  - destruct left as [left_expression left_attribute].
    destruct right as [right_expression right_attribute].
    destruct Hhead as [Hattribute _].
    subst right_attribute.
    cbn [map].
    now f_equal.
}
assert (Hlookup :
  forall attribute,
    option_map
      (Interp.interp_aggterm TNull left_env)
      (Oset.find (OAtt TNull) attribute
        (map (@Projection.pair_of_select TNull) left_items)) =
    option_map
      (Interp.interp_aggterm TNull right_env)
      (Oset.find (OAtt TNull) attribute
        (map (@Projection.pair_of_select TNull) right_items))).
{
  intro attribute.
  clear Houtputs.
  induction Hagree as
    [|left right left_tail right_tail Hhead _ IH].
  - reflexivity.
  - destruct left as [left_expression left_attribute].
    destruct right as [right_expression right_attribute].
    destruct Hhead as [Hattribute Hvalue].
    subst right_attribute.
    change
      (option_map
        (Interp.interp_aggterm TNull left_env)
        (if Oset.eq_bool (OAtt TNull) attribute left_attribute
         then Some left_expression
         else Oset.find (OAtt TNull) attribute
           (map (@Projection.pair_of_select TNull) left_tail)) =
       option_map
        (Interp.interp_aggterm TNull right_env)
        (if Oset.eq_bool (OAtt TNull) attribute left_attribute
         then Some right_expression
         else Oset.find (OAtt TNull) attribute
           (map (@Projection.pair_of_select TNull) right_tail))).
    destruct (Oset.eq_bool (OAtt TNull) attribute left_attribute).
    + unfold option_map.
      now f_equal.
    + exact IH.
}
unfold TNullRowEq, TNullRowOrder, Projection.projection.
apply mk_tuple_eq.
- unfold select_list_sort, select_list_outputs, SelectList.
  rewrite Houtputs.
  apply Fset.equal_refl.
- intros attribute _ _.
  specialize (Hlookup attribute).
  unfold SelectList, Projection.pairs_of_selects in Hlookup |- *.
  destruct
    (Oset.find (OAtt TNull) attribute
      (map (@Projection.pair_of_select TNull) left_items))
    as [left_expression|] eqn:Hleft;
  destruct
    (Oset.find (OAtt TNull) attribute
      (map (@Projection.pair_of_select TNull) right_items))
    as [right_expression|] eqn:Hright;
  unfold option_map in Hlookup;
  try discriminate; try reflexivity.
  now injection Hlookup.
Qed.

(** Row-oriented specialization of the environment-level projection law. *)
Lemma tnull_projection_rows_eq_of_select_items :
  forall env left_row right_row
      (left_items right_items : list SelectItemT),
    Forall2
      (fun left right =>
        match left, right with
        | @Projection.Select_As _ left_expression left_attribute,
          @Projection.Select_As _ right_expression right_attribute =>
            left_attribute = right_attribute /\
            Interp.interp_aggterm TNull (env_t TNull env left_row)
              left_expression =
            Interp.interp_aggterm TNull (env_t TNull env right_row)
              right_expression
        end)
      left_items right_items ->
    TNullRowEq
      (TNullProjectRow env (SelectList left_items) left_row)
      (TNullProjectRow env (SelectList right_items) right_row).
Proof.
intros env left_row right_row left_items right_items Hagree.
unfold TNullProjectRow, projected_tuple.
now apply tnull_projection_envs_eq_of_select_items.
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

(** Projecting any two rows through the same SELECT list produces the same
    output-label set.  This exposes projection metadata without unfolding
    [projected_tuple] or the tuple comparator. *)
Lemma tnull_same_select_projection_labels :
  forall env select left right,
    TNullAttributeSetEq
      (TNullRowLabels (TNullProjectRow env select left))
      (TNullRowLabels (TNullProjectRow env select right)).
Proof.
intros env [items] left right.
unfold TNullAttributeSetEq, TNullRowLabels, TNullProjectRow,
  projected_tuple.
rewrite Fset.equal_spec; intro attribute.
rewrite (Fset.mem_eq_2 _ _ _
  (@Projection.labels_projection TNull _ items)).
rewrite (Fset.mem_eq_2 _ _ _
  (@Projection.labels_projection TNull _ items)).
reflexivity.
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
