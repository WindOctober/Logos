(** TNull specialization of the exact normalized-query semantics.

    Query observations are relations over ordered row lists.  Possible-bag
    reasoning is used only through abstraction for order-insensitive proof
    regions; it is not a second query semantics. *)
From Stdlib Require Import List ZArith.
From SQLFS Require Import SqlSyntax GenericInstance Values Bool3 Env FiniteSet FlatData
  Formula SchemaConstraints SqlAlgebra SqlOutcome SqlQuerySyntax SqlQuerySemantics
  SqlQueryWellFormed SqlOrder.
From Logos Require Export FormalSQL.TNullSyntax.

Import ListNotations.
Import Tuple.

Definition QueryExpr := @query_expr TNull relname.
Definition QueryProgram := list QueryExpr.
Definition FormulaExpr := @formula_expr TNull relname.
Definition QueryWindowItemT := query_window_item TNull.

(** PostgreSQL ranking functions return non-NULL BIGINT.  The generic query
    semantics turns failure of this checked embedding into SQLSTATE 22003
    (numeric value out of range), so the unbounded logical list carrier never
    becomes stuck at an unrepresentable position. *)
Definition PgRankInt64Value
    (rank : nat) : option (Tuple.value TNull) :=
  match int64_checked (Z.of_nat rank) with
  | Some value => Some (NullValues.Value_int64 (Some value))
  | None => None
  end.

Definition RankExpr
    (partition_keys order_keys : list SortKeyT)
    (rank_attribute : Tuple.attribute TNull)
    (input : QueryExpr) : QueryExpr :=
  @QExpr_Rank TNull relname partition_keys order_keys rank_attribute
    PgRankInt64Value input.

Definition WindowRowNumberItem
    (output : Tuple.attribute TNull) : QueryWindowItemT :=
  @QueryWindowItem TNull output (QueryWindowRowNumber PgRankInt64Value).

Definition WindowAggregateItem
    (output : Tuple.attribute TNull) (term : AggTerm) : QueryWindowItemT :=
  @QueryWindowItem TNull output (QueryWindowAggregate term).

Definition WindowExpr
    (partition_keys order_keys : list SortKeyT)
    (items : list QueryWindowItemT)
    (input : QueryExpr) : QueryExpr :=
  @QExpr_Window TNull relname partition_keys order_keys items input.

(** A declarative, order-preserving row adapter with an explicitly resolved
    result schema. *)
Definition RowMapExpr
    (output_attributes : list (attribute TNull))
    (row_map : tuple TNull -> sql_outcome (tuple TNull))
    (input : QueryExpr) : QueryExpr :=
  @QExpr_RowMap TNull relname
    output_attributes row_map input.

(** Abstract result of PostgreSQL's exact NUMERIC [exp] language operation.
    The model supplies both the finite value and PostgreSQL display scale, or
    reports SQLSTATE 22003. *)
Inductive NumericExpResult : Type :=
  | NumericExpSuccess : numeric -> Z -> NumericExpResult
  | NumericExpValueOutOfRange : NumericExpResult.

Definition NumericExpModel : Type := numeric -> Z -> NumericExpResult.

Definition NumericExpOutputAttributes
    (passthrough : list (attribute TNull))
    (output_numeric_attribute output_dscale_attribute : attribute TNull) :
    list (attribute TNull) :=
  passthrough ++ [output_numeric_attribute; output_dscale_attribute].

Definition NumericExpOutputRow
    (passthrough : list (attribute TNull))
    (output_numeric_attribute output_dscale_attribute : attribute TNull)
    (input : tuple TNull)
    (result : option numeric) (dscale : option Z) : tuple TNull :=
  mk_tuple_lists
    (NumericExpOutputAttributes passthrough
      output_numeric_attribute output_dscale_attribute)
    (map (dot TNull input) passthrough ++
      [NullValues.Value_numeric result; NullValues.Value_Z dscale]).

(** A successful abstract model result is admitted only when it is an exact
    PostgreSQL-storable finite NUMERIC at the supplied display scale.  Requiring
    a fixed point of [numeric_round_to_scale] prevents a model from attaching
    stale scale metadata to a more precise value. *)
Definition NumericExpSuccessValid (result : numeric) (dscale : Z) : bool :=
  match result with
  | NumericFinite _ =>
      numeric_display_scale_valid_bool dscale &&
      (dscale <=? postgres_numeric_max_display_scale) &&
      numeric_runtime_fits_bool result &&
      numeric_eqb (numeric_round_to_scale result dscale) result
  | NumericNegInfinity | NumericPosInfinity | NumericNaN => false
  end.

Definition NumericExpRangeError {A : Type} : sql_outcome A :=
  SqlError (DataException NumericValueOutOfRange).

(** Declarative adapter for [EXP(AVG(int4))].  NULL AVG bypasses the abstract
    EXP model and produces NULL value/scale.  Every non-NULL path consumes the
    AVG display scale explicitly and validates the model result before exposing
    it as SQL data. *)
Definition NumericExpRowAdapter
    (passthrough : list (attribute TNull))
    (avg_value_attribute avg_dscale_attribute : attribute TNull)
    (output_numeric_attribute output_dscale_attribute : attribute TNull)
    (model : NumericExpModel)
    (row : tuple TNull) : sql_outcome (tuple TNull) :=
  match dot TNull row avg_value_attribute with
  | NullValues.Value_numeric None =>
      SqlSuccess
        (NumericExpOutputRow passthrough
          output_numeric_attribute output_dscale_attribute row None None)
  | NullValues.Value_numeric (Some average) =>
      match dot TNull row avg_dscale_attribute with
      | NullValues.Value_Z (Some average_dscale) =>
          match model average average_dscale with
          | NumericExpValueOutOfRange => NumericExpRangeError
          | NumericExpSuccess result result_dscale =>
              if NumericExpSuccessValid result result_dscale
              then
                SqlSuccess
                  (NumericExpOutputRow passthrough
                    output_numeric_attribute output_dscale_attribute row
                    (Some result) (Some result_dscale))
              else NumericExpRangeError
          end
      | _ => NumericExpRangeError
      end
  | _ => NumericExpRangeError
  end.

Definition NumericExpRowMapExpr
    (passthrough : list (attribute TNull))
    (avg_value_attribute avg_dscale_attribute : attribute TNull)
    (output_numeric_attribute output_dscale_attribute : attribute TNull)
    (model : NumericExpModel)
    (input : QueryExpr) : QueryExpr :=
  RowMapExpr
    (NumericExpOutputAttributes passthrough
      output_numeric_attribute output_dscale_attribute)
    (NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model)
    input.

Lemma NumericExpOutputRow_labels :
  forall passthrough output_numeric_attribute output_dscale_attribute
         input result dscale,
    labels TNull
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute input result dscale)
    =S=
    Fset.mk_set (A TNull)
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute).
Proof.
intros; unfold NumericExpOutputRow, mk_tuple_lists.
apply labels_mk_tuple.
Qed.

Lemma NumericExpRowAdapter_well_sorted :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model,
    @query_row_map_well_sorted TNull
      (Fset.mk_set (A TNull)
        (NumericExpOutputAttributes passthrough
          output_numeric_attribute output_dscale_attribute))
      (NumericExpRowAdapter passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model).
Proof.
intros passthrough avg_value_attribute avg_dscale_attribute
  output_numeric_attribute output_dscale_attribute model input output Houtput.
unfold NumericExpRowAdapter in Houtput.
repeat
  match type of Houtput with
  | context [match ?scrutinee with _ => _ end] =>
      destruct scrutinee eqn:?
  end;
  try discriminate;
  inversion Houtput; subst;
  apply NumericExpOutputRow_labels.
Qed.

Lemma NumericExpRowMapExpr_admissible :
  forall basesort passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model input,
    @query_expr_admissible TNull relname basesort input ->
    @query_output_attributes_unique TNull
      (NumericExpOutputAttributes passthrough
        output_numeric_attribute output_dscale_attribute) ->
    @query_expr_admissible TNull relname basesort
      (NumericExpRowMapExpr passthrough avg_value_attribute
        avg_dscale_attribute output_numeric_attribute
        output_dscale_attribute model input).
Proof.
intros basesort passthrough avg_value_attribute avg_dscale_attribute
  output_numeric_attribute output_dscale_attribute model input Hinput Hunique.
repeat split; try assumption.
apply NumericExpRowAdapter_well_sorted.
Qed.

Lemma NumericExpRowAdapter_null :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row,
    dot TNull row avg_value_attribute = NullValues.Value_numeric None ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    SqlSuccess
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute row None None).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H.
Qed.

Lemma NumericExpRowAdapter_success :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale result result_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale =
      NumericExpSuccess result result_dscale ->
    NumericExpSuccessValid result result_dscale = true ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    SqlSuccess
      (NumericExpOutputRow passthrough
        output_numeric_attribute output_dscale_attribute row
        (Some result) (Some result_dscale)).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H, H0, H1, H2.
Qed.

Lemma NumericExpRowAdapter_invalid_success :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale result result_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale =
      NumericExpSuccess result result_dscale ->
    NumericExpSuccessValid result result_dscale = false ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    @NumericExpRangeError (tuple TNull).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H, H0, H1, H2.
Qed.

Lemma NumericExpRowAdapter_out_of_range :
  forall passthrough avg_value_attribute avg_dscale_attribute
         output_numeric_attribute output_dscale_attribute model row
         average average_dscale,
    dot TNull row avg_value_attribute =
      NullValues.Value_numeric (Some average) ->
    dot TNull row avg_dscale_attribute =
      NullValues.Value_Z (Some average_dscale) ->
    model average average_dscale = NumericExpValueOutOfRange ->
    NumericExpRowAdapter passthrough avg_value_attribute avg_dscale_attribute
      output_numeric_attribute output_dscale_attribute model row =
    @NumericExpRangeError (tuple TNull).
Proof.
intros; unfold NumericExpRowAdapter; now rewrite H, H0, H1.
Qed.

Lemma NumericExpSuccessValid_invalid_scale :
  forall result dscale,
    numeric_display_scale_valid_bool dscale = false ->
    NumericExpSuccessValid result dscale = false.
Proof.
intros [| finite | |] dscale Hscale; try reflexivity.
unfold NumericExpSuccessValid; now rewrite Hscale.
Qed.

Lemma NumericExpSuccessValid_nonfinite :
  forall dscale,
    NumericExpSuccessValid NumericNegInfinity dscale = false /\
    NumericExpSuccessValid NumericPosInfinity dscale = false /\
    NumericExpSuccessValid NumericNaN dscale = false.
Proof.
intro; repeat split; reflexivity.
Qed.

Definition eval_query_expr_outcome_in_env
    (db : db_state)
    (env : Env.env TNull)
    (q : QueryExpr) :=
  @eval_query_expr_outcome TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    q.

Lemma eval_query_expr_row_map_child_error :
  forall db env output_attributes row_map input error,
    eval_query_expr_outcome_in_env db env input (SqlError error) ->
    eval_query_expr_outcome_in_env db env
      (RowMapExpr output_attributes row_map input) (SqlError error).
Proof.
intros; apply EQuery_RowMapChildError; exact H.
Qed.

Definition eval_query_expr_outcome_in_state
    (db : db_state)
    (q : QueryExpr) :=
  eval_query_expr_outcome_in_env db nil q.

Definition query_expr_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryExpr) : Prop :=
  @query_expr_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_expr_equiv_in_state
    (db : db_state)
    (left right : QueryExpr) : Prop :=
  query_expr_equiv_in_env db nil left right.

Definition query_expr_outcome_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryExpr) : Prop :=
  @query_expr_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_expr_outcome_equiv_in_state
    (db : db_state)
    (left right : QueryExpr) : Prop :=
  query_expr_outcome_equiv_in_env db nil left right.

Definition query_program_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryProgram) : Prop :=
  @query_program_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_program_equiv_in_state
    (db : db_state)
    (left right : QueryProgram) : Prop :=
  query_program_equiv_in_env db nil left right.

Definition query_program_outcome_equiv_in_env
    (db : db_state)
    (env : Env.env TNull)
    (left right : QueryProgram) : Prop :=
  @query_program_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    contains_nulls
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value
    env
    left
    right.

Definition query_program_outcome_equiv_in_state
    (db : db_state)
    (left right : QueryProgram) : Prop :=
  query_program_outcome_equiv_in_env db nil left right.

(** General compositional transport for generated exact-query admissibility.
    These results use only extensional equality of base-table sorts; they do
    not inspect instances, assert query success, or weaken SQL semantics. *)
Section AdmissibilityBaseSortTransport.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variables first_basesort second_basesort :
  generic_relname -> Fset.set (A T).
Hypothesis Hbasesort :
  forall relation, first_basesort relation =S= second_basesort relation.

Lemma query_sort_basesort_extensional :
  forall query,
    @sort T generic_relname first_basesort query =S=
    @sort T generic_relname second_basesort query.
Proof.
  intro query; induction query; cbn [sort].
  - apply Fset.equal_refl.
  - apply Fset.equal_refl.
  - apply Hbasesort.
  - exact IHquery1.
  - now apply Fset.union_eq.
  - apply Fset.equal_refl.
  - exact IHquery.
  - apply Fset.equal_refl.
Qed.

Lemma query_output_sorts_disjoint_basesort_extensional :
  forall left_first right_first left_second right_second,
    left_first =S= left_second ->
    right_first =S= right_second ->
    @query_output_sorts_disjoint T left_first right_first ->
    @query_output_sorts_disjoint T left_second right_second.
Proof.
  intros left_first right_first left_second right_second
    Hleft Hright Hdisjoint.
  unfold query_output_sorts_disjoint in *.
  rewrite <-
    (Fset.equal_eq_1 _ _ _ _ (Fset.inter_eq _ _ _ _ _ Hleft Hright)).
  exact Hdisjoint.
Qed.

Scheme bag_query_admissible_induction :=
  Induction for bag_query_admissible Sort Prop
with bag_formula_admissible_induction :=
  Induction for bag_formula_admissible Sort Prop.

Combined Scheme bag_query_formula_admissible_mutind
  from bag_query_admissible_induction, bag_formula_admissible_induction.

Lemma bag_query_formula_admissible_basesort_extensional :
  (forall query,
    @bag_query_admissible T generic_relname first_basesort query ->
    @bag_query_admissible T generic_relname second_basesort query) /\
  (forall formula,
    @bag_formula_admissible T generic_relname first_basesort formula ->
    @bag_formula_admissible T generic_relname second_basesort formula).
Proof.
  apply bag_query_formula_admissible_mutind; intros.
  - constructor.
  - constructor.
  - constructor.
  - econstructor; [assumption | assumption |].
    match goal with
    | H : @sort T generic_relname first_basesort ?left =S=
          @sort T generic_relname first_basesort ?right
      |- @sort T generic_relname second_basesort ?left =S=
          @sort T generic_relname second_basesort ?right =>
        rewrite Fset.equal_spec in H |- *;
        intro attribute;
        let Hleft := fresh "Hleft" in
        let Hright := fresh "Hright" in
        pose proof (query_sort_basesort_extensional left) as Hleft;
        pose proof (query_sort_basesort_extensional right) as Hright;
        rewrite Fset.equal_spec in Hleft, Hright;
        rewrite <- (Hleft attribute), <- (Hright attribute);
        exact (H attribute)
    end.
  - econstructor; [assumption | assumption |].
    eapply query_output_sorts_disjoint_basesort_extensional.
    + apply query_sort_basesort_extensional.
    + apply query_sort_basesort_extensional.
    + assumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - constructor.
  - econstructor; eassumption.
  - econstructor; [assumption | assumption | |].
    + rewrite <-
        (Fset.elements_spec1 _ _ _
          (query_sort_basesort_extensional subquery));
      assumption.
    + rewrite <-
        (Fset.elements_spec1 _ _ _
          (query_sort_basesort_extensional subquery));
      assumption.
  - econstructor; [assumption | assumption | |].
    + rewrite <-
        (Fset.elements_spec1 _ _ _
          (query_sort_basesort_extensional subquery));
      assumption.
    + rewrite <-
        (Fset.elements_spec1 _ _ _
          (query_sort_basesort_extensional subquery));
      assumption.
  - now constructor.
Qed.

Lemma bag_query_admissible_basesort_extensional :
  forall query,
    @bag_query_admissible T generic_relname first_basesort query ->
    @bag_query_admissible T generic_relname second_basesort query.
Proof.
  exact (proj1 bag_query_formula_admissible_basesort_extensional).
Qed.

Lemma bag_formula_admissible_basesort_extensional :
  forall formula,
    @bag_formula_admissible T generic_relname first_basesort formula ->
    @bag_formula_admissible T generic_relname second_basesort formula.
Proof.
  exact (proj2 bag_query_formula_admissible_basesort_extensional).
Qed.

Scheme query_expr_admissibility_induction := Induction for query_expr Sort Prop
with formula_expr_admissibility_induction :=
  Induction for formula_expr Sort Prop.

Combined Scheme query_formula_expr_admissibility_mutind
  from query_expr_admissibility_induction,
    formula_expr_admissibility_induction.

Lemma query_formula_expr_admissible_basesort_extensional :
  (forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query) /\
  (forall formula,
    @formula_expr_admissible T generic_relname first_basesort formula ->
    @formula_expr_admissible T generic_relname second_basesort formula).
Proof.
  apply query_formula_expr_admissibility_mutind; intros; cbn in *; try tauto.
  destruct H as [Houtputs [Hquery Hsort]].
  repeat split; try assumption.
  - now apply bag_query_admissible_basesort_extensional.
  - pose proof (query_sort_basesort_extensional q) as Hquery_sort.
    rewrite Fset.equal_spec in Hquery_sort, Hsort |- *.
    intro attribute.
    rewrite <- (Hquery_sort attribute).
    exact (Hsort attribute).
Qed.

Theorem query_expr_admissible_basesort_extensional :
  forall query,
    @query_expr_admissible T generic_relname first_basesort query ->
    @query_expr_admissible T generic_relname second_basesort query.
Proof.
  exact (proj1 query_formula_expr_admissible_basesort_extensional).
Qed.

Theorem formula_expr_admissible_basesort_extensional :
  forall formula,
    @formula_expr_admissible T generic_relname first_basesort formula ->
    @formula_expr_admissible T generic_relname second_basesort formula.
Proof.
  exact (proj2 query_formula_expr_admissible_basesort_extensional).
Qed.

End AdmissibilityBaseSortTransport.

(** A typed lowering can expose the expected output sort of each compact bag
    node.  Pairing that small certificate with admissibility lets generated
    proofs compose without repeatedly reducing a whole nested query against a
    generated database schema. *)
Section CompositionalBagAdmissibility.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variable basesort : generic_relname -> Fset.set (A T).

Definition bag_query_admissible_with_sort
    (query : @query T generic_relname) (expected_sort : Fset.set (A T)) : Prop :=
  @bag_query_admissible T generic_relname basesort query /\
  @sort T generic_relname basesort query =S= expected_sort.

Lemma query_sort_equal_symmetry :
  forall left right : Fset.set (A T), left =S= right -> right =S= left.
Proof.
  intros left right Hequal.
  rewrite Fset.equal_spec in Hequal |- *.
  intro attribute; symmetry; apply Hequal.
Qed.

Lemma query_sort_equal_transitivity :
  forall first second third : Fset.set (A T),
    first =S= second -> second =S= third -> first =S= third.
Proof.
  intros first second third Hfirst Hsecond.
  rewrite Fset.equal_spec in Hfirst, Hsecond |- *.
  intro attribute; now rewrite Hfirst, Hsecond.
Qed.

Lemma bag_query_admissible_with_sort_empty_tuple :
  bag_query_admissible_with_sort
    (@Q_Empty_Tuple T generic_relname) (Fset.empty (A T)).
Proof.
  split; [constructor | apply Fset.equal_refl].
Qed.

Lemma bag_query_admissible_with_sort_empty_relation :
  forall expected_sort,
    bag_query_admissible_with_sort
      (@Q_Empty_Relation T generic_relname expected_sort) expected_sort.
Proof.
  intro expected_sort; split; [constructor | apply Fset.equal_refl].
Qed.

Lemma bag_query_admissible_with_sort_table :
  forall table expected_sort,
    basesort table =S= expected_sort ->
    bag_query_admissible_with_sort
      (@Q_Table T generic_relname table) expected_sort.
Proof.
  intros table expected_sort Hsort.
  split; [constructor | exact Hsort].
Qed.

Lemma bag_query_admissible_with_sort_set :
  forall operation left right left_sort right_sort,
    bag_query_admissible_with_sort left left_sort ->
    bag_query_admissible_with_sort right right_sort ->
    left_sort =S= right_sort ->
    bag_query_admissible_with_sort
      (@Q_Set T generic_relname operation left right) left_sort.
Proof.
  intros operation left right left_sort right_sort
    [Hleft Hleft_sort] [Hright Hright_sort] Hsorts.
  split.
  - econstructor; try eassumption.
    eapply query_sort_equal_transitivity; [exact Hleft_sort |].
    eapply query_sort_equal_transitivity; [exact Hsorts |].
    now apply query_sort_equal_symmetry.
  - exact Hleft_sort.
Qed.

Lemma bag_query_admissible_with_sort_cross_join :
  forall left right left_sort right_sort,
    bag_query_admissible_with_sort left left_sort ->
    bag_query_admissible_with_sort right right_sort ->
    @query_output_sorts_disjoint T left_sort right_sort ->
    bag_query_admissible_with_sort
      (@Q_CrossJoin T generic_relname left right)
      (Fset.union (A T) left_sort right_sort).
Proof.
  intros left right left_sort right_sort
    [Hleft Hleft_sort] [Hright Hright_sort] Hdisjoint.
  split.
  - econstructor; try eassumption.
    eapply (query_output_sorts_disjoint_basesort_extensional
      left_sort right_sort
      (@sort T generic_relname basesort left)
      (@sort T generic_relname basesort right)).
    + now apply query_sort_equal_symmetry.
    + now apply query_sort_equal_symmetry.
    + exact Hdisjoint.
  - cbn [sort]; now apply Fset.union_eq.
Qed.

Lemma bag_query_admissible_with_sort_project :
  forall select_list input input_sort,
    bag_query_admissible_with_sort input input_sort ->
    query_select_list_outputs_unique select_list ->
    bag_query_admissible_with_sort
      (@Q_Pi T generic_relname select_list input)
      (select_list_sort select_list).
Proof.
  intros select_list input input_sort [Hinput _] Hunique.
  split; [now constructor | apply Fset.equal_refl].
Qed.

Lemma bag_query_admissible_with_sort_filter :
  forall formula input input_sort,
    @bag_formula_admissible T generic_relname basesort formula ->
    bag_query_admissible_with_sort input input_sort ->
    bag_query_admissible_with_sort
      (@Q_Sigma T generic_relname formula input) input_sort.
Proof.
  intros formula input input_sort Hformula [Hinput Hsort].
  split; [now constructor | exact Hsort].
Qed.

Lemma bag_query_admissible_with_sort_aggregate :
  forall select_list group_terms having input input_sort,
    group_terms <> nil ->
    @bag_formula_admissible T generic_relname basesort having ->
    bag_query_admissible_with_sort input input_sort ->
    query_select_list_outputs_unique select_list ->
    bag_query_admissible_with_sort
      (@Q_Gamma T generic_relname select_list group_terms having input)
      (select_list_sort select_list).
Proof.
  intros select_list group_terms having input input_sort
    Hgroups Hhaving [Hinput _] Hunique.
  split; [now constructor | apply Fset.equal_refl].
Qed.

Lemma bag_formula_in_admissible_from_sort :
  forall (select_items : list (@select T)) subquery expected_sort,
    bag_query_admissible_with_sort subquery expected_sort ->
    length select_items = 1%nat ->
    length (Fset.elements (A T) expected_sort) = 1%nat ->
    query_in_positionally_aligned (@_Select_List T select_items)
      (Fset.elements (A T) expected_sort) ->
    @bag_formula_admissible T generic_relname basesort
      (@Sql_In T (@query T generic_relname) select_items subquery).
Proof.
  intros select_items subquery expected_sort [Hquery Hsort]
    Hselect Hlength Haligned.
  econstructor; try eassumption.
  - now rewrite (Fset.elements_spec1 _ _ _ Hsort).
  - now rewrite (Fset.elements_spec1 _ _ _ Hsort).
Qed.

Lemma bag_formula_exists_admissible_from_sort :
  forall subquery expected_sort,
    bag_query_admissible_with_sort subquery expected_sort ->
    @bag_formula_admissible T generic_relname basesort
      (@Sql_Exists T (@query T generic_relname) subquery).
Proof.
  intros subquery expected_sort [Hquery _].
  now constructor.
Qed.

Lemma query_expr_bag_admissible_from_sort :
  forall (outputs : list (attribute T))
      (query : @query T generic_relname) (expected_sort : Fset.set (A T)),
    @query_output_attributes_unique T outputs ->
    bag_query_admissible_with_sort query expected_sort ->
    @query_outputs_sort T outputs =S= expected_sort ->
    @query_expr_admissible T generic_relname basesort
      (QExpr_Bag outputs query).
Proof.
  intros outputs query expected_sort Houtputs [Hquery Hquery_sort] Hsort.
  cbn [query_expr_admissible].
  repeat split; try assumption.
  eapply query_sort_equal_transitivity; [exact Hsort |].
  now apply query_sort_equal_symmetry.
Qed.

End CompositionalBagAdmissibility.

(** Exact-query certificates carry the authoritative ordered output witness in
    addition to admissibility.  Generated proofs can therefore discharge
    parent-node side conditions against a small typed list instead of
    reducing the complete child query again. *)
Section CompositionalQueryExprAdmissibility.

Context {T : Tuple.Rcd} {generic_relname : Type}.
Variable basesort : generic_relname -> Fset.set (A T).

Definition query_expr_admissible_with_outputs
    (query : @query_expr T generic_relname)
    (expected_outputs : list (attribute T)) : Prop :=
  @query_expr_admissible T generic_relname basesort query /\
  query_expr_outputs query = expected_outputs.

Lemma query_expr_admissible_with_outputs_change :
  forall query first_outputs second_outputs,
    query_expr_admissible_with_outputs query first_outputs ->
    first_outputs = second_outputs ->
    query_expr_admissible_with_outputs query second_outputs.
Proof.
  intros query first_outputs second_outputs
    [Hadmissible Houtputs] Hequal.
  split; [exact Hadmissible | now rewrite Houtputs].
Qed.

Lemma query_output_attributes_unique_from_all_diff :
  forall outputs : list (attribute T),
    ListFacts.all_diff outputs ->
    @query_output_attributes_unique T outputs.
Proof.
  intros outputs Hdistinct.
  unfold query_output_attributes_unique.
  rewrite Fset.cardinal_spec.
  exact
    (ListPermut._permut_length
      (Fset.permut_elements_mk_set (A T) outputs Hdistinct)).
Qed.

Lemma query_sort_keys_in_outputs :
  forall (outputs : list (attribute T)) keys,
    Forall
      (fun key => In (sort_key_attribute key) outputs)
      keys ->
    query_sort_keys_in_scope (@query_outputs_sort T outputs) keys.
Proof.
  intros outputs keys Hkeys key Hkey.
  unfold query_outputs_sort.
  rewrite Fset.mem_mk_set, OrderedSet.Oset.mem_bool_true_iff.
  rewrite Forall_forall in Hkeys; now apply Hkeys.
Qed.

Lemma query_attribute_not_in_outputs :
  forall (outputs : list (attribute T)) attribute,
    ~ In attribute outputs ->
    ~ attribute inS (@query_outputs_sort T outputs).
Proof.
  intros outputs attribute Hnot_in.
  unfold query_outputs_sort.
  rewrite Fset.mem_mk_set, OrderedSet.Oset.mem_bool_true_iff.
  exact Hnot_in.
Qed.

Lemma query_expr_admissible_with_outputs_error :
  forall (outputs : list (attribute T)) error,
    @query_output_attributes_unique T outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Error T generic_relname outputs error) outputs.
Proof.
  intros outputs error Houtputs; split; cbn; assumption || reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_values :
  forall (outputs : list (attribute T)) rows,
    @query_output_attributes_unique T outputs ->
    @query_values_well_sorted T (@query_outputs_sort T outputs) rows ->
    query_expr_admissible_with_outputs
      (@QExpr_Values T generic_relname outputs rows) outputs.
Proof.
  intros outputs rows Houtputs Hrows; split; cbn; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_bag :
  forall (outputs : list (attribute T)) query expected_sort,
    @query_output_attributes_unique T outputs ->
    @bag_query_admissible_with_sort T generic_relname basesort
      query expected_sort ->
    @query_outputs_sort T outputs =S= expected_sort ->
    query_expr_admissible_with_outputs
      (@QExpr_Bag T generic_relname outputs query) outputs.
Proof.
  intros outputs query expected_sort Houtputs Hquery Hsort.
  split.
  - exact
      (@query_expr_bag_admissible_from_sort T generic_relname basesort
        outputs query expected_sort Houtputs Hquery Hsort).
  - reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_set :
  forall operation left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    left_outputs = right_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Set T generic_relname operation left right) left_outputs.
Proof.
  intros operation left right left_outputs right_outputs
    [Hleft Hleft_outputs] [Hright Hright_outputs] Houtputs.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    now rewrite Hleft_outputs, Hright_outputs.
  - cbn [query_expr_outputs]; exact Hleft_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_natural_join :
  forall left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_NaturalJoin T generic_relname left right)
      (@query_natural_join_outputs T left_outputs right_outputs).
Proof.
  intros left right left_outputs right_outputs
    [Hleft Hleft_outputs] [Hright Hright_outputs].
  split.
  - cbn [query_expr_admissible]; now split.
  - cbn [query_expr_outputs]; now rewrite Hleft_outputs, Hright_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_cross_join :
  forall left right left_outputs right_outputs,
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    @query_output_sorts_disjoint T
      (@query_outputs_sort T left_outputs)
      (@query_outputs_sort T right_outputs) ->
    query_expr_admissible_with_outputs
      (@QExpr_CrossJoin T generic_relname left right)
      (left_outputs ++ right_outputs).
Proof.
  intros left right left_outputs right_outputs
    [Hleft Hleft_outputs] [Hright Hright_outputs] Hdisjoint.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    unfold query_expr_sort; now rewrite Hleft_outputs, Hright_outputs.
  - cbn [query_expr_outputs]; now rewrite Hleft_outputs, Hright_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_join :
  forall kind predicate matched_select left_select right_select
      left right left_outputs right_outputs,
    @formula_expr_admissible T generic_relname basesort predicate ->
    query_expr_admissible_with_outputs left left_outputs ->
    query_expr_admissible_with_outputs right right_outputs ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select ->
    query_join_projections_unique
      kind matched_select left_select right_select ->
    query_expr_admissible_with_outputs
      (@QExpr_Join T generic_relname kind predicate
        matched_select left_select right_select left right)
      (match kind with
       | QueryJoinSemi | QueryJoinAnti => select_list_outputs left_select
       | _ => select_list_outputs matched_select
       end).
Proof.
  intros kind predicate matched_select left_select right_select
    left right left_outputs right_outputs Hpredicate
    [Hleft _] [Hright _] Hcompatible Hunique.
  split.
  - cbn [query_expr_admissible]; tauto.
  - reflexivity.
Qed.

Lemma query_expr_admissible_with_outputs_project :
  forall select_list input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_select_list_outputs_unique select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_Project T generic_relname select_list input)
      (select_list_outputs select_list).
Proof.
  intros select_list input input_outputs [Hinput _] Hunique.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_row_map :
  forall (outputs : list (attribute T)) row_map input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @query_output_attributes_unique T outputs ->
    @query_row_map_well_sorted T (@query_outputs_sort T outputs) row_map ->
    query_expr_admissible_with_outputs
      (@QExpr_RowMap T generic_relname outputs row_map input) outputs.
Proof.
  intros outputs row_map input input_outputs [Hinput _] Houtputs Hrow_map.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_filter :
  forall predicate input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @formula_expr_admissible T generic_relname basesort predicate ->
    query_expr_admissible_with_outputs
      (@QExpr_Filter T generic_relname predicate input) input_outputs.
Proof.
  intros predicate input input_outputs
    [Hinput Hinput_outputs] Hpredicate.
  split.
  - cbn [query_expr_admissible]; now split.
  - cbn [query_expr_outputs]; exact Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_group :
  forall select_list group_terms having input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    @formula_expr_admissible T generic_relname basesort having ->
    query_select_list_outputs_unique select_list ->
    query_expr_admissible_with_outputs
      (@QExpr_Group T generic_relname
        select_list group_terms having input)
      (select_list_outputs select_list).
Proof.
  intros select_list group_terms having input input_outputs
    [Hinput _] Hhaving Hunique.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_grouping_sets :
  forall grouping_sets input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_grouping_sets_well_formed grouping_sets ->
    query_expr_admissible_with_outputs
      (@QExpr_GroupingSets T generic_relname grouping_sets input)
      (query_grouping_sets_outputs grouping_sets).
Proof.
  intros grouping_sets input input_outputs [Hinput _] Hgroups.
  split; cbn [query_expr_admissible query_expr_outputs]; intuition.
Qed.

Lemma query_expr_admissible_with_outputs_rank :
  forall partition_keys order_keys rank_attribute embed_rank
      input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) partition_keys ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) order_keys ->
    ~ rank_attribute inS (@query_outputs_sort T input_outputs) ->
    query_expr_admissible_with_outputs
      (@QExpr_Rank T generic_relname partition_keys order_keys
        rank_attribute embed_rank input)
      (input_outputs ++ rank_attribute :: nil).
Proof.
  intros partition_keys order_keys rank_attribute embed_rank
    input input_outputs [Hinput Hinput_outputs]
    Hpartition Horder Hfresh.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption;
      unfold query_expr_sort; now rewrite Hinput_outputs.
  - cbn [query_expr_outputs]; now rewrite Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_window :
  forall partition_keys order_keys items input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) partition_keys ->
    query_sort_keys_in_scope
      (@query_outputs_sort T input_outputs) order_keys ->
    Forall
      (fun item =>
        ~ qwi_attribute item inS (@query_outputs_sort T input_outputs))
      items ->
    length (map (@qwi_attribute T) items) =
      Fset.cardinal (A T)
        (Fset.mk_set (A T) (map (@qwi_attribute T) items)) ->
    query_expr_admissible_with_outputs
      (@QExpr_Window T generic_relname partition_keys order_keys items input)
      (input_outputs ++ map (@qwi_attribute T) items).
Proof.
  intros partition_keys order_keys items input input_outputs
    [Hinput Hinput_outputs] Hpartition Horder Hfresh Hunique.
  split.
  - cbn [query_expr_admissible].
    repeat split; try assumption.
    + unfold query_expr_sort; now rewrite Hinput_outputs.
    + unfold query_expr_sort; now rewrite Hinput_outputs.
    + unfold query_expr_sort; now rewrite Hinput_outputs.
  - cbn [query_expr_outputs]; now rewrite Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_distinct :
  forall input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Distinct T generic_relname input) input_outputs.
Proof.
  intros input input_outputs [Hinput Hinput_outputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma query_expr_admissible_with_outputs_order_by :
  forall keys input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_sort_keys_in_scope (@query_outputs_sort T input_outputs) keys ->
    query_expr_admissible_with_outputs
      (@QExpr_OrderBy T generic_relname keys input) input_outputs.
Proof.
  intros keys input input_outputs [Hinput Hinput_outputs] Hkeys.
  split.
  - cbn [query_expr_admissible]; split; [assumption |].
    unfold query_expr_sort; now rewrite Hinput_outputs.
  - cbn [query_expr_outputs]; exact Hinput_outputs.
Qed.

Lemma query_expr_admissible_with_outputs_offset :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Offset T generic_relname count input) input_outputs.
Proof.
  intros count input input_outputs [Hinput Hinput_outputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma query_expr_admissible_with_outputs_fetch :
  forall count input input_outputs,
    query_expr_admissible_with_outputs input input_outputs ->
    query_expr_admissible_with_outputs
      (@QExpr_Fetch T generic_relname count input) input_outputs.
Proof.
  intros count input input_outputs [Hinput Hinput_outputs].
  split; cbn [query_expr_admissible query_expr_outputs]; assumption.
Qed.

Lemma formula_expr_quant_admissible_from_outputs :
  forall quantifier predicate arguments subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    length arguments = 1%nat ->
    length expected_outputs = 1%nat ->
    (length arguments + length expected_outputs)%nat =
      predicate_arity T predicate ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Quant T generic_relname
        quantifier predicate arguments subquery).
Proof.
  intros quantifier predicate arguments subquery expected_outputs
    [Hquery Houtputs] Harguments Hsubquery Harity.
  cbn [formula_expr_admissible].
  repeat split; try assumption; now rewrite Houtputs.
Qed.

Lemma formula_expr_in_admissible_from_outputs :
  forall (select_items : list (@select T)) subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    query_in_positionally_aligned
      (@_Select_List T select_items) expected_outputs ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_In T generic_relname select_items subquery).
Proof.
  intros select_items subquery expected_outputs
    [Hquery Houtputs] Haligned.
  cbn [formula_expr_admissible].
  split; [exact Hquery |].
  split.
  - unfold query_expr_sort, select_list_sort, query_outputs_sort.
    rewrite Houtputs.
    pose proof Haligned as Hposition.
    destruct Hposition as [_ [_ Hposition]].
    rewrite Hposition; apply Fset.equal_refl.
  - now rewrite Houtputs.
Qed.

Lemma formula_expr_exists_admissible_from_outputs :
  forall subquery expected_outputs,
    query_expr_admissible_with_outputs subquery expected_outputs ->
    @formula_expr_admissible T generic_relname basesort
      (@FExpr_Exists T generic_relname subquery).
Proof.
  intros subquery expected_outputs [Hquery _].
  exact Hquery.
Qed.

End CompositionalQueryExprAdmissibility.

(** Schema conformance states the same pointwise base-sort equality in the
    opposite orientation from certificate transport. *)
Theorem query_expr_admissible_database_schema_transport :
  forall expected constraints actual query,
    database_conforms_schema expected constraints actual ->
    @query_expr_admissible TNull relname (@_basesort TNull expected) query ->
    @query_expr_admissible TNull relname (@_basesort TNull actual) query.
Proof.
  intros expected constraints actual query Hschema Hadmissible.
  eapply query_expr_admissible_basesort_extensional.
  - intro relation.
    pose proof
      (database_conforms_schema_basesort
        expected constraints actual Hschema relation) as Hactual.
    rewrite Fset.equal_spec in Hactual |- *.
    intro attribute; symmetry; apply Hactual.
  - exact Hadmissible.
Qed.
