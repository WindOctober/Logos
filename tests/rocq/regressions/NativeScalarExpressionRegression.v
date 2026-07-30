From Stdlib Require Import Lia List Sorting.Permutation String ZArith.
From SQLFS Require Import Bool3 Env FiniteBag FiniteCollection FiniteSet
  Formula GenericInstance SqlOrder SqlOutcome SqlQueryFacts SqlQuerySemantics SqlQuerySyntax
  SqlBagAbstraction SqlQueryWellFormed SqlSyntax Values.
From Logos.FormalSQL Require Import QueryTNullSyntax TNullSyntax.

Import ListNotations.
Import Tuple.
Open Scope string_scope.
Open Scope Z_scope.

Definition native_scalar_x : attribute TNull := AttrZ "native_scalar_x".

Definition native_scalar_row_one : tuple TNull :=
  mk_tuple_lists [native_scalar_x] [Value_Z (Some 1)].

Definition native_scalar_row_null : tuple TNull :=
  mk_tuple_lists [native_scalar_x] [Value_Z None].

Local Abbreviation native_eval_query :=
  (@eval_query_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value).

Local Abbreviation native_eval_scalar_value :=
  (@eval_scalar_value_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value).

Local Abbreviation native_eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value).

Local Abbreviation native_eval_exists :=
  (@eval_query_exists_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value).

Lemma native_values_observation :
  forall env outputs rows,
    native_eval_query env
      (QExpr_Values outputs (rows_bag TNull rows)) (SqlSuccess rows).
Proof.
  intros env outputs rows; apply EQuery_Values.
  unfold query_same_rows_as_bag, rows_bag; apply Febag.equal_refl.
Qed.

Example scalar_subquery_zero_rows_is_typed_null :
  native_eval_scalar_value nil
    (@SExpr_Subquery TNull relname type_Z (Value_Z None)
      (QExpr_Values [native_scalar_x] (rows_bag TNull [])))
    (SqlSuccess (Value_Z None)).
Proof.
  replace (SqlSuccess (Value_Z None)) with
    (@scalar_subquery_value_outcome TNull (Value_Z None) [native_scalar_x]
      (SqlSuccess [])) by reflexivity.
  eapply EScalar_Subquery.
  - reflexivity.
  - apply native_values_observation.
Qed.

Example scalar_subquery_one_row_is_its_value :
  native_eval_scalar_value nil
    (@SExpr_Subquery TNull relname type_Z (Value_Z None)
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one])))
    (SqlSuccess (dot TNull native_scalar_row_one native_scalar_x)).
Proof.
  replace (SqlSuccess (dot TNull native_scalar_row_one native_scalar_x)) with
    (@scalar_subquery_value_outcome TNull (Value_Z None) [native_scalar_x]
      (SqlSuccess [native_scalar_row_one])) by reflexivity.
  eapply EScalar_Subquery.
  - reflexivity.
  - apply native_values_observation.
Qed.

Example scalar_subquery_two_rows_is_cardinality_violation :
  native_eval_scalar_value nil
    (@SExpr_Subquery TNull relname type_Z (Value_Z None)
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one; native_scalar_row_null])))
    (SqlError CardinalityViolation).
Proof.
  replace (SqlError CardinalityViolation) with
    (@scalar_subquery_value_outcome TNull (Value_Z None) [native_scalar_x]
      (SqlSuccess [native_scalar_row_one; native_scalar_row_null]))
    by reflexivity.
  eapply EScalar_Subquery.
  - reflexivity.
  - apply native_values_observation.
Qed.

Definition native_scalar_one :=
  @SExpr_Leaf TNull relname type_Z (CstZ 1).

Lemma native_scalar_one_evaluates_in_env :
  forall env,
    native_eval_scalar_value env native_scalar_one
      (SqlSuccess (Value_Z (Some 1))).
Proof.
  intros; apply EScalar_Leaf.
Qed.

Lemma native_scalar_one_evaluates_once :
  native_eval_scalar_value nil native_scalar_one
    (SqlSuccess (Value_Z (Some 1))).
Proof.
  apply native_scalar_one_evaluates_in_env.
Qed.

Lemma native_scalar_one_argument_list_evaluates_in_env :
  forall env,
    @eval_scalar_values_outcome TNull relname
      (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env [native_scalar_one] (SqlSuccess [Value_Z (Some 1)]).
Proof.
  intro env.
  replace (SqlSuccess [Value_Z (Some 1)]) with
    (@scalar_value_cons_outcome TNull (Value_Z (Some 1)) (SqlSuccess []))
    by reflexivity.
  eapply EScalarValues_Cons.
  - apply native_scalar_one_evaluates_in_env.
  - constructor.
Qed.

Lemma native_scalar_one_argument_list_evaluates_once :
  @eval_scalar_values_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    nil [native_scalar_one] (SqlSuccess [Value_Z (Some 1)]).
Proof.
  apply native_scalar_one_argument_list_evaluates_in_env.
Qed.

Lemma native_query_canonical_rows_empty :
  @query_canonical_rows TNull [] = [].
Proof.
  unfold query_canonical_rows, query_rows_bag; cbn [Febag.mk_bag].
  apply Febag.elements_empty.
Qed.

Example native_in_true_projection_truth :
  native_eval_scalar_boolean nil
    (SExpr_In [native_scalar_one]
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one])))
    (SqlSuccess true3).
Proof.
  eapply EScalar_InSuccess with
    (values := [Value_Z (Some 1)]) (rows := [native_scalar_row_one]).
  - apply native_scalar_one_argument_list_evaluates_once.
  - apply native_values_observation.
Qed.

Example native_in_false_projection_truth :
  native_eval_scalar_boolean nil
    (SExpr_In [native_scalar_one]
      (QExpr_Values [native_scalar_x] (rows_bag TNull [])))
    (SqlSuccess false3).
Proof.
  replace false3 with
    (interp_quant Bool3 Exists_F
      (fun row : tuple TNull =>
        @query_value_lists_equal TNull unknown3 NullValues.is_null_value
          [Value_Z (Some 1)]
          (@query_row_output_values TNull [native_scalar_x] row))
      (@query_canonical_rows TNull []));
    [ | now rewrite native_query_canonical_rows_empty].
  eapply (@EScalar_InSuccess TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    nil [native_scalar_one]
    (QExpr_Values [native_scalar_x] (rows_bag TNull []))
    [Value_Z (Some 1)] []).
  - apply native_scalar_one_argument_list_evaluates_once.
  - apply native_values_observation.
Qed.

Example native_in_unknown_projection_truth :
  native_eval_scalar_boolean nil
    (SExpr_In [native_scalar_one]
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_null])))
    (SqlSuccess unknown3).
Proof.
  eapply EScalar_InSuccess with
    (values := [Value_Z (Some 1)]) (rows := [native_scalar_row_null]).
  - apply native_scalar_one_argument_list_evaluates_once.
  - apply native_values_observation.
Qed.

Definition native_in_true_expression :=
  @SExpr_In TNull relname [native_scalar_one]
    (QExpr_Values [native_scalar_x]
      (rows_bag TNull [native_scalar_row_one])).

Definition native_in_false_expression :=
  @SExpr_In TNull relname [native_scalar_one]
    (QExpr_Values [native_scalar_x] (rows_bag TNull [])).

Definition native_in_unknown_expression :=
  @SExpr_In TNull relname [native_scalar_one]
    (QExpr_Values [native_scalar_x]
      (rows_bag TNull [native_scalar_row_null])).

Lemma native_in_true_evaluates_in_env :
  forall env,
    native_eval_scalar_boolean env native_in_true_expression
      (SqlSuccess true3).
Proof.
  intro env; eapply EScalar_InSuccess with
    (values := [Value_Z (Some 1)]) (rows := [native_scalar_row_one]).
  - apply native_scalar_one_argument_list_evaluates_in_env.
  - apply native_values_observation.
Qed.

Lemma native_in_false_evaluates_in_env :
  forall env,
    native_eval_scalar_boolean env native_in_false_expression
      (SqlSuccess false3).
Proof.
  intro env.
  replace false3 with
    (interp_quant Bool3 Exists_F
      (fun row : tuple TNull =>
        @query_value_lists_equal TNull unknown3 NullValues.is_null_value
          [Value_Z (Some 1)]
          (@query_row_output_values TNull [native_scalar_x] row))
      (@query_canonical_rows TNull []));
    [ | now rewrite native_query_canonical_rows_empty].
  eapply (@EScalar_InSuccess TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env [native_scalar_one]
    (QExpr_Values [native_scalar_x] (rows_bag TNull []))
    [Value_Z (Some 1)] []).
  - apply native_scalar_one_argument_list_evaluates_in_env.
  - apply native_values_observation.
Qed.

Lemma native_in_unknown_evaluates_in_env :
  forall env,
    native_eval_scalar_boolean env native_in_unknown_expression
      (SqlSuccess unknown3).
Proof.
  intro env; eapply EScalar_InSuccess with
    (values := [Value_Z (Some 1)]) (rows := [native_scalar_row_null]).
  - apply native_scalar_one_argument_list_evaluates_in_env.
  - apply native_values_observation.
Qed.

Definition native_scalar_truth : attribute TNull :=
  AttrBool "native_scalar_truth".

Definition native_boolean_value
    (expression : @scalar_expr TNull relname ScalarResultBoolean) :=
  @SExpr_BoolValue TNull relname type_bool NullValues.bool3_to_value_bool
    expression.

Definition native_boolean_projection_item
    (expression : @scalar_expr TNull relname ScalarResultBoolean) :=
  (native_boolean_value expression, native_scalar_truth).

Definition native_boolean_projection_row
    (expression : @scalar_expr TNull relname ScalarResultBoolean)
    (truth : bool3) : tuple TNull :=
  @scalar_project_row TNull relname
    [native_boolean_projection_item expression]
    [NullValues.bool3_to_value_bool truth].

Lemma native_boolean_value_evaluates_once :
  forall env expression truth,
    native_eval_scalar_boolean env expression (SqlSuccess truth) ->
    native_eval_scalar_value env (native_boolean_value expression)
      (SqlSuccess (NullValues.bool3_to_value_bool truth)).
Proof.
  intros env expression truth Heval.
  replace (SqlSuccess (NullValues.bool3_to_value_bool truth)) with
    (@scalar_bool_value_outcome TNull NullValues.bool3_to_value_bool
      (SqlSuccess truth)) by reflexivity.
  now apply EScalar_BoolValue.
Qed.

Lemma native_boolean_scalar_project_observes_nullable_value :
  forall expression truth,
    native_eval_scalar_boolean
      (env_t TNull nil native_scalar_row_one) expression
      (SqlSuccess truth) ->
    native_eval_query nil
      (QExpr_ScalarProject [native_boolean_projection_item expression]
        (QExpr_Values [native_scalar_x]
          (rows_bag TNull [native_scalar_row_one])))
      (SqlSuccess [native_boolean_projection_row expression truth]).
Proof.
  intros expression truth Heval.
  eapply EQuery_ScalarProjectRows with
    (input_rows := [native_scalar_row_one]).
  - apply native_values_observation.
  - replace (SqlSuccess [native_boolean_projection_row expression truth]) with
      (@scalar_project_cons_outcome TNull
        (native_boolean_projection_row expression truth) (SqlSuccess []))
      by reflexivity.
    eapply EScalarProjectRows_Cons with
      (values := [NullValues.bool3_to_value_bool truth])
      (tail := SqlSuccess []).
    + change (@eval_scalar_values_outcome TNull relname
        (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        (env_t TNull nil native_scalar_row_one)
        [native_boolean_value expression]
        (SqlSuccess [NullValues.bool3_to_value_bool truth])).
      replace (SqlSuccess [NullValues.bool3_to_value_bool truth]) with
        (@scalar_value_cons_outcome TNull
          (NullValues.bool3_to_value_bool truth) (SqlSuccess []))
        by reflexivity.
      eapply EScalarValues_Cons.
      * now apply native_boolean_value_evaluates_once.
      * constructor.
    + constructor.
Qed.

Example native_in_true_scalar_projection_value :
  native_eval_query nil
    (QExpr_ScalarProject
      [native_boolean_projection_item native_in_true_expression]
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one])))
    (SqlSuccess
      [native_boolean_projection_row native_in_true_expression true3]).
Proof.
  apply native_boolean_scalar_project_observes_nullable_value.
  apply native_in_true_evaluates_in_env.
Qed.

Example native_in_false_scalar_projection_value :
  native_eval_query nil
    (QExpr_ScalarProject
      [native_boolean_projection_item native_in_false_expression]
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one])))
    (SqlSuccess
      [native_boolean_projection_row native_in_false_expression false3]).
Proof.
  apply native_boolean_scalar_project_observes_nullable_value.
  apply native_in_false_evaluates_in_env.
Qed.

Example native_in_unknown_scalar_projection_is_null_boolean :
  native_eval_query nil
    (QExpr_ScalarProject
      [native_boolean_projection_item native_in_unknown_expression]
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one])))
    (SqlSuccess
      [native_boolean_projection_row native_in_unknown_expression unknown3]).
Proof.
  apply native_boolean_scalar_project_observes_nullable_value.
  apply native_in_unknown_evaluates_in_env.
Qed.

(** Analysis errors are admitted only as a root query outcome.  Executor
    demand, including FETCH 0 and dead SELECT targets under EXISTS, cannot
    suppress a nested undefined-function/column error. *)
Example fetch_zero_nested_analysis_error_is_rejected :
  ~ @query_expr_analysis_error_well_placed TNull relname
      (QExpr_Fetch 0
        (@QExpr_Error TNull relname [native_scalar_x] UndefinedFunction)).
Proof.
  cbn [query_expr_analysis_error_well_placed
    query_expr_contains_analysis_error].
  discriminate.
Qed.

Example scalar_target_nested_analysis_error_is_rejected :
  ~ @query_expr_analysis_error_well_placed TNull relname
      (QExpr_ScalarProject
        [(@SExpr_Subquery TNull relname type_Z (Value_Z None)
            (@QExpr_Error TNull relname [native_scalar_x] UndefinedFunction),
          native_scalar_x)]
        (QExpr_Values [native_scalar_x]
          (rows_bag TNull [native_scalar_row_one]))).
Proof.
  cbn [query_expr_analysis_error_well_placed
    query_expr_contains_analysis_error scalar_expr_contains_analysis_error].
  discriminate.
Qed.

Definition native_dead_division_output : attribute TNull :=
  AttrInt32 "native_dead_division_output".

Definition native_int32_one : int32.
Proof.
  refine (Int32 1 _); unfold int32_min, int32_max; lia.
Defined.

Definition native_int32_zero : int32.
Proof.
  refine (Int32 0 _); unfold int32_min, int32_max; lia.
Defined.

Definition native_int32_one_term : AggTerm :=
  AExpr (Constant (Value_int32 (Some native_int32_one))).

Definition native_int32_zero_term : AggTerm :=
  AExpr (Constant (Value_int32 (Some native_int32_zero))).

Definition native_one_div_zero :=
  @SExpr_Call TNull relname type_int32 (ScalarDivide ScalarInt32)
    [@SExpr_Leaf TNull relname type_int32 native_int32_one_term;
     @SExpr_Leaf TNull relname type_int32 native_int32_zero_term].

Definition native_one_div_zero_aggregate_term : AggTerm :=
  AScalarCall (ScalarDivide ScalarInt32)
    [native_int32_one_term; native_int32_zero_term].

Lemma native_one_div_zero_ordinary_evaluation_errors :
  forall env,
    native_eval_scalar_value env native_one_div_zero
      (SqlError (DataException DivisionByZero)).
Proof.
  intro env.
  replace (SqlError (DataException DivisionByZero)) with
    (@scalar_call_value_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      (ScalarDivide ScalarInt32)
      [Value_int32 (Some native_int32_one);
       Value_int32 (Some native_int32_zero)]).
  2: {
    cbn [scalar_call_value_outcome
      NullValues.interp_scalar_operator_runtime_error
      NullValues.first_observation_error NullValues.observation_values
      NullValues.scalar_operator_local_runtime_error
      NullValues.int32_div_runtime_error NullValues.division_by_zero
      native_int32_zero].
    reflexivity.
  }
  apply EScalar_CallSuccess.
  replace
    (SqlSuccess
      [Value_int32 (Some native_int32_one);
       Value_int32 (Some native_int32_zero)]) with
    (@scalar_value_cons_outcome TNull (Value_int32 (Some native_int32_one))
      (@scalar_value_cons_outcome TNull (Value_int32 (Some native_int32_zero))
        (SqlSuccess []))) by reflexivity.
  eapply (@EScalarValues_Cons TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value env
    (@SExpr_Leaf TNull relname type_int32 native_int32_one_term)
    [@SExpr_Leaf TNull relname type_int32 native_int32_zero_term]
    (Value_int32 (Some native_int32_one))
    (@scalar_value_cons_outcome TNull
      (Value_int32 (Some native_int32_zero)) (SqlSuccess []))).
  - change (native_eval_scalar_value env
      (@SExpr_Leaf TNull relname type_int32 native_int32_one_term)
      (@scalar_leaf_value_outcome TNull
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error env native_int32_one_term)).
    apply EScalar_Leaf.
  - eapply (@EScalarValues_Cons TNull relname
      (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value env
      (@SExpr_Leaf TNull relname type_int32 native_int32_zero_term) []
      (Value_int32 (Some native_int32_zero)) (SqlSuccess [])).
    + change (native_eval_scalar_value env
        (@SExpr_Leaf TNull relname type_int32 native_int32_zero_term)
        (@scalar_leaf_value_outcome TNull
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error env native_int32_zero_term)).
      apply EScalar_Leaf.
    + constructor.
Qed.

Definition native_division_projection : QueryExpr :=
  QExpr_ScalarProject
    [(native_one_div_zero, native_dead_division_output)]
    (QExpr_Values [native_scalar_x]
      (rows_bag TNull [native_scalar_row_one])).

Definition native_count_div_zero_term : AggTerm :=
  AAggregate AggregateCount AggregateAll
    (ScalarCall (ScalarDivide ScalarInt32)
      [Constant (Value_int32 (Some native_int32_one));
       Constant (Value_int32 (Some native_int32_zero))]).

Definition native_count_div_zero_output : attribute TNull :=
  AttrInt64 "native_count_div_zero_output".

Definition native_count_div_zero_select :=
  [(@SExpr_Leaf TNull relname type_int64 native_count_div_zero_term,
    native_count_div_zero_output)].

Definition native_count_div_zero_group : QueryExpr :=
  QExpr_ScalarGroup native_count_div_zero_select []
    (@SExpr_True TNull relname)
    (QExpr_Values [native_scalar_x]
      (rows_bag TNull [native_scalar_row_one])).

Lemma native_division_projection_errors :
  native_eval_query nil native_division_projection
    (SqlError (DataException DivisionByZero)).
Proof.
  unfold native_division_projection.
  eapply EQuery_ScalarProjectRows with
    (input_rows := [native_scalar_row_one]).
  - apply native_values_observation.
  - apply EScalarProjectRows_HeadError.
    apply EScalarValues_HeadError.
    apply native_one_div_zero_ordinary_evaluation_errors.
Qed.

(** Aggregate target finalization is live under EXISTS even though the
    post-HAVING projected value itself is not demanded. *)
Example exists_group_prefinalizes_target_aggregate :
  native_eval_exists nil native_count_div_zero_group
    (SqlError (DataException DivisionByZero)).
Proof.
  replace (SqlError (DataException DivisionByZero)) with
    (@query_exists_cardinality_outcome TNull
      (SqlError (DataException DivisionByZero))) by reflexivity.
  eapply EExists_Cardinality.
  - reflexivity.
  - unfold native_count_div_zero_group.
    eapply ECardinality_ScalarGroup with
      (group_terms := []) (input_rows := [native_scalar_row_one]).
    + reflexivity.
    + apply native_values_observation.
    + eapply EScalarGroupCardinality_Process with
        (representative := [native_scalar_row_one]).
      * unfold query_same_rows_as_bag, rows_bag; apply Febag.equal_refl.
      * reflexivity.
      * cbn [query_make_groups].
        apply EScalarGroupsCardinality_SelectAggregateError.
        reflexivity.
Qed.

(** The target is the modeled PostgreSQL integer [1 / 0] call.  EXISTS sees
    the input row and never invokes that dead target expression. *)
Example exists_scalar_project_does_not_evaluate_one_div_zero_target :
  native_eval_exists nil
    (QExpr_ScalarProject
      [(native_one_div_zero, native_dead_division_output)]
      (QExpr_Values [native_scalar_x]
        (rows_bag TNull [native_scalar_row_one])))
    (SqlSuccess true3).
Proof.
  apply EExists_ScalarProject.
  replace (SqlSuccess true3) with
    (@query_exists_rows_outcome TNull (SqlSuccess [native_scalar_row_one]))
    by reflexivity.
  eapply EExists_Demanded.
  - reflexivity.
  - apply native_values_observation.
Qed.

(** Bare DISTINCT is removable under direct EXISTS, so the ordinary target
    remains dead just as it is without DISTINCT. *)
Example exists_distinct_does_not_evaluate_one_div_zero_target :
  native_eval_exists nil (QExpr_Distinct native_division_projection)
    (SqlSuccess true3).
Proof.
  apply EExists_Distinct.
  unfold native_division_projection.
  apply EExists_ScalarProject.
  replace (SqlSuccess true3) with
    (@query_exists_rows_outcome TNull (SqlSuccess [native_scalar_row_one]))
    by reflexivity.
  eapply EExists_Demanded.
  - reflexivity.
  - apply native_values_observation.
Qed.

(** OFFSET is a PostgreSQL demand barrier: even OFFSET 0 retains ordinary
    target evaluation before existential cardinality is observed. *)
Example exists_offset_evaluates_one_div_zero_target :
  native_eval_exists nil (QExpr_Offset 0 native_division_projection)
    (SqlError (DataException DivisionByZero)).
Proof.
  replace (SqlError (DataException DivisionByZero)) with
    (@query_exists_rows_outcome TNull
      (SqlError (DataException DivisionByZero))) by reflexivity.
  eapply EExists_Demanded.
  - reflexivity.
  - apply EQuery_OffsetChildError.
    exact native_division_projection_errors.
Qed.

(** FETCH 0 still suppresses executable runtime work; unlike a nested
    [QExpr_Error], this query contains no analysis-time failure. *)
Example exists_fetch_zero_suppresses_runtime_division :
  native_eval_exists nil (QExpr_Fetch 0 native_division_projection)
    (SqlSuccess false3).
Proof.
  apply EExists_FetchZero.
  reflexivity.
Qed.

Definition native_division_window : QueryExpr :=
  WindowExpr [] []
    [WindowAggregateItem native_dead_division_output
      native_one_div_zero_aggregate_term]
    (QExpr_Values [native_scalar_x]
      (rows_bag TNull [native_scalar_row_one])).

Lemma native_division_window_errors :
  native_eval_query nil native_division_window
    (SqlError (DataException DivisionByZero)).
Proof.
  unfold native_division_window, WindowExpr.
  eapply EQuery_WindowRowsError with
    (input_rows := [native_scalar_row_one])
    (ordered_rows := [native_scalar_row_one]).
  - apply native_values_observation.
  - split.
    + unfold query_same_rows_as_bag; apply Febag.equal_refl.
    + cbn [ordered_rows ordered_pair compare_order_keys]; split; exact I.
  - reflexivity.
Qed.

Example exists_window_evaluates_one_div_zero_item :
  native_eval_exists nil native_division_window
    (SqlError (DataException DivisionByZero)).
Proof.
  replace (SqlError (DataException DivisionByZero)) with
    (@query_exists_rows_outcome TNull
      (SqlError (DataException DivisionByZero))) by reflexivity.
  eapply EExists_Demanded.
  - reflexivity.
  - apply native_division_window_errors.
Qed.

Definition native_false_expression :=
  @SExpr_Not TNull relname (@SExpr_True TNull relname).

(** The next two examples characterize the raw closed [SExpr_Conj] relation.
    They are intentionally outside the SQL-lowering image: the host accepts an
    AND/OR term only after proving every operand runtime-total, and rejects
    either of these error-capable right operands before Rocq emission. *)
Example native_and_short_circuits_false_left :
  native_eval_scalar_boolean nil
    (@SExpr_Conj TNull relname And_F native_false_expression
      (@SExpr_Pred TNull relname PredicateEq
        [native_one_div_zero;
         @SExpr_Leaf TNull relname type_int32 native_int32_zero_term]))
    (SqlSuccess false3).
Proof.
  apply EScalar_ConjShortCircuit with (left_truth := false3).
  - apply EScalar_NotSuccess with (truth := true3).
    apply EScalar_True.
  - reflexivity.
Qed.

Example native_or_short_circuits_true_left :
  native_eval_scalar_boolean nil
    (@SExpr_Conj TNull relname Or_F (@SExpr_True TNull relname)
      (@SExpr_Pred TNull relname PredicateEq
        [native_one_div_zero;
         @SExpr_Leaf TNull relname type_int32 native_int32_zero_term]))
    (SqlSuccess true3).
Proof.
  apply EScalar_ConjShortCircuit with (left_truth := true3).
  - apply EScalar_True.
  - reflexivity.
Qed.

Section GenericShortCircuit.

Context {T : Tuple.Rcd} {relname0 : Type}.
Variable basesort : relname0 -> Fset.set (A T).
Variable instance : relname0 -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.

Example filter_exists_stops_after_safe_first_match :
  forall env formula first later truth,
    @eval_formula_expr_outcome T relname0 basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      (env_t T env first) formula (SqlSuccess truth) ->
    Bool.is_true (B T) truth = true ->
    @eval_filter_exists_outcome T relname0 basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula (first :: later) (SqlSuccess (Bool.true (B T))).
Proof.
  intros; now apply EFilterExists_HeadTrue with (truth := truth).
Qed.

End GenericShortCircuit.

(** Any legal row chosen by an unordered FETCH-1 observation feeds the scalar
    subquery once; there is no second child replay from which to pick a
    different top row. *)
Lemma native_scalar_subquery_topk_uses_one_chosen_observation :
  forall env child row,
    query_expr_outputs child = [native_scalar_x] ->
    native_eval_query env
      (QExpr_Fetch 1 (QExpr_OrderBy [] child)) (SqlSuccess [row]) ->
    native_eval_scalar_value env
      (@SExpr_Subquery TNull relname type_Z (Value_Z None)
        (QExpr_Fetch 1 (QExpr_OrderBy [] child)))
      (SqlSuccess (dot TNull row native_scalar_x)).
Proof.
  intros env child row Houtputs Hchosen.
  replace (SqlSuccess (dot TNull row native_scalar_x)) with
    (@scalar_subquery_value_outcome TNull (Value_Z None)
      (query_expr_outputs (QExpr_Fetch 1 (QExpr_OrderBy [] child)))
      (SqlSuccess [row])).
  - eapply EScalar_Subquery; [reflexivity | exact Hchosen].
  - cbn [query_expr_outputs]; now rewrite Houtputs.
Qed.

Definition native_two_row_values : QueryExpr :=
  QExpr_Values [native_scalar_x]
    (rows_bag TNull [native_scalar_row_one; native_scalar_row_null]).

Definition native_two_row_unordered_topk : QueryExpr :=
  QExpr_Fetch 1 (QExpr_OrderBy [] native_two_row_values).

Definition native_two_row_scalar_subquery :=
  @SExpr_Subquery TNull relname type_Z (Value_Z None)
    native_two_row_unordered_topk.

Lemma native_two_row_values_reversed_observation :
  forall env,
    native_eval_query env native_two_row_values
      (SqlSuccess [native_scalar_row_null; native_scalar_row_one]).
Proof.
  intro env; unfold native_two_row_values.
  apply EQuery_Values.
  eapply query_same_rows_as_bag_transport with
    (first := [native_scalar_row_one; native_scalar_row_null]).
  - unfold query_same_rows_as_bag, query_rows_bag, rows_bag.
    apply Febag.equal_refl.
  - apply concrete_permutation_rows_bag_eq, perm_swap.
Qed.

Lemma native_two_row_topk_can_choose_first_row :
  native_eval_query nil native_two_row_unordered_topk
    (SqlSuccess [native_scalar_row_one]).
Proof.
  unfold native_two_row_unordered_topk.
  eapply (@EQuery_FetchSuccess TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value nil
    1 (QExpr_OrderBy [] native_two_row_values)
    [native_scalar_row_one; native_scalar_row_null]).
  eapply EQuery_OrderBySuccess with
    (input_rows := [native_scalar_row_one; native_scalar_row_null]).
  - unfold native_two_row_values; apply native_values_observation.
  - split.
    + unfold query_same_rows_as_bag; apply Febag.equal_refl.
    + cbn [ordered_rows ordered_pair compare_order_keys]; split; exact I.
Qed.

Lemma native_two_row_topk_can_choose_second_row :
  native_eval_query nil native_two_row_unordered_topk
    (SqlSuccess [native_scalar_row_null]).
Proof.
  unfold native_two_row_unordered_topk.
  eapply (@EQuery_FetchSuccess TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value nil
    1 (QExpr_OrderBy [] native_two_row_values)
    [native_scalar_row_null; native_scalar_row_one]).
  eapply EQuery_OrderBySuccess with
    (input_rows := [native_scalar_row_null; native_scalar_row_one]).
  - apply native_two_row_values_reversed_observation.
  - split.
    + unfold query_same_rows_as_bag; apply Febag.equal_refl.
    + cbn [ordered_rows ordered_pair compare_order_keys]; split; exact I.
Qed.

(** The same unordered two-row query has both legal FETCH-1 observations, and
    each chosen row flows to its own scalar value.  There is no independent
    replay capable of pairing one top row with the other row's value. *)
Example native_two_row_topk_scalar_subquery_preserves_each_choice :
  native_eval_scalar_value nil native_two_row_scalar_subquery
    (SqlSuccess (dot TNull native_scalar_row_one native_scalar_x)) /\
  native_eval_scalar_value nil native_two_row_scalar_subquery
    (SqlSuccess (dot TNull native_scalar_row_null native_scalar_x)).
Proof.
  split; unfold native_two_row_scalar_subquery, native_two_row_unordered_topk.
  - eapply native_scalar_subquery_topk_uses_one_chosen_observation.
    + reflexivity.
    + apply native_two_row_topk_can_choose_first_row.
  - eapply native_scalar_subquery_topk_uses_one_chosen_observation.
    + reflexivity.
    + apply native_two_row_topk_can_choose_second_row.
Qed.

(** [EQuery_WindowSuccess] has exactly one child observation.  The complete
    partition aggregate and the returned input rows are both computed from the
    [input_rows] selected by this single premise. *)
Lemma full_partition_window_uses_one_chosen_child_observation :
  forall env partition_keys order_keys output_attribute term input
      input_rows ordered_rows window_rows output,
    native_eval_query env input (SqlSuccess input_rows) ->
    @order_by_rows TNull NullValues.is_null_value
      (partition_keys ++ order_keys)
      (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows ->
    @query_window_rows_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env partition_keys
      [WindowFullPartitionAggregateItem output_attribute term]
      None 0 [] ordered_rows = Some (SqlSuccess window_rows) ->
    @query_same_rows_as_bag TNull output (query_rows_bag window_rows) ->
    native_eval_query env
      (QExpr_Window partition_keys order_keys
        [WindowFullPartitionAggregateItem output_attribute term] input)
      (SqlSuccess output).
Proof.
  intros; eapply EQuery_WindowSuccess; eassumption.
Qed.

Definition native_full_frame_count_output : attribute TNull :=
  AttrInt64 "native_full_frame_count_output".

Definition native_full_frame_count_item : QueryWindowItemT :=
  WindowFullPartitionAggregateItem native_full_frame_count_output ACountStar.

(** COUNT-star over the full partition is the benchmark-supported instance of
    the shared-child full-frame constructor. *)
Lemma full_partition_count_uses_one_chosen_child_observation :
  forall env partition_keys order_keys input input_rows ordered_rows
      window_rows output,
    native_eval_query env input (SqlSuccess input_rows) ->
    @order_by_rows TNull NullValues.is_null_value
      (partition_keys ++ order_keys)
      (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows ->
    @query_window_rows_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env partition_keys [native_full_frame_count_item]
      None 0 [] ordered_rows = Some (SqlSuccess window_rows) ->
    @query_same_rows_as_bag TNull output (query_rows_bag window_rows) ->
    native_eval_query env
      (QExpr_Window partition_keys order_keys
        [native_full_frame_count_item] input)
      (SqlSuccess output).
Proof.
  intros; unfold native_full_frame_count_item in *.
  eapply full_partition_window_uses_one_chosen_child_observation; eassumption.
Qed.

(** Every grouping-set branch receives the same bag made from one selected
    child row list.  The branch relation cannot independently replay [input]. *)
Lemma grouping_sets_use_one_chosen_child_observation :
  forall env grouping_sets input input_rows output_bag output,
    native_eval_query env input (SqlSuccess input_rows) ->
    @eval_grouping_sets_bag_outcome TNull relname
      (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env grouping_sets (query_rows_bag input_rows)
      (SqlSuccess output_bag) ->
    @query_same_rows_as_bag TNull output output_bag ->
    native_eval_query env (QExpr_GroupingSets grouping_sets input)
      (SqlSuccess output).
Proof.
  intros; eapply EQuery_GroupingSetsSuccess; eassumption.
Qed.

Example nonnull_scalar_subquery_witness_is_rejected :
  ~ @scalar_expr_witnesses_valid TNull relname NullValues.is_null_value
      ScalarResultValue
      (@SExpr_Subquery TNull relname type_Z (Value_Z (Some 1))
        (QExpr_Values [native_scalar_x] (rows_bag TNull []))).
Proof.
  cbn [scalar_expr_witnesses_valid].
  intros [Hnull _]; discriminate Hnull.
Qed.

Example wrong_leaf_type_witness_is_rejected :
    ~ @scalar_expr_types_valid TNull relname
        TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
        type_int64 type_bool ScalarResultValue
        (@SExpr_Leaf TNull relname type_bool (CstZ 1)).
Proof.
  cbn [scalar_expr_types_valid TNullLeafHasType TNullAggTermType
    TNullAggTermTypeFuel TNullFunTermType TNullFunTermTypeFuel].
  discriminate.
Qed.

Example nonboolean_value_to_truth_is_rejected :
    ~ @scalar_expr_types_valid TNull relname
        TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
        type_int64 type_bool ScalarResultBoolean
        (@SExpr_ValueBool TNull relname NullValues.value_bool_to_bool3
          (@SExpr_Leaf TNull relname type_Z (CstZ 1))).
Proof.
  intros Hvalid.
  cbn [scalar_expr_types_valid] in Hvalid.
  destruct Hvalid as [_ Htype]; discriminate Htype.
Qed.

Definition native_scalar_int32_one :=
  @SExpr_Leaf TNull relname type_int32 (CstInt32 1).

Example scalar_call_wrong_operand_type_is_rejected :
    ~ @scalar_expr_types_valid TNull relname
        TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
        type_int64 type_bool ScalarResultValue
        (@SExpr_Call TNull relname type_int32 (ScalarAdd ScalarInt32)
          [native_scalar_one; native_scalar_one]).
Proof.
  intros [_ Hcall].
  cbn [TNullCallHasType TNullScalarOperatorOutputType
    TNullRequireArgumentTypes TNullTypeListEqb TNullTypeEqb] in Hcall.
  discriminate Hcall.
Qed.

Example scalar_call_wrong_arity_is_rejected :
    ~ @scalar_expr_types_valid TNull relname
        TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
        type_int64 type_bool ScalarResultValue
        (@SExpr_Call TNull relname type_int32 (ScalarAdd ScalarInt32)
          [native_scalar_int32_one]).
Proof.
  intros [_ Hcall].
  cbn [TNullCallHasType TNullScalarOperatorOutputType
    TNullRequireArgumentTypes TNullTypeListEqb TNullTypeEqb] in Hcall.
  discriminate Hcall.
Qed.

Example scalar_predicate_wrong_operand_type_is_rejected :
    ~ @scalar_expr_types_valid TNull relname
        TNullLeafHasType TNullCallHasType TNullPredicateHasTypes
        type_int64 type_bool ScalarResultBoolean
        (@SExpr_Pred TNull relname PredicateIsTrue [native_scalar_one]).
Proof.
  intros [_ Hpredicate].
  cbn [TNullPredicateHasTypes TNullPredicateArgumentTypesValid
    TNullTypeListEqb TNullTypeEqb] in Hpredicate.
  discriminate Hpredicate.
Qed.

Example flat_case_signature_accepts_boolean_value_pairs_and_else :
  TNullCallHasType type_Z ScalarCase
    [type_bool; type_Z; type_bool; type_Z; type_Z].
Proof.
  reflexivity.
Qed.

Example flat_case_leaf_infers_its_common_value_type :
  TNullAggTermType
    (AScalarCall ScalarCase
      [CstBool true; CstZ 1; CstBool false; CstZ 2; CstZ 3]) =
    Some type_Z.
Proof.
  reflexivity.
Qed.

Example flat_case_rejects_mismatched_branch_type :
  TNullScalarOperatorOutputType ScalarCase
    [type_bool; type_Z; type_bool; type_int32; type_Z] = None.
Proof.
  reflexivity.
Qed.

Example aggregate_leaf_rejects_wrong_input_type :
  TNullAggTermType
    (AAggregate AggregateSumInt32 AggregateAll
      (Constant
        (Value_string (StringValue StringText (Some "not an int32"))))) =
    None.
Proof.
  reflexivity.
Qed.
