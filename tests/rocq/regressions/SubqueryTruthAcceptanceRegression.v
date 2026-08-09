(******************************************************************************)
(** Typed exact-truth and acceptance interfaces for SQL subqueries.          **)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Lia List String ZArith.
From SQLFS Require Import Bool3 Env FiniteBag FiniteCollection FiniteSet Formula
  FTuples GenericInstance OrderedSet SqlBagAbstraction SqlErrorSemantics SqlOutcome
  SqlQuerySemantics SqlQuerySyntax SqlSyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts RelationalAlgebraFacts SubqueryFacts TNullSyntax.

Import ListNotations.
Import Tuple.

Open Scope string_scope.
Open Scope Z_scope.

Section GenericSubqueryTruthAcceptance.

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
Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Example sql_not_requires_exact_truth_regression :
  forall env expression expected,
    @scalar_expr_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env expression expected ->
    @scalar_expr_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_Not expression) (Bool.negb (B T) expected).
Proof.
  intros; now apply scalar_expr_not_truth_exact.
Qed.

Example exact_truth_to_acceptance_regression :
  forall env expression expected,
    @scalar_expr_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env expression expected ->
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env expression (Bool.is_true (B T) expected).
Proof.
  intros; now apply scalar_expr_truth_exact_acceptance_exact.
Qed.

Example sql_not_acceptance_from_exact_truth_regression :
  forall env expression expected,
    @scalar_expr_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env expression expected ->
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_Not expression)
      (Bool.is_true (B T) (Bool.negb (B T) expected)).
Proof.
  intros; now apply scalar_expr_not_acceptance_exact.
Qed.

Example tuple_membership_exact_truth_regression :
  forall env arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth unknown value_is_null values subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    @scalar_expr_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_In arguments subquery) fixed_truth.
Proof.
  intros; now eapply scalar_expr_in_truth_exact.
Qed.

Example tuple_membership_acceptance_regression :
  forall env arguments subquery
      (accept : list (value T) -> tuple T -> bool) accepted,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs (query_expr_outputs subquery)) rows) ->
    (forall values,
      eval_scalar_values env arguments (SqlSuccess values) ->
      forall row,
        Bool.is_true (B T) (in_row_truth unknown value_is_null
          values subquery row) = accept values row) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      existsb (accept values) rows = accepted) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_In arguments subquery) accepted.
Proof.
intros env arguments subquery accept accepted
  Hvalues Hrows Houtputs Haccept Hfixed Hargument_errors Hquery_errors.
exact (@scalar_expr_in_acceptance_exact T relname basesort instance unknown
  symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
  env arguments subquery accept accepted Hvalues Hrows Houtputs Haccept Hfixed
  Hargument_errors Hquery_errors).
Qed.

Example not_in_fixed_truth_regression :
  forall env arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth unknown value_is_null values subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_Not (SExpr_In arguments subquery))
      (Bool.is_true (B T) (Bool.negb (B T) fixed_truth)).
Proof.
  intros; now eapply scalar_expr_not_in_acceptance_exact_of_fixed_truth.
Qed.

Example not_exists_emptiness_regression :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_Not (SExpr_Exists subquery)) empty.
Proof.
  intros; now eapply scalar_expr_not_exists_acceptance_exact.
Qed.

Example exists_exact_truth_regression :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    @scalar_expr_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env (SExpr_Exists subquery)
      (exists_truth_from_empty empty).
Proof.
  intros; now eapply scalar_expr_exists_truth_exact.
Qed.

Example not_exists_boolean_bridge_regression :
  forall empty,
    Bool.is_true (B T)
      (Bool.negb (B T) (exists_truth_from_empty (T := T) empty)) = empty.
Proof.
  intros; now apply exists_truth_from_empty_negation_acceptance.
Qed.

Example membership_support_acceptance_regression :
  forall values subquery left right,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) left ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) right ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null values subquery left) =
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null values subquery right).
Proof.
  intros; now apply in_rows_acceptance_support_rel.
Qed.

Example membership_append_acceptance_regression :
  forall values subquery left right,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) left ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) right ->
    Bool.is_true (B T)
      (@in_rows_truth T relname unknown value_is_null values subquery
        (left ++ right)) =
    Datatypes.orb
      (Bool.is_true (B T)
        (@in_rows_truth T relname unknown value_is_null values subquery left))
      (Bool.is_true (B T)
        (@in_rows_truth T relname unknown value_is_null values subquery right)).
Proof.
  intros; now apply in_rows_acceptance_append.
Qed.

End GenericSubqueryTruthAcceptance.

(******************************************************************************)
(** Closed TNull executions of the typed semantic paths above.               **)
(******************************************************************************)

Section ConcreteTNullSubquerySemantics.

Definition truth_regression_x : attribute TNull := AttrZ "x".
Definition truth_regression_y : attribute TNull := AttrZ "y".

Definition truth_regression_row_one : tuple TNull :=
  mk_tuple_lists [truth_regression_x] [Value_Z (Some 1)].

Definition truth_regression_row_two : tuple TNull :=
  mk_tuple_lists [truth_regression_x] [Value_Z (Some 2)].

Definition truth_regression_row_pair : tuple TNull :=
  mk_tuple_lists
    [truth_regression_x; truth_regression_y]
    [Value_Z (Some 1); Value_Z (Some 2)].

Definition truth_regression_boolean_schedule
    (_ : boolean_site) : boolean_evaluation_order := BooleanLeftFirst.

Local Abbreviation truth_regression_eval_query :=
  (@eval_query_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    truth_regression_boolean_schedule).

Local Abbreviation truth_regression_eval_scalar_value :=
  (@eval_scalar_value_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    truth_regression_boolean_schedule).

Local Abbreviation truth_regression_eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    truth_regression_boolean_schedule).

Local Abbreviation truth_regression_eval_scalar_values :=
  (@eval_scalar_values_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    truth_regression_boolean_schedule).

Definition truth_regression_empty_query : @query_expr TNull relname :=
  QExpr_Values [truth_regression_x] (rows_bag TNull []).

Definition truth_regression_one_query : @query_expr TNull relname :=
  QExpr_Values [truth_regression_x]
    (rows_bag TNull [truth_regression_row_one]).

Definition truth_regression_pair_query : @query_expr TNull relname :=
  QExpr_Values [truth_regression_x; truth_regression_y]
    (rows_bag TNull [truth_regression_row_pair]).

Definition truth_regression_scalar_one :=
  @SExpr_Leaf TNull relname type_Z (CstZ 1).

Lemma truth_regression_values_observation :
  forall env outputs rows,
    truth_regression_eval_query env
      (QExpr_Values outputs (rows_bag TNull rows)) (SqlSuccess rows).
Proof.
  intros; apply EQuery_Values.
  unfold query_same_rows_as_bag, rows_bag; apply Febag.equal_refl.
Qed.

Lemma truth_regression_scalar_one_values :
  forall env,
    truth_regression_eval_scalar_values env [truth_regression_scalar_one]
      (SqlSuccess [Value_Z (Some 1)]).
Proof.
intro env.
replace (SqlSuccess [Value_Z (Some 1)]) with
  (@scalar_value_cons_outcome TNull (Value_Z (Some 1)) (SqlSuccess []))
  by reflexivity.
eapply EScalarValues_Cons; [apply EScalar_Leaf|constructor].
Qed.

(** SQL NOT does not turn UNKNOWN into TRUE. *)
Example not_unknown_remains_nonaccepting_semantics :
  @in_row_truth TNull relname unknown3 NullValues.is_null_value
      [Value_Z None] truth_regression_one_query truth_regression_row_one =
      unknown3 /\
  Bool.is_true Bool3
    (Bool.negb Bool3
      (@in_row_truth TNull relname unknown3 NullValues.is_null_value
        [Value_Z None] truth_regression_one_query
        truth_regression_row_one)) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example in_empty_input_is_false_semantics :
  @in_rows_truth TNull relname unknown3 NullValues.is_null_value
    [Value_Z (Some 1)] truth_regression_empty_query [] = false3.
Proof.
  vm_compute; reflexivity.
Qed.

Example in_duplicate_membership_is_true_semantics :
  @in_rows_truth TNull relname unknown3 NullValues.is_null_value
    [Value_Z (Some 1)] truth_regression_one_query
    [truth_regression_row_one; truth_regression_row_one] = true3.
Proof.
  vm_compute; reflexivity.
Qed.

Example in_two_column_tuple_equality_and_acceptance_semantics :
  @in_row_truth TNull relname unknown3 NullValues.is_null_value
      [Value_Z (Some 1); Value_Z (Some 2)]
      truth_regression_pair_query truth_regression_row_pair = true3 /\
  Bool.is_true Bool3
    (@in_row_truth TNull relname unknown3 NullValues.is_null_value
      [Value_Z (Some 1); Value_Z (Some 2)]
      truth_regression_pair_query truth_regression_row_pair) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition truth_regression_int32_one : int32.
Proof.
  refine (Int32 1 _); unfold int32_min, int32_max; lia.
Defined.

Definition truth_regression_int32_zero : int32.
Proof.
  refine (Int32 0 _); unfold int32_min, int32_max; lia.
Defined.

Definition truth_regression_int32_one_term : AggTerm :=
  AExpr (Constant (Value_int32 (Some truth_regression_int32_one))).

Definition truth_regression_int32_zero_term : AggTerm :=
  AExpr (Constant (Value_int32 (Some truth_regression_int32_zero))).

Definition truth_regression_division :=
  @SExpr_Call TNull relname type_int32 (ScalarDivide ScalarInt32)
    [@SExpr_Leaf TNull relname type_int32 truth_regression_int32_one_term;
     @SExpr_Leaf TNull relname type_int32 truth_regression_int32_zero_term].

Lemma truth_regression_division_errors :
  forall env,
    truth_regression_eval_scalar_value env truth_regression_division
      (SqlError (DataException DivisionByZero)).
Proof.
intro env.
replace (SqlError (DataException DivisionByZero)) with
  (@scalar_call_value_outcome TNull
    NullValues.interp_scalar_operator_runtime_error
    (ScalarDivide ScalarInt32)
    [Value_int32 (Some truth_regression_int32_one);
     Value_int32 (Some truth_regression_int32_zero)]).
2: {
  cbn [scalar_call_value_outcome
    NullValues.interp_scalar_operator_runtime_error
    NullValues.first_observation_error NullValues.observation_values
    NullValues.scalar_operator_local_runtime_error
    NullValues.int32_div_runtime_error NullValues.division_by_zero
    truth_regression_int32_zero].
  reflexivity.
}
apply EScalar_CallSuccess.
replace
  (SqlSuccess
    [Value_int32 (Some truth_regression_int32_one);
     Value_int32 (Some truth_regression_int32_zero)]) with
  (@scalar_value_cons_outcome TNull
    (Value_int32 (Some truth_regression_int32_one))
    (@scalar_value_cons_outcome TNull
      (Value_int32 (Some truth_regression_int32_zero)) (SqlSuccess [])))
  by reflexivity.
eapply (@EScalarValues_Cons TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule env
  (@SExpr_Leaf TNull relname type_int32 truth_regression_int32_one_term)
  [@SExpr_Leaf TNull relname type_int32 truth_regression_int32_zero_term]
  (Value_int32 (Some truth_regression_int32_one))
  (@scalar_value_cons_outcome TNull
    (Value_int32 (Some truth_regression_int32_zero)) (SqlSuccess []))).
- apply EScalar_Leaf.
- eapply (@EScalarValues_Cons TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    truth_regression_boolean_schedule env
    (@SExpr_Leaf TNull relname type_int32 truth_regression_int32_zero_term)
    [] (Value_int32 (Some truth_regression_int32_zero)) (SqlSuccess [])).
  + apply EScalar_Leaf.
  + constructor.
Qed.

Example in_argument_error_is_reached_before_child_semantics :
  truth_regression_eval_scalar_boolean nil
    (SExpr_In [truth_regression_division]
      (@QExpr_Error TNull relname [AttrInt32 "quotient"] UndefinedFunction))
    (SqlError (DataException DivisionByZero)).
Proof.
apply EScalar_InArgumentsError.
apply EScalarValues_HeadError.
apply truth_regression_division_errors.
Qed.

Example in_child_error_propagates_semantics :
  truth_regression_eval_scalar_boolean nil
    (SExpr_In [truth_regression_scalar_one]
      (@QExpr_Error TNull relname [truth_regression_x] UndefinedFunction))
    (SqlError UndefinedFunction).
Proof.
eapply EScalar_InSubqueryError with (values := [Value_Z (Some 1)]).
- apply truth_regression_scalar_one_values.
- constructor.
Qed.

Example quantified_argument_error_is_preserved_semantics :
  truth_regression_eval_scalar_boolean nil
    (@SExpr_Quant TNull relname Forall_F PredicateEq [truth_regression_division]
      truth_regression_empty_query)
    (SqlError (DataException DivisionByZero)).
Proof.
apply EScalar_QuantArgumentsError.
apply EScalarValues_HeadError.
apply truth_regression_division_errors.
Qed.

Example quantified_child_error_is_preserved_semantics :
  truth_regression_eval_scalar_boolean nil
    (@SExpr_Quant TNull relname Exists_F PredicateEq [truth_regression_scalar_one]
      (@QExpr_Error TNull relname [truth_regression_x] UndefinedFunction))
    (SqlError UndefinedFunction).
Proof.
eapply EScalar_QuantSubqueryError with (values := [Value_Z (Some 1)]).
- apply truth_regression_scalar_one_values.
- constructor.
Qed.

Example quantified_forall_empty_is_true_semantics :
  truth_regression_eval_scalar_boolean nil
    (@SExpr_Quant TNull relname Forall_F PredicateEq [truth_regression_scalar_one]
      truth_regression_empty_query)
    (SqlSuccess true3).
Proof.
eapply (@eval_scalar_boolean_quant_forall_empty TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil PredicateEq
  [truth_regression_scalar_one] truth_regression_empty_query
  [Value_Z (Some 1)]).
- apply truth_regression_scalar_one_values.
- unfold truth_regression_empty_query; apply truth_regression_values_observation.
Qed.

Example quantified_exists_empty_is_false_semantics :
  truth_regression_eval_scalar_boolean nil
    (@SExpr_Quant TNull relname Exists_F PredicateEq [truth_regression_scalar_one]
      truth_regression_empty_query)
    (SqlSuccess false3).
Proof.
eapply (@eval_scalar_boolean_quant_exists_empty TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil PredicateEq
  [truth_regression_scalar_one] truth_regression_empty_query
  [Value_Z (Some 1)]).
- apply truth_regression_scalar_one_values.
- unfold truth_regression_empty_query; apply truth_regression_values_observation.
Qed.

Example scalar_subquery_zero_rows_is_typed_null_semantics :
  truth_regression_eval_scalar_value nil
    (@SExpr_Subquery TNull relname type_Z (Value_Z None)
      truth_regression_empty_query)
    (SqlSuccess (Value_Z None)).
Proof.
apply (@eval_scalar_value_subquery_empty TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil type_Z (Value_Z None)
  truth_regression_empty_query).
- reflexivity.
- unfold truth_regression_empty_query; apply truth_regression_values_observation.
Qed.

Example scalar_subquery_one_row_is_value_semantics :
  truth_regression_eval_scalar_value nil
    (@SExpr_Subquery TNull relname type_Z (Value_Z None)
      truth_regression_one_query)
    (SqlSuccess (dot TNull truth_regression_row_one truth_regression_x)).
Proof.
eapply (@eval_scalar_value_subquery_singleton TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil type_Z (Value_Z None)
  truth_regression_one_query truth_regression_x truth_regression_row_one).
- reflexivity.
- reflexivity.
- unfold truth_regression_one_query; apply truth_regression_values_observation.
Qed.

Example scalar_subquery_many_rows_is_cardinality_violation_semantics :
  truth_regression_eval_scalar_value nil
    (@SExpr_Subquery TNull relname type_Z (Value_Z None)
      (QExpr_Values [truth_regression_x]
        (rows_bag TNull [truth_regression_row_one; truth_regression_row_two])))
    (SqlError CardinalityViolation).
Proof.
eapply (@eval_scalar_value_subquery_cardinality_violation TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil type_Z (Value_Z None)
  (QExpr_Values [truth_regression_x]
    (rows_bag TNull [truth_regression_row_one; truth_regression_row_two]))
  truth_regression_row_one truth_regression_row_two []).
- reflexivity.
- apply truth_regression_values_observation.
Qed.

(** NOT EXISTS accepts an empty successful child. *)
Example not_exists_empty_child_accepts_semantics :
  truth_regression_eval_scalar_boolean nil
    (SExpr_Not (SExpr_Exists truth_regression_empty_query))
    (SqlSuccess true3).
Proof.
replace true3 with (Bool.negb (B TNull) (Bool.false (B TNull)))
  by now rewrite Bool.negb_false.
apply EScalar_NotSuccess.
apply EScalar_ExistsSuccess.
replace (SqlSuccess false3) with
  (@query_exists_rows_outcome TNull (SqlSuccess [])) by reflexivity.
eapply (@EExists_Demanded TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil truth_regression_empty_query
  (SqlSuccess [])).
- reflexivity.
- unfold truth_regression_empty_query; apply truth_regression_values_observation.
Qed.

(** NOT EXISTS rejects a nonempty successful child. *)
Example not_exists_nonempty_child_rejects_semantics :
  truth_regression_eval_scalar_boolean nil
    (SExpr_Not (SExpr_Exists truth_regression_one_query))
    (SqlSuccess false3).
Proof.
replace false3 with (Bool.negb (B TNull) (Bool.true (B TNull)))
  by now rewrite Bool.negb_true.
apply EScalar_NotSuccess.
apply EScalar_ExistsSuccess.
replace (SqlSuccess true3) with
  (@query_exists_rows_outcome TNull
    (SqlSuccess [truth_regression_row_one])) by reflexivity.
eapply (@EExists_Demanded TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value
  truth_regression_boolean_schedule nil truth_regression_one_query
  (SqlSuccess [truth_regression_row_one])).
- reflexivity.
- unfold truth_regression_one_query; apply truth_regression_values_observation.
Qed.

End ConcreteTNullSubquerySemantics.

Print Assumptions sql_not_requires_exact_truth_regression.
Print Assumptions exact_truth_to_acceptance_regression.
Print Assumptions sql_not_acceptance_from_exact_truth_regression.
Print Assumptions tuple_membership_exact_truth_regression.
Print Assumptions tuple_membership_acceptance_regression.
Print Assumptions not_in_fixed_truth_regression.
Print Assumptions not_exists_emptiness_regression.
Print Assumptions exists_exact_truth_regression.
Print Assumptions not_exists_boolean_bridge_regression.
Print Assumptions membership_support_acceptance_regression.
Print Assumptions membership_append_acceptance_regression.
Print Assumptions not_unknown_remains_nonaccepting_semantics.
Print Assumptions in_empty_input_is_false_semantics.
Print Assumptions in_duplicate_membership_is_true_semantics.
Print Assumptions in_two_column_tuple_equality_and_acceptance_semantics.
Print Assumptions in_argument_error_is_reached_before_child_semantics.
Print Assumptions in_child_error_propagates_semantics.
Print Assumptions quantified_argument_error_is_preserved_semantics.
Print Assumptions quantified_child_error_is_preserved_semantics.
Print Assumptions quantified_forall_empty_is_true_semantics.
Print Assumptions quantified_exists_empty_is_false_semantics.
Print Assumptions scalar_subquery_zero_rows_is_typed_null_semantics.
Print Assumptions scalar_subquery_one_row_is_value_semantics.
Print Assumptions scalar_subquery_many_rows_is_cardinality_violation_semantics.
Print Assumptions not_exists_empty_child_accepts_semantics.
Print Assumptions not_exists_nonempty_child_rejects_semantics.
