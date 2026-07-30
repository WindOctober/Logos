(******************************************************************************)
(** Generic exact-truth and acceptance interfaces for predicate subqueries.  **)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Lia List String ZArith.
From SQLFS Require Import Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples
  GenericInstance OrderedSet Projection SqlBagAbstraction SqlErrorSemantics SqlOutcome
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

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Example sql_not_requires_exact_truth_regression :
  forall env formula expected,
    @formula_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula expected ->
    @formula_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (FExpr_Not formula) (Bool.negb (B T) expected).
Proof.
intros env formula expected Hexact.
now apply formula_not_truth_exact.
Qed.

Example exact_truth_to_acceptance_regression :
  forall env formula expected,
    @formula_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula expected ->
    @formula_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula (Bool.is_true (B T) expected).
Proof.
intros env formula expected Hexact.
now apply formula_truth_exact_acceptance_exact.
Qed.

Example sql_not_acceptance_from_exact_truth_regression :
  forall env formula expected,
    @formula_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula expected ->
    @formula_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (FExpr_Not formula)
      (Bool.is_true (B T) (Bool.negb (B T) expected)).
Proof.
intros env formula expected Hexact.
now apply formula_not_acceptance_exact.
Qed.

Example tuple_membership_exact_truth_regression :
  forall env select_items subquery fixed_truth,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth unknown value_is_null env select_items rows = fixed_truth) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    @formula_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (FExpr_In select_items subquery) fixed_truth.
Proof.
intros env select_items subquery fixed_truth
  Harguments Hsuccess Htruth Herrors.
now eapply formula_in_truth_exact.
Qed.

Example tuple_membership_acceptance_regression :
  forall env select_items subquery (accept : tuple T -> bool) accepted,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall row,
      Bool.is_true (B T)
        (in_row_truth unknown value_is_null env select_items row) =
      accept row) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      existsb accept rows = accepted) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    @formula_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (FExpr_In select_items subquery) accepted.
Proof.
intros env select_items subquery accept accepted
  Harguments Hsuccess Hrows Hdecision Herrors.
now eapply formula_in_acceptance_exact.
Qed.

Example not_in_fixed_truth_regression :
  forall env select_items subquery fixed_truth,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth unknown value_is_null env select_items rows = fixed_truth) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    @formula_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (FExpr_Not (FExpr_In select_items subquery))
      (Bool.is_true (B T) (Bool.negb (B T) fixed_truth)).
Proof.
intros env select_items subquery fixed_truth
  Harguments Hsuccess Htruth Herrors.
now eapply formula_not_in_acceptance_exact_of_fixed_truth.
Qed.

Example not_exists_emptiness_regression :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    @formula_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (FExpr_Not (FExpr_Exists subquery)) empty.
Proof.
intros env subquery empty Hsuccess Hempty Herrors.
now eapply formula_not_exists_acceptance_exact.
Qed.

Example exists_exact_truth_regression :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    @formula_truth_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (FExpr_Exists subquery) (exists_truth_from_empty empty).
Proof.
intros env subquery empty Hsuccess Hempty Herrors.
now eapply formula_exists_truth_exact.
Qed.

Example not_exists_boolean_bridge_regression :
  forall empty,
    Bool.is_true (B T)
      (Bool.negb (B T) (exists_truth_from_empty (T := T) empty)) = empty.
Proof.
intros empty.
now apply exists_truth_from_empty_negation_acceptance.
Qed.

Example membership_support_acceptance_regression :
  forall env select_items left right,
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    Bool.is_true (B T)
      (in_rows_truth unknown value_is_null env select_items left) =
    Bool.is_true (B T)
      (in_rows_truth unknown value_is_null env select_items right).
Proof.
intros env select_items left right Hsupport.
now apply in_rows_acceptance_support_rel.
Qed.

Example membership_append_acceptance_regression :
  forall env select_items left right,
    Bool.is_true (B T)
      (in_rows_truth unknown value_is_null env select_items (left ++ right)) =
    Datatypes.orb
      (Bool.is_true (B T)
        (in_rows_truth unknown value_is_null env select_items left))
      (Bool.is_true (B T)
        (in_rows_truth unknown value_is_null env select_items right)).
Proof.
intros env select_items left right.
apply in_rows_acceptance_append.
Qed.

End GenericSubqueryTruthAcceptance.

(******************************************************************************)
(** Closed TNull executions of the semantic paths above.                      **)
(******************************************************************************)

Section ConcreteTNullSubquerySemantics.

Definition truth_regression_x : attribute TNull := AttrZ "x".
Definition truth_regression_y : attribute TNull := AttrZ "y".

Definition truth_regression_row_one : tuple TNull :=
  mk_tuple_lists [truth_regression_x] [Value_Z (Some 1)].

Definition truth_regression_row_pair : tuple TNull :=
  mk_tuple_lists
    [truth_regression_x; truth_regression_y]
    [Value_Z (Some 1); Value_Z (Some 2)].

Definition truth_regression_select_one : list SelectItemT :=
  [SelectAs (CstZ 1) truth_regression_x].

Definition truth_regression_select_null : list SelectItemT :=
  [SelectAs (AExpr (Constant (Value_Z None))) truth_regression_x].

Definition truth_regression_select_pair : list SelectItemT :=
  [SelectAs (CstZ 1) truth_regression_x;
   SelectAs (CstZ 2) truth_regression_y].

Definition truth_regression_int32_one : int32.
Proof.
refine (Int32 1 _); unfold int32_min, int32_max; lia.
Defined.

Definition truth_regression_int32_zero : int32.
Proof.
refine (Int32 0 _); unfold int32_min, int32_max; lia.
Defined.

Definition truth_regression_error_select : list SelectItemT :=
  [SelectAs
    (AExpr
      (ScalarCall (ScalarDivide ScalarInt32)
        [Constant (Value_int32 (Some truth_regression_int32_one));
         Constant (Value_int32 (Some truth_regression_int32_zero))]))
    (AttrInt32 "quotient")].

Local Abbreviation truth_regression_eval_query :=
  (@eval_query_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value).

Local Abbreviation truth_regression_eval_formula :=
  (@eval_formula_expr_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value).

Lemma truth_regression_values_observation :
  forall outputs rows,
    truth_regression_eval_query nil
      (QExpr_Values outputs (rows_bag TNull rows)) (SqlSuccess rows).
Proof.
intros outputs rows.
apply EQuery_Values.
unfold query_same_rows_as_bag, rows_bag.
apply Febag.equal_refl.
Qed.

(** SQL NOT does not turn UNKNOWN into TRUE.  This computes through the
    concrete TNull tuple projection/equality semantics before applying NOT. *)
Example not_unknown_remains_nonaccepting_semantics :
  @in_row_truth TNull unknown3 NullValues.is_null_value nil
      truth_regression_select_null truth_regression_row_one = unknown3 /\
  Bool.is_true Bool3
    (Bool.negb Bool3
      (@in_row_truth TNull unknown3 NullValues.is_null_value nil
        truth_regression_select_null truth_regression_row_one)) = false.
Proof.
vm_compute; split; reflexivity.
Qed.

(** Empty IN is FALSE, not UNKNOWN. *)
Example in_empty_input_is_false_semantics :
  @in_rows_truth TNull unknown3 NullValues.is_null_value nil
    truth_regression_select_one [] = false3.
Proof.
vm_compute; reflexivity.
Qed.

(** Duplicate candidates remain duplicate occurrences, but one or more TRUE
    candidates give the same existential membership truth. *)
Example in_duplicate_membership_is_true_semantics :
  @in_rows_truth TNull unknown3 NullValues.is_null_value nil
    truth_regression_select_one
    [truth_regression_row_one; truth_regression_row_one] = true3.
Proof.
vm_compute; reflexivity.
Qed.

(** Tuple-valued IN compares both projected columns using SQL tuple equality;
    this is a real two-column TNull row, not a Rocq pair equality shortcut. *)
Example in_two_column_tuple_equality_and_acceptance_semantics :
  @in_row_truth TNull unknown3 NullValues.is_null_value nil
      truth_regression_select_pair truth_regression_row_pair = true3 /\
  Bool.is_true Bool3
    (@in_row_truth TNull unknown3 NullValues.is_null_value nil
      truth_regression_select_pair truth_regression_row_pair) = true.
Proof.
vm_compute; split; reflexivity.
Qed.

(** IN evaluates its tuple arguments before its child.  Division by zero is
    therefore observable even though the child below carries a different
    closed analysis error. *)
Example in_argument_error_is_reached_before_child_semantics :
  first_runtime_error
      (@eval_select_runtime_error TNull
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error nil)
      truth_regression_error_select =
    Some (DataException DivisionByZero) /\
  truth_regression_eval_formula nil
    (FExpr_In truth_regression_error_select
      (@QExpr_Error TNull relname
        [AttrInt32 "quotient"] UndefinedFunction))
    (SqlError (DataException DivisionByZero)).
Proof.
split.
- cbn [truth_regression_error_select SelectAs AExpr ScalarCall Constant
    eval_select_runtime_error eval_aggterm_runtime_error
    eval_funterm_runtime_error Interp.interp_funterm first_runtime_error
    first_error NullValues.interp_scalar_operator_runtime_error
    NullValues.first_observation_error NullValues.observation_values
    NullValues.scalar_operator_local_runtime_error
    NullValues.int32_div_runtime_error NullValues.division_by_zero
    truth_regression_int32_zero].
  reflexivity.
- apply EFormula_InArgumentsError.
  cbn [truth_regression_error_select SelectAs AExpr ScalarCall Constant
    eval_select_runtime_error eval_aggterm_runtime_error
    eval_funterm_runtime_error Interp.interp_funterm first_runtime_error
    first_error NullValues.interp_scalar_operator_runtime_error
    NullValues.first_observation_error NullValues.observation_values
    NullValues.scalar_operator_local_runtime_error
    NullValues.int32_div_runtime_error NullValues.division_by_zero
    truth_regression_int32_zero].
  reflexivity.
Qed.

(** With safe arguments, an exact child error propagates through IN. *)
Example in_child_error_propagates_semantics :
  truth_regression_eval_formula nil
    (FExpr_In truth_regression_select_one
      (@QExpr_Error TNull relname
        [truth_regression_x] UndefinedFunction))
    (SqlError UndefinedFunction).
Proof.
apply EFormula_InSubqueryError.
- reflexivity.
- constructor.
Qed.

(** NOT EXISTS accepts an empty successful child. *)
Example not_exists_empty_child_accepts_semantics :
  truth_regression_eval_formula nil
    (FExpr_Not
      (FExpr_Exists
        (QExpr_Values [truth_regression_x] (rows_bag TNull []))))
    (SqlSuccess true3).
Proof.
replace true3 with (Bool.negb (B TNull) (Bool.false (B TNull)))
  by now rewrite Bool.negb_false.
apply EFormula_NotSuccess.
apply EFormula_ExistsSuccessEmpty.
replace (SqlSuccess false3) with
  (@query_exists_rows_outcome TNull (SqlSuccess [])) by reflexivity.
eapply (@EExists_Demanded TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value nil
  (QExpr_Values [truth_regression_x] (rows_bag TNull []))
  (SqlSuccess [])).
- reflexivity.
- apply truth_regression_values_observation.
Qed.

(** NOT EXISTS rejects a nonempty successful child. *)
Example not_exists_nonempty_child_rejects_semantics :
  truth_regression_eval_formula nil
    (FExpr_Not
      (FExpr_Exists
        (QExpr_Values [truth_regression_x]
          (rows_bag TNull [truth_regression_row_one]))))
    (SqlSuccess false3).
Proof.
replace false3 with (Bool.negb (B TNull) (Bool.true (B TNull)))
  by now rewrite Bool.negb_true.
apply EFormula_NotSuccess.
apply EFormula_ExistsSuccessNonempty.
replace (SqlSuccess true3) with
  (@query_exists_rows_outcome TNull
    (SqlSuccess [truth_regression_row_one])) by reflexivity.
eapply (@EExists_Demanded TNull relname
  (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
  NullValues.interp_scalar_operator_runtime_error
  NullValues.interp_aggregate_runtime_error NullValues.is_null_value nil
  (QExpr_Values [truth_regression_x]
    (rows_bag TNull [truth_regression_row_one]))
  (SqlSuccess [truth_regression_row_one])).
- reflexivity.
- apply truth_regression_values_observation.
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
Print Assumptions not_exists_empty_child_accepts_semantics.
Print Assumptions not_exists_nonempty_child_rejects_semantics.
