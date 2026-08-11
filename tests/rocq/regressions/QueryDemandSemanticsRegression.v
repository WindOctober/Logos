From SQLFS Require Import Bool3 Env FiniteBag FiniteCollection FiniteSet Formula
  FTuples GenericInstance SqlBagAbstraction SqlOutcome SqlQuerySemantics
  SqlQuerySyntax SqlSyntax Values.
From Logos.FormalSQL Require Import QueryBindingSemantics QueryTNullSyntax
  TNullSyntax.
From Stdlib Require Import List String.

Import ListNotations.
Import Tuple.
Open Scope string_scope.

(** These negative interface regressions document why a local binding cannot
    be classified as demanded from [query_expr_table_references].  The syntax
    records a reference below FETCH 0, while the dedicated EXISTS evaluator
    reaches FALSE without evaluating that reference. *)
Definition demand_regression_relation : relname :=
  Rel "__logos_demand_regression_cte".

Definition demand_regression_reference : QueryExpr :=
  @QExpr_Table TNull relname nil demand_regression_relation.

Definition demand_regression_fetch_zero : QueryExpr :=
  QExpr_Fetch 0 demand_regression_reference.

Example a_syntactic_reference_below_fetch_zero_is_still_recorded :
  In (demand_regression_relation, nil)
    (query_expr_table_references demand_regression_fetch_zero).
Proof.
now left.
Qed.

Definition demand_regression_schedule
    (_ : boolean_site) : boolean_evaluation_order :=
  BooleanLeftFirst.

Local Abbreviation demand_regression_eval_exists :=
  (@eval_query_exists_outcome TNull relname
    (@_basesort TNull init_db) (@_instance TNull init_db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    demand_regression_schedule nil).

Example exists_fetch_zero_does_not_demand_its_syntactically_referenced_child :
  demand_regression_eval_exists demand_regression_fetch_zero
    (SqlSuccess false3).
Proof.
apply EExists_FetchZero.
reflexivity.
Qed.

(** The ordinary row evaluator has no corresponding demand trace.  In
    particular, its binary-query rules record outcomes, but do not expose
    whether a child was operationally skipped.  This constructor-level
    regression makes the gap explicit: even when the left result is empty,
    the current CrossJoin relation can propagate an error from the right.
    A lazy CTE certificate must therefore not infer non-demand merely from
    the empty final product. *)
Section EmptyCrossJoinDoesNotWitnessNonDemand.

Context {T : Tuple.Rcd} {relation_name : Type}.

Variable basesort : relation_name -> Fset.set (A T).
Variable instance : relation_name -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.
Variable schedule : boolean_site -> boolean_evaluation_order.
Variable env : Env.env T.
Variables left right : query_expr T relation_name.
Variable error : sql_runtime_error.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relation_name basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule env).

Example empty_left_cross_join_still_propagates_a_right_error :
  eval_query left (SqlSuccess nil) ->
  eval_query right (SqlError error) ->
  eval_query (QExpr_CrossJoin left right) (SqlError error).
Proof.
intros Hleft Hright.
now apply EQuery_CrossJoinRightError with (left_rows := nil).
Qed.

End EmptyCrossJoinDoesNotWitnessNonDemand.
