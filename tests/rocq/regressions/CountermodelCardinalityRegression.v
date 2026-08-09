(******************************************************************************)
(** Regressions for generic successful-outcome cardinality composition.       **)
(******************************************************************************)

From Stdlib Require Import List NArith.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet Formula Projection
  SqlOutcome SqlErrorSemantics SqlQuerySyntax SqlQuerySemantics.
From Logos.FormalSQL Require Import QueryCardinality OrderedQueryFacts.

Import Tuple.

Section CountermodelCardinalityRegression.

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

Local Abbreviation length_le :=
  (@query_success_length_le T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Theorem error_bound_regression :
  forall env outputs error bound,
    length_le env (QExpr_Error outputs error) bound.
Proof.
intros; apply query_success_length_le_error.
Qed.

Theorem values_bound_regression :
  forall env outputs values bound,
    (Febag.cardinal (Fecol.CBag (CTuple T)) values <=
      N.of_nat bound)%N ->
    length_le env (QExpr_Values outputs values) bound.
Proof.
intros; now apply query_success_length_le_values.
Qed.

Theorem table_bound_regression :
  forall env outputs table bound,
    @query_outputs_sort T outputs =S= basesort table ->
    (Febag.cardinal (Fecol.CBag (CTuple T)) (instance table) <=
      N.of_nat bound)%N ->
    length_le env (QExpr_Table outputs table) bound.
Proof.
intros; now apply query_success_length_le_table.
Qed.

Theorem project_bound_regression :
  forall env select_list input bound,
    length_le env input bound ->
    length_le env (QExpr_Project select_list input) bound.
Proof.
intros; now apply query_success_length_le_project.
Qed.

Theorem row_map_bound_regression :
  forall env outputs row_map input bound,
    length_le env input bound ->
    length_le env (QExpr_RowMap outputs row_map input) bound.
Proof.
intros; now apply query_success_length_le_row_map.
Qed.

Theorem filter_bound_regression :
  forall env formula input bound,
    length_le env input bound ->
    length_le env (QExpr_Filter formula input) bound.
Proof.
intros; now apply query_success_length_le_filter.
Qed.

Theorem distinct_bound_regression :
  forall env input bound,
    length_le env input bound ->
    length_le env (QExpr_Distinct input) bound.
Proof.
intros; now apply query_success_length_le_distinct.
Qed.

Theorem order_by_bound_regression :
  forall env keys input bound,
    length_le env input bound ->
    length_le env (QExpr_OrderBy keys input) bound.
Proof.
intros; now apply query_success_length_le_order_by.
Qed.

Theorem offset_bound_regression :
  forall env offset input bound,
    length_le env input bound ->
    length_le env (QExpr_Offset offset input) (bound - offset).
Proof.
intros; now apply query_success_length_le_offset.
Qed.

Theorem fetch_bound_regression :
  forall env count input bound,
    length_le env input bound ->
    length_le env (QExpr_Fetch count input) (Nat.min count bound).
Proof.
intros; now apply query_success_length_le_fetch.
Qed.

Theorem fetch_intrinsic_bound_regression :
  forall env count input,
    length_le env (QExpr_Fetch count input) count.
Proof.
intros; now apply query_success_length_le_fetch_count.
Qed.

Theorem set_bound_regression :
  forall env operation left right left_bound right_bound output_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    @query_set_cardinality_bound T relname
      operation left right left_bound right_bound output_bound ->
    length_le env (QExpr_Set operation left right) output_bound.
Proof.
intros env operation left right left_bound right_bound output_bound
  Hleft Hright Hoperation.
eapply query_success_length_le_set.
- exact Hleft.
- exact Hright.
- exact Hoperation.
Qed.

Theorem set_union_bound_regression :
  forall env left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env (QExpr_Set Union left right)
      (left_bound + right_bound).
Proof.
intros env left right left_bound right_bound Hleft Hright.
eapply query_success_length_le_set; [exact Hleft|exact Hright|].
apply query_set_cardinality_bound_union.
Qed.

Theorem set_union_max_bound_regression :
  forall env left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env (QExpr_Set UnionMax left right)
      (left_bound + right_bound).
Proof.
intros env left right left_bound right_bound Hleft Hright.
eapply query_success_length_le_set; [exact Hleft|exact Hright|].
apply query_set_cardinality_bound_union_max.
Qed.

Theorem set_inter_bound_regression :
  forall env left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env (QExpr_Set Inter left right)
      (Nat.min left_bound right_bound).
Proof.
intros env left right left_bound right_bound Hleft Hright.
eapply query_success_length_le_set; [exact Hleft|exact Hright|].
apply query_set_cardinality_bound_inter.
Qed.

Theorem set_diff_bound_regression :
  forall env left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env (QExpr_Set Diff left right) left_bound.
Proof.
intros env left right left_bound right_bound Hleft Hright.
eapply query_success_length_le_set; [exact Hleft|exact Hright|].
apply query_set_cardinality_bound_diff.
Qed.

Theorem cross_join_bound_regression :
  forall env left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env (QExpr_CrossJoin left right)
      (left_bound * right_bound).
Proof.
intros; now apply query_success_length_le_cross_join.
Qed.

Theorem natural_join_bound_regression :
  forall env left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env (QExpr_NaturalJoin left right)
      (left_bound * right_bound).
Proof.
intros; now apply query_success_length_le_natural_join.
Qed.

Theorem native_join_bound_regression :
  forall env kind predicate matched_select left_select right_select
      left right left_bound right_bound,
    length_le env left left_bound ->
    length_le env right right_bound ->
    length_le env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right)
      (query_join_length_upper_bound kind left_bound right_bound).
Proof.
intros; now apply query_success_length_le_join.
Qed.

Theorem rank_bound_regression :
  forall env partition_keys order_keys rank_attribute rank_value input bound,
    length_le env input bound ->
    length_le env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      bound.
Proof.
intros; now apply query_success_length_le_rank.
Qed.

Theorem window_bound_regression :
  forall env partition_keys order_keys items input bound,
    length_le env input bound ->
    length_le env
      (QExpr_Window partition_keys order_keys items input) bound.
Proof.
intros; now apply query_success_length_le_window.
Qed.

End CountermodelCardinalityRegression.
