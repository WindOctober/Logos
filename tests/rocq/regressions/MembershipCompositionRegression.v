(** Regression coverage for NULL-aware [NOT IN] case and outcome interfaces. *)

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance OrderedSet Projection SqlBagAbstraction SqlErrorSemantics
  SqlOutcome SqlQueryFacts SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts RelationalAlgebraFacts
  SubqueryFacts TNullSyntax.

Import ListNotations.
Import Tuple.

Section RowCaseRegression.

Context {relname : Type}.
Variable values : list (value TNull).
Variable subquery : query_expr TNull relname.
Variable rows : list (tuple TNull).

Example not_in_four_cases_regression :
  ((@query_canonical_rows TNull rows = nil) /\
    @in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery rows = false3) \/
  ((exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery row = true3) /\
    @in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery rows = true3) \/
  ((Exists
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = unknown3)
      (@query_canonical_rows TNull rows) /\
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row <> true3)
      (@query_canonical_rows TNull rows)) /\
    @in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery rows = unknown3) \/
  ((@query_canonical_rows TNull rows <> nil) /\
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = false3)
      (@query_canonical_rows TNull rows) /\
    @in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery rows = false3).
Proof. apply tnull_in_rows_semantic_cases. Qed.

Example not_in_null_aware_marker_regression :
  Bool.is_true Bool3
    (negb3
      (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery rows)) = true <->
  (~ exists row,
    In row (@query_canonical_rows TNull rows) /\
    @in_row_truth TNull relname unknown3 NullValues.is_null_value
      values subquery row = true3) /\
  (~ exists row,
    In row (@query_canonical_rows TNull rows) /\
    @in_row_truth TNull relname unknown3 NullValues.is_null_value
      values subquery row = unknown3).
Proof. apply tnull_not_in_rows_acceptance_iff_no_true_or_unknown. Qed.

End RowCaseRegression.

Section UnionAllOutcomeRegression.

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

Local Abbreviation eval_query_generic :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_values_generic :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Variable env : Env.env T.
Variable arguments : list (scalar_expr T relname ScalarResultValue).
Variables left right : query_expr T relname.
Variable accept : list (value T) -> tuple T -> bool.
Variables left_accepted right_accepted : bool.

Hypothesis output_sorts_match :
  query_expr_sort left =S= query_expr_sort right.
Hypothesis union_arguments_success :
  exists values,
    eval_scalar_values_generic env arguments (SqlSuccess values).
Hypothesis left_success :
  exists rows, eval_query_generic env left (SqlSuccess rows).
Hypothesis right_success :
  exists rows, eval_query_generic env right (SqlSuccess rows).
Hypothesis union_rows_have_outputs : forall rows,
  eval_query_generic env (QExpr_Set Union left right) (SqlSuccess rows) ->
  Forall
    (query_row_has_outputs
      (query_expr_outputs (QExpr_Set Union left right))) rows.
Hypothesis row_acceptance : forall values,
  eval_scalar_values_generic env arguments (SqlSuccess values) ->
  forall row,
    Bool.is_true (B T)
      (@in_row_truth T relname unknown value_is_null
        values (QExpr_Set Union left right) row) =
    accept values row.
Hypothesis left_decision : forall values rows,
  eval_scalar_values_generic env arguments (SqlSuccess values) ->
  eval_query_generic env left (SqlSuccess rows) ->
  existsb (accept values) rows = left_accepted.
Hypothesis right_decision : forall values rows,
  eval_scalar_values_generic env arguments (SqlSuccess values) ->
  eval_query_generic env right (SqlSuccess rows) ->
  existsb (accept values) rows = right_accepted.
Hypothesis argument_errors_absent : forall error,
  ~ eval_scalar_values_generic env arguments (SqlError error).
Hypothesis left_errors_absent : forall error,
  ~ eval_query_generic env left (SqlError error).
Hypothesis right_errors_absent : forall error,
  ~ eval_query_generic env right (SqlError error).

Variable distinct_values : list (value T).
Variable distinct_subquery : query_expr T relname.
Variables distinct_input distinct_output : list (tuple T).
Hypothesis distinct_input_rows :
  Forall
    (query_row_has_outputs (query_expr_outputs distinct_subquery))
    distinct_input.
Hypothesis distinct_output_rows :
  query_same_rows_as_bag distinct_output
    (query_distinct_bag (query_rows_bag distinct_input)).

Example distinct_support_regression :
  list_support_rel
    (fun first second =>
      OrderedSet.Oeset.compare (OTuple T) first second = Eq)
    distinct_output distinct_input.
Proof. now apply query_distinct_rows_support_rel. Qed.

Example distinct_membership_acceptance_regression :
  Bool.is_true (B T)
    (@in_rows_truth T relname unknown value_is_null
      distinct_values distinct_subquery distinct_output) =
  Bool.is_true (B T)
    (@in_rows_truth T relname unknown value_is_null
      distinct_values distinct_subquery distinct_input).
Proof. eapply in_rows_acceptance_distinct; eassumption. Qed.

Example in_union_all_acceptance_regression :
  scalar_expr_acceptance_exact_at
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null boolean_schedule env
    (SExpr_In arguments (QExpr_Set Union left right))
    (orb left_accepted right_accepted).
Proof.
eapply scalar_expr_in_union_all_acceptance_exact; eassumption.
Qed.

End UnionAllOutcomeRegression.

Section OutcomeRegression.

Context {relname : Type}.
Variable basesort : relname -> Fset.set (A TNull).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple TNull)).
Variable symbol_runtime_error :
  scalar_operator TNull ->
  list (option sql_runtime_error * value TNull) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate TNull ->
  list (option sql_runtime_error * value TNull) ->
  option sql_runtime_error.
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error
    NullValues.is_null_value boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error
    NullValues.is_null_value boolean_schedule).

Variable env : Env.env TNull.
Variable arguments : list (scalar_expr TNull relname ScalarResultValue).
Variable subquery : query_expr TNull relname.

Hypothesis arguments_success :
  exists values,
    eval_scalar_values env arguments (SqlSuccess values).
Hypothesis child_success :
  exists rows, eval_query env subquery (SqlSuccess rows).
Hypothesis argument_errors_absent :
  forall error, ~ eval_scalar_values env arguments (SqlError error).
Hypothesis child_errors_absent :
  forall error, ~ eval_query env subquery (SqlError error).
Hypothesis every_comparison_false :
  forall values rows,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess rows) ->
    Forall
      (fun row =>
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = false3)
      (@query_canonical_rows TNull rows).

Example not_in_exact_acceptance_regression :
  scalar_expr_acceptance_exact_at
    basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value boolean_schedule env
    (SExpr_Not (SExpr_In arguments subquery)) true.
Proof.
eapply tnull_scalar_expr_not_in_accepts_exact_of_all_false; eassumption.
Qed.

End OutcomeRegression.

Print Assumptions tnull_in_rows_unknown_iff.
Print Assumptions tnull_in_rows_semantic_cases.
Print Assumptions tnull_not_in_rows_acceptance_iff_all_false.
Print Assumptions tnull_not_in_rows_acceptance_iff_no_true_or_unknown.
Print Assumptions query_distinct_rows_support_rel.
Print Assumptions in_rows_acceptance_distinct.
Print Assumptions scalar_expr_in_union_all_acceptance_exact.
Print Assumptions tnull_scalar_expr_not_in_accepts_exact_of_all_false.
Print Assumptions tnull_scalar_expr_not_in_rejects_exact_of_true_match.
Print Assumptions tnull_scalar_expr_not_in_rejects_exact_of_unknown_without_match.
Print Assumptions not_in_exact_acceptance_regression.
