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

Variables env : Env.env TNull.
Variable select_items : list (@select TNull).
Variable rows : list (tuple TNull).

Example not_in_four_cases_regression :
  ((@query_canonical_rows TNull rows = nil) /\
    @in_rows_truth TNull unknown3 NullValues.is_null_value
      env select_items rows = false3) \/
  ((exists row,
      In row (@query_canonical_rows TNull rows) /\
      @in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items row = true3) /\
    @in_rows_truth TNull unknown3 NullValues.is_null_value
      env select_items rows = true3) \/
  ((Exists
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = unknown3)
      (@query_canonical_rows TNull rows) /\
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row <> true3)
      (@query_canonical_rows TNull rows)) /\
    @in_rows_truth TNull unknown3 NullValues.is_null_value
      env select_items rows = unknown3) \/
  ((@query_canonical_rows TNull rows <> nil) /\
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = false3)
      (@query_canonical_rows TNull rows) /\
    @in_rows_truth TNull unknown3 NullValues.is_null_value
      env select_items rows = false3).
Proof. apply tnull_in_rows_semantic_cases. Qed.

Example not_in_null_aware_marker_regression :
  Bool.is_true Bool3
    (negb3
      (@in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items rows)) = true <->
  (~ exists row,
    In row (@query_canonical_rows TNull rows) /\
    @in_row_truth TNull unknown3 NullValues.is_null_value
      env select_items row = true3) /\
  (~ exists row,
    In row (@query_canonical_rows TNull rows) /\
    @in_row_truth TNull unknown3 NullValues.is_null_value
      env select_items row = unknown3).
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

Local Abbreviation eval_query_generic :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Variable env : Env.env T.
Variable select_items : list (@select T).
Variables left right : query_expr T relname.
Variable accept : tuple T -> bool.
Variables left_accepted right_accepted : bool.

Hypothesis output_sorts_match :
  query_expr_sort left =S= query_expr_sort right.
Hypothesis union_arguments_safe :
  first_runtime_error
    (@eval_select_runtime_error T
      symbol_runtime_error aggregate_runtime_error env)
    select_items = None.
Hypothesis left_success :
  exists rows, eval_query_generic env left (SqlSuccess rows).
Hypothesis right_success :
  exists rows, eval_query_generic env right (SqlSuccess rows).
Hypothesis row_acceptance : forall row,
  Bool.is_true (B T)
    (@in_row_truth T unknown value_is_null env select_items row) =
  accept row.
Hypothesis left_decision : forall rows,
  eval_query_generic env left (SqlSuccess rows) ->
  existsb accept rows = left_accepted.
Hypothesis right_decision : forall rows,
  eval_query_generic env right (SqlSuccess rows) ->
  existsb accept rows = right_accepted.
Hypothesis left_errors_absent : forall error,
  ~ eval_query_generic env left (SqlError error).
Hypothesis right_errors_absent : forall error,
  ~ eval_query_generic env right (SqlError error).

Variables distinct_input distinct_output : list (tuple T).
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
    (@in_rows_truth T unknown value_is_null
      env select_items distinct_output) =
  Bool.is_true (B T)
    (@in_rows_truth T unknown value_is_null
      env select_items distinct_input).
Proof. now apply in_rows_acceptance_distinct. Qed.

Example in_union_all_acceptance_regression :
  formula_acceptance_exact_at
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env
    (FExpr_In select_items (QExpr_Set Union left right))
    (orb left_accepted right_accepted).
Proof.
eapply formula_in_union_all_acceptance_exact; eassumption.
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

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error
    NullValues.is_null_value).

Variable env : Env.env TNull.
Variable select_items : list (@select TNull).
Variable subquery : query_expr TNull relname.

Hypothesis arguments_safe :
  first_runtime_error
    (@eval_select_runtime_error TNull
      symbol_runtime_error aggregate_runtime_error env)
    select_items = None.
Hypothesis child_success :
  exists rows, eval_query env subquery (SqlSuccess rows).
Hypothesis child_errors_absent :
  forall error, ~ eval_query env subquery (SqlError error).
Hypothesis every_comparison_false :
  forall rows,
    eval_query env subquery (SqlSuccess rows) ->
    Forall
      (fun row =>
        @in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items row = false3)
      (@query_canonical_rows TNull rows).

Example not_in_exact_acceptance_regression :
  formula_acceptance_exact_at
    basesort instance unknown3 symbol_runtime_error
    aggregate_runtime_error NullValues.is_null_value env
    (FExpr_Not (FExpr_In select_items subquery)) true.
Proof.
eapply tnull_formula_not_in_accepts_exact_of_all_false; eassumption.
Qed.

End OutcomeRegression.

Print Assumptions tnull_in_rows_unknown_iff.
Print Assumptions tnull_in_rows_semantic_cases.
Print Assumptions tnull_not_in_rows_acceptance_iff_all_false.
Print Assumptions tnull_not_in_rows_acceptance_iff_no_true_or_unknown.
Print Assumptions query_distinct_rows_support_rel.
Print Assumptions in_rows_acceptance_distinct.
Print Assumptions formula_in_union_all_acceptance_exact.
Print Assumptions tnull_formula_not_in_accepts_exact_of_all_false.
Print Assumptions tnull_formula_not_in_rejects_exact_of_true_match.
Print Assumptions tnull_formula_not_in_rejects_exact_of_unknown_without_match.
Print Assumptions not_in_exact_acceptance_regression.
