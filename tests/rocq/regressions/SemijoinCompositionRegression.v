(** Generic regression coverage for semijoin support and exact join safety. *)

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  ListPermut Projection
  SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts RelationalAlgebraFacts
  SemijoinCompositionFacts.

Import ListNotations.
Import Tuple.

Section ProjectionSupportRegression.

Context {Row LeftView RightView : Type}.
Variable relation : LeftView -> RightView -> Prop.
Variables
  (join : Row -> Row -> Row)
  (accept : Row -> Row -> bool)
  (emit : Row -> LeftView)
  (project : Row -> RightView)
  (left right : list Row).

Hypothesis projected_cell_related :
  forall left_row right_row,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    relation (emit left_row) (project (join left_row right_row)).

(** The right input may contain any number of accepted occurrences.  The
    interface records only bidirectional support, so a caller must cross a
    DISTINCT-like boundary before forgetting the joined multiplicity. *)
Example partial_semijoin_projection_support_regression :
  list_support_rel relation
    (map emit
      (filter (fun left_row => existsb (accept left_row) right) left))
    (map project (partial_semijoin_rows join accept left right)).
Proof.
eapply partial_semijoin_projection_support_rel.
exact projected_cell_related.
Qed.

End ProjectionSupportRegression.


Section ExactJoinSafetyRegression.

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

Variable env : Env.env T.
Variable kind : query_join_kind.
Variable predicate : formula_expr T relname.
Variables matched_select left_select right_select : @_select_list T.
Variables left right : query_expr T relname.
Variable accepted : tuple T -> tuple T -> bool.
Variable emit : query_join_source T -> tuple T.

Hypothesis left_safe :
  forall error, ~ eval_query env left (SqlError error).
Hypothesis right_safe :
  forall error, ~ eval_query env right (SqlError error).
Hypothesis conditions_exact :
  forall left_row right_row,
    @join_condition_acceptance_exact_at T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env predicate left_row right_row (accepted left_row right_row).
Hypothesis projection_exact :
  forall source,
    @project_join_source_outcome T symbol_runtime_error
      aggregate_runtime_error env
      matched_select left_select right_select source =
    SqlSuccess (emit source).

Example exact_join_safety_regression : forall error,
  ~ eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlError error).
Proof.
eapply query_expr_join_no_error_of_acceptance_projection_exact;
  eassumption.
Qed.

End ExactJoinSafetyRegression.

Print Assumptions partial_semijoin_projection_support_regression.
Print Assumptions exact_join_safety_regression.
