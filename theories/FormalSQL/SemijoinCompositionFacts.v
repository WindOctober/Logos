(** Occurrence-preserving semijoin composition and exact join safety. *)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples ListPermut
  OrderedSet SqlErrorSemantics SqlOutcome SqlQueryFacts SqlQuerySemantics
  SqlQuerySyntax.
From Logos.FormalSQL Require Import
  CardinalityCombinators GroupedFilterOutcomeFacts RelationalAlgebraFacts.

Import ListNotations.
Import Tuple.

(** A complete native join cannot introduce an error when both children are
    error-free and every reached condition and branch projection has an exact
    successful observation.  This is deliberately a safety theorem: it does
    not infer error preservation from a successful bag equality. *)
Section ExactJoinSafety.

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

Theorem query_expr_join_no_error_of_acceptance_projection_exact :
  forall env kind predicate matched_select left_select right_select
      left right (accepted : tuple T -> tuple T -> bool)
      (emit : query_join_source T -> tuple T),
    (forall error, ~ eval_query env left (SqlError error)) ->
    (forall error, ~ eval_query env right (SqlError error)) ->
    (forall left_row right_row,
      @join_condition_acceptance_exact_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env predicate left_row right_row (accepted left_row right_row)) ->
    (forall source,
      @project_join_source_outcome T symbol_runtime_error
        aggregate_runtime_error env
        matched_select left_select right_select source =
      SqlSuccess (emit source)) ->
    forall error,
      ~ eval_query env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error).
Proof.
intros env kind predicate matched_select left_select right_select
  left right accepted emit Hleft_safe Hright_safe
  Hconditions Hprojection error Herror.
apply eval_query_expr_join_error_iff in Herror.
destruct Herror as
  [Hleft_error |
   [left_rows [Hleft_success
     [Hright_error | [right_rows [Hright_success Hjoin_error]]]]]].
- exact (Hleft_safe error Hleft_error).
- exact (Hright_safe error Hright_error).
- pose proof
    (@eval_join_bag_safe_of_acceptance_projection_exact
      T relname basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env kind predicate
      matched_select left_select right_select accepted emit
      (query_rows_bag left_rows) (query_rows_bag right_rows)
      Hconditions Hprojection) as [_ Hjoin_safe].
  exact (Hjoin_safe error Hjoin_error).
Qed.

End ExactJoinSafety.

(** Support-level projection law for one semijoin boundary.  This exposes the
    operator-local relation between surviving left rows and projected join
    cells without fixing a larger query topology. *)
Section SemijoinProjectionSupport.

Context {Row : Type}.

Definition partial_semijoin_rows
    (join : Row -> Row -> Row) (accept : Row -> Row -> bool)
    (left right : list Row) : list Row :=
  Join.theta_join_list Row join accept left right.

(** A semijoin's surviving left support is exactly the support of the
    projected matching join cells.  No functionality premise is required:
    multiple right matches may duplicate the joined projection, and this law
    deliberately forgets only that multiplicity for a later DISTINCT or
    other duplicate-elimination boundary. *)
Theorem partial_semijoin_projection_support_rel :
  forall (LeftView RightView : Type)
      (R : LeftView -> RightView -> Prop)
      (join : Row -> Row -> Row) (accept : Row -> Row -> bool)
      (emit : Row -> LeftView) (project : Row -> RightView)
      left right,
    (forall left_row right_row,
      In left_row left ->
      In right_row right ->
      accept left_row right_row = true ->
      R (emit left_row) (project (join left_row right_row))) ->
    list_support_rel R
      (map emit
        (filter (fun left_row => existsb (accept left_row) right) left))
      (map project (partial_semijoin_rows join accept left right)).
Proof.
intros LeftView RightView R join accept emit project left right Hrelated.
split.
- intros left_view Hleft_view.
  apply in_map_iff in Hleft_view.
  destruct Hleft_view as [left_row [Hleft_view Hleft]].
  subst left_view.
  apply filter_In in Hleft as [Hleft Hexists].
  apply existsb_exists in Hexists.
  destruct Hexists as [right_row [Hright Haccepted]].
  exists (project (join left_row right_row)); split.
  + apply in_map.
    unfold partial_semijoin_rows, Join.theta_join_list.
    apply in_flat_map.
    exists left_row; split; [exact Hleft|].
    unfold Join.d_join_list.
    apply in_map.
    apply filter_In; now split.
  + now apply Hrelated.
- intros right_view Hright_view.
  apply in_map_iff in Hright_view.
  destruct Hright_view as [joined [Hright_view Hjoined]].
  subst right_view.
  unfold partial_semijoin_rows, Join.theta_join_list in Hjoined.
  apply in_flat_map in Hjoined.
  destruct Hjoined as [left_row [Hleft Hjoined]].
  unfold Join.d_join_list in Hjoined.
  apply in_map_iff in Hjoined.
  destruct Hjoined as [right_row [Hjoined Hright]].
  subst joined.
  apply filter_In in Hright as [Hright Haccepted].
  exists (emit left_row); split.
  + apply in_map.
    apply filter_In; split; [exact Hleft|].
    apply existsb_exists.
    exists right_row; now split.
  + now apply Hrelated.
Qed.

End SemijoinProjectionSupport.
