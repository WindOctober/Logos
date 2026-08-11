(** Generic regressions for membership/EXISTS composition. *)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance OrderedSet Projection SqlBagAbstraction SqlErrorSemantics
  SqlOutcome SqlQueryContexts SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts
  MembershipJoinCompositionFacts OrderedQueryFacts PossibleOutcomeFacts
  SubqueryFacts.

Import ListNotations.
Import Tuple.

Section CorrelatedScalarRegression.

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
Local Abbreviation scalar_exact :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Variables outer_env : Env.env T.
Variables output_select : query_select_list T relname.
Variables filter_predicate : scalar_expr T relname ScalarResultBoolean.
Variables filter_input : query_expr T relname.
Variable filter_keep : tuple T -> bool.
Hypothesis filter_predicate_exact : forall row,
  scalar_exact (env_t T outer_env row)
    filter_predicate (filter_keep row).
Hypothesis output_projection_safe : forall row,
  @scalar_select_values_runtime_safe_at T relname
    basesort instance unknown symbol_runtime_error
    aggregate_runtime_error value_is_null boolean_schedule
    (env_t T outer_env row) output_select.
Hypothesis filter_input_safe :
  @query_expr_runtime_safe T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule outer_env filter_input.

End CorrelatedScalarRegression.

(** A plain no-TRUE anti-join test would retain this row, but SQL NOT IN
    rejects it because the only candidate comparison is UNKNOWN. *)
Example not_in_unknown_is_not_plain_antijoin :
  Bool.is_true Bool3
    (negb3 (interp_quant Bool3 Exists_F (fun truth : bool3 => truth)
      [unknown3])) = false /\
  negb (existsb (fun truth => Bool.is_true Bool3 truth) [unknown3]) = true.
Proof. split; reflexivity. Qed.

Section CorrelatedFilterJoinRegression.

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
Variable schedule : boolean_site -> boolean_evaluation_order.

Variables env : Env.env T.
Variable formula : scalar_expr T relname ScalarResultBoolean.
Variables left_rows right_rows : list (tuple T).
Variable matches : tuple T -> tuple T -> bool.

Hypothesis correlated_semijoin_exact :
  @correlated_filter_join_acceptance_exact_at T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule env formula right_rows matches
    (fun matched => matched) left_rows.

(** The public row bridge is directly applicable: no manual induction over
    the outer rows or reconstruction of native join sources is required. *)
Example correlated_filter_reaches_native_semijoin_sources :
  forall outcome,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env formula left_rows outcome <->
    outcome =
      SqlSuccess
        (map (@query_join_source_row T)
          (query_join_sources T QueryJoinSemi left_rows right_rows
            (map (fun left => map (matches left) right_rows) left_rows))).
Proof.
intro outcome.
now apply eval_filter_rows_correlated_semijoin_sources_exact.
Qed.

Variables input right : query_expr T relname.
Variable target_predicate : scalar_expr T relname ScalarResultBoolean.
Variables matched_select left_select right_select : query_select_list T relname.
Variable row_rel : tuple T -> tuple T -> Prop.

Hypothesis right_success : exists rows,
  @eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule
    env right (SqlSuccess rows).
Hypothesis right_safe : forall error,
  ~ @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env right (SqlError error).
Hypothesis local_transport : forall source_rows target_rows,
  @eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule
    env right (SqlSuccess target_rows) ->
  outcome_relation_transport (Forall2 row_rel)
    (@eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env formula source_rows)
    (@query_join_rows_outcomes T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env QueryJoinSemi target_predicate matched_select left_select
      right_select source_rows target_rows).

(** Child evaluation and error plumbing are discharged by the scheduled
    constructor lift; the caller supplies only the reusable local contract. *)
Example correlated_filter_semijoin_scheduled_transport :
  outcome_relation_transport (Forall2 row_rel)
    (@eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env (QExpr_Filter formula input))
    (@eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env (QExpr_Join QueryJoinSemi target_predicate
        matched_select left_select right_select input right)).
Proof.
eapply query_expr_correlated_filter_join_relation_transport;
  eassumption.
Qed.

End CorrelatedFilterJoinRegression.

Print Assumptions query_join_semi_sources_boolean_matrix.
Print Assumptions tnull_scalar_expr_correlated_not_in_antijoin_acceptance_exact.
Print Assumptions query_expr_correlated_filter_join_possible_outcome_related.
