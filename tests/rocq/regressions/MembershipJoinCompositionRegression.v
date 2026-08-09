(** Generic regressions for membership/EXISTS composition. *)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance OrderedSet Projection SqlBagAbstraction SqlErrorSemantics
  SqlOutcome SqlQueryContexts SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts
  MembershipJoinCompositionFacts OrderedQueryFacts SubqueryFacts.

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
