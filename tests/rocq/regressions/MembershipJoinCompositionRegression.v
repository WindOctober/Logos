(** Generic regressions for membership/EXISTS composition. *)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance OrderedSet Projection SqlBagAbstraction SqlErrorSemantics
  SqlOutcome SqlQueryContexts SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts
  MembershipJoinCompositionFacts ProofAgentFacade SubqueryFacts TNullSyntax.

Import ListNotations.
Import Tuple.

Section CorrelatedFormulaRegression.

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
Local Abbreviation formula_exact :=
  (@formula_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Variables outer_env : Env.env T.
Variables output_select : @_select_list T.
Variables filter_formula : formula_expr T relname.
Variables filter_input : query_expr T relname.
Variable filter_keep : tuple T -> bool.
Hypothesis filter_formula_exact : forall row,
  formula_exact (env_t T outer_env row)
    filter_formula (filter_keep row).
Hypothesis output_projection_safe : forall row,
  @eval_select_list_runtime_error T symbol_runtime_error
    aggregate_runtime_error (env_t T outer_env row) output_select = None.
Hypothesis filter_input_safe :
  @query_expr_runtime_safe T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    outer_env filter_input.

Example project_filter_error_contract_regression :
  @query_expr_runtime_safe T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null outer_env
    (QExpr_Project output_select
      (QExpr_Filter filter_formula filter_input)).
Proof.
eapply query_expr_project_filter_runtime_safe_exact; eassumption.
Qed.

End CorrelatedFormulaRegression.

Print Assumptions project_filter_error_contract_regression.
