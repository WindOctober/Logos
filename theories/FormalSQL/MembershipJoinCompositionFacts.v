(** Correlation-preserving membership/EXISTS composition. *)

Set Implicit Arguments.

From Stdlib Require Import List Lia.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance ListPermut OrderedSet Projection SqlBagAbstraction
  SqlErrorSemantics SqlOutcome SqlQueryContexts SqlQueryFacts
  SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts OrderedQueryFacts
  SubqueryFacts.

Import ListNotations.
Import Tuple.

(** DISTINCT can change duplicate multiplicity and the complete FALSE versus
    UNKNOWN observation of an [IN], but it cannot change whether [IN] is
    accepted.  This lift therefore consumes and produces only exact acceptance
    contracts.  Child errors are transported exactly because DISTINCT has no
    operator-local runtime error. *)
Section DistinctMembershipComposition.

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
Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation scalar_exact :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Theorem scalar_expr_in_distinct_acceptance_exact_of_inner :
  forall env arguments input accepted,
    (forall rows,
      eval_query env input (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs (query_expr_outputs input)) rows) ->
    scalar_exact env (SExpr_In arguments input) accepted ->
    scalar_exact env
      (SExpr_In arguments (QExpr_Distinct input)) accepted.
Proof.
intros env arguments input accepted Houtputs
  [[truth [Htruth Haccepted]] [Hsuccess Herrors]].
apply eval_scalar_boolean_in_success_iff in Htruth.
destruct Htruth as
  [values [input_rows [Harguments [Hinput Htruth]]]].
subst truth.
set (output :=
  Febag.elements (Fecol.CBag (CTuple T))
    (query_distinct_bag (query_rows_bag input_rows))).
assert (Houtput_bag :
  query_same_rows_as_bag output
    (query_distinct_bag (query_rows_bag input_rows))).
{
  unfold output; apply query_elements_same_rows_as_bag.
}
assert (Houtput :
  eval_query env (QExpr_Distinct input) (SqlSuccess output)).
{
  apply eval_query_expr_distinct_success_iff.
  exists input_rows; now split.
}
unfold scalar_exact, scalar_expr_acceptance_exact_at.
split.
- exists
    (@in_rows_truth T relname unknown value_is_null
      values (QExpr_Distinct input) output).
  split.
  + apply eval_scalar_boolean_in_success_iff.
    exists values, output; repeat split; try assumption; reflexivity.
  + change
      (Bool.is_true (B T)
        (@in_rows_truth T relname unknown value_is_null
          values input output) = accepted).
    rewrite
      (in_rows_acceptance_distinct
        unknown value_is_null values input
        (Houtputs input_rows Hinput) Houtput_bag).
    exact Haccepted.
- split.
  + intros observed Hobserved.
    apply eval_scalar_boolean_in_success_iff in Hobserved.
    destruct Hobserved as
      [observed_values [output_rows
        [Hobserved_arguments [Hdistinct Hobserved]]]].
    subst observed.
    apply eval_query_expr_distinct_success_iff in Hdistinct.
    destruct Hdistinct as
      [observed_input [Hobserved_input Hobserved_bag]].
    assert (Hinner :
      eval_scalar_boolean env (SExpr_In arguments input)
        (SqlSuccess
          (@in_rows_truth T relname unknown value_is_null
            observed_values input observed_input))).
    {
      apply eval_scalar_boolean_in_success_iff.
      exists observed_values, observed_input.
      repeat split; try assumption; reflexivity.
    }
    change
      (Bool.is_true (B T)
        (@in_rows_truth T relname unknown value_is_null
          observed_values input output_rows) = accepted).
    rewrite
      (in_rows_acceptance_distinct
        unknown value_is_null observed_values input
        (Houtputs observed_input Hobserved_input) Hobserved_bag).
    exact (Hsuccess _ Hinner).
  + intros error Herror.
    apply eval_scalar_boolean_in_error_iff in Herror.
    apply (Herrors error), eval_scalar_boolean_in_error_iff.
    destruct Herror as
      [Harguments_error |
        [observed_values [Harguments_safe Hdistinct_error]]].
    * now left.
    * right; exists observed_values; split; [exact Harguments_safe|].
      inversion Hdistinct_error; subst; assumption.
Qed.

(** A filter's exact acceptance contract and a projection's explicit local
    no-error contract compose without hiding either failure boundary.  This
    safety lemma is intentionally separate from the relational/bag laws below:
    successful bag equality alone cannot establish runtime-error equivalence. *)
Theorem query_expr_project_filter_runtime_safe_exact :
  forall env select_list predicate input (keep : tuple T -> bool),
    (forall row,
      scalar_exact (env_t T env row) predicate (keep row)) ->
    (forall row,
      @scalar_select_values_runtime_safe_at T relname
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) select_list) ->
    @query_expr_runtime_safe T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env input ->
    @query_expr_runtime_safe T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env
      (QExpr_Project select_list (QExpr_Filter predicate input)).
Proof.
intros env select_list predicate input keep Hpredicate Hproject Hinput.
apply query_expr_project_runtime_safe.
- exact Hproject.
- now apply query_expr_filter_runtime_safe_exact with (keep := keep).
Qed.

End DistinctMembershipComposition.
