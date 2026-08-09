From Stdlib Require Import Bool Lia List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples ListPermut
  SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import
  CardinalityCombinators FilterFkEliminationFacts OuterJoinFilterFacts.

Import ListNotations.
Import FTuples.Tuple.

(** The post-filter factorization retains both copies of every duplicate
    input occurrence. *)
Example duplicate_filter_movement_regression :
  forall (left right : list bool),
    filter
      (fun pair => andb (fst pair) (negb (snd pair)))
      (join_matched_rows pair Bool.eqb left right) =
    join_matched_rows pair Bool.eqb
      (filter (fun value => value) left)
      (filter (fun value => negb value) right).
Proof.
intros left right.
apply inner_filter_to_input_filters_exact.
intros left_row right_row.
destruct left_row, right_row; reflexivity.
Qed.

(** Reflexive equality witnesses that both pre-join guard schedules reach
    exactly the rows reached by the corresponding post-join guard. *)
Example self_match_reaches_both_sides_regression :
  forall (rows : list bool),
    (forall row,
      join_left_guard_reached Bool.eqb rows rows row <-> In row rows) /\
    (forall row,
      join_right_guard_reached Bool.eqb rows rows row <-> In row rows).
Proof.
intro rows.
apply join_self_guard_reachability_exact.
intros [|] Hrow; reflexivity.
Qed.


Section UnsafeFilterSchedules.

Context {T : FTuples.Tuple.Rcd} {relname : Type}.

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
Variable env : Env.env T.
Variable formula : scalar_expr T relname ScalarResultBoolean.
Variable row : tuple T.
Variable expected : sql_runtime_error.

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Hypothesis row_errors :
  eval_scalar_boolean (env_t T env row) formula (SqlError expected).
Hypothesis row_has_no_success :
  forall truth,
    ~ eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth).
Hypothesis row_error_category_exact :
  forall observed,
    eval_scalar_boolean (env_t T env row) formula (SqlError observed) ->
    observed = expected.

(** The first schedule comes from two accepted left occurrences joined to one
    right occurrence.  The second is a single pre-join input FILTER. *)
Definition regression_joined_filter_rows : list (tuple T) :=
  join_matched_rows
    (fun left _ : tuple T => left)
    (fun _ _ : tuple T => true)
    [row; row] [row].

Local Lemma regression_joined_filter_member_eq :
  forall candidate,
    In candidate regression_joined_filter_rows -> candidate = row.
Proof.
intros candidate Hcandidate.
cbn [regression_joined_filter_rows join_matched_rows] in Hcandidate.
destruct Hcandidate as [Hcandidate|[Hcandidate|[]]]; now symmetry.
Qed.

Local Lemma regression_joined_filter_bad_member :
  In row regression_joined_filter_rows.
Proof.
cbn [regression_joined_filter_rows join_matched_rows].
now left.
Qed.

(** This specifically exercises the accepted-cell reachability bridge rather
    than asserting an opaque equality between two error relations. *)
Example joined_filter_witness_error_regression :
  eval_filter_rows env formula regression_joined_filter_rows
    (SqlError expected).
Proof.
unfold regression_joined_filter_rows.
eapply eval_filter_rows_uniform_error_of_join_witness
  with (left_row := row) (right_row := row).
- now left.
- now left.
- reflexivity.
- exact row_errors.
- intros candidate Hcandidate; right.
  cbn [join_matched_rows] in Hcandidate.
  destruct Hcandidate as [Hcandidate|[Hcandidate|[]]];
    subst candidate; exact row_errors.
Qed.

(** The post-join duplicate schedule and the one-row input schedule both
    expose the fixed category, have no successful traversal, and have no
    other error category. *)
Example structurally_different_filter_error_exact_regression :
  (eval_filter_rows env formula regression_joined_filter_rows
      (SqlError expected) /\
   (forall output,
      ~ eval_filter_rows env formula regression_joined_filter_rows
        (SqlSuccess output)) /\
   (forall observed,
      eval_filter_rows env formula regression_joined_filter_rows
        (SqlError observed) -> observed = expected)) /\
  (eval_filter_rows env formula [row] (SqlError expected) /\
   (forall output,
      ~ eval_filter_rows env formula [row] (SqlSuccess output)) /\
   (forall observed,
      eval_filter_rows env formula [row] (SqlError observed) ->
      observed = expected)).
Proof.
split.
- eapply eval_filter_rows_reached_uniform_error_exact
    with (bad := row).
  + exact regression_joined_filter_bad_member.
  + exact row_errors.
  + intros candidate Hcandidate; right.
    rewrite (regression_joined_filter_member_eq candidate Hcandidate).
    exact row_errors.
  + exact row_has_no_success.
  + intros candidate Hcandidate observed Herror.
    rewrite (regression_joined_filter_member_eq candidate Hcandidate)
      in Herror.
    now apply row_error_category_exact.
- eapply eval_filter_rows_reached_uniform_error_exact
    with (bad := row).
  + now left.
  + exact row_errors.
  + intros candidate [Hcandidate|[]]; subst candidate; now right.
  + exact row_has_no_success.
  + intros candidate [Hcandidate|[]] observed Herror; subst candidate.
    now apply row_error_category_exact.
Qed.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Variable first_query second_query : query_expr T relname.
Hypothesis exact_error_outputs :
  query_expr_outputs first_query = query_expr_outputs second_query.
Hypothesis first_query_error :
  eval_query env first_query (SqlError expected).
Hypothesis second_query_error :
  eval_query env second_query (SqlError expected).
Hypothesis first_query_no_success :
  forall rows, ~ eval_query env first_query (SqlSuccess rows).
Hypothesis second_query_no_success :
  forall rows, ~ eval_query env second_query (SqlSuccess rows).
Hypothesis first_query_error_category :
  forall observed,
    eval_query env first_query (SqlError observed) -> observed = expected.
Hypothesis second_query_error_category :
  forall observed,
    eval_query env second_query (SqlError observed) -> observed = expected.

(** The query lift consumes separately proved existence, success exclusion,
    and category uniqueness; it is not supplied a raw error iff. *)
Example exact_error_only_query_lift_regression :
  @query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule env first_query second_query.
Proof.
eapply query_expr_outcome_equiv_of_shared_exact_error; eassumption.
Qed.

End UnsafeFilterSchedules.

Check nonnull_foreign_key_direct_accept_has_middle.
Check nonnull_foreign_key_no_middle_rejects_direct.
Check map_left_join_functional_branch_permut.
Check stable_total_filter_acceptance.
Check query_filter_success_bags_of_stable_total_acceptance.
Check query_filter_error_iff_of_stable_total_acceptance.
Check eval_filter_rows_uniform_error_of_reached_member.
Check eval_filter_rows_error_category_of_reached_categories.
Check eval_filter_rows_success_excludes_reached_exact_error.
Check eval_filter_rows_uniform_error_of_self_match.
Check query_expr_outcome_equiv_of_shared_exact_error.

Print Assumptions duplicate_filter_movement_regression.
Print Assumptions self_match_reaches_both_sides_regression.
Print Assumptions joined_filter_witness_error_regression.
Print Assumptions structurally_different_filter_error_exact_regression.
Print Assumptions exact_error_only_query_lift_regression.
Print Assumptions query_filter_success_bags_of_stable_total_acceptance.
Print Assumptions query_filter_error_iff_of_stable_total_acceptance.
Print Assumptions query_expr_outcome_equiv_of_shared_exact_error.
Print Assumptions map_left_join_functional_branch_permut.
