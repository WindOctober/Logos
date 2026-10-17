From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula OrderedSet
  SqlOutcome SqlErrorSemantics SqlQueryContexts SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import GroupedFilterOutcomeFacts PossibleOutcomeFacts.
From Stdlib Require Import List.

Import ListNotations.
Import Tuple.

Section GenericInterfaces.
Context {T : Tuple.Rcd} {relname : Type}.
Variable basesort : relname -> Fset.set (A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple T)).
Variable unknown : Bool.b (B T).
Variable symbol_error : scalar_operator T ->
  list (option sql_runtime_error * value T) -> option sql_runtime_error.
Variable aggregate_error : aggregate T ->
  list (option sql_runtime_error * value T) -> option sql_runtime_error.
Variable is_null : value T -> bool.
Variable schedule : boolean_site -> boolean_evaluation_order.
Variable env : Env.env T.

Local Abbreviation exact_value :=
  (@scalar_value_expr_exact_at T relname basesort instance unknown
    symbol_error aggregate_error is_null schedule env).
Local Abbreviation acceptance :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_error aggregate_error is_null schedule env).
Local Abbreviation eval_value :=
  (@eval_scalar_value_expr_outcome T relname basesort instance unknown
    symbol_error aggregate_error is_null schedule env).

(** No safety or value contract is imposed on the unselected arm. *)
Example case_then_only result_type condition yes no expected :
  acceptance condition true -> exact_value yes expected ->
  exact_value (SExpr_Case result_type condition yes no) expected.
Proof.
intros Hcondition Hyes.
eapply scalar_value_expr_case_exact_from_acceptance with (accepted := true);
  eassumption.
Qed.

Example case_else_with_error_in_unselected_arm
    result_type condition yes no expected error :
  acceptance condition false -> eval_value yes (SqlError error) ->
  exact_value no expected ->
  exact_value (SExpr_Case result_type condition yes no) expected.
Proof.
intros Hcondition Hunselected Hno.
eapply scalar_value_expr_case_exact_from_acceptance with (accepted := false);
  eassumption.
Qed.

(** A selected error cannot be erased by the success-exactness interface. *)
Example case_selected_error_not_exact
    result_type condition yes no expected error :
  acceptance condition true -> eval_value yes (SqlError error) ->
  ~ exact_value (SExpr_Case result_type condition yes no) expected.
Proof.
intros [[truth [Htruth Haccept]] _] Herror [_ [_ Hsafe]].
apply (Hsafe error).
eapply EScalar_CaseThen; eassumption.
Qed.

(** Different annotations and arbitrary leaf terms, not just column names. *)
Example heterogeneous_leaf_values first_type second_type first second :
  (forall term, In term [first; second] ->
    @eval_aggterm_runtime_error T symbol_error aggregate_error env term = None) ->
  @scalar_value_list_exact_at T relname basesort instance unknown
    symbol_error aggregate_error is_null schedule env
    [SExpr_Leaf first_type first; SExpr_Leaf second_type second]
    [Interp.interp_aggterm T env first; Interp.interp_aggterm T env second].
Proof.
intro Hsafe.
apply scalar_value_leaf_list_exact with (terms := [first; second]); [|exact Hsafe].
constructor; [exists first_type; reflexivity|].
constructor; [exists second_type; reflexivity|constructor].
Qed.

Example empty_leaf_projection :
  @eval_project_rows_outcome T relname basesort instance unknown
    symbol_error aggregate_error is_null schedule env [] [] (SqlSuccess []).
Proof.
constructor.
Qed.

(** Duplicate occurrences remain duplicated, not set-deduplicated. *)
Example leaf_projection_keeps_duplicates select_list terms row :
  Forall2 (fun expression term =>
    exists result_type, expression = SExpr_Leaf result_type term)
    (map fst select_list) terms ->
  (forall term, In term terms ->
    @eval_aggterm_runtime_error T symbol_error aggregate_error
      (env_t T env row) term = None) ->
  @eval_project_rows_outcome T relname basesort instance unknown
    symbol_error aggregate_error is_null schedule env select_list [row; row]
    (SqlSuccess [project_row select_list
      (map (Interp.interp_aggterm T (env_t T env row)) terms);
      project_row select_list
      (map (Interp.interp_aggterm T (env_t T env row)) terms)]).
Proof.
intros Hleaves Hsafe.
assert (Hrows : forall other term, In other [row; row] -> In term terms ->
  @eval_aggterm_runtime_error T symbol_error aggregate_error
    (env_t T env other) term = None).
{
  intros other term Hin Hterm.
  destruct Hin as [Heq|[Heq|Hfalse]]; try contradiction;
    subst other; now apply Hsafe.
}
apply (proj2 (@eval_project_leaf_rows_exact_map T relname
  basesort instance unknown symbol_error aggregate_error is_null schedule
  env select_list terms [row; row] Hleaves Hrows _)); reflexivity.
Qed.

Example leaf_projection_respects_semantic_rows
    (select_list : query_select_list T relname) terms left right :
  Oeset.compare (OTuple T) left right = Eq ->
  Oeset.compare (OTuple T)
    (project_row select_list (map (Interp.interp_aggterm T (env_t T env left)) terms))
    (project_row select_list (map (Interp.interp_aggterm T (env_t T env right)) terms)) = Eq.
Proof.
apply leaf_project_row_semantic_proper.
Qed.

(** Neither the exactness nor observation bridge assumes child safety. *)
Example filter_acceptance_preserves_child_errors left right input error :
  (forall sched outer, exists accepted,
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_error aggregate_error is_null sched outer left accepted /\
    @scalar_expr_acceptance_exact_at T relname basesort instance unknown
      symbol_error aggregate_error is_null sched outer right accepted) ->
  (@eval_query_expr_outcome T relname basesort instance unknown symbol_error
    aggregate_error is_null schedule env (QExpr_Filter left input) (SqlError error) <->
   @eval_query_expr_outcome T relname basesort instance unknown symbol_error
    aggregate_error is_null schedule env (QExpr_Filter right input) (SqlError error)).
Proof.
intro Haccept.
pose proof (@query_expr_filter_uniform_global_typed_of_acceptance_exact
  T relname basesort instance unknown symbol_error aggregate_error is_null
  left right input Haccept schedule) as [_ Houtcomes].
apply Houtcomes.
Qed.

Example filter_observation_preserves_predicate_errors left right input error :
  (forall sched outer,
    @filter_scalar_observation_equiv_at T relname basesort instance unknown
      symbol_error aggregate_error is_null sched outer left outer right) ->
  (@eval_query_expr_outcome T relname basesort instance unknown symbol_error
    aggregate_error is_null schedule env (QExpr_Filter left input) (SqlError error) <->
   @eval_query_expr_outcome T relname basesort instance unknown symbol_error
    aggregate_error is_null schedule env (QExpr_Filter right input) (SqlError error)).
Proof.
intro Hobs.
pose proof (@query_expr_filter_uniform_global_typed_of_observation
  T relname basesort instance unknown symbol_error aggregate_error is_null
  left right input Hobs schedule) as [_ Houtcomes].
apply Houtcomes.
Qed.
End GenericInterfaces.

(** The acceptance boundary is deliberately weaker than Bool3 equality. *)
Example false_and_unknown_share_acceptance_not_truth :
  Bool.is_true Bool3 false3 = Bool.is_true Bool3 unknown3 /\ false3 <> unknown3.
Proof. split; [reflexivity|discriminate]. Qed.

Print Assumptions scalar_value_expr_case_exact_from_acceptance.
Print Assumptions scalar_value_list_exact_map.
Print Assumptions scalar_value_leaf_list_exact.
Print Assumptions eval_project_leaf_rows_exact_map.
Print Assumptions leaf_project_row_equal_of_row_equiv.
Print Assumptions leaf_project_row_semantic_proper.
Print Assumptions query_expr_filter_uniform_global_typed_of_observation.
Print Assumptions query_expr_filter_uniform_global_typed_of_acceptance_exact.
