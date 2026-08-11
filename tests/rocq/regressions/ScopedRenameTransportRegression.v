(******************************************************************************)
(** Scoped alpha-renaming transport and shadowing regressions.              **)
(******************************************************************************)

From Stdlib Require Import List String.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  SqlOutcome SqlQueryContexts SqlQueryRenameTransport SqlQuerySyntax SqlSyntax
  Values.
From Logos.FormalSQL Require Import
  QueryTNullSyntax RenameTransportFacts TNullSyntax.

Import ListNotations.
Import Tuple.

Definition regression_inner_name (name : string) : string :=
  if String.eqb name "a" then "c" else name.

Definition regression_outer_name (name : string) : string :=
  if String.eqb name "a" then "d" else name.

Example shadowed_names_use_distinct_scope_maps :
  rename_tnull_attribute_name regression_inner_name (Attr_int32 "a") =
    Attr_int32 "c" /\
  rename_tnull_attribute_name regression_outer_name (Attr_int32 "a") =
    Attr_int32 "d".
Proof. split; reflexivity. Qed.

(** One global function cannot send the same typed attribute occurrence to
    two different targets.  Scoped frames avoid requiring this contradiction. *)
Example shadowed_names_cannot_share_one_global_map :
  forall rho : attribute TNull -> attribute TNull,
    rho (Attr_int32 "a") = Attr_int32 "c" ->
    rho (Attr_int32 "a") = Attr_int32 "d" ->
    False.
Proof.
intros rho Hinner Houter.
rewrite Hinner in Houter; discriminate.
Qed.

Section GenericProjectScopeBoundary.

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
Variable leaf_has_type : type T -> aggterm T -> Prop.
Variable call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Variable predicate_has_types : predicate T -> list (type T) -> Prop.
Variables rank_type boolean_type : type T.

Variables inner_environment_relation outer_environment_relation :
  Env.env T -> Env.env T -> Prop.
Variables inner_rho outer_rho : attribute T -> attribute T.
Variables left_select right_select : query_select_list T relname.
Variables input input' : query_expr T relname.

Hypothesis environments_narrow : forall left_env right_env,
  outer_environment_relation left_env right_env ->
  inner_environment_relation left_env right_env.
Hypothesis project_schema :
  @query_rename_schema_compatible T relname basesort value_is_null
    leaf_has_type call_has_type predicate_has_types rank_type boolean_type
    outer_rho
    (QExpr_Project left_select input)
    (QExpr_Project right_select input').
Hypothesis child_transport :
  @query_rename_transport_under T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule
    leaf_has_type call_has_type predicate_has_types rank_type boolean_type
    inner_environment_relation inner_rho input input'.
Hypothesis project_local :
  @query_unary_local_scoped_rename_compatible T
    outer_environment_relation inner_rho outer_rho
    (fun env =>
      @query_project_local T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select)
    (fun env =>
      @query_project_local T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select).

Example project_changes_the_visible_rename_scope :
  @query_rename_transport_under T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule
    leaf_has_type call_has_type predicate_has_types rank_type boolean_type
    outer_environment_relation outer_rho
    (QExpr_Project left_select input)
    (QExpr_Project right_select input').
Proof.
eapply QExpr_Project_scoped_rename_transport; eassumption.
Qed.

End GenericProjectScopeBoundary.

Section TNullScopedChain.

Variable db : db_state.
Variables inner_relation middle_relation outer_relation :
  Env.env TNull -> Env.env TNull -> Prop.
Variables inner_name middle_name outer_name : string -> string.
Variables inner_left inner_right : QueryExpr.
Variables middle_left_context middle_right_context :
  query_expr_context TNull relname.
Variables outer_left_context outer_right_context :
  query_expr_context TNull relname.

Hypothesis inner_transport :
  tnull_query_rename_transport_under db inner_relation inner_name
    inner_left inner_right.
Hypothesis middle_scope :
  tnull_query_scoped_rename_context_compatible db
    inner_relation middle_relation inner_name middle_name
    middle_left_context middle_right_context.
Hypothesis outer_scope :
  tnull_query_scoped_rename_context_compatible db
    middle_relation outer_relation middle_name outer_name
    outer_left_context outer_right_context.

Definition regression_scope_steps : list tnull_query_rename_scope_step :=
  [TNullQueryRenameScopeStep
      middle_left_context middle_right_context middle_relation middle_name;
   TNullQueryRenameScopeStep
      outer_left_context outer_right_context outer_relation outer_name].

Lemma regression_scope_steps_compatible :
  tnull_query_rename_scope_steps_compatible db
    inner_relation inner_name regression_scope_steps.
Proof.
cbn; split.
- exact middle_scope.
- split; [exact outer_scope | exact I].
Qed.

Example two_independent_scope_renames_compose :
  tnull_query_rename_transport_under db outer_relation outer_name
    (plug_query_expr_context outer_left_context
      (plug_query_expr_context middle_left_context inner_left))
    (plug_query_expr_context outer_right_context
      (plug_query_expr_context middle_right_context inner_right)).
Proof.
change
  (tnull_query_rename_transport_under db
    (tnull_query_rename_scope_steps_final_environment_relation
      inner_relation regression_scope_steps)
    (tnull_query_rename_scope_steps_final_name
      inner_name regression_scope_steps)
    (plug_tnull_query_rename_scope_steps_left
      regression_scope_steps inner_left)
    (plug_tnull_query_rename_scope_steps_right
      regression_scope_steps inner_right)).
eapply tnull_query_scoped_renaming_context_chain_transport.
- exact regression_scope_steps_compatible.
- exact inner_transport.
Qed.

End TNullScopedChain.

Section CorrelatedSubqueryScopeBoundary.

Variable db : db_state.
Variables subquery_relation outer_relation :
  Env.env TNull -> Env.env TNull -> Prop.
Variables subquery_name outer_name : string -> string.
Variables subquery_left subquery_right : QueryExpr.
Variables outer_input_left outer_input_right : QueryExpr.

Definition correlated_exists_left_context :
    query_expr_context TNull relname :=
  QCtx_FilterExpression (@SCtx_ExistsSubquery TNull relname)
    outer_input_left.

Definition correlated_exists_right_context :
    query_expr_context TNull relname :=
  QCtx_FilterExpression (@SCtx_ExistsSubquery TNull relname)
    outer_input_right.

Hypothesis correlated_exists_scope :
  tnull_query_scoped_rename_context_compatible db
    subquery_relation outer_relation subquery_name outer_name
    correlated_exists_left_context correlated_exists_right_context.

Example correlated_exists_returns_to_the_outer_rename_scope :
  tnull_query_rename_transport_under db subquery_relation subquery_name
    subquery_left subquery_right ->
  tnull_query_rename_transport_under db outer_relation outer_name
    (QExpr_Filter (SExpr_Exists subquery_left) outer_input_left)
    (QExpr_Filter (SExpr_Exists subquery_right) outer_input_right).
Proof.
intro Hsubquery.
change (tnull_query_rename_transport_under db outer_relation outer_name
  (plug_query_expr_context correlated_exists_left_context subquery_left)
  (plug_query_expr_context correlated_exists_right_context subquery_right)).
eapply tnull_query_scoped_renaming_context_transport;
  [exact correlated_exists_scope | exact Hsubquery].
Qed.

End CorrelatedSubqueryScopeBoundary.

Print Assumptions QExpr_Project_scoped_rename_transport.
Print Assumptions tnull_query_scoped_renaming_context_chain_transport.
