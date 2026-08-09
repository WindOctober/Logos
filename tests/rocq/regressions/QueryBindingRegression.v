From SQLFS Require Import FiniteBag FiniteCollection Formula FTuples GenericInstance
  SqlSyntax SqlOutcome SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics
  SqlQueryWellFormed Values.
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.QueryTNullSyntax
  FormalSQL.QueryBindingSemantics.
From Stdlib Require Import List String ZArith.

Import ListNotations.
Import Tuple.

Open Scope string_scope.
Open Scope Z_scope.

Definition regression_schedule (_ : boolean_site) : boolean_evaluation_order :=
  BooleanLeftFirst.

(** The one TNull admission hook keeps strict calls distinct from the typed
    control-flow constructors. *)
Example boolean_call_bypass_is_rejected :
  ~ TNullCallHasType type_bool (ScalarBoolean ScalarAnd)
      [type_bool; type_bool].
Proof.
  intros [Hallowed _].
  discriminate Hallowed.
Qed.

Example predicate_value_call_bypass_is_rejected :
  ~ TNullCallHasType type_bool (ScalarPredicateValue PredicateEq)
      [type_Z; type_Z].
Proof.
  intros [Hallowed _].
  discriminate Hallowed.
Qed.

Example case_call_bypass_is_rejected :
  ~ TNullCallHasType type_Z ScalarCase [type_bool; type_Z; type_Z].
Proof.
  intros [Hallowed _].
  discriminate Hallowed.
Qed.

(** Flat leaves are atomic or true aggregates.  An ordinary flat call, and a
    control-flow call hidden inside an aggregate argument, are both closed. *)
Example flat_scalar_call_leaf_bypass_is_rejected :
  ~ TNullLeafHasType type_int32
      (AScalarCall (ScalarAdd ScalarInt32) []).
Proof.
  intros [Hallowed _].
  discriminate Hallowed.
Qed.

Example aggregate_control_flow_leaf_bypass_is_rejected :
  ~ TNullLeafHasType type_int64
      (AAggregate AggregateCount AggregateAll
        (ScalarCall (ScalarBoolean ScalarAnd) [])).
Proof.
  intros [Hallowed _].
  discriminate Hallowed.
Qed.

Example true_aggregate_leaf_remains_admissible :
  TNullLeafHasType type_int64 ACountStar.
Proof.
  split; reflexivity.
Qed.

Definition regression_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_regression_cte")
    nil
    (@QExpr_Error TNull relname nil UndefinedFunction).

Definition regression_binding_schema : LocalQuerySchema :=
  local_query_binding_schema regression_binding.

Definition regression_body : QueryExpr :=
  @QExpr_Values TNull relname nil
    (Febag.empty (Fecol.CBag (CTuple TNull))).

Definition regression_bound_query : BoundQuery :=
  MakeBoundQuery [regression_binding] regression_body.

Example eager_binding_relation_exposes_definition_error :
  eval_bound_query_possible_outcome
    init_db [regression_binding_schema] nil regression_bound_query
    (SqlError UndefinedFunction).
Proof.
exists regression_schedule.
cbn [regression_bound_query regression_binding regression_body
  eval_local_query_bindings_with_schedule].
left; exists UndefinedFunction; split; [constructor | reflexivity].
Qed.

Definition regression_later_error_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_regression_later_error") nil
    (@QExpr_Error TNull relname nil UndefinedColumn).

Definition regression_two_error_bound_query : BoundQuery :=
  MakeBoundQuery
    [regression_binding; regression_later_error_binding]
    regression_body.

Definition regression_two_error_schemas : list LocalQuerySchema :=
  [local_query_binding_schema regression_binding;
   local_query_binding_schema regression_later_error_binding].

Example first_binding_error_short_circuits_later_bindings :
  eval_bound_query_possible_outcome
    init_db regression_two_error_schemas nil regression_two_error_bound_query
    (SqlError UndefinedFunction) /\
  ~ eval_bound_query_possible_outcome
      init_db regression_two_error_schemas nil regression_two_error_bound_query
      (SqlError UndefinedColumn).
Proof.
split.
- exists regression_schedule.
  cbn [regression_two_error_bound_query regression_binding
    regression_later_error_binding regression_body
    eval_local_query_bindings_with_schedule].
  left; exists UndefinedFunction; split; [constructor|reflexivity].
- intros [schedule Heval].
  cbn [regression_two_error_bound_query regression_binding
    regression_later_error_binding regression_body
    eval_local_query_bindings_with_schedule] in Heval.
  destruct Heval as
    [[error [Hfirst Houtcome]] | [rows [Hfirst _]]].
  + inversion Hfirst; subst; discriminate Houtcome.
  + inversion Hfirst.
Qed.

Example unused_error_binding_is_not_runtime_safe :
  ~ bound_query_runtime_safe
      init_db [regression_binding_schema] nil regression_bound_query.
Proof.
intros [_ Hno_errors].
apply (Hno_errors UndefinedFunction).
exact eager_binding_relation_exposes_definition_error.
Qed.

Example a_common_eager_error_is_not_a_trusted_outcome_equivalence :
  ~ bound_query_program_demand_safe_outcome_equiv
      init_db [regression_binding_schema] nil
      [regression_bound_query] [regression_bound_query].
Proof.
intros [Hsource_safe _].
cbn in Hsource_safe.
destruct Hsource_safe as [Hquery_safe _].
exact (unused_error_binding_is_not_runtime_safe Hquery_safe).
Qed.

Example an_always_failing_prefix_has_no_reachable_body_outcome :
  forall outcome,
    ~ eval_bound_query_body_possible_outcome
        init_db [regression_binding_schema] nil regression_bound_query outcome.
Proof.
intros outcome [schedule [reached [Hreach _]]].
inversion Hreach as
  [|db binding rest rows reached' Hbinding Hrest]; subst.
inversion Hbinding.
Qed.

Example an_unreachable_body_is_not_vacuously_liftable :
  ~ bound_query_body_possible_outcome_lift
      init_db [regression_binding_schema] nil
      regression_bound_query regression_bound_query.
Proof.
intros [_ [_ [[outcome Houtcome] _]]].
exact (an_always_failing_prefix_has_no_reachable_body_outcome
  outcome Houtcome).
Qed.

Example unbound_query_reuses_the_existing_possible_outcome_interface :
  forall outcome,
    eval_bound_query_possible_outcome init_db nil nil
      (MakeBoundQuery nil regression_body) outcome <->
    eval_query_expr_outcome_in_state init_db regression_body outcome.
Proof.
intro outcome; apply eval_bound_query_without_bindings.
Qed.

Definition regression_x : attribute TNull := AttrZ "binding_x".
Definition regression_y : attribute TNull := AttrBool "binding_y".

Definition regression_empty_rows (outputs : list (attribute TNull)) : QueryExpr :=
  @QExpr_Values TNull relname outputs
    (Febag.empty (Fecol.CBag (CTuple TNull))).

Definition regression_good_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_good_cte") nil (regression_empty_rows nil).

Example successful_local_binding_is_installed_as_exactly_one_bag :
  forall rows,
    @_instance TNull
      (set_local_query_binding_rows init_db regression_good_binding rows)
      (Rel "__logos_good_cte") = query_rows_bag rows.
Proof.
intro rows.
unfold set_local_query_binding_rows, regression_good_binding.
cbn; reflexivity.
Qed.

Definition regression_good_schema : LocalQuerySchema :=
  local_query_binding_schema regression_good_binding.

Definition regression_safe_bound_query : BoundQuery :=
  MakeBoundQuery [regression_good_binding] regression_body.

Definition regression_unbound_error_query : BoundQuery :=
  MakeBoundQuery nil
    (@QExpr_Error TNull relname nil UndefinedColumn).

Definition regression_mixed_outcome_program : BoundQueryProgram :=
  [regression_safe_bound_query; regression_unbound_error_query].

Lemma regression_safe_bound_query_runtime_safe :
  bound_query_runtime_safe init_db [regression_good_schema] nil
    regression_safe_bound_query.
Proof.
split.
- exists nil, regression_schedule.
  cbn [regression_safe_bound_query regression_good_binding
    regression_empty_rows regression_body
    eval_local_query_bindings_with_schedule].
  right; exists nil; split.
  + apply EQuery_Values.
    unfold query_same_rows_as_bag, query_rows_bag.
    apply Febag.equal_refl.
  + apply EQuery_Values.
    unfold query_same_rows_as_bag, query_rows_bag.
    apply Febag.equal_refl.
- intros error [schedule Heval].
  cbn [regression_safe_bound_query regression_good_binding
    regression_empty_rows regression_body
    eval_local_query_bindings_with_schedule] in Heval.
  destruct Heval as
    [[binding_error [Hbinding _]] | [rows [Hbinding Hbody]]].
  + inversion Hbinding.
  + inversion Hbody.
Qed.

Lemma regression_safe_bound_query_body_outcome :
  eval_bound_query_body_possible_outcome
    init_db [regression_good_schema] nil regression_safe_bound_query
    (SqlSuccess nil).
Proof.
unfold eval_bound_query_body_possible_outcome.
exists regression_schedule.
exists (set_local_query_binding_rows
  (declare_local_query_schemas init_db [regression_good_schema])
  regression_good_binding nil).
split.
- cbn [regression_safe_bound_query].
  apply LocalQueryBindingsReachableCons with (rows := nil).
  + apply EQuery_Values.
    unfold regression_good_binding, regression_empty_rows,
      query_same_rows_as_bag, query_rows_bag.
    apply Febag.equal_refl.
  + constructor.
- apply EQuery_Values.
  unfold regression_safe_bound_query, regression_body,
    query_same_rows_as_bag, query_rows_bag.
  apply Febag.equal_refl.
Qed.

Lemma regression_safe_bound_query_body_lift :
  bound_query_body_possible_outcome_lift
    init_db [regression_good_schema] nil
    regression_safe_bound_query regression_safe_bound_query.
Proof.
apply bound_query_body_possible_outcome_lift_refl.
exists (SqlSuccess nil).
exact regression_safe_bound_query_body_outcome.
Qed.

Example reachable_body_possible_outcomes_lift_through_local_bindings :
  bound_query_possible_outcome_equiv
    init_db [regression_good_schema] nil
    regression_safe_bound_query regression_safe_bound_query.
Proof.
apply bound_query_body_possible_outcome_lift_sound.
exact regression_safe_bound_query_body_lift.
Qed.

Example reachable_body_program_lift_keeps_materialization_safety_explicit :
  bound_query_program_demand_safe_outcome_equiv
    init_db [regression_good_schema] nil
    [regression_safe_bound_query] [regression_safe_bound_query].
Proof.
apply bound_query_program_body_possible_outcome_lift_demand_safe.
- cbn; split; [exact regression_safe_bound_query_body_lift|exact I].
- cbn [bound_query_materialization_safe regression_safe_bound_query].
  split; [exact regression_safe_bound_query_runtime_safe|exact I].
- cbn [bound_query_materialization_safe regression_safe_bound_query].
  split; [exact regression_safe_bound_query_runtime_safe|exact I].
Qed.

Lemma regression_unbound_error_outcome :
  eval_bound_query_possible_outcome init_db [regression_good_schema] nil
    regression_unbound_error_query (SqlError UndefinedColumn).
Proof.
exists regression_schedule.
cbn [regression_unbound_error_query eval_local_query_bindings_with_schedule].
constructor.
Qed.

Example mixed_bound_program_preserves_an_unbound_root_error :
  bound_query_program_demand_safe_outcome_equiv
    init_db [regression_good_schema] nil
    regression_mixed_outcome_program regression_mixed_outcome_program.
Proof.
unfold bound_query_program_demand_safe_outcome_equiv.
split.
- cbn [regression_mixed_outcome_program
    bound_query_program_materialization_safe
    bound_query_materialization_safe regression_safe_bound_query
    regression_unbound_error_query].
  split; [exact regression_safe_bound_query_runtime_safe | split; exact I].
- split.
  + cbn [regression_mixed_outcome_program
      bound_query_program_materialization_safe
      bound_query_materialization_safe regression_safe_bound_query
      regression_unbound_error_query].
    split; [exact regression_safe_bound_query_runtime_safe | split; exact I].
  + cbn [regression_mixed_outcome_program
      bound_query_program_possible_outcome_equiv].
    split.
    * unfold bound_query_possible_outcome_equiv; split; [reflexivity|].
      apply outcome_relation_equiv_refl.
      -- intro rows; apply ordered_rows_equiv_refl.
      -- destruct regression_safe_bound_query_runtime_safe as
           [[rows Hsuccess] _].
         now exists (SqlSuccess rows).
    * split.
      -- unfold bound_query_possible_outcome_equiv; split; [reflexivity|].
         apply outcome_relation_equiv_refl.
         ++ intro rows; apply ordered_rows_equiv_refl.
         ++ exists (SqlError UndefinedColumn).
            exact regression_unbound_error_outcome.
      -- exact I.
Qed.

Example binding_root_analysis_error_is_rejected :
  ~ local_query_binding_admissible
      init_db [regression_binding_schema] regression_binding.
Proof.
intros [_ [_ [Herror _]]].
discriminate Herror.
Qed.

Definition regression_root_error_bound_query : BoundQuery :=
  MakeBoundQuery [regression_good_binding]
    (@QExpr_Error TNull relname nil UndefinedColumn).

Example body_root_analysis_error_requires_no_bindings :
  ~ bound_query_admissible init_db [regression_good_schema]
      regression_root_error_bound_query.
Proof.
intros [_ [_ [_ [_ [_ [Hroot _]]]]]].
discriminate Hroot.
Qed.

Definition regression_collision_db : db_state :=
  @mk_state TNull [Rel "__logos_good_cte"]
    (@_basesort TNull init_db) (@_instance TNull init_db).

Example local_schema_cannot_shadow_a_base_relation :
  ~ bound_query_admissible regression_collision_db [regression_good_schema]
      (MakeBoundQuery [regression_good_binding] regression_body).
Proof.
intros [_ [Hfresh _]].
unfold local_query_schemas_fresh, regression_good_schema,
  regression_good_binding, local_query_binding_schema,
  local_query_schema_relations, regression_collision_db in Hfresh.
cbn in Hfresh.
inversion Hfresh as [|relation relations Habsent _]; subst.
apply Habsent; now left.
Qed.

Definition regression_later_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_later_cte") [regression_x]
    (regression_empty_rows [regression_x]).

Definition regression_forward_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_forward_cte") [regression_x]
    (@QExpr_Table TNull relname [regression_x] (Rel "__logos_later_cte")).

Definition regression_forward_bound_query : BoundQuery :=
  MakeBoundQuery [regression_forward_binding; regression_later_binding]
    (regression_empty_rows nil).

Definition regression_forward_schemas : list LocalQuerySchema :=
  [local_query_binding_schema regression_forward_binding;
   local_query_binding_schema regression_later_binding].

Example forward_local_reference_is_rejected :
  ~ bound_query_admissible init_db regression_forward_schemas
      regression_forward_bound_query.
Proof.
intros [_ [_ [_ [_ [Hreferences _]]]]].
unfold bound_query_local_references_well_formed,
  regression_forward_bound_query, regression_forward_schemas,
  regression_forward_binding, regression_later_binding,
  query_local_references_allowed in Hreferences.
cbn [local_query_schema_relations local_query_binding_relations
  local_query_binding_dependencies_well_formed
  query_expr_table_references] in Hreferences.
destruct Hreferences as [[Hfirst _] _].
inversion Hfirst as [|reference references Hallowed _]; subst.
specialize (Hallowed (or_intror (or_introl eq_refl))).
destruct Hallowed as [Havailable _].
exact Havailable.
Qed.

Definition regression_ordered_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_ordered_cte") [regression_x; regression_y]
    (regression_empty_rows [regression_x; regression_y]).

Definition regression_swapped_body : QueryExpr :=
  @QExpr_Table TNull relname [regression_y; regression_x]
    (Rel "__logos_ordered_cte").

Definition regression_swapped_bound_query : BoundQuery :=
  MakeBoundQuery [regression_ordered_binding] regression_swapped_body.

Example local_reference_requires_the_exact_ordered_signature :
  ~ bound_query_admissible init_db
      [local_query_binding_schema regression_ordered_binding]
      regression_swapped_bound_query.
Proof.
intros [_ [_ [_ [_ [Hreferences _]]]]].
unfold bound_query_local_references_well_formed,
  regression_swapped_bound_query, regression_ordered_binding,
  regression_swapped_body, query_local_references_allowed in Hreferences.
cbn [local_query_schema_relations local_query_binding_relations
  local_query_binding_dependencies_well_formed
  query_expr_table_references] in Hreferences.
destruct Hreferences as [_ Hbody].
inversion Hbody as [|reference references Hallowed _]; subst.
specialize (Hallowed (or_introl eq_refl)).
destruct Hallowed as [_ Hschema].
destruct Hschema as [Hequal | Habsent]; [discriminate Hequal | exact Habsent].
Qed.

Definition regression_site_truth (site : boolean_site) :
    @scalar_expr TNull relname ScalarResultBoolean :=
  SExpr_ConjList [nil; [site]] And_F [SExpr_True; SExpr_True].

Definition regression_site_query (site : boolean_site) : QueryExpr :=
  QExpr_Filter (regression_site_truth site) (regression_empty_rows nil).

Definition regression_site_binding : LocalQueryBinding :=
  MakeLocalQueryBinding
    (Rel "__logos_site_cte") nil (regression_site_query "shared-site").

Definition regression_reused_site_bound_query : BoundQuery :=
  MakeBoundQuery [regression_site_binding]
    (regression_site_query "shared-site").

Example bound_components_cannot_reuse_a_boolean_site :
  ~ bound_query_admissible init_db
      [local_query_binding_schema regression_site_binding]
      regression_reused_site_bound_query.
Proof.
intros [_ [_ [_ [_ [_ [_ [Hsites _]]]]]]].
unfold bound_query_boolean_sites, regression_reused_site_bound_query,
  regression_site_binding, regression_site_query, regression_site_truth in Hsites.
cbn [query_expr_boolean_sites scalar_expr_boolean_sites] in Hsites.
destruct Hsites as [Hnodup _].
inversion Hnodup as [|head tail Hfresh _]; subst.
apply Hfresh; now left.
Qed.

Example empty_boolean_site_is_rejected :
  ~ TNullQueryExprAdmissible (@_basesort TNull init_db)
      (regression_site_query "").
Proof.
intros [_ [_ Hsites]].
unfold query_expr_boolean_sites_well_formed, regression_site_query,
  regression_site_truth in Hsites.
cbn [query_expr_boolean_sites scalar_expr_boolean_sites] in Hsites.
destruct Hsites as [_ Hnonempty].
inversion Hnonempty as [|site sites Hsite _]; subst.
apply Hsite; reflexivity.
Qed.

Definition regression_empty_conjunction :
    @scalar_expr TNull relname ScalarResultBoolean :=
  SExpr_ConjList nil And_F nil.

Example empty_boolean_operand_list_is_rejected :
  ~ TNullScalarExprAdmissible (@_basesort TNull init_db)
      ScalarPhaseWhere regression_empty_conjunction.
Proof.
intros [Hshape _].
unfold regression_empty_conjunction in Hshape.
cbn [scalar_expr_admissible] in Hshape.
apply (proj1 Hshape); reflexivity.
Qed.

Example root_analysis_error_remains_canonical :
  TNullQueryExprAdmissible (@_basesort TNull init_db)
    (@QExpr_Error TNull relname nil UndefinedColumn).
Proof.
unfold TNullQueryExprAdmissible.
repeat split; constructor.
Qed.

Example nested_query_analysis_error_is_rejected :
  ~ TNullQueryExprAdmissible (@_basesort TNull init_db)
      (QExpr_Filter SExpr_True
        (@QExpr_Error TNull relname nil UndefinedColumn)).
Proof.
intros [_ [Herror _]].
discriminate Herror.
Qed.

Definition regression_error_subquery :
    @scalar_expr TNull relname ScalarResultValue :=
  @SExpr_Subquery TNull relname type_Z (Value_Z None)
    (@QExpr_Error TNull relname [regression_x] UndefinedColumn).

Example scalar_subquery_analysis_error_is_rejected :
  ~ TNullScalarExprAdmissible (@_basesort TNull init_db)
      ScalarPhaseSelect regression_error_subquery.
Proof.
intros [_ [Herror _]].
discriminate Herror.
Qed.

Definition regression_two_column_subquery : QueryExpr :=
  regression_empty_rows [regression_x; AttrZ "binding_z"].

Definition regression_zero_left_quantifier :
    @scalar_expr TNull relname ScalarResultBoolean :=
  @SExpr_Quant TNull relname Exists_F PredicateEq nil
    regression_two_column_subquery.

Definition regression_two_left_quantifier :
    @scalar_expr TNull relname ScalarResultBoolean :=
  @SExpr_Quant TNull relname Exists_F PredicateEq
    [@SExpr_Leaf TNull relname type_Z
       (AExpr (Constant (Value_Z (Some 1))));
     @SExpr_Leaf TNull relname type_Z
       (AExpr (Constant (Value_Z (Some 2))))]
    (regression_empty_rows nil).

Example quantified_comparison_rejects_zero_left_two_right :
  ~ TNullScalarExprAdmissible (@_basesort TNull init_db)
      ScalarPhaseWhere regression_zero_left_quantifier.
Proof.
intros [Hshape _].
unfold regression_zero_left_quantifier in Hshape.
cbn [scalar_expr_admissible] in Hshape.
destruct Hshape as [_ [_ [_ [Hnonempty _]]]].
apply Hnonempty; reflexivity.
Qed.

Example quantified_comparison_rejects_two_left_zero_right :
  ~ TNullScalarExprAdmissible (@_basesort TNull init_db)
      ScalarPhaseWhere regression_two_left_quantifier.
Proof.
intros [Hshape _].
unfold regression_two_left_quantifier in Hshape.
cbn [scalar_expr_admissible] in Hshape.
destruct Hshape as [_ [_ [_ [_ [Harity _]]]]].
discriminate Harity.
Qed.
