(******************************************************************************)
(** Type-level regression checks for the unified proof-agent facade.         **)
(******************************************************************************)

From SQLFS Require Import SqlSyntax GenericInstance Values Bool3 Env FTuples FiniteSet FiniteBag FiniteCollection OrderedSet SqlBagAbstraction
  SqlErrorSemantics SqlOutcome SqlOrder SqlQuerySyntax SqlQuerySemantics
  SqlQueryFacts SqlQueryContexts SchemaConstraints.
From Logos.FormalSQL Require Import
  TNullSyntax QueryTNullSyntax SchemaCardinality QueryCardinality
  CardinalityCombinators OrderedQueryFacts
  GroupingRewriteFacts RelationalAlgebraFacts GroupedFilterOutcomeFacts
  NumericRegroupFacts
  ProofAgentFacade.
From Stdlib Require Import List String NArith SetoidList Lia.

Import ListNotations.
Import Tuple.

Section FacadeRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variable outputs : list TNullAttribute.
Variable error : sql_runtime_error.

(** The facade exposes the authoritative QueryExpr outcome relation directly;
    no compact-query reset or inter-AST bridge is involved. *)
Example tnull_query_expr_error_regression :
  TNullQueryExprOutcome db env
    (QExpr_Error outputs error) (SqlError error).
Proof.
unfold TNullQueryExprOutcome, eval_query_expr_outcome_in_env.
constructor.
Qed.

Example tnull_row_extensional_refl :
  forall row, TNullRowEq row row.
Proof.
intro row; apply tnull_row_eq_of_labels_and_values.
- unfold TNullAttributeSetEq; apply Fset.equal_refl.
- intros; reflexivity.
Qed.

Variables single outer inner : TNullSelectList.
Variable bag : TNullRowBag.
Hypothesis projection_composition :
  forall row,
    In row (Febag.elements TNullRowBagRecord bag) ->
    TNullRowEq
      (TNullProjectRow env single row)
      (TNullProjectRow env outer (TNullProjectRow env inner row)).

Example tnull_single_double_projection_bag_regression :
  TNullBagEq
    (TNullBagMap (fun row => TNullProjectRow env single row) bag)
    (TNullBagMap
      (fun row => TNullProjectRow env outer row)
      (TNullBagMap (fun row => TNullProjectRow env inner row) bag)).
Proof.
apply tnull_single_double_projection_bag_eq.
exact projection_composition.
Qed.

End FacadeRegression.

Section ObservationCertificateRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables left right : TNullQueryExpr.
Variables left_rows right_rows : list TNullRow.

(** Functionality is stated modulo SQL's exact ordered-row observation, not
    Leibniz equality of the tuple representation. *)
Hypothesis left_functional :
  forall first second,
    TNullQueryExprOutcome db env left (SqlSuccess first) ->
    TNullQueryExprOutcome db env left (SqlSuccess second) ->
    TNullRowsObservationEq first second.

Example tnull_observation_functionality_regression :
  TNullQueryExprObservationFunctional db env left.
Proof.
exact left_functional.
Qed.

Hypothesis left_witness :
  TNullQueryExprOutcome db env left (SqlSuccess left_rows).

Hypothesis right_bag_functional :
  TNullQuerySuccessBagFunctional db env right.
Hypothesis left_witness_separates :
  forall candidate,
    TNullQueryExprOutcome db env right (SqlSuccess candidate) ->
    ~ TNullRowsObservationEq left_rows candidate.

(** The witness is compared with every legal right success.  This remains a
    valid certificate even when either query has several possible lists. *)
Example tnull_left_success_separation_regression :
  TNullQueryExprOutcomeSeparation db env left right.
Proof.
eapply OutcomeSeparationLeftSuccess.
- exact left_witness.
- exact left_witness_separates.
Qed.

Hypothesis right_witness :
  TNullQueryExprOutcome db env right (SqlSuccess right_rows).
Hypothesis right_witness_separates :
  forall candidate,
    TNullQueryExprOutcome db env left (SqlSuccess candidate) ->
    ~ TNullRowsObservationEq candidate right_rows.

Example tnull_right_success_separation_regression :
  TNullQueryExprOutcomeSeparation db env left right.
Proof.
eapply OutcomeSeparationRightSuccess.
- exact right_witness.
- exact right_witness_separates.
Qed.

Variable observed_error : sql_runtime_error.
Hypothesis left_error_witness :
  TNullQueryExprOutcome db env left (SqlError observed_error).
Hypothesis right_lacks_left_error :
  ~ TNullQueryExprOutcome db env right (SqlError observed_error).

Example tnull_left_error_separation_regression :
  TNullQueryExprOutcomeSeparation db env left right.
Proof.
eapply OutcomeSeparationLeftError;
  eassumption.
Qed.

Hypothesis right_error_witness :
  TNullQueryExprOutcome db env right (SqlError observed_error).
Hypothesis left_lacks_right_error :
  ~ TNullQueryExprOutcome db env left (SqlError observed_error).

Example tnull_right_error_separation_regression :
  TNullQueryExprOutcomeSeparation db env left right.
Proof.
eapply OutcomeSeparationRightError;
  eassumption.
Qed.

Example tnull_separation_refutes_outcome_equivalence_regression :
  ~ TNullQueryExprOutcomeEq db env left right.
Proof.
apply tnull_query_expr_outcome_separation_sound.
exact tnull_left_success_separation_regression.
Qed.

Hypothesis observed_bags_differ :
  ~ TNullBagEq (TNullRowsBag left_rows) (TNullRowsBag right_rows).

Example tnull_functional_bag_difference_separation_regression :
  TNullQueryExprOutcomeSeparation db env left right.
Proof.
eapply tnull_query_expr_outcome_separation_of_right_functional_bag_difference;
  eassumption.
Qed.

Variables left_tail right_tail : TNullQueryProgram.

Example tnull_program_head_separation_regression :
  ~ TNullQueryProgramOutcomeEq db env
      (left :: left_tail) (right :: right_tail).
Proof.
apply tnull_query_program_head_separation_sound.
exact tnull_left_success_separation_regression.
Qed.

Variables left_prefix right_prefix : TNullQueryProgram.
Hypothesis prefixes_have_equal_length :
  length left_prefix = length right_prefix.

Example tnull_program_later_statement_separation_regression :
  ~ TNullQueryProgramOutcomeEq db env
      (left_prefix ++ left :: left_tail)
      (right_prefix ++ right :: right_tail).
Proof.
eapply tnull_query_program_prefix_separation_sound.
- exact prefixes_have_equal_length.
- exact tnull_left_success_separation_regression.
Qed.

End ObservationCertificateRegression.

Section ProjectionFusionContractBridgeRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables single outer inner : TNullSelectList.
Variable input : TNullQueryExpr.

Hypothesis total_projection_composition :
  forall row,
    TNullRowEq
      (TNullProjectRow env single row)
      (TNullProjectRow env outer (TNullProjectRow env inner row)).

(** The optional all-row bridge discharges the named residual contract while
    leaving its original reachable-bag formulation unchanged. *)
Example tnull_project_fusion_contract_of_row_eq_regression :
  @project_fusion_success_bag_contract TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env single outer inner input.
Proof.
apply tnull_project_fusion_success_bag_contract_of_row_eq.
exact total_projection_composition.
Qed.

End ProjectionFusionContractBridgeRegression.

Section DirectProjectionFusionBridgeRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables single outer inner : TNullSelectList.
Variable input : TNullQueryExpr.

Hypothesis direct_fusion_outputs :
  TNullAttributeSetEq
    (@Projection.select_list_sort TNull single)
    (@Projection.select_list_sort TNull outer).

Hypothesis direct_fusion_lookups :
  forall target,
    target inS (@Projection.select_list_sort TNull single) ->
    exists source middle,
      TNullSelectLookup single target = Some (AExpr (Dot source)) /\
      TNullSelectLookup inner middle = Some (AExpr (Dot source)) /\
      TNullSelectLookup outer target = Some (AExpr (Dot middle)).

(** The lookup contract has no row-label premise, so this quantifies over
    rows where the source may be absent and correlated fallback is observable. *)
Example tnull_direct_projection_fusion_row_regression :
  forall row,
    TNullRowEq
      (TNullProjectRow env single row)
      (TNullProjectRow env outer (TNullProjectRow env inner row)).
Proof.
apply tnull_direct_projection_fusion_row_eq;
  assumption.
Qed.

(** The row law feeds the reusable residual bridge without reopening any
    finite-bag representation or reachable-row side condition. *)
Example tnull_direct_projection_fusion_contract_regression :
  @project_fusion_success_bag_contract TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env single outer inner input.
Proof.
apply tnull_project_fusion_success_bag_contract_of_row_eq.
apply tnull_direct_projection_fusion_row_eq;
  assumption.
Qed.

Example tnull_select_columns_lookup_output_regression :
  forall columns attribute,
    attribute inS
      (@Projection.select_list_sort TNull (SelectColumns columns)) ->
    TNullSelectLookup (SelectColumns columns) attribute =
      Some (AExpr (Dot attribute)).
Proof.
apply tnull_select_columns_lookup_output.
Qed.

Example tnull_select_columns_projection_fusion_regression :
  forall env single outer inner,
    TNullAttributeSetEq
      (@Projection.select_list_sort TNull (SelectColumns single))
      (@Projection.select_list_sort TNull (SelectColumns outer)) ->
    (@Projection.select_list_sort TNull (SelectColumns outer)) subS
      (@Projection.select_list_sort TNull (SelectColumns inner)) ->
    forall row,
      TNullRowEq
        (TNullProjectRow env (SelectColumns single) row)
        (TNullProjectRow env (SelectColumns outer)
          (TNullProjectRow env (SelectColumns inner) row)).
Proof.
apply tnull_select_columns_projection_fusion_row_eq.
Qed.

End DirectProjectionFusionBridgeRegression.

Section DeterministicAssemblyTacticRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables left right : TNullQueryExpr.
Variable select_list : TNullSelectList.
Variable keys : list (sort_key TNull).

Hypothesis core_equivalence :
  TNullQueryExprOutcomeEq db env left right.
Hypothesis select_list_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) select_list = None.

(** The unified tactic removes identical unary structure and reuses explicit
    core and projection-safety hypotheses already present in the context. *)
Example shared_outcome_shell_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Project select_list
      (QExpr_OrderBy keys
        (QExpr_Fetch 2 (QExpr_Distinct left))))
    (QExpr_Project select_list
      (QExpr_OrderBy keys
        (QExpr_Fetch 2 (QExpr_Distinct right)))).
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
logos.
Qed.

(** Definitionally safe projections do not leave a spurious side goal. *)
Example definitional_projection_safety_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Project (SelectList []) left)
    (QExpr_Project (SelectList []) right).
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
logos.
Qed.

(** A restoring Project can hide incompatible ordered child signatures.  In
    the absence of a child alignment fact, [logos] must keep that outer
    semantic boundary instead of speculatively descending to an impossible
    child outcome-equivalence goal. *)
Example restoring_project_does_not_force_child_signature_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Project (SelectList [])
      (QExpr_OrderBy keys
        (@QExpr_Table TNull relname
          [AttrInt32 "left_only"] (Rel "left_table"))))
    (QExpr_Project (SelectList [])
      (QExpr_OrderBy keys
        (@QExpr_Table TNull relname
          [AttrInt32 "right_only"] (Rel "right_table")))).
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
logos.
lazymatch goal with
| |- @query_expr_outcome_equiv _ _ _ _ _ _ _ _ _
      (QExpr_Project _ _) (QExpr_Project _ _) => idtac
| _ => fail "logos crossed an unaligned restoring-Project boundary"
end.
Abort.

(** DISTINCT is itself structurally bag-closed, but an already available exact
    child equivalence is the cheaper proof.  The transactional fast path must
    close this goal before the partial bag bridge commits. *)
Example exact_core_precedes_bag_bridge_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Distinct left)
    (QExpr_Distinct right).
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
logos.
Qed.

Variable rank_attribute : TNullAttribute.

(** OFFSET and RANK exercise two other shared-shell branches.  RANK remains
    error exact: its congruence theorem transports the modeled BIGINT embedding
    failure rather than treating the operator as a pure list map. *)
Example shared_rank_offset_shell_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Offset 1
      (RankExpr [] keys rank_attribute left))
    (QExpr_Offset 1
      (RankExpr [] keys rank_attribute right)).
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
logos.
Qed.

Variables left_select right_select : TNullSelectList.
Hypothesis extensional_outputs :
  Projection.select_list_outputs left_select =
  Projection.select_list_outputs right_select.
Hypothesis left_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) left_select = None.
Hypothesis right_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) right_select = None.
Hypothesis extensional_projection :
  forall input_rows row,
    TNullQueryExprOutcome db env right (SqlSuccess input_rows) ->
    In row input_rows ->
    Oeset.compare (OTuple TNull)
      (Projection.projection TNull (env_t TNull env row)
        (@Projection.Select_List TNull left_select))
      (Projection.projection TNull (env_t TNull env row)
        (@Projection.Select_List TNull right_select)) = Eq.

(** The generic extensional Project law changes both the child and the SELECT
    list without encoding a nested-project rewrite shape. *)
Example extensional_project_congruence_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Project left_select left)
    (QExpr_Project right_select right).
Proof.
unfold TNullQueryExprOutcomeEq, TNullQueryExprOutcome,
  query_expr_outcome_equiv_in_env, eval_query_expr_outcome_in_env in *.
eapply query_expr_project_outcome_equiv_congr_extensional_safe;
  eassumption.
Qed.

Variables outputs : list TNullAttribute.
Variables first_table second_table : relname.

Definition structurally_safe_query : TNullQueryExpr :=
  QExpr_Project (SelectList [])
    (QExpr_Offset 1
      (QExpr_Fetch 2
        (QExpr_OrderBy keys
          (QExpr_Distinct
            (QExpr_Set Union
              (QExpr_Table outputs first_table)
              (QExpr_Table outputs second_table)))))).

Definition structurally_cross_query : TNullQueryExpr :=
  QExpr_CrossJoin
    (QExpr_Table outputs first_table)
    (QExpr_Table outputs second_table).

Definition structurally_reset_query : TNullQueryExpr :=
  QExpr_Distinct (QExpr_Table outputs first_table).

Definition structurally_error_query : TNullQueryExpr :=
  QExpr_Fetch 2
    (QExpr_Offset 1
      (QExpr_OrderBy keys
        (QExpr_Distinct
          (QExpr_Error outputs (DataException DivisionByZero))))).

Variable alternate_keys : list (sort_key TNull).

Definition distinct_order_left : TNullQueryExpr :=
  QExpr_Distinct
    (QExpr_OrderBy keys (QExpr_Table outputs first_table)).

Definition distinct_order_right : TNullQueryExpr :=
  QExpr_Distinct
    (QExpr_OrderBy alternate_keys (QExpr_Table outputs first_table)).

Hypothesis distinct_order_success_bags :
  rel_equiv
    (@query_success_bags TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env distinct_order_left)
    (@query_success_bags TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env distinct_order_right).

(** DISTINCT resets the child order.  Even with different ORDER BY keys below
    it, [logos] must choose the certified bag boundary before attempting the
    strictly stronger child ordered-outcome congruence. *)
Example bag_reset_precedes_shared_shell_regression :
  TNullQueryExprOutcomeEq db env distinct_order_left distinct_order_right.
Proof.
unfold TNullQueryExprOutcomeEq, TNullQueryExprOutcome,
  query_expr_outcome_equiv_in_env, eval_query_expr_outcome_in_env,
  distinct_order_left, distinct_order_right in *.
logos.
Qed.

(** Success and safety automation follows only operators with a proven
    compositional contract and terminates at the two total table leaves. *)
Example structural_success_regression :
  @query_expr_has_success TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env structurally_safe_query.
Proof.
unfold structurally_safe_query.
logos.
Qed.

Example structural_runtime_safety_regression :
  @query_expr_runtime_safe TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env structurally_safe_query.
Proof.
unfold structurally_safe_query.
logos.
Qed.

Example structural_outcome_regression :
  exists outcome,
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env structurally_safe_query outcome.
Proof.
unfold structurally_safe_query.
logos.
Qed.

Example cross_join_success_regression :
  @query_expr_has_success TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env structurally_cross_query.
Proof.
unfold structurally_cross_query.
logos.
Qed.

Example cross_join_runtime_safety_regression :
  @query_expr_runtime_safe TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env structurally_cross_query.
Proof.
unfold structurally_cross_query.
logos.
Qed.

(** Outcome construction is not secretly success construction: an explicit
    SQL error remains a valid inhabited outcome through transparent shells. *)
Example structural_error_outcome_regression :
  exists outcome,
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env structurally_error_query outcome.
Proof.
unfold structurally_error_query.
logos.
Qed.

(** The bag bridge leaves only success inhabitation as a semantic obligation
    for this reflexive reset query; closure, bag relation, and errors are
    discharged through their exact public interfaces. *)
Example structural_bag_outcome_regression :
  TNullQueryExprOutcomeEq db env
    structurally_reset_query structurally_reset_query.
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env,
  structurally_reset_query.
logos.
Qed.

(** Project and Filter are transparent to the certified closure analysis;
    CROSS JOIN supplies the inner bag reset. *)
Example structural_bag_closed_regression :
  BagClosed TNull
    (fun rows =>
      @eval_query_expr_outcome TNull relname
        (@_basesort TNull db) (@_instance TNull db) unknown3
        NullValues.interp_scalar_operator_runtime_error
        NullValues.interp_aggregate_runtime_error NullValues.is_null_value
        env
        (QExpr_Project (SelectList [])
          (QExpr_Filter FExpr_True
            (QExpr_CrossJoin
              (QExpr_Table outputs first_table)
              (QExpr_Table outputs second_table))))
        (SqlSuccess rows)).
Proof.
logos.
Qed.

(** The public dispatcher removes a mechanical outer shell even when the
    child is a semantic operator.  The caller supplies only the irreducible
    FILTER fact; no separate "project success" tactic must be discovered. *)
Hypothesis semantic_filter_success :
  @query_expr_has_success TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env (QExpr_Filter FExpr_True (QExpr_Table outputs first_table)).

Example structural_success_partial_peel_regression :
  @query_expr_has_success TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env
    (QExpr_Project (SelectList [])
      (QExpr_Filter FExpr_True (QExpr_Table outputs first_table))).
Proof.
logos.
Qed.

Variable semantic_left semantic_right : TNullQueryExpr.
Hypothesis semantic_core_outcome :
  TNullQueryExprOutcomeEq db env semantic_left semantic_right.

(** The same interface transports an exact semantic core through a shared
    order-sensitive prefix and stops at the supplied core theorem. *)
Example structural_shared_context_partial_peel_regression :
  TNullQueryExprOutcomeEq db env
    (QExpr_Project (SelectList []) (QExpr_Fetch 3
      (QExpr_OrderBy keys semantic_left)))
    (QExpr_Project (SelectList []) (QExpr_Fetch 3
      (QExpr_OrderBy keys semantic_right))).
Proof.
unfold TNullQueryExprOutcomeEq, query_expr_outcome_equiv_in_env in *.
logos.
Qed.

(** Error normalization removes only constructors whose exact error law has
    no side condition. *)
Example forwarded_error_normalization_regression :
  forall error,
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (QExpr_Fetch 2 (QExpr_OrderBy keys (QExpr_Distinct left)))
      (SqlError error) <->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env left (SqlError error).
Proof.
intro error.
logos.
Qed.

Example forwarded_error_hypothesis_regression :
  forall error,
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env (QExpr_Fetch 2 (QExpr_OrderBy keys (QExpr_Distinct left)))
      (SqlError error) ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env left (SqlError error).
Proof.
intros error Herror.
logos in Herror.
exact Herror.
Qed.

(** The inversion tactic consumes the unary Project/FETCH/ORDER BY/DISTINCT
    prefix and intentionally stops at the binary SET node. *)
Example transparent_success_inversion_regression :
  forall output,
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env structurally_safe_query (SqlSuccess output) ->
    True.
Proof.
intros output Hsuccess.
unfold structurally_safe_query in Hsuccess.
logos in Hsuccess.
exact I.
Qed.

Variable row_map : TNullRow -> sql_outcome TNullRow.

(** RowMap and Filter are safe to invert through exact success iff laws, even
    though neither is guessed by the success-construction tactic. *)
Example row_map_filter_success_inversion_regression :
  forall output,
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env
      (QExpr_RowMap outputs row_map
        (QExpr_Filter FExpr_True
          (QExpr_Table outputs first_table)))
      (SqlSuccess output) ->
    True.
Proof.
intros output Hsuccess.
logos in Hsuccess.
exact I.
Qed.

Variable columns : list ColumnRef.
Variable rows : list TNullRow.

Example direct_columns_local_safety_regression :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) (SelectColumns columns) = None.
Proof.
intro row.
logos.
Qed.

Example direct_columns_aggregate_local_safety_regression :
  @eval_select_list_aggregate_runtime_error TNull
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    env (SelectColumns columns) = None.
Proof.
logos.
Qed.

Example direct_columns_group_keys_local_safety_regression :
  @group_keys_runtime_error TNull
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    env (map DotColumn columns) rows = None.
Proof.
logos.
Qed.

End DeterministicAssemblyTacticRegression.

Section AliasProjectionRegression.

Variable env : TNullEnvironment.
Variable items : list SelectItemT.
Variable source target : TNullAttribute.
Variable row : TNullRow.

Hypothesis selected_alias :
  In (SelectAs (AExpr (Dot source)) target) items.
Hypothesis unique_aliases :
  select_list_has_unique_outputs (SelectList items).
Hypothesis source_present : source inS TNullRowLabels row.

(** The source and output attributes are independent binders: this exercises
    direct renaming rather than the same-name preservation wrapper. *)
Example tnull_direct_projection_alias_regression :
  TNullRowValue (TNullProjectRow env (SelectList items) row) target =
  TNullRowValue row source.
Proof.
eapply tnull_direct_projection_alias_value; eassumption.
Qed.

Example tnull_direct_projection_alias_retained_regression :
  target inS
    TNullRowLabels (TNullProjectRow env (SelectList items) row) /\
  TNullRowValue (TNullProjectRow env (SelectList items) row) target =
    TNullRowValue row source.
Proof.
eapply tnull_direct_projection_alias_retained; eassumption.
Qed.

Variable other : TNullRow.
Hypothesis other_source_present : source inS TNullRowLabels other.
Hypothesis projected_rows_equal :
  TNullRowEq
    (TNullProjectRow env (SelectList items) row)
    (TNullProjectRow env (SelectList items) other).

Example tnull_direct_projection_alias_reflection_regression :
  TNullRowValue row source = TNullRowValue other source.
Proof.
eapply tnull_direct_projection_alias_reflects_value; eassumption.
Qed.

End AliasProjectionRegression.

Section TargetedProjectionLookupRegression.

Variable env : TNullEnvironment.
Variables direct_first_list constant_first_list second : TNullSelectList.
Variables source middle target : TNullAttribute.
Variable row : TNullRow.
Variable value : TNullValue.

Hypothesis direct_first :
  TNullSelectLookup direct_first_list middle = Some (AExpr (Dot source)).
Hypothesis constant_first :
  TNullSelectLookup constant_first_list middle = Some (AExpr (Constant value)).
Hypothesis direct_second :
  TNullSelectLookup second target = Some (AExpr (Dot middle)).

(** No source-presence premise is in scope: the conclusion retains the
    original expression interpretation, including correlated fallback. *)
Example targeted_direct_projection_compose_interp_regression :
  TNullRowValue
    (TNullProjectRow env second
      (TNullProjectRow env direct_first_list row)) target =
  Interp.interp_aggterm TNull (env_t TNull env row)
    (AExpr (Dot source)).
Proof.
eapply tnull_select_lookup_direct_compose_interp_value; eassumption.
Qed.

Hypothesis source_present : source inS TNullRowLabels row.

(** The lookup-only interface does not inspect or normalize unrelated SELECT
    items, which keeps wide generated projections cheap to instantiate. *)
Example targeted_direct_projection_compose_regression :
  target inS
    TNullRowLabels
      (TNullProjectRow env second
        (TNullProjectRow env direct_first_list row)) /\
  TNullRowValue
    (TNullProjectRow env second
      (TNullProjectRow env direct_first_list row)) target =
  TNullRowValue row source.
Proof.
eapply tnull_select_lookup_direct_compose; eassumption.
Qed.

Example targeted_constant_projection_compose_regression :
  target inS
    TNullRowLabels
      (TNullProjectRow env second
        (TNullProjectRow env constant_first_list row)) /\
  TNullRowValue
    (TNullProjectRow env second
      (TNullProjectRow env constant_first_list row)) target = value.
Proof.
eapply tnull_select_lookup_constant_direct_compose; eassumption.
Qed.

End TargetedProjectionLookupRegression.

Section ProjectedAliasPrimaryKeyRegression.

Variable env : TNullEnvironment.
Variable items : list SelectItemT.
Variables source_name target_name : string.
Variable fixed : TNullValue.
Variables raw_rows projected_rows : list TNullRow.
Variable raw_bag : TNullRowBag.

Hypothesis raw_rows_typed :
  Forall
    (row_attribute_present_conforms (Attr_int32 source_name)) raw_rows.
Hypothesis raw_primary_key :
  primary_key_conforms [Attr_int32 source_name] raw_rows.
Hypothesis selected_alias :
  In (SelectAs (DotInt32 source_name) (AttrInt32 target_name)) items.
Hypothesis unique_aliases :
  select_list_has_unique_outputs (SelectList items).
Hypothesis fixed_typed :
  value_conforms_attribute (Attr_int32 source_name) fixed.
Hypothesis raw_represents_bag :
  @query_same_rows_as_bag TNull raw_rows raw_bag.
Hypothesis projected_represents_mapped_bag :
  @query_same_rows_as_bag TNull projected_rows
    (@query_project_bag TNull env (SelectList items) raw_bag).

(** This deliberately uses an arbitrary projected representative rather than
    the literal [map] of [raw_rows]. *)
Example projected_alias_primary_key_match_count_regression :
  (List.length
    (filter
      (fun row =>
        postgres_int32_equal_true fixed
          (TNullRowValue row (Attr_int32 target_name)))
      projected_rows) <= 1)%nat.
Proof.
eapply tnull_projected_alias_int32_primary_key_matches_at_most_one;
  eassumption.
Qed.

End ProjectedAliasPrimaryKeyRegression.

Section PartialFunctionalLeftJoinRegression.

Variable row : TNullRow.
Variables
  (join : TNullRow -> TNullRow -> TNullRow)
  (accept : TNullRow -> TNullRow -> bool)
  (project emit : TNullRow -> TNullRow)
  (pad : TNullRow -> TNullRow).

Hypothesis matched_projection :
  forall left right,
    TNullRowEq (project (join left right)) (emit left).
Hypothesis padded_projection :
  TNullRowEq (project (pad row)) (emit row).

(** Two duplicate left occurrences and no right rows exercise the unmatched
    branch without any foreign-key totality hypothesis. *)
Example tnull_partial_left_join_unmatched_duplicates_regression :
  TNullRowPermut
    (map project
      (TNullLeftJoinRows join accept pad [row; row] nil))
    [emit row; emit row].
Proof.
change
  (TNullRowPermut
    (map project (TNullLeftJoinRows join accept pad [row; row] nil))
    (map emit [row; row])).
eapply tnull_map_left_join_functional_permut.
- exact matched_projection.
- intros left [Hleft|[Hleft|Hnone]].
  + subst left; exact padded_projection.
  + subst left; exact padded_projection.
  + contradiction.
- intros left Hleft; cbn; repeat constructor.
Qed.

End PartialFunctionalLeftJoinRegression.

Section NativePartialFunctionalLeftJoinRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variable predicate : TNullFormulaExpr.
Variables matched_select left_select right_select : TNullSelectList.
Variables project emit : TNullRow -> TNullRow.
Variables left_bag right_bag joined_bag : TNullRowBag.

Hypothesis project_proper :
  forall first second,
    TNullRowEq first second -> TNullRowEq (project first) (project second).
Hypothesis emit_proper :
  forall first second,
    TNullRowEq first second -> TNullRowEq (emit first) (emit second).
Hypothesis join_functional :
  forall left_rows right_rows matrix,
    query_same_rows_as_bag left_rows left_bag ->
    query_same_rows_as_bag right_rows right_bag ->
    @eval_join_conditions_outcome TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      env predicate left_rows right_rows (SqlSuccess matrix) ->
    Forall
      (fun flags =>
        (length (filter (fun flag : bool => flag) flags) <= 1)%nat)
      matrix.
Hypothesis matched_source_projection :
  forall left right output,
    @project_join_source_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env matched_select left_select right_select
      (JoinSourceMatched TNull (join_tuple TNull left right)) =
    SqlSuccess output ->
    TNullRowEq (project output) (emit left).
Hypothesis padded_source_projection :
  forall left output,
    @project_join_source_outcome TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      env matched_select left_select right_select
      (JoinSourceLeft TNull left) = SqlSuccess output ->
    TNullRowEq (project output) (emit left).
Hypothesis join_success :
  @eval_join_bag_outcome TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env QueryJoinLeft predicate matched_select left_select right_select
    left_bag right_bag (SqlSuccess joined_bag).

(** The native theorem relates the post-projection joined bag to the mapped
    left bag; runtime-error equivalence intentionally remains outside it. *)
Example tnull_native_partial_left_join_projection_bag_regression :
  TNullBagEq
    (TNullBagMap project joined_bag)
    (TNullBagMap emit left_bag).
Proof.
unfold TNullBagEq, TNullBagMap, TNullRowEq in *.
eapply query_join_left_functional_projection_bag_on_representatives;
  try eassumption.
- intros left_rows right_rows left right output
    Hleft_rows Hright_rows Hleft_in Hright_in Hsource.
  exact (matched_source_projection left right output Hsource).
- intros left_rows left output Hleft_rows Hleft_in Hsource.
  exact (padded_source_projection left output Hsource).
Qed.

End NativePartialFunctionalLeftJoinRegression.

Section ReusableWitnessInterfacesRegression.

Variable env : TNullEnvironment.
Variable select : TNullSelectList.
Variables left_row right_row : TNullRow.

Example same_select_projection_labels_regression :
  TNullAttributeSetEq
    (TNullRowLabels (TNullProjectRow env select left_row))
    (TNullRowLabels (TNullProjectRow env select right_row)).
Proof. apply tnull_same_select_projection_labels. Qed.

Variable group_terms : list AggTerm.
Variable rows : list TNullRow.
Variable keep_key : list TNullValue -> bool.
Variable key : list TNullValue.
Hypothesis group_terms_nonempty : group_terms <> nil.
Hypothesis accepted_key_constant :
  forall row,
    In row
      (filter
        (fun item => keep_key (query_grouping_key env group_terms item))
        rows) ->
    query_grouping_key env group_terms row = key.

Example one_key_group_selection_regression :
  filter
    (fun members =>
      match members with
      | nil => false
      | row :: _ => keep_key (query_grouping_key env group_terms row)
      end)
    (@query_make_groups TNull env rows group_terms) =
  match
    filter
      (fun item => keep_key (query_grouping_key env group_terms item)) rows
  with
  | nil => nil
  | _ :: _ =>
      [rev
        (filter
          (fun item => keep_key (query_grouping_key env group_terms item))
          rows)]
  end.
Proof.
eapply tnull_query_groups_matching_one_key; eassumption.
Qed.

Variables
  (join : TNullRow -> TNullRow -> TNullRow)
  (accept : TNullRow -> TNullRow -> bool)
  (project emit : TNullRow -> TNullRow)
  (left right : list TNullRow) (witness : bool).
Hypothesis witness_projection :
  forall l r, TNullRowEq (project (join l r)) (emit l).
Hypothesis witness_total :
  witness = true ->
  forall l, In l left ->
    exists r, In r right /\ accept l r = true.
Hypothesis witness_functional :
  forall l, In l left ->
    (length (filter (accept l) right) <= 1)%nat.
Hypothesis witness_absent :
  witness = false ->
  forall l r, In l left -> In r right -> accept l r = false.

Example theta_join_witness_regression :
  TNullRowPermut
    (map project (TNullThetaJoinRows join accept left right))
    (if witness then map emit left else nil).
Proof.
eapply tnull_theta_join_by_witness; eassumption.
Qed.

Hypothesis emitted_nodup : NoDupA TNullRowEq (map emit left).

Hypothesis accepted_projection :
  forall l r,
    In l left ->
    In r right ->
    accept l r = true ->
    TNullRowEq (project (join l r)) (emit l).

Example accepted_total_functional_join_permut_regression :
  witness = true ->
  TNullRowPermut
    (map project (TNullThetaJoinRows join accept left right))
    (map emit left).
Proof.
intro Htrue.
eapply tnull_map_theta_join_total_functional_permut_accepted.
- exact accepted_projection.
- now apply witness_total.
- exact witness_functional.
Qed.

Example accepted_total_functional_join_nodup_regression :
  witness = true ->
  NoDupA TNullRowEq
    (map project (TNullThetaJoinRows join accept left right)).
Proof.
intro Htrue.
eapply tnull_total_functional_theta_project_nodup_accepted.
- exact accepted_projection.
- now apply witness_total.
- exact witness_functional.
- exact emitted_nodup.
Qed.

Example total_functional_join_nodup_regression :
  witness = true ->
  NoDupA TNullRowEq
    (map project (TNullThetaJoinRows join accept left right)).
Proof.
intro Htrue.
eapply tnull_total_functional_theta_project_nodup.
- exact witness_projection.
- now apply witness_total.
- exact witness_functional.
- exact emitted_nodup.
Qed.

Example nodup_occurrence_bound_regression :
  forall row,
    (Oeset.nb_occ TNullRowOrder row (map emit left) <= 1)%N.
Proof. now apply tnull_nodup_occ_le_one. Qed.

End ReusableWitnessInterfacesRegression.

Section PartialFunctionalThetaKeyRegression.

Variable Key : Type.
Variable key_relation : Key -> Key -> Prop.
Variable key : TNullRow -> Key.
Variables
  (join : TNullRow -> TNullRow -> TNullRow)
  (accept : TNullRow -> TNullRow -> bool)
  (project emit : TNullRow -> TNullRow)
  (left right : list TNullRow).

Hypothesis source_keys_nodup : NoDupA key_relation (map key left).
Hypothesis theta_functional :
  forall left_row,
    In left_row left ->
    (length (filter (accept left_row) right) <= 1)%nat.
Hypothesis projected_output_reflects_key :
  forall left_first left_second right_first right_second,
    In left_first left -> In left_second left ->
    In right_first right -> In right_second right ->
    accept left_first right_first = true ->
    accept left_second right_second = true ->
    TNullRowEq
      (project (join left_first right_first))
      (project (join left_second right_second)) ->
    key_relation (key left_first) (key left_second).

(** No totality premise is present: unmatched left rows emit no theta output. *)
Example partial_functional_theta_key_nodup_regression :
  NoDupA TNullRowEq
    (map project (TNullThetaJoinRows join accept left right)).
Proof.
eapply tnull_functional_theta_project_nodup_of_key_reflection;
  eassumption.
Qed.

Hypothesis accepted_projection :
  forall left_row right_row,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    TNullRowEq (project (join left_row right_row)) (emit left_row).

Example partial_functional_theta_semijoin_regression :
  TNullRowPermut
    (map project (TNullThetaJoinRows join accept left right))
    (map emit
      (filter
        (fun left_row => existsb (accept left_row) right) left)).
Proof.
eapply tnull_map_theta_join_functional_permut_filter_exists;
  eassumption.
Qed.

End PartialFunctionalThetaKeyRegression.

Section DecomposedBagOperatorRegression.

Variables left_keep right_keep : TNullRow -> bool.
Variable bag : TNullRowBag.
Hypothesis left_proper :
  forall first second,
    TNullRowEq first second -> left_keep first = left_keep second.
Hypothesis right_proper :
  forall first second,
    TNullRowEq first second -> right_keep first = right_keep second.
Hypothesis bag_nodup : query_bag_duplicate_free bag.

Example filter_occurrence_regression : forall row,
  Febag.nb_occ TNullRowBagRecord row
    (Febag.filter TNullRowBagRecord left_keep bag) =
  if left_keep row
  then Febag.nb_occ TNullRowBagRecord row bag
  else 0%N.
Proof.
intro row.
apply query_bag_filter_occurrence_exact.
intros first second Hequal; now apply left_proper.
Qed.

Example union_occurrence_regression : forall row,
  Febag.nb_occ TNullRowBagRecord row
    (query_set_bag Union
      (Febag.filter TNullRowBagRecord left_keep bag)
      (Febag.filter TNullRowBagRecord right_keep bag)) =
  (Febag.nb_occ TNullRowBagRecord row
      (Febag.filter TNullRowBagRecord left_keep bag) +
   Febag.nb_occ TNullRowBagRecord row
      (Febag.filter TNullRowBagRecord right_keep bag))%N.
Proof.
apply query_set_union_occurrence_exact.
Qed.

Example distinct_occurrence_regression : forall row,
  Febag.nb_occ TNullRowBagRecord row (query_distinct_bag bag) =
  if Febag.mem TNullRowBagRecord row bag then 1%N else 0%N.
Proof.
apply query_distinct_bag_occurrence_exact.
Qed.

Example filtered_bag_duplicate_free_regression :
  query_bag_duplicate_free
    (Febag.filter TNullRowBagRecord left_keep bag).
Proof.
eapply query_bag_filter_duplicate_free; eassumption.
Qed.

End DecomposedBagOperatorRegression.


Section SemanticListBagBoundaryRegression.

Variable rows : list TNullRow.
Hypothesis rows_nodup : NoDupA TNullRowEq rows.

Example semantic_nodup_rows_duplicate_free_regression :
  query_bag_duplicate_free (TNullRowsBag rows).
Proof.
unfold TNullRowsBag, TNullRowEq in *.
now apply query_bag_duplicate_free_of_rows_NoDupA.
Qed.

Variables left_bag right_bag : TNullRowBag.
Hypothesis bags_equal : TNullBagEq left_bag right_bag.
Hypothesis left_bag_nodup : query_bag_duplicate_free left_bag.

Example duplicate_free_bag_transport_regression :
  query_bag_duplicate_free right_bag.
Proof.
unfold TNullBagEq in bags_equal.
eapply query_bag_duplicate_free_transport; eassumption.
Qed.

End SemanticListBagBoundaryRegression.

Section DuplicateFreeSupportRegression.

Variables left right : TNullRowBag.
Hypothesis left_nodup : query_bag_duplicate_free left.
Hypothesis right_nodup : query_bag_duplicate_free right.
Hypothesis same_support :
  forall row,
    Febag.nb_occ TNullRowBagRecord row left = 0%N <->
    Febag.nb_occ TNullRowBagRecord row right = 0%N.

Example duplicate_free_support_bag_eq_regression : TNullBagEq left right.
Proof.
unfold TNullBagEq.
eapply query_duplicate_free_support_bag_eq; eassumption.
Qed.

End DuplicateFreeSupportRegression.

Section FacadeEquivalenceAndSafetyRegression.

Variables first second third : TNullRow.
Hypothesis first_second : TNullRowEq first second.
Hypothesis second_third : TNullRowEq second third.

Example tnull_row_eq_refl_regression : TNullRowEq first first.
Proof. apply tnull_row_eq_refl. Qed.

Example tnull_row_eq_sym_regression : TNullRowEq second first.
Proof. now apply tnull_row_eq_sym. Qed.

Example tnull_row_eq_trans_regression : TNullRowEq first third.
Proof. eapply tnull_row_eq_trans; eassumption. Qed.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variable columns : list ColumnRef.
Variable rows : list TNullRow.
Variable input : TNullQueryExpr.
Variable input_bag : TNullRowBag.
Variable error : sql_runtime_error.
Variable select : TNullSelectList.
Variable attribute : TNullAttribute.
Variable row : TNullRow.

Example tnull_lookup_some_label_regression :
  (exists expression,
    TNullSelectLookup select attribute = Some expression) <->
  attribute inS TNullRowLabels (TNullProjectRow env select row).
Proof. apply tnull_select_lookup_some_iff_projected_label. Qed.

Example tnull_lookup_none_label_regression :
  TNullSelectLookup select attribute = None <->
  (attribute inS? TNullRowLabels (TNullProjectRow env select row)) = false.
Proof. apply tnull_select_lookup_none_iff_projected_label_absent. Qed.

Example tnull_select_columns_project_rows_regression :
  @project_rows_outcome TNull
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    env (SelectColumns columns) rows =
  SqlSuccess
    (map
      (fun input_row =>
        TNullProjectRow env (SelectColumns columns) input_row)
      rows).
Proof. apply tnull_project_rows_select_columns_success. Qed.

Example tnull_select_columns_project_error_regression :
  TNullQueryExprOutcome db env
    (QExpr_Project (SelectColumns columns) input) (SqlError error) <->
  TNullQueryExprOutcome db env input (SqlError error).
Proof. apply tnull_query_expr_project_select_columns_error_iff. Qed.

Example tnull_direct_group_no_error_regression :
  ~ @eval_group_bag_outcome TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env (SelectColumns columns) (map DotColumn columns) FExpr_True
    input_bag (SqlError error).
Proof. apply tnull_eval_group_bag_direct_columns_true_no_error. Qed.

End FacadeEquivalenceAndSafetyRegression.

Section SuccessBagAutomationRegression.

Variable db : TNullDatabase.
Variable env : TNullEnvironment.
Variables left right fixed : TNullQueryExpr.
Variables outputs alternate_outputs : list TNullAttribute.
Variables left_values right_values : TNullRowBag.
Variables left_table right_table : relname.
Variables left_error right_error : sql_runtime_error.
Variable columns : list ColumnRef.
Variable formula : TNullFormulaExpr.
Variable keep : TNullRow -> bool.
Variable row_map : TNullRow -> sql_outcome TNullRow.
Variable mapping : TNullRow -> TNullRow.
Variables single_select outer_select inner_select : TNullSelectList.
Variable rank_attribute : TNullAttribute.
Variable rank_value : nat -> option TNullValue.
Variable partition_keys order_keys alternate_keys : list (sort_key TNull).
Variable window_items : list (query_window_item TNull).

Local Definition test_success_bags (query : TNullQueryExpr) :=
  @query_success_bags TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env query.

Local Definition test_table_bag
    (table_outputs : list TNullAttribute) (table : relname) : TNullRowBag :=
  @query_table_bag TNull relname
    (@_basesort TNull db) (@_instance TNull db) table_outputs table.

Local Definition test_outcome_equiv (left_query right_query : TNullQueryExpr) :=
  @query_expr_outcome_equiv TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    env left_query right_query.

Hypothesis child_bags :
  rel_equiv (test_success_bags left) (test_success_bags right).

Hypothesis child_sorts :
  query_expr_sort left =S= query_expr_sort right.

Hypothesis values_bags : TNullBagEq left_values right_values.

Hypothesis table_bags :
  TNullBagEq
    (test_table_bag outputs left_table)
    (test_table_bag alternate_outputs right_table).

Hypothesis keep_proper :
  forall first second,
    TNullRowEq first second ->
    keep first = keep second.

Hypothesis formula_exact :
  forall row,
    @formula_acceptance_exact_at TNull relname
      (@_basesort TNull db) (@_instance TNull db) unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error NullValues.is_null_value
      (env_t TNull env row) formula (keep row).

Hypothesis row_map_total :
  @row_map_total_as TNull row_map mapping.

Hypothesis mapping_proper :
  @row_mapping_semantic_proper TNull mapping.

Hypothesis single_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) single_select = None.

Hypothesis outer_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) outer_select = None.

Hypothesis inner_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) inner_select = None.

Hypothesis project_fusion :
  forall input_bag,
    test_success_bags left input_bag ->
    TNullBagEq
      (query_project_bag env single_select input_bag)
      (query_project_bag env outer_select
        (query_project_bag env inner_select input_bag)).

Example logos_project_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Project (SelectColumns columns) left))
    (test_success_bags (QExpr_Project (SelectColumns columns) right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_project_fusion_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Project single_select left))
    (test_success_bags
      (QExpr_Project outer_select (QExpr_Project inner_select left))).
Proof.
unfold test_success_bags, TNullBagEq in *; logos.
Qed.

Example logos_project_fusion_success_bags_symmetric_regression :
  rel_equiv
    (test_success_bags
      (QExpr_Project outer_select (QExpr_Project inner_select left)))
    (test_success_bags (QExpr_Project single_select left)).
Proof.
unfold test_success_bags, TNullBagEq in *; logos.
Qed.

(** Without the semantic fusion fact, [logos.] deterministically exposes the
    named residual rather than failing and forcing a [try logos] probe. *)
Variables residual_single_select residual_outer_select residual_inner_select :
  TNullSelectList.
Hypothesis residual_single_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) residual_single_select = None.
Hypothesis residual_outer_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) residual_outer_select = None.
Hypothesis residual_inner_select_safe :
  forall row,
    @eval_select_list_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (env_t TNull env row) residual_inner_select = None.

Goal rel_equiv
  (test_success_bags (QExpr_Project residual_single_select left))
  (test_success_bags
    (QExpr_Project residual_outer_select
      (QExpr_Project residual_inner_select left))).
Proof.
unfold test_success_bags in *.
logos.
lazymatch goal with
| |- @project_fusion_success_bag_contract
    _ _ _ _ _ _ _ _ env residual_single_select residual_outer_select
    residual_inner_select left => idtac
| |- _ => fail "logos did not expose the named projection-fusion residual"
end.
Abort.

Example logos_row_map_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_RowMap outputs row_map left))
    (test_success_bags (QExpr_RowMap outputs row_map right)).
Proof.
unfold test_success_bags in *; logos.
exists mapping; now split.
Qed.

Example logos_filter_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Filter formula left))
    (test_success_bags (QExpr_Filter formula right)).
Proof.
unfold test_success_bags in *; logos.
exists keep; split; [exact keep_proper |].
split; exact formula_exact.
Qed.

Example logos_set_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Set Union left fixed))
    (test_success_bags (QExpr_Set Union right fixed)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_natural_join_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_NaturalJoin left fixed))
    (test_success_bags (QExpr_NaturalJoin right fixed)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_cross_join_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_CrossJoin left fixed))
    (test_success_bags (QExpr_CrossJoin right fixed)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_join_success_bags_regression :
  rel_equiv
    (test_success_bags
      (QExpr_Join QueryJoinInner FExpr_True
        (SelectList []) (SelectList []) (SelectList []) left fixed))
    (test_success_bags
      (QExpr_Join QueryJoinInner FExpr_True
        (SelectList []) (SelectList []) (SelectList []) right fixed)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_group_success_bags_regression :
  rel_equiv
    (test_success_bags
      (QExpr_Group (SelectList []) [] FExpr_True left))
    (test_success_bags
      (QExpr_Group (SelectList []) [] FExpr_True right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_grouping_sets_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_GroupingSets [] left))
    (test_success_bags (QExpr_GroupingSets [] right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_rank_success_bags_regression :
  rel_equiv
    (test_success_bags
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value left))
    (test_success_bags
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_window_success_bags_regression :
  rel_equiv
    (test_success_bags
      (QExpr_Window partition_keys order_keys window_items left))
    (test_success_bags
      (QExpr_Window partition_keys order_keys window_items right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_distinct_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Distinct left))
    (test_success_bags (QExpr_Distinct right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_order_by_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_OrderBy order_keys left))
    (test_success_bags (QExpr_OrderBy alternate_keys right)).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_values_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Values outputs left_values))
    (test_success_bags (QExpr_Values alternate_outputs right_values)).
Proof.
unfold test_success_bags, TNullBagEq in *; logos.
Qed.

Example logos_table_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Table outputs left_table))
    (test_success_bags (QExpr_Table alternate_outputs right_table)).
Proof.
unfold test_success_bags, test_table_bag, TNullBagEq in *; logos.
Qed.

(** Positional consumers are accepted only when their children are already
    certified permutation-closed. *)
Example logos_offset_closed_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Offset 1 (QExpr_Distinct left)))
    (test_success_bags (QExpr_Offset 1 (QExpr_Distinct right))).
Proof.
unfold test_success_bags in *; logos.
Qed.

Example logos_fetch_closed_success_bags_regression :
  rel_equiv
    (test_success_bags (QExpr_Fetch 1 (QExpr_Distinct left)))
    (test_success_bags (QExpr_Fetch 1 (QExpr_Distinct right))).
Proof.
unfold test_success_bags in *; logos.
Qed.

Goal rel_equiv
  (test_success_bags (QExpr_Offset 1 left))
  (test_success_bags (QExpr_Offset 1 right)).
Proof.
unfold test_success_bags in *.
Fail solve [logos].
Abort.

Goal rel_equiv
  (test_success_bags (QExpr_Fetch 1 left))
  (test_success_bags (QExpr_Fetch 1 right)).
Proof.
unfold test_success_bags in *.
Fail solve [logos].
Abort.

(** Success-bag rules must not leak into error categories or the ordered root
    observation. *)
Goal test_outcome_equiv
  (QExpr_Error outputs left_error)
  (QExpr_Error outputs right_error).
Proof.
unfold test_outcome_equiv.
Fail solve [logos].
Abort.

(** Unsupported propositions remain available to the caller, while the same
    public invocation still closes another currently focused structural goal. *)
Goal (True \/ True) /\
  rel_equiv
    (test_success_bags (QExpr_Offset 1 (QExpr_Distinct left)))
    (test_success_bags (QExpr_Offset 1 (QExpr_Distinct right))).
Proof.
unfold test_success_bags in *.
split; logos.
left; exact I.
Qed.

Goal True \/ True.
Proof.
logos.
left; exact I.
Qed.

Goal test_outcome_equiv
  (QExpr_OrderBy order_keys (QExpr_Table outputs left_table))
  (QExpr_OrderBy alternate_keys (QExpr_Table outputs left_table)).
Proof.
unfold test_outcome_equiv.
Fail solve [logos].
Abort.

End SuccessBagAutomationRegression.

(** These commands audit that the facade contributes no assumptions. *)
Print Assumptions tnull_query_expr_error_regression.
Print Assumptions tnull_observation_functionality_regression.
Print Assumptions tnull_separation_refutes_outcome_equivalence_regression.
Print Assumptions tnull_functional_bag_difference_separation_regression.
Print Assumptions tnull_program_head_separation_regression.
Print Assumptions outcome_relation_separation_sound.
Print Assumptions
  tnull_query_expr_outcome_separation_of_right_functional_observation_difference.
Print Assumptions
  tnull_query_expr_outcome_separation_of_left_functional_observation_difference.
Print Assumptions
  tnull_query_expr_outcome_separation_of_right_functional_bag_difference.
Print Assumptions
  tnull_query_expr_outcome_separation_of_left_functional_bag_difference.
Print Assumptions tnull_query_program_head_separation_sound.
Print Assumptions tnull_direct_projection_alias_value.
Print Assumptions tnull_direct_projection_alias_retained.
Print Assumptions tnull_direct_projection_alias_reflects_value.
Print Assumptions tnull_select_lookup_retained.
Print Assumptions tnull_select_lookup_some_iff_projected_label.
Print Assumptions tnull_select_lookup_none_iff_projected_label_absent.
Print Assumptions tnull_select_lookup_direct_compose.
Print Assumptions tnull_select_lookup_direct_compose_interp_value.
Print Assumptions tnull_select_lookup_constant_direct_compose.
Print Assumptions
  tnull_projected_alias_int32_primary_key_matches_at_most_one.
Print Assumptions projected_alias_primary_key_match_count_regression.
Print Assumptions tnull_row_eq_of_labels_and_values.
Print Assumptions tnull_projection_rows_eq_of_output_values.
Print Assumptions tnull_direct_projection_fusion_row_eq.
Print Assumptions tnull_select_columns_lookup_output.
Print Assumptions tnull_select_columns_projection_fusion_row_eq.
Print Assumptions tnull_single_double_projection_bag_eq.
Print Assumptions tnull_project_fusion_success_bag_contract_of_row_eq.
Print Assumptions map_left_join_functional_permut.
Print Assumptions tnull_map_left_join_functional_permut.
Print Assumptions query_join_left_functional_projection_bag_on_representatives.
Print Assumptions tnull_same_select_projection_labels.
Print Assumptions tnull_query_groups_matching_one_key.
Print Assumptions tnull_theta_join_by_witness.
Print Assumptions tnull_map_theta_join_total_functional_permut_accepted.
Print Assumptions map_theta_join_functional_permut_filter_exists.
Print Assumptions tnull_map_theta_join_functional_permut_filter_exists.
Print Assumptions tnull_total_functional_theta_project_nodup.
Print Assumptions tnull_total_functional_theta_project_nodup_accepted.
Print Assumptions NoDupA_map_of_reflection.
Print Assumptions NoDupA_flat_map_filter_map_functional_reflection.
Print Assumptions tnull_functional_theta_project_nodup_of_key_reflection.
Print Assumptions tnull_nodup_occ_le_one.
Print Assumptions query_set_union_occurrence_exact.
Print Assumptions query_bag_duplicate_free_of_rows_NoDupA.
Print Assumptions query_bag_duplicate_free_transport.
Print Assumptions query_distinct_bag_occurrence_exact.
Print Assumptions query_bag_filter_occurrence_exact.
Print Assumptions query_duplicate_free_support_bag_eq.
Print Assumptions tnull_row_eq_refl.
Print Assumptions tnull_row_eq_sym.
Print Assumptions tnull_row_eq_trans.
Print Assumptions tnull_join_condition_pred_acceptance_exact_safe.
Print Assumptions tnull_project_rows_select_columns_success.
Print Assumptions tnull_query_expr_project_select_columns_error_iff.
Print Assumptions tnull_eval_group_bag_direct_columns_true_no_error.
Print Assumptions
  tnull_direct_columns_group_outcome_equiv_of_projected_support.
Print Assumptions query_project_success_bags_congr_extensional_safe.
Print Assumptions query_project_success_bags_fusion_safe.
Print Assumptions query_filter_success_bags_congr_extensional_exact.
Print Assumptions query_filter_success_bags_congr_of_contract.
Print Assumptions query_row_map_success_bags_congr_extensional_total.
Print Assumptions query_row_map_success_bags_congr_of_contract.
Print Assumptions query_row_map_success_bags_congr_extensional_of_contract.
Print Assumptions query_order_by_success_bags_congr.
Print Assumptions query_offset_success_bags_congr_closed.
Print Assumptions query_fetch_success_bags_congr_closed.
Print Assumptions query_values_success_bags_congr.
Print Assumptions query_table_success_bags_congr.
