(******************************************************************************)
(** Type-level regression checks for the unified proof-agent facade.         **)
(******************************************************************************)

From SQLFS Require Import SqlSyntax GenericInstance Values Bool3 FTuples FiniteSet FiniteBag FiniteCollection OrderedSet SqlBagAbstraction
  SqlErrorSemantics SqlOutcome SqlQuerySyntax SqlQuerySemantics
  SchemaConstraints.
From Logos.FormalSQL Require Import
  TNullSyntax QueryTNullSyntax SchemaCardinality QueryCardinality
  CardinalityCombinators OrderedQueryFacts
  GroupingRewriteFacts RelationalAlgebraFacts NumericRegroupFacts
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

(** These commands audit that the facade contributes no assumptions. *)
Print Assumptions tnull_query_expr_error_regression.
Print Assumptions tnull_direct_projection_alias_value.
Print Assumptions tnull_direct_projection_alias_retained.
Print Assumptions tnull_direct_projection_alias_reflects_value.
Print Assumptions tnull_select_lookup_retained.
Print Assumptions tnull_select_lookup_some_iff_projected_label.
Print Assumptions tnull_select_lookup_none_iff_projected_label_absent.
Print Assumptions tnull_select_lookup_direct_compose.
Print Assumptions tnull_select_lookup_constant_direct_compose.
Print Assumptions
  tnull_projected_alias_int32_primary_key_matches_at_most_one.
Print Assumptions projected_alias_primary_key_match_count_regression.
Print Assumptions tnull_row_eq_of_labels_and_values.
Print Assumptions tnull_single_double_projection_bag_eq.
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
