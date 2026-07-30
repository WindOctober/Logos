(******************************************************************************)
(** Generic aggregate-selection and partition-key support interfaces.       **)
(******************************************************************************)

From SQLFS Require Import OrderedSet Partition Values.
From Logos.FormalSQL Require Import
  AggregateRuntimeFacts GroupingRewriteFacts.
From Stdlib Require Import List Sorting.Permutation ZArith.

Import ListNotations.
Import NullValues.

Section AggregateSelection.

Variable values selected : list value.
Variable P : value -> Prop.

Theorem aggregate_distinct_support_regression :
  NoDup selected ->
  (forall value, In value selected <-> In value values) ->
  Permutation
    (aggregate_input_values AggregateDistinct values)
    (aggregate_input_values AggregateAll selected).
Proof.
  exact (aggregate_distinct_input_Permutation_of_NoDup_support values selected).
Qed.

Theorem aggregate_input_Forall_regression :
  forall quantifier,
    Forall P values ->
    Forall P (aggregate_input_values quantifier values).
Proof.
  intros quantifier Hvalues.
  now apply aggregate_input_values_preserves_Forall.
Qed.

Theorem count_star_permutation_regression :
  forall left right,
    Permutation left right ->
    interp_aggregate AggregateCountStar left =
    interp_aggregate AggregateCountStar right /\
    aggregate_local_runtime_error AggregateCountStar left =
    aggregate_local_runtime_error AggregateCountStar right.
Proof.
  intros left right Hpermutation; split.
  - now apply interp_aggregate_count_star_permutation.
  - now apply aggregate_count_star_local_runtime_error_permutation.
Qed.

Theorem nonnull_count_length_regression :
  Forall (fun value => is_null_value value = false) values ->
  non_null_count values = Z.of_nat (length values).
Proof.
  apply non_null_count_eq_length_of_Forall_nonnull.
Qed.

Theorem aggregate_sum_int32_nonnull_regression :
  forall quantifier,
    values <> [] ->
    Forall
      (fun value =>
        is_int32_value value = true /\ is_null_value value = false)
      values ->
    aggregate_local_runtime_error
      (AggregateCall AggregateSumInt32 quantifier) values = None ->
    is_null_value
      (interp_aggregate
        (AggregateCall AggregateSumInt32 quantifier) values) = false.
Proof.
  intro quantifier.
  exact
    (aggregate_sum_int32_nonnull_of_nonempty_runtime_safe quantifier values).
Qed.

Theorem aggregate_sum_numeric_nonnull_regression :
  forall quantifier,
    values <> [] ->
    Forall
      (fun value =>
        is_numeric_value value = true /\ is_null_value value = false)
      values ->
    is_null_value
      (interp_aggregate
        (AggregateCall AggregateSumNumeric quantifier) values) = false.
Proof.
  intro quantifier.
  exact (aggregate_sum_numeric_nonnull_of_nonempty quantifier values).
Qed.

End AggregateSelection.

Section PartitionKeys.

Variables (A Key : Type) (key_order : Oset.Rcd Key) (key_of : A -> Key).
Variables (rows : list A) (selected_keys : list Key).

Theorem partition_keys_support_regression :
  NoDup selected_keys ->
  (forall key,
    In key selected_keys <-> In key (map key_of rows)) ->
  Permutation
    (map fst (@Partition.partition A Key key_order key_of rows))
    selected_keys.
Proof.
  exact
    (partition_keys_Permutation_of_NoDup_support
      A Key key_order key_of rows selected_keys).
Qed.

End PartitionKeys.

Section GroupingSetSchedulerContracts.

Variable T : FTuples.Tuple.Rcd.
Variable relname : Type.
Variable basesort : relname -> FiniteSet.Fset.set (FTuples.Tuple.A T).
Variable instance :
  relname ->
  FiniteBag.Febag.bag
    (FiniteCollection.Fecol.CBag (FTuples.Tuple.CTuple T)).
Variable unknown : Bool3.Bool.b (FTuples.Tuple.B T).
Variable symbol_runtime_error :
  FTuples.Tuple.scalar_operator T ->
  list (option SqlOutcome.sql_runtime_error * FTuples.Tuple.value T) ->
  option SqlOutcome.sql_runtime_error.
Variable aggregate_runtime_error :
  FTuples.Tuple.aggregate T ->
  list (option SqlOutcome.sql_runtime_error * FTuples.Tuple.value T) ->
  option SqlOutcome.sql_runtime_error.
Variable value_is_null : FTuples.Tuple.value T -> bool.

Local Definition grouping_bag :=
  FiniteBag.Febag.bag
    (FiniteCollection.Fecol.CBag (FTuples.Tuple.CTuple T)).

Theorem grouping_sets_success_fold_contract_regression :
  forall env input_bag grouping_sets output_bag,
    @SqlQuerySemantics.eval_grouping_sets_bag_outcome
      T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env grouping_sets input_bag (SqlOutcome.SqlSuccess output_bag) <->
    exists branch_bags,
      Forall2
        (@grouping_set_success_at T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          env input_bag)
        grouping_sets branch_bags /\
      output_bag = @grouping_sets_union_fold T branch_bags.
Proof.
  exact
    (@eval_grouping_sets_success_fold_iff T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null).
Qed.

Theorem grouping_sets_error_prefix_contract_regression :
  forall env input_bag grouping_sets error,
    @SqlQuerySemantics.eval_grouping_sets_bag_outcome
      T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env grouping_sets input_bag (SqlOutcome.SqlError error) <->
    exists (prefix : list (@SqlQuerySyntax.query_grouping_set T))
        (current : @SqlQuerySyntax.query_grouping_set T)
        (suffix : list (@SqlQuerySyntax.query_grouping_set T))
        (prefix_bags : list grouping_bag),
      grouping_sets = prefix ++ current :: suffix /\
      Forall2
        (@grouping_set_success_at T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          env input_bag)
        prefix prefix_bags /\
      @grouping_set_error_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env input_bag current error.
Proof.
  exact
    (@eval_grouping_sets_error_prefix_iff T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null).
Qed.

Theorem grouping_sets_ordered_congruence_contract_regression :
  forall env input_bag left_sets right_sets,
    Forall2
      (@grouping_set_exact_outcome_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env input_bag)
      left_sets right_sets ->
    forall outcome,
      @SqlQuerySemantics.eval_grouping_sets_bag_outcome
        T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left_sets input_bag outcome <->
      @SqlQuerySemantics.eval_grouping_sets_bag_outcome
        T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env right_sets input_bag outcome.
Proof.
  exact
    (@eval_grouping_sets_outcome_Forall2_congr T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error value_is_null).
Qed.

End GroupingSetSchedulerContracts.

Print Assumptions aggregate_distinct_input_Permutation_of_NoDup_support.
Print Assumptions aggregate_input_values_preserves_Forall.
Print Assumptions count_star_permutation_regression.
Print Assumptions non_null_count_eq_length_of_Forall_nonnull.
Print Assumptions aggregate_sum_int32_nonnull_regression.
Print Assumptions aggregate_sum_numeric_nonnull_regression.
Print Assumptions partition_keys_Permutation_of_NoDup_support.
Check grouping_set_exact_outcome_at.
Check eval_grouping_sets_outcome_Forall2_congr.
Check eval_grouping_sets_success_fold_iff.
Check eval_grouping_sets_error_prefix_iff.
Print Assumptions eval_grouping_sets_outcome_Forall2_congr.
Print Assumptions eval_grouping_sets_success_fold_iff.
Print Assumptions eval_grouping_sets_error_prefix_iff.
Print Assumptions grouping_sets_success_fold_contract_regression.
Print Assumptions grouping_sets_error_prefix_contract_regression.
Print Assumptions grouping_sets_ordered_congruence_contract_regression.
