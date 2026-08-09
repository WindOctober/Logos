(******************************************************************************)
(** Generic regressions for ordered-query outcome and constructor bridges.    **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData
  SqlErrorSemantics SqlOutcome SqlOrder OrderedSet SqlBagAbstraction
  SqlQueryContexts SqlQueryFacts SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import GroupedFilterOutcomeFacts OrderedQueryFacts.

Import Tuple.

Section OrderedGroupChildOutcomeRegression.

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
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** Order behavior is local to the outer constructor.  These regressions keep
    preservation, reset, establishment, and consumption distinct without
    pretending to decide whole-query semantic closure. *)
Example project_order_behavior_regression :
  forall (select_list : query_select_list T relname)
      (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Project select_list input) =
      OrderPreserving.
Proof. reflexivity. Qed.

Example filter_order_behavior_regression :
  forall (predicate : scalar_expr T relname ScalarResultBoolean)
      (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Filter predicate input) =
      OrderPreserving.
Proof. reflexivity. Qed.

Example row_map_order_behavior_regression :
  forall (outputs : list (attribute T))
      (row_map : tuple T -> sql_outcome (tuple T))
      (input : query_expr T relname),
    query_expr_order_behavior (QExpr_RowMap outputs row_map input) =
      OrderPreserving.
Proof. reflexivity. Qed.

Example group_order_behavior_regression :
  forall (select_list : query_select_list T relname)
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean)
      (input : query_expr T relname),
    query_expr_order_behavior
      (QExpr_Group select_list group_terms having input) = BagReset.
Proof. reflexivity. Qed.

Example order_by_order_behavior_regression :
  forall (keys : list (sort_key T)) (input : query_expr T relname),
    query_expr_order_behavior (QExpr_OrderBy keys input) =
      OrderEstablishing.
Proof. reflexivity. Qed.

Example offset_order_behavior_regression :
  forall (count : nat) (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Offset count input) = OrderConsuming.
Proof. reflexivity. Qed.

Example fetch_order_behavior_regression :
  forall (count : nat) (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Fetch count input) = OrderConsuming.
Proof. reflexivity. Qed.

Example distinct_order_behavior_regression :
  forall (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Distinct input) = BagReset.
Proof. reflexivity. Qed.

Example rank_order_behavior_regression :
  forall (partition_keys order_keys : list (sort_key T))
      (rank_attribute : attribute T) (rank_value : nat -> option (value T))
      (input : query_expr T relname),
    query_expr_order_behavior
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input) =
      BagReset.
Proof. reflexivity. Qed.

Example window_order_behavior_regression :
  forall (partition_keys order_keys : list (sort_key T))
      (items : list (query_window_item T)) (input : query_expr T relname),
    query_expr_order_behavior
      (QExpr_Window partition_keys order_keys items input) = BagReset.
Proof. reflexivity. Qed.

Example group_resets_consumed_order_regression :
  forall (select_list : query_select_list T relname)
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean) (count : nat)
      (input : query_expr T relname),
    query_expr_order_behavior
      (QExpr_Group select_list group_terms having
        (QExpr_Fetch count input)) = BagReset.
Proof. reflexivity. Qed.

(** CROSS JOIN establishes concrete permutation closure.  A typed FILTER is
    deliberately not syntax-certified: scalar subqueries may contribute
    relational successes and errors, so its bag proof requires the exact
    predicate contract exercised below. *)
Example filter_cross_join_not_structurally_certified_regression :
  forall (predicate : scalar_expr T relname ScalarResultBoolean)
      (left right : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Filter predicate (QExpr_CrossJoin left right)) = false.
Proof. reflexivity. Qed.

Theorem cross_join_bag_closed_regression :
  forall env left right,
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_CrossJoin left right) (SqlSuccess rows)).
Proof.
intros.
apply query_structural_successes_bag_closed.
reflexivity.
Qed.

(** A reset-derived certificate propagates through a deterministic RowMap.
    Project and Filter instead use their explicit scalar success/safety and
    exact-acceptance interfaces below. *)
Example row_map_group_closure_certificate_regression :
  forall (outputs : list (attribute T))
      (row_map : tuple T -> sql_outcome (tuple T))
      (group_select : query_select_list T relname)
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean)
      (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_RowMap outputs row_map
        (QExpr_Group group_select group_terms having input)) = true.
Proof. reflexivity. Qed.

Theorem row_map_group_bag_closed_regression :
  forall env outputs row_map
      group_select group_terms having input,
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_RowMap outputs row_map
            (QExpr_Group group_select group_terms having input))
          (SqlSuccess rows)).
Proof.
intros.
apply query_structural_successes_bag_closed.
reflexivity.
Qed.

(** The conservative classifier intentionally does not infer closure across an
    order-establishing node, even when a surrounding projection might happen
    to erase every observable order distinction in a special case. *)
Example project_order_by_group_not_closure_certified_regression :
  forall (project_select group_select : query_select_list T relname)
      (keys : list (sort_key T))
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean)
      (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_OrderBy keys
          (QExpr_Group group_select group_terms having input))) = false.
Proof. reflexivity. Qed.

Example project_offset_group_not_closure_certified_regression :
  forall (project_select group_select : query_select_list T relname)
      (count : nat)
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean)
      (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_Offset count
          (QExpr_Group group_select group_terms having input))) = false.
Proof. reflexivity. Qed.

Example project_fetch_group_not_closure_certified_regression :
  forall (project_select group_select : query_select_list T relname)
      (count : nat)
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean)
      (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_Fetch count
          (QExpr_Group group_select group_terms having input))) = false.
Proof. reflexivity. Qed.

Theorem group_child_eval_iff_regression :
  forall env select_list group_terms having left right,
    query_outcome_equiv env left right ->
    forall outcome,
      eval_query env
        (QExpr_Group select_list group_terms having left) outcome <->
      eval_query env
        (QExpr_Group select_list group_terms having right) outcome.
Proof.
intros; now apply eval_query_expr_group_outcome_iff_of_child_outcome_equiv.
Qed.

Theorem group_child_outcome_congruence_regression :
  forall env select_list group_terms having left right,
    query_outcome_equiv env left right ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms having left) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
Proof.
intros; eapply query_expr_group_outcome_equiv_congr; eassumption.
Qed.

(** The wrapper deliberately accepts an error-only parent.  This locks the
    one-sided inhabitation contract independently of successful evaluation. *)
Example group_error_only_congruence_regression :
  forall env select_list group_terms having outputs error,
    query_outcome_equiv env
      (QExpr_Group select_list group_terms having
        (QExpr_Error outputs error))
      (QExpr_Group select_list group_terms having
        (QExpr_Error outputs error)).
Proof.
intros env select_list group_terms having outputs error.
apply query_expr_group_outcome_equiv_congr.
- apply query_expr_outcome_equiv_refl.
  exists (SqlError error); constructor.
- exists (SqlError error).
  apply EQuery_GroupChildError; constructor.
Qed.

(** Exercise all three success constructors as one ordinary proof chain. *)
Theorem table_project_filter_has_success_regression :
  forall env outputs table select_list predicate (keep : tuple T -> bool),
    (forall row,
      scalar_select_values_has_success_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) select_list) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) predicate (keep row)) ->
    query_has_success env
      (QExpr_Filter predicate
        (QExpr_Project select_list (QExpr_Table outputs table))).
Proof.
intros env outputs table select_list predicate keep Hselect Hpredicate.
eapply query_expr_filter_has_success_exact; [exact Hpredicate |].
eapply query_expr_project_has_success_safe; [exact Hselect |].
apply query_table_has_success.
Qed.

Theorem project_error_iff_safe_regression :
  forall env select_list input,
    (forall row,
      scalar_select_values_runtime_safe_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) select_list) ->
    forall error,
      eval_query env (QExpr_Project select_list input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros; now apply eval_query_expr_project_error_iff_safe.
Qed.

(** A base table supplies the child-functionality premise required by exact
    proper filtering. *)
Theorem filter_table_success_bags_functional_regression :
  forall env outputs table predicate (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) predicate (keep row)) ->
    forall first second,
      success_bags env
        (QExpr_Filter predicate (QExpr_Table outputs table)) first ->
      success_bags env
        (QExpr_Filter predicate (QExpr_Table outputs table)) second ->
      bag_eq T first second.
Proof.
intros env outputs table predicate keep Hproper Hexact
  first second Hfirst Hsecond.
eapply query_filter_success_bags_functional_exact.
- exact Hproper.
- exact Hexact.
- intros child_first child_second Hchild_first Hchild_second.
  eapply query_table_success_bags_functional; eassumption.
- exact Hfirst.
- exact Hsecond.
Qed.

Theorem filter_table_bag_closed_regression :
  forall env outputs table predicate (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      scalar_expr_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule
        (env_t T env row) predicate (keep row)) ->
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_Filter predicate (QExpr_Table outputs table))
          (SqlSuccess rows)).
Proof.
intros env outputs table predicate keep Hproper Hexact.
eapply query_expr_filter_bag_closed_exact.
- exact Hproper.
- exact Hexact.
- apply query_bag_reset_sound; reflexivity.
Qed.

(** Typed projection is excluded from the syntax-only certificate even over an
    immediately reset child.  Its success/safety contracts retain exact scalar
    subquery outcomes, while this certificate covers only operators whose own
    semantics provide the required permutation closure. *)
Example project_table_not_structurally_certified_regression :
  forall (outputs : list (attribute T)) (table : relname)
      (select_list : query_select_list T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project select_list (QExpr_Table outputs table)) = false.
Proof. reflexivity. Qed.

Example project_group_not_structurally_certified_regression :
  forall (outputs : list (attribute T)) (table : relname)
      (project_select group_select : query_select_list T relname)
      (group_terms : list (scalar_expr T relname ScalarResultValue))
      (having : scalar_expr T relname ScalarResultBoolean),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_Group group_select group_terms having
          (QExpr_Table outputs table))) = false.
Proof. reflexivity. Qed.

End OrderedGroupChildOutcomeRegression.

Print Assumptions eval_query_expr_group_outcome_iff_of_child_outcome_equiv.
Print Assumptions query_expr_group_outcome_equiv_congr.
Print Assumptions query_table_has_success.
Print Assumptions query_expr_project_has_success_safe.
Print Assumptions eval_query_expr_project_error_iff_safe.
Print Assumptions query_expr_filter_has_success_exact.
Print Assumptions query_filter_success_bags_functional_exact.
Print Assumptions query_expr_filter_bag_closed_exact.
Print Assumptions query_structural_successes_bag_closed.
