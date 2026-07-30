(******************************************************************************)
(** Generic regressions for ordered-query outcome and constructor bridges.    **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Projection
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

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** Order behavior is local to the outer constructor.  These regressions keep
    preservation, reset, establishment, and consumption distinct without
    pretending to decide whole-query semantic closure. *)
Example project_order_behavior_regression :
  forall (select_list : _select_list T) (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Project select_list input) =
      OrderPreserving.
Proof. reflexivity. Qed.

Example filter_order_behavior_regression :
  forall (formula : formula_expr T relname) (input : query_expr T relname),
    query_expr_order_behavior (QExpr_Filter formula input) =
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
  forall (select_list : _select_list T) (group_terms : list (@aggterm T))
      (having : formula_expr T relname) (input : query_expr T relname),
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
  forall (select_list : _select_list T) (group_terms : list (@aggterm T))
      (having : formula_expr T relname) (count : nat)
      (input : query_expr T relname),
    query_expr_order_behavior
      (QExpr_Group select_list group_terms having
        (QExpr_Fetch count input)) = BagReset.
Proof. reflexivity. Qed.

(** In the relational inner-join expansion, CROSS JOIN establishes concrete
    permutation closure and FILTER preserves it while retaining exact
    predicate-error behavior. *)
Example filter_cross_join_closure_certificate_regression :
  forall (formula : formula_expr T relname) (left right : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Filter formula (QExpr_CrossJoin left right)) = true.
Proof. reflexivity. Qed.

Theorem filter_cross_join_bag_closed_regression :
  forall env formula left right,
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_Filter formula (QExpr_CrossJoin left right))
          (SqlSuccess rows)).
Proof.
intros.
apply query_structural_successes_bag_closed.
reflexivity.
Qed.

(** A reset-derived certificate propagates structurally through the three
    pointwise unary constructors.  No projection-safety or predicate
    extensionality premise is needed here because the certificate reorders the
    same concrete rows; it does not replace them by merely equivalent rows. *)
Example transparent_stack_group_closure_certificate_regression :
  forall (project_select : _select_list T)
      (filter_formula : formula_expr T relname)
      (outputs : list (attribute T))
      (row_map : tuple T -> sql_outcome (tuple T))
      (group_select : _select_list T) (group_terms : list (@aggterm T))
      (having : formula_expr T relname) (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_Filter filter_formula
          (QExpr_RowMap outputs row_map
            (QExpr_Group group_select group_terms having input)))) = true.
Proof. reflexivity. Qed.

Theorem transparent_stack_group_bag_closed_regression :
  forall env project_select filter_formula outputs row_map
      group_select group_terms having input,
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_Project project_select
            (QExpr_Filter filter_formula
              (QExpr_RowMap outputs row_map
                (QExpr_Group group_select group_terms having input))))
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
  forall (project_select group_select : _select_list T)
      (keys : list (sort_key T)) (group_terms : list (@aggterm T))
      (having : formula_expr T relname) (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_OrderBy keys
          (QExpr_Group group_select group_terms having input))) = false.
Proof. reflexivity. Qed.

Example project_offset_group_not_closure_certified_regression :
  forall (project_select group_select : _select_list T) (count : nat)
      (group_terms : list (@aggterm T)) (having : formula_expr T relname)
      (input : query_expr T relname),
    query_expr_permutation_closure_certified
      (QExpr_Project project_select
        (QExpr_Offset count
          (QExpr_Group group_select group_terms having input))) = false.
Proof. reflexivity. Qed.

Example project_fetch_group_not_closure_certified_regression :
  forall (project_select group_select : _select_list T) (count : nat)
      (group_terms : list (@aggterm T)) (having : formula_expr T relname)
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
  forall env outputs table select_list formula (keep : tuple T -> bool),
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    query_has_success env
      (QExpr_Filter formula
        (QExpr_Project select_list (QExpr_Table outputs table))).
Proof.
intros env outputs table select_list formula keep Hselect Hformula.
eapply query_expr_filter_has_success_exact; [exact Hformula |].
eapply query_expr_project_has_success_safe; [exact Hselect |].
apply query_table_has_success.
Qed.

Theorem project_error_iff_safe_regression :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    forall error,
      eval_query env (QExpr_Project select_list input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros; now apply eval_query_expr_project_error_iff_safe.
Qed.

(** A base table supplies the child-functionality premise required by exact
    proper filtering. *)
Theorem filter_table_success_bags_functional_regression :
  forall env outputs table formula (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    forall first second,
      success_bags env
        (QExpr_Filter formula (QExpr_Table outputs table)) first ->
      success_bags env
        (QExpr_Filter formula (QExpr_Table outputs table)) second ->
      bag_eq T first second.
Proof.
intros env outputs table formula keep Hproper Hexact
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
  forall env outputs table formula (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_Filter formula (QExpr_Table outputs table))
          (SqlSuccess rows)).
Proof.
intros env outputs table formula keep Hproper Hexact.
eapply query_expr_filter_bag_closed_exact.
- exact Hproper.
- exact Hexact.
- apply query_bag_reset_sound; reflexivity.
Qed.

Theorem project_table_bag_closed_regression :
  forall env outputs table select_list,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_Project select_list (QExpr_Table outputs table))
          (SqlSuccess rows)).
Proof.
intros env outputs table select_list Hsafe.
apply query_expr_project_bag_closed_safe; [exact Hsafe |].
apply query_bag_reset_sound; reflexivity.
Qed.

(** A final projection over a grouped child is the shape exercised by the
    harder FULL JOIN/grouping rewrites: closure stops at the immediate Group
    reset and never inspects its input tree. *)
Theorem project_group_bag_closed_regression :
  forall env outputs table project_select group_select group_terms having,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) project_select = None) ->
    BagClosed T
      (fun rows =>
        eval_query env
          (QExpr_Project project_select
            (QExpr_Group group_select group_terms having
              (QExpr_Table outputs table)))
          (SqlSuccess rows)).
Proof.
intros env outputs table project_select group_select group_terms having Hsafe.
apply query_expr_project_bag_closed_safe; [exact Hsafe |].
apply query_bag_reset_sound; reflexivity.
Qed.

(** The project bridge is intentionally tested on a list-sensitive parent
    whose table child is bag-closed.  Its possible-bag premise is reflexive,
    while the bridge itself reconstructs ordered projection observations. *)
Theorem project_table_outcome_from_success_bags_regression :
  forall env outputs table select_list,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_outcome_equiv env
      (QExpr_Project select_list (QExpr_Table outputs table))
      (QExpr_Project select_list (QExpr_Table outputs table)).
Proof.
intros env outputs table select_list Hsafe.
assert (Hsuccess : query_has_success env
  (QExpr_Project select_list (QExpr_Table outputs table))).
{
  eapply query_expr_project_has_success_safe; [exact Hsafe |].
  apply query_table_has_success.
}
eapply query_expr_project_outcome_equiv_of_success_bags_safe_closed.
- reflexivity.
- exact Hsafe.
- exact Hsafe.
- apply query_bag_reset_sound; reflexivity.
- apply query_bag_reset_sound; reflexivity.
- intro bag; tauto.
- destruct Hsuccess as [rows Hrows].
  now exists (SqlSuccess rows).
- destruct Hsuccess as [rows Hrows].
  now exists (SqlSuccess rows).
- intro error; tauto.
Qed.

End OrderedGroupChildOutcomeRegression.

Print Assumptions eval_query_expr_group_outcome_iff_of_child_outcome_equiv.
Print Assumptions query_expr_group_outcome_equiv_congr.
Print Assumptions query_table_has_success.
Print Assumptions query_expr_project_has_success_safe.
Print Assumptions eval_query_expr_project_error_iff_safe.
Print Assumptions query_expr_filter_has_success_exact.
Print Assumptions query_filter_success_bags_functional_exact.
Print Assumptions query_expr_filter_bag_closed_exact.
Print Assumptions query_expr_project_bag_closed_safe.
Print Assumptions query_expr_project_outcome_equiv_of_success_bags_safe_closed.
Print Assumptions query_structural_successes_bag_closed.
