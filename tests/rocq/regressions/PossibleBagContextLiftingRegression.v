(******************************************************************************)
(** Generic possible-bag/outcome context lifting and fail-closed boundaries.  *)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Permutation NArith.
From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
  GenericInstance Values
  SqlOutcome SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics SqlQueryFacts
  SqlQueryContexts.
From Logos.FormalSQL Require Import TNullSyntax ProofAgentFacade.

Import Tuple.
Import ListNotations.

Section GenericPossibleBagOutcomeContract.

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
Variable env : Env.env T.

Local Definition bagT := Febag.bag (Fecol.CBag (CTuple T)).

Local Definition EvalPossible (query : query_expr T relname) :=
  @eval_query_expr_possible_outcome T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env query.

Local Definition PossibleBagOutcomes (query : query_expr T relname) :
    sql_outcome bagT -> Prop :=
  @query_possible_bag_outcomes T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env query.

Local Definition ScheduledBagOutcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (query : query_expr T relname) : sql_outcome bagT -> Prop :=
  @query_scheduled_bag_outcomes T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule env query.

Local Definition ScheduledRows
    (schedule : boolean_site -> boolean_evaluation_order)
    (query : query_expr T relname) :
    sql_outcome (list (tuple T)) -> Prop :=
  @eval_query_expr_outcome T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule env query.

Local Definition PossibleBagOutcomeEq
    (left right : query_expr T relname) : Prop :=
  @query_expr_possible_bag_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left right.

Local Definition PossibleOutcomeEq
    (left right : query_expr T relname) : Prop :=
  @query_expr_possible_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left right.

Example possible_bag_contract_intro_regression :
  forall left right,
    query_expr_outputs left = query_expr_outputs right ->
    outcome_relation_equiv (@bag_eq T)
      (PossibleBagOutcomes left) (PossibleBagOutcomes right) ->
    PossibleBagOutcomeEq left right.
Proof.
intros left right Houtputs Houtcomes.
unfold PossibleBagOutcomeEq, PossibleBagOutcomes.
now apply query_expr_possible_bag_outcome_equiv_intro.
Qed.

Example possible_bag_contract_projections_regression :
  forall left right,
    PossibleBagOutcomeEq left right ->
    query_expr_outputs left = query_expr_outputs right /\
    outcome_relation_equiv (@bag_eq T)
      (PossibleBagOutcomes left) (PossibleBagOutcomes right).
Proof.
intros left right Hequiv; split.
- unfold PossibleBagOutcomeEq in Hequiv.
  now apply query_expr_possible_bag_outcome_equiv_outputs in Hequiv.
- unfold PossibleBagOutcomeEq in Hequiv.
  unfold PossibleBagOutcomes.
  now apply query_expr_possible_bag_outcome_equiv_outcomes in Hequiv.
Qed.

(** Forgetting exact list order is always sound and keeps error outcomes. *)
Example exact_possible_outcome_to_possible_bag_regression :
  forall left right,
    PossibleOutcomeEq left right ->
    PossibleBagOutcomeEq left right.
Proof.
intros left right Hequiv.
unfold PossibleOutcomeEq, PossibleBagOutcomeEq in *.
now apply query_expr_possible_outcome_equiv_implies_possible_bag_outcome_equiv.
Qed.

Example possible_bag_outcomes_are_scheduled_union_regression :
  forall query outcome,
    PossibleBagOutcomes query outcome <->
    exists schedule, ScheduledBagOutcomes schedule query outcome.
Proof.
intros query outcome.
unfold PossibleBagOutcomes, ScheduledBagOutcomes.
apply query_possible_bag_outcomes_iff_scheduled.
Qed.

Example schedule_transport_to_possible_bag_regression :
  forall left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    PossibleBagOutcomeEq left right.
Proof.
intros left right Htransport.
unfold PossibleBagOutcomeEq.
now apply
  query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
Qed.

(** The reverse direction is deliberately all-representatives reasoning:
    [BagClosed] is required for both actual success-list relations.  No chosen
    representative can justify OFFSET/FETCH or any other ordered observation. *)
Example possible_bag_to_exact_possible_outcome_closed_regression :
  forall left right,
    BagClosed T (fun rows => EvalPossible left (SqlSuccess rows)) ->
    BagClosed T (fun rows => EvalPossible right (SqlSuccess rows)) ->
    PossibleBagOutcomeEq left right ->
    PossibleOutcomeEq left right.
Proof.
intros left right Hleft_closed Hright_closed Hequiv.
unfold EvalPossible, PossibleBagOutcomeEq, PossibleOutcomeEq in *.
eapply query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv;
  eassumption.
Qed.

(** Dedicated constructor adapters are exercised as proofs, rather than only
    looked up below.  DISTINCT, RANK, and ORDER BY consume the complete child
    bag contract while retaining their actual result-list observations. *)
Example distinct_possible_bag_adapter_regression :
  forall left right,
    PossibleBagOutcomeEq left right ->
    PossibleOutcomeEq (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros left right Hequiv.
unfold PossibleBagOutcomeEq, PossibleOutcomeEq in *.
now apply
  query_expr_distinct_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Qed.

Example rank_possible_bag_adapter_regression :
  forall partition_keys order_keys rank_attribute rank_value left right,
    PossibleBagOutcomeEq left right ->
    PossibleOutcomeEq
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value right).
Proof.
intros partition_keys order_keys rank_attribute rank_value left right Hequiv.
unfold PossibleBagOutcomeEq, PossibleOutcomeEq in *.
now apply query_expr_rank_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Qed.

Example order_by_possible_bag_adapter_regression :
  forall keys left right,
    PossibleBagOutcomeEq left right ->
    PossibleOutcomeEq
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
Proof.
intros keys left right Hequiv.
unfold PossibleBagOutcomeEq, PossibleOutcomeEq in *.
now apply
  query_expr_order_by_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Qed.

(** OFFSET and FETCH expose both all-representatives premises at every use.
    This prevents an accidental weakening to a chosen bag representative. *)
Example offset_possible_bag_adapter_requires_both_closed_regression :
  forall count left right,
    BagClosed T (fun rows => EvalPossible left (SqlSuccess rows)) ->
    BagClosed T (fun rows => EvalPossible right (SqlSuccess rows)) ->
    PossibleBagOutcomeEq left right ->
    PossibleOutcomeEq
      (QExpr_Offset count left) (QExpr_Offset count right).
Proof.
intros count left right Hleft_closed Hright_closed Hequiv.
unfold EvalPossible, PossibleBagOutcomeEq, PossibleOutcomeEq in *.
eapply query_expr_offset_possible_outcome_equiv_of_possible_bag_outcome_equiv;
  eassumption.
Qed.

Example fetch_possible_bag_adapter_requires_both_closed_regression :
  forall count left right,
    BagClosed T (fun rows => EvalPossible left (SqlSuccess rows)) ->
    BagClosed T (fun rows => EvalPossible right (SqlSuccess rows)) ->
    PossibleBagOutcomeEq left right ->
    PossibleOutcomeEq
      (QExpr_Fetch count left) (QExpr_Fetch count right).
Proof.
intros count left right Hleft_closed Hright_closed Hequiv.
unfold EvalPossible, PossibleBagOutcomeEq, PossibleOutcomeEq in *.
eapply query_expr_fetch_possible_outcome_equiv_of_possible_bag_outcome_equiv;
  eassumption.
Qed.

Variable unary_operation : @unary_bag_outcome_relation T.
Variable binary_operation : @binary_bag_outcome_relation T.
Variables first_inputs second_inputs fixed_inputs :
  @possible_bag_outcome_relation T.

(** Unary context compatibility is outcome-level: it retains successful bag
    multiplicity, relation inhabitation, and exact runtime-error categories. *)
Example unary_possible_bag_outcome_context_regression :
  @unary_bag_outcome_relation_compatible T unary_operation ->
  outcome_relation_equiv (@bag_eq T) first_inputs second_inputs ->
  outcome_relation_equiv (@bag_eq T)
    (@plug_possible_bag_outcome_context T
      (@PBOC_Unary T unary_operation (@PBOC_Hole T)) first_inputs)
    (@plug_possible_bag_outcome_context T
      (@PBOC_Unary T unary_operation (@PBOC_Hole T)) second_inputs).
Proof.
intros Hoperation Hinputs.
eapply possible_bag_outcome_context_congr.
- cbn; now split.
- exact Hinputs.
Qed.

(** Both hole positions of a binary context require one inhabited fixed input;
    this prevents vacuous equivalence from hiding an unevaluated/error branch. *)
Example binary_possible_bag_outcome_context_regression :
  @binary_bag_outcome_relation_compatible T binary_operation ->
  @possible_bag_outcome_relation_inhabited T fixed_inputs ->
  outcome_relation_equiv (@bag_eq T) first_inputs second_inputs ->
  outcome_relation_equiv (@bag_eq T)
    (@plug_possible_bag_outcome_context T
      (@PBOC_BinaryLeft T binary_operation (@PBOC_Hole T) fixed_inputs)
      first_inputs)
    (@plug_possible_bag_outcome_context T
      (@PBOC_BinaryLeft T binary_operation (@PBOC_Hole T) fixed_inputs)
      second_inputs) /\
  outcome_relation_equiv (@bag_eq T)
    (@plug_possible_bag_outcome_context T
      (@PBOC_BinaryRight T binary_operation fixed_inputs (@PBOC_Hole T))
      first_inputs)
    (@plug_possible_bag_outcome_context T
      (@PBOC_BinaryRight T binary_operation fixed_inputs (@PBOC_Hole T))
      second_inputs).
Proof.
intros Hoperation Hfixed Hinputs; split.
- eapply possible_bag_outcome_context_congr.
  + change
      (@binary_bag_outcome_relation_compatible T binary_operation /\
       True /\
       @possible_bag_outcome_relation_inhabited T fixed_inputs).
    split; [exact Hoperation |].
    split; [exact I | exact Hfixed].
  + exact Hinputs.
- eapply possible_bag_outcome_context_congr.
  + change
      (@binary_bag_outcome_relation_compatible T binary_operation /\
       @possible_bag_outcome_relation_inhabited T fixed_inputs /\ True).
    split; [exact Hoperation |].
    split; [exact Hfixed | exact I].
  + exact Hinputs.
Qed.

Variable context : @possible_bag_outcome_context T.
Variables child_left child_right parent_left parent_right :
  query_expr T relname.

(** Actual query use remains fail-closed.  Both parent abstractions need exact,
    two-sided [rel_equiv] characterizations; these are where a concrete SQL
    operator accounts for shared schedules, correlation, NULL/Bool3, tuple
    order and multiplicity, group/window local outcomes, and runtime errors. *)
Example exact_query_boundary_characterization_regression :
  @possible_bag_outcome_context_well_formed T context ->
  PossibleBagOutcomeEq child_left child_right ->
  query_expr_outputs parent_left = query_expr_outputs parent_right ->
  rel_equiv
    (PossibleBagOutcomes parent_left)
    (@plug_possible_bag_outcome_context T context
      (PossibleBagOutcomes child_left)) ->
  rel_equiv
    (PossibleBagOutcomes parent_right)
    (@plug_possible_bag_outcome_context T context
      (PossibleBagOutcomes child_right)) ->
  PossibleBagOutcomeEq parent_left parent_right.
Proof.
intros Hcontext Hchildren Houtputs Hleft Hright.
unfold PossibleBagOutcomeEq, PossibleBagOutcomes in *.
eapply query_expr_possible_bag_outcome_context_boundary_congr; eassumption.
Qed.

(** The unary wrapper consumes a complete local parent law under exactly the
    schedule pair supplied by child transport; it never guesses that law. *)
Example unary_schedule_wrapper_regression :
  @query_expr_possible_bag_schedule_transport T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env child_left child_right ->
  query_expr_outputs parent_left = query_expr_outputs parent_right ->
  (forall left_schedule right_schedule,
    outcome_relation_equiv (@bag_eq T)
      (ScheduledBagOutcomes left_schedule child_left)
      (ScheduledBagOutcomes right_schedule child_right) ->
    outcome_relation_equiv (@bag_eq T)
      (ScheduledBagOutcomes left_schedule parent_left)
      (ScheduledBagOutcomes right_schedule parent_right)) ->
  PossibleBagOutcomeEq parent_left parent_right.
Proof.
intros Hchildren Houtputs Hlocal.
unfold ScheduledBagOutcomes, PossibleBagOutcomeEq in *.
eapply query_expr_possible_bag_unary_wrapper_congr; eassumption.
Qed.

Variables left_first left_second right_first right_second :
  query_expr T relname.

(** The binary contract carries one jointly chosen target schedule for both
    child pairs.  This is stronger than two independent marginal transports
    and is the required boundary for Set/Natural/Cross/Join wrappers. *)
Example joint_binary_schedule_wrapper_regression :
  @query_expr_possible_bag_joint_schedule_transport T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left_first left_second right_first right_second ->
  query_expr_outputs parent_left = query_expr_outputs parent_right ->
  (forall left_schedule right_schedule,
    outcome_relation_equiv (@bag_eq T)
      (ScheduledBagOutcomes left_schedule left_first)
      (ScheduledBagOutcomes right_schedule right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (ScheduledBagOutcomes left_schedule left_second)
      (ScheduledBagOutcomes right_schedule right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (ScheduledBagOutcomes left_schedule parent_left)
      (ScheduledBagOutcomes right_schedule parent_right)) ->
  PossibleBagOutcomeEq parent_left parent_right.
Proof.
intros Hjoint Houtputs Hlocal.
unfold ScheduledBagOutcomes, PossibleBagOutcomeEq in *.
eapply query_expr_possible_bag_binary_wrapper_congr; eassumption.
Qed.

(** The finalized binary constructor layer consumes the joint schedule
    transport directly.  All four set operations are instantiated so this
    regression fails if any variant falls out of the public family. *)
Example set_possible_bag_adapters_all_operations_regression :
  @query_expr_possible_bag_joint_schedule_transport T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left_first left_second right_first right_second ->
  PossibleBagOutcomeEq
    (QExpr_Set Union left_first left_second)
    (QExpr_Set Union right_first right_second) /\
  PossibleBagOutcomeEq
    (QExpr_Set UnionMax left_first left_second)
    (QExpr_Set UnionMax right_first right_second) /\
  PossibleBagOutcomeEq
    (QExpr_Set Inter left_first left_second)
    (QExpr_Set Inter right_first right_second) /\
  PossibleBagOutcomeEq
    (QExpr_Set Diff left_first left_second)
    (QExpr_Set Diff right_first right_second).
Proof.
intro Hjoint; split.
- unfold PossibleBagOutcomeEq.
  eapply query_expr_set_possible_bag_outcome_equiv; exact Hjoint.
- split.
  + unfold PossibleBagOutcomeEq.
    eapply query_expr_set_possible_bag_outcome_equiv; exact Hjoint.
  + split; unfold PossibleBagOutcomeEq;
      eapply query_expr_set_possible_bag_outcome_equiv; exact Hjoint.
Qed.

Example natural_join_possible_bag_adapter_regression :
  @query_expr_possible_bag_joint_schedule_transport T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left_first left_second right_first right_second ->
  PossibleBagOutcomeEq
    (QExpr_NaturalJoin left_first left_second)
    (QExpr_NaturalJoin right_first right_second).
Proof.
intro Hjoint; unfold PossibleBagOutcomeEq.
now apply query_expr_natural_join_possible_bag_outcome_equiv.
Qed.

Example cross_join_possible_bag_adapter_regression :
  @query_expr_possible_bag_joint_schedule_transport T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left_first left_second right_first right_second ->
  PossibleBagOutcomeEq
    (QExpr_CrossJoin left_first left_second)
    (QExpr_CrossJoin right_first right_second).
Proof.
intro Hjoint; unfold PossibleBagOutcomeEq.
now apply query_expr_cross_join_possible_bag_outcome_equiv.
Qed.

(** Separate joint premises expose a changed left hole and a changed right
    hole.  Sharing the syntactic fixed child does not waive its obligation to
    be matched under the one schedule selected for the other child. *)
Example set_possible_bag_adapter_both_hole_positions_regression :
  forall operation changed_left changed_right fixed,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env changed_left fixed changed_right fixed ->
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env fixed changed_left fixed changed_right ->
    PossibleBagOutcomeEq
      (QExpr_Set operation changed_left fixed)
      (QExpr_Set operation changed_right fixed) /\
    PossibleBagOutcomeEq
      (QExpr_Set operation fixed changed_left)
      (QExpr_Set operation fixed changed_right).
Proof.
intros operation changed_left changed_right fixed Hleft Hright; split;
  unfold PossibleBagOutcomeEq.
- now apply query_expr_set_possible_bag_outcome_equiv.
- now apply query_expr_set_possible_bag_outcome_equiv.
Qed.

(** JOIN remains generic in its join kind.  Its local premise is precisely
    compatibility of the two authoritative bag evaluators, including local
    predicate/projection errors and multiplicity behavior. *)
Example join_possible_bag_adapter_regression :
  forall kind predicate matched_select left_select right_select,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left_first)
        (ScheduledBagOutcomes right_schedule right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left_second)
        (ScheduledBagOutcomes right_schedule right_second) ->
      query_binary_bag_outcome_operations_compatible
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env kind predicate
          matched_select left_select right_select)
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env kind predicate
          matched_select left_select right_select)) ->
    PossibleBagOutcomeEq
      (QExpr_Join kind predicate matched_select left_select right_select
        left_first left_second)
      (QExpr_Join kind predicate matched_select left_select right_select
        right_first right_second).
Proof.
intros kind predicate matched_select left_select right_select Hjoint Hlocal.
unfold ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_join_possible_bag_outcome_equiv; eassumption.
Qed.

(** Independent schedule marginals cannot in general be combined into the
    one target schedule required by a binary SQL constructor.  The first
    component below can be matched only by the same Boolean choice, while the
    second can be matched only by the opposite choice.  Each marginal has a
    witness, but the pair has none.  This finite witness is the reason the
    production binary contract carries a joint schedule transport premise. *)
Example independent_schedule_matches_do_not_supply_joint_match :
  (forall left : bool, exists right : bool, right = left) /\
  (forall left : bool, exists right : bool, negb right = left) /\
  ~ (forall left : bool,
      exists right : bool, right = left /\ negb right = left).
Proof.
split.
- intro left; now exists left.
- split.
  + intro left; exists (negb left); now destruct left.
  + intro Hjoint.
    destruct (Hjoint false) as [[|] [Hsame Hopposite]];
      discriminate.
Qed.

Local Definition UniformScheduledOutcomeEq
    (left right : query_expr T relname) : Prop :=
  @query_expr_uniform_scheduled_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null env left right.

(** Binary set composition preserves one shared Boolean schedule on each side;
    two unrelated existential schedule witnesses are intentionally insufficient. *)
Example set_shared_schedule_regression :
  forall operation left left' right right',
    UniformScheduledOutcomeEq left left' ->
    UniformScheduledOutcomeEq right right' ->
    PossibleOutcomeEq
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
Proof.
intros operation left left' right right' Hleft Hright.
unfold UniformScheduledOutcomeEq, PossibleOutcomeEq in *.
now apply query_expr_set_possible_outcome_equiv_congr_uniform.
Qed.

Variables left_predicate right_predicate :
  @scalar_expr T relname ScalarResultBoolean.
Variable filter_input : query_expr T relname.

(** A filter rewrite retains exact typed Bool3 outcomes for every environment
    and schedule, including predicate errors; TRUE-acceptance alone is not this
    premise and is not synthesized by the regression. *)
Example filter_bool3_error_boundary_regression :
  @scalar_expr_uniform_global_outcome_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null ScalarResultBoolean left_predicate right_predicate ->
  (exists outcome,
    EvalPossible (QExpr_Filter left_predicate filter_input) outcome) ->
  PossibleOutcomeEq
    (QExpr_Filter left_predicate filter_input)
    (QExpr_Filter right_predicate filter_input).
Proof.
intros Hpredicate Houtcome.
unfold EvalPossible, PossibleOutcomeEq in *.
now apply query_expr_filter_predicate_possible_outcome_equiv.
Qed.

Variables left_select right_select :
  list (@scalar_expr T relname ScalarResultValue * attribute T).
Variable group_keys : list (@scalar_expr T relname ScalarResultValue).
Variables left_having right_having :
  @scalar_expr T relname ScalarResultBoolean.
Variable group_input : query_expr T relname.

(** GROUP lifting exposes exact local group-list outcomes under the same
    schedule and group environment.  This blocks an unrestricted bag lift for
    order-sensitive aggregate finalization such as floating SUM/AVG. *)
Example group_exact_local_outcome_boundary_regression :
  scalar_select_outputs left_select = scalar_select_outputs right_select ->
  (forall schedule current_env group_terms groups outcome,
    @eval_groups_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule current_env
      left_select group_terms left_having groups outcome <->
    @eval_groups_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule current_env
      right_select group_terms right_having groups outcome) ->
  (exists outcome,
    EvalPossible
      (QExpr_Group left_select group_keys left_having group_input) outcome) ->
  PossibleOutcomeEq
    (QExpr_Group left_select group_keys left_having group_input)
    (QExpr_Group right_select group_keys right_having group_input).
Proof.
intros Houtputs Hlocal Houtcome.
unfold EvalPossible, PossibleOutcomeEq in *.
eapply query_expr_group_possible_outcome_equiv_of_exact_local_outcomes;
  eassumption.
Qed.

(** WINDOW composition retains same-schedule child equivalence plus explicit
    per-schedule parent outcomes.  Partition/order legality, peer choices,
    local aggregate finalization, and errors stay inside those exact outcomes. *)
Example window_shared_schedule_local_outcome_regression :
  forall partition_keys order_keys items left right,
    UniformScheduledOutcomeEq left right ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env
        (QExpr_Window partition_keys order_keys items left) outcome) ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env
        (QExpr_Window partition_keys order_keys items right) outcome) ->
    PossibleOutcomeEq
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
Proof.
intros partition_keys order_keys items left right
  Hchildren Hleft Hright.
unfold UniformScheduledOutcomeEq, PossibleOutcomeEq in *.
eapply query_expr_window_possible_outcome_equiv_congr_uniform; eassumption.
Qed.

(** Concrete unary adapters expose the authoritative local row-to-bag
    operation reached after one successful child observation.  These are
    intentionally stronger premises than equality of possible child bags. *)
Example project_possible_bag_adapter_regression :
  forall
      (left_project right_project :
        list (@scalar_expr T relname ScalarResultValue * attribute T))
      (left right : query_expr T relname),
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_project = scalar_select_outputs right_project ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left)
        (ScheduledBagOutcomes right_schedule right) ->
      scheduled_local_rows_to_bag_contract
        (ScheduledRows left_schedule left)
        (ScheduledRows right_schedule right)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_project)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_project)) ->
    PossibleBagOutcomeEq
      (QExpr_Project left_project left)
      (QExpr_Project right_project right).
Proof.
intros left_project right_project left right Hchildren Houtputs Hlocal.
unfold ScheduledRows, ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_project_possible_bag_outcome_equiv; eassumption.
Qed.

Example row_map_possible_bag_adapter_regression :
  forall (left_outputs right_outputs : list (attribute T))
      (left_map right_map : tuple T -> sql_outcome (tuple T))
      (left right : query_expr T relname),
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    left_outputs = right_outputs ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left)
        (ScheduledBagOutcomes right_schedule right) ->
      scheduled_local_rows_to_bag_contract
        (ScheduledRows left_schedule left)
        (ScheduledRows right_schedule right)
        (@query_row_map_rows_bag_outcomes T left_map)
        (@query_row_map_rows_bag_outcomes T right_map)) ->
    PossibleBagOutcomeEq
      (QExpr_RowMap left_outputs left_map left)
      (QExpr_RowMap right_outputs right_map right).
Proof.
intros left_outputs right_outputs left_map right_map left right
  Hchildren Houtputs Hlocal.
unfold ScheduledRows, ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_row_map_possible_bag_outcome_equiv; eassumption.
Qed.

Example filter_possible_bag_adapter_regression :
  forall
      (left_filter right_filter :
        @scalar_expr T relname ScalarResultBoolean)
      (left right : query_expr T relname),
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left)
        (ScheduledBagOutcomes right_schedule right) ->
      scheduled_local_rows_to_bag_contract
        (ScheduledRows left_schedule left)
        (ScheduledRows right_schedule right)
        (@query_filter_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_filter)
        (@query_filter_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_filter)) ->
    PossibleBagOutcomeEq
      (QExpr_Filter left_filter left)
      (QExpr_Filter right_filter right).
Proof.
intros left_filter right_filter left right Hchildren Hlocal.
unfold ScheduledRows, ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_filter_possible_bag_outcome_equiv; eassumption.
Qed.

Example group_possible_bag_adapter_regression :
  forall
      (left_group_select right_group_select :
        list (@scalar_expr T relname ScalarResultValue * attribute T))
      (left_group_keys right_group_keys :
        list (@scalar_expr T relname ScalarResultValue))
      (left_group_having right_group_having :
        @scalar_expr T relname ScalarResultBoolean)
      (left right : query_expr T relname),
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_group_select =
      scalar_select_outputs right_group_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left)
        (ScheduledBagOutcomes right_schedule right) ->
      scheduled_local_rows_to_bag_contract
        (ScheduledRows left_schedule left)
        (ScheduledRows right_schedule right)
        (@query_group_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null left_schedule env
          left_group_select left_group_keys left_group_having)
        (@query_group_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null right_schedule env
          right_group_select right_group_keys right_group_having)) ->
    PossibleBagOutcomeEq
      (QExpr_Group left_group_select left_group_keys left_group_having left)
      (QExpr_Group right_group_select right_group_keys right_group_having right).
Proof.
intros left_group_select right_group_select
  left_group_keys right_group_keys left_group_having right_group_having
  left right Hchildren Houtputs Hlocal.
unfold ScheduledRows, ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_group_possible_bag_outcome_equiv; eassumption.
Qed.

Example grouping_sets_possible_bag_adapter_regression :
  forall (left_sets right_sets : list (@query_grouping_set T relname))
      (left right : query_expr T relname),
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_grouping_sets_outputs T relname left_sets =
      @query_grouping_sets_outputs T relname right_sets ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left)
        (ScheduledBagOutcomes right_schedule right) ->
      scheduled_local_rows_to_bag_contract
        (ScheduledRows left_schedule left)
        (ScheduledRows right_schedule right)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_sets)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_sets)) ->
    PossibleBagOutcomeEq
      (QExpr_GroupingSets left_sets left)
      (QExpr_GroupingSets right_sets right).
Proof.
intros left_sets right_sets left right Hchildren Houtputs Hlocal.
unfold ScheduledRows, ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_grouping_sets_possible_bag_outcome_equiv; eassumption.
Qed.

Example window_possible_bag_adapter_regression :
  forall (left_partition left_order : list (SqlOrder.sort_key T))
      (left_window_items : list (query_window_item T))
      (right_partition right_order : list (SqlOrder.sort_key T))
      (right_window_items : list (query_window_item T))
      (left right : query_expr T relname),
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    map (@qwi_attribute T) left_window_items =
      map (@qwi_attribute T) right_window_items ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (ScheduledBagOutcomes left_schedule left)
        (ScheduledBagOutcomes right_schedule right) ->
      scheduled_local_rows_to_bag_contract
        (ScheduledRows left_schedule left)
        (ScheduledRows right_schedule right)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          left_partition left_order left_window_items)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          right_partition right_order right_window_items)) ->
    PossibleBagOutcomeEq
      (QExpr_Window left_partition left_order left_window_items left)
      (QExpr_Window right_partition right_order right_window_items right).
Proof.
intros left_partition left_order left_window_items
  right_partition right_order right_window_items left right
  Hchildren Houtputs Hlocal.
unfold ScheduledRows, ScheduledBagOutcomes in Hlocal.
unfold PossibleBagOutcomeEq.
eapply query_expr_window_possible_bag_outcome_equiv; eassumption.
Qed.

(** ROW MAP is sequential over the exact child list.  These applications of
    the authoritative semantics facts pin down first-error propagation and
    preservation of successful row order without unfolding the evaluator. *)
Variable row_adapter : tuple T -> sql_outcome (tuple T).

Example row_map_first_error_regression :
  forall first later rest first_error later_error,
    row_adapter first = SqlError first_error ->
    row_adapter later = SqlError later_error ->
    row_map_rows_outcome row_adapter (first :: later :: rest) =
      SqlError first_error.
Proof.
intros first later rest first_error later_error Hfirst _.
eapply row_map_rows_outcome_head_error; exact Hfirst.
Qed.

Example row_map_tail_error_after_success_regression :
  forall first later rest mapped_first later_error,
    row_adapter first = SqlSuccess mapped_first ->
    row_adapter later = SqlError later_error ->
    row_map_rows_outcome row_adapter (first :: later :: rest) =
      SqlError later_error.
Proof.
intros first later rest mapped_first later_error Hfirst Hlater.
eapply row_map_rows_outcome_tail_error; [exact Hfirst |].
eapply row_map_rows_outcome_head_error; exact Hlater.
Qed.

Example row_map_success_order_regression :
  forall first second rest mapped_first mapped_second mapped_rest,
    row_adapter first = SqlSuccess mapped_first ->
    row_adapter second = SqlSuccess mapped_second ->
    row_map_rows_outcome row_adapter rest = SqlSuccess mapped_rest ->
    row_map_rows_outcome row_adapter (first :: second :: rest) =
      SqlSuccess (mapped_first :: mapped_second :: mapped_rest).
Proof.
intros first second rest mapped_first mapped_second mapped_rest
  Hfirst Hsecond Hrest.
eapply row_map_rows_outcome_cons_success; [exact Hfirst |].
eapply row_map_rows_outcome_cons_success; eassumption.
Qed.

End GenericPossibleBagOutcomeContract.

(** Ordinary list permutation is the neutral finite-bag equality witness.
    Nevertheless, FETCH's [firstn] and OFFSET's [skipn] observe different
    positions on these two representatives.  A single representative is
    therefore not a sound top-k certificate. *)
Example bag_equal_representatives_disagree_positionally :
  Permutation [0; 1] [1; 0] /\
  firstn 1 [0; 1] <> firstn 1 [1; 0] /\
  skipn 1 [0; 1] <> skipn 1 [1; 0].
Proof.
split.
- apply perm_swap.
- split; cbn; discriminate.
Qed.

(** The concrete SUM/AVG fail-closed boundary reuses the authoritative
    floating-point witnesses.  Only the named aggregate interpreter is
    reduced; no query evaluator is unfolded. *)
Example float_sum_order_sensitive_boundary_regression :
  exists first second third,
    NullValues.interp_sum_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some second);
       NullValues.Value_float (Some third)] <>
    NullValues.interp_sum_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some third);
       NullValues.Value_float (Some second)].
Proof.
destruct float32_add_order_sensitive as
  [first [second [third Horder]]].
exists first, second, third.
cbn [NullValues.interp_sum_float].
intro Hequal; injection Hequal as Hequal; now apply Horder.
Qed.

Example float_average_order_sensitive_boundary_regression :
  exists first second third,
    NullValues.interp_avg_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some second);
       NullValues.Value_float (Some third)] <>
    NullValues.interp_avg_float
      [NullValues.Value_float (Some first);
       NullValues.Value_float (Some third);
       NullValues.Value_float (Some second)].
Proof.
destruct float32_average_order_sensitive as
  [first [second [third Horder]]].
exists first, second, third.
cbn [NullValues.interp_avg_float NullValues.interp_avg_float64_values].
intro Hequal; injection Hequal as Hequal; now apply Horder.
Qed.

Section ConstructorInventories.

(** The arbitrary kind is destructed, so adding a set-operation constructor
    makes this inventory fail until the regression is updated. *)
Example set_operation_inventory_regression (operation : set_op) :
  operation = Union \/ operation = UnionMax \/
  operation = Inter \/ operation = Diff.
Proof.
destruct operation; auto.
Qed.

(** Likewise this is an exhaustive inventory of the shared-child join modes. *)
Example query_join_kind_inventory_regression (kind : query_join_kind) :
  kind = QueryJoinInner \/ kind = QueryJoinLeft \/
  kind = QueryJoinRight \/ kind = QueryJoinFull \/
  kind = QueryJoinSemi \/ kind = QueryJoinAnti.
Proof.
destruct kind.
- now left.
- right; now left.
- right; right; now left.
- right; right; right; now left.
- right; right; right; right; now left.
- right; right; right; right; right; reflexivity.
Qed.

(** The four constructors implement four distinct SQL bag-count operations:
    addition for UNION ALL, maximum for UNION, minimum for INTERSECT, and
    truncated subtraction for EXCEPT. *)
Section SetOperationMultiplicity.

Context {T : Tuple.Rcd}.

Local Definition setBagT := Febag.bag (Fecol.CBag (CTuple T)).

Example query_set_bag_multiplicity_inventory_regression :
  forall (left right : setBagT) row,
    Febag.nb_occ (Fecol.CBag (CTuple T)) row
      (query_set_bag Union left right) =
      N.add
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row left)
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row right) /\
    Febag.nb_occ (Fecol.CBag (CTuple T)) row
      (query_set_bag UnionMax left right) =
      N.max
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row left)
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row right) /\
    Febag.nb_occ (Fecol.CBag (CTuple T)) row
      (query_set_bag Inter left right) =
      N.min
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row left)
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row right) /\
    Febag.nb_occ (Fecol.CBag (CTuple T)) row
      (query_set_bag Diff left right) =
      N.sub
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row left)
        (Febag.nb_occ (Fecol.CBag (CTuple T)) row right).
Proof.
intros left right row; unfold query_set_bag, Febag.interp_set_op; cbn.
repeat split.
- apply Febag.nb_occ_union.
- apply Febag.nb_occ_union_max.
- apply Febag.nb_occ_inter.
- apply Febag.nb_occ_diff.
Qed.

End SetOperationMultiplicity.

End ConstructorInventories.

Section TNullFacadeAliases.

Variables db : TNullDatabase.
Variable tnull_env : TNullEnvironment.
Variables query left right : TNullQueryExpr.

Example tnull_possible_bag_outcomes_alias_regression :
  TNullQueryPossibleBagOutcomes db tnull_env query =
  @query_possible_bag_outcomes TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    tnull_env query.
Proof. reflexivity. Qed.

Example tnull_possible_bag_outcome_equiv_alias_regression :
  TNullQueryExprPossibleBagOutcomeEq db tnull_env left right <->
  @query_expr_possible_bag_outcome_equiv TNull relname
    (@_basesort TNull db) (@_instance TNull db) unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error NullValues.is_null_value
    tnull_env left right.
Proof. reflexivity. Qed.

End TNullFacadeAliases.

(** Facade-exported generic contract and bridge surface. *)
Check TNullQueryPossibleBagOutcomes.
Check TNullQueryExprPossibleBagOutcomeEq.
Check query_possible_bag_outcomes.
Check query_expr_possible_bag_outcome_equiv.
Check query_expr_possible_bag_outcome_equiv_intro.
Check query_expr_possible_bag_outcome_equiv_outputs.
Check query_expr_possible_bag_outcome_equiv_outcomes.
Check query_expr_possible_outcome_equiv_implies_possible_bag_outcome_equiv.
Check query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv.
Check query_scheduled_bag_outcomes.
Check query_possible_bag_outcomes_iff_scheduled.
Check query_expr_possible_bag_schedule_transport.
Check query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
Check query_expr_possible_bag_unary_wrapper_congr.
Check query_expr_possible_bag_joint_schedule_transport.
Check query_expr_possible_bag_binary_wrapper_congr.
Check query_expr_distinct_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Check query_expr_rank_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Check query_expr_order_by_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Check query_expr_offset_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Check query_expr_fetch_possible_outcome_equiv_of_possible_bag_outcome_equiv.
Check lift_possible_bag_outcome_unary_congr.
Check lift_possible_bag_outcome_binary_congr.
Check possible_bag_outcome_context_congr.
Check query_expr_possible_bag_outcome_context_boundary_congr.
Check query_expr_possible_bag_outcome_context_boundary_final.

(** Stable constructor-facing schedule transports and their outcome bridges. *)
Check scheduled_local_rows_to_bag_contract.
Check query_binary_bag_outcome_operations_compatible.
Check query_expr_set_possible_bag_schedule_transport.
Check query_expr_set_possible_bag_outcome_equiv.
Check query_expr_natural_join_possible_bag_schedule_transport.
Check query_expr_natural_join_possible_bag_outcome_equiv.
Check query_expr_cross_join_possible_bag_schedule_transport.
Check query_expr_cross_join_possible_bag_outcome_equiv.
Check query_expr_join_possible_bag_schedule_transport.
Check query_expr_join_possible_bag_outcome_equiv.
Check query_expr_project_possible_bag_schedule_transport.
Check query_expr_project_possible_bag_outcome_equiv.
Check query_expr_row_map_possible_bag_schedule_transport.
Check query_expr_row_map_possible_bag_outcome_equiv.
Check query_expr_filter_possible_bag_schedule_transport.
Check query_expr_filter_possible_bag_outcome_equiv.
Check query_expr_group_possible_bag_schedule_transport.
Check query_expr_group_possible_bag_outcome_equiv.
Check query_expr_grouping_sets_possible_bag_schedule_transport.
Check query_expr_grouping_sets_possible_bag_outcome_equiv.
Check query_expr_window_possible_bag_schedule_transport.
Check query_expr_window_possible_bag_outcome_equiv.

(** Exact scheduled per-family semantics remain visible for concrete parent
    characterizations.  These checks cover every non-leaf query family. *)
Check query_expr_set_global_typed_congr.
Check query_expr_natural_join_global_typed_congr.
Check query_expr_cross_join_global_typed_congr.
Check query_expr_join_global_typed_congr.
Check query_expr_project_global_typed_congr.
Check query_expr_row_map_global_typed_congr.
Check query_expr_filter_global_typed_congr.
Check query_expr_group_global_typed_congr.
Check query_expr_grouping_sets_global_typed_congr.
Check query_expr_rank_global_typed_congr.
Check query_expr_window_global_typed_congr.
Check query_expr_distinct_global_typed_congr.
Check query_expr_order_by_global_typed_congr.
Check query_expr_offset_global_typed_congr.
Check query_expr_fetch_global_typed_congr.

(** Public possible-outcome interfaces expose the sound stronger premises.
    In particular, Group keeps local aggregate outcomes; Window keeps shared
    schedules and parent outcomes; ordered consumers do not accept one bag
    representative as a top-k certificate. *)
Check query_expr_set_possible_outcome_equiv_congr_uniform.
Check query_expr_cross_join_possible_outcome_equiv_congr_uniform.
Check query_expr_join_possible_outcome_equiv_of_uniform_predicate.
Check query_expr_project_select_possible_outcome_equiv.
Check query_expr_filter_predicate_possible_outcome_equiv.
Check query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes.
Check query_expr_group_possible_outcome_equiv_of_exact_local_outcomes.
Check query_expr_group_clauses_possible_outcome_equiv.
Check query_expr_window_possible_outcome_equiv_congr_uniform.
Check query_expr_rank_possible_outcome_equiv_congr.
Check query_expr_distinct_possible_outcome_equiv_congr.
Check query_expr_order_by_possible_outcome_equiv_congr.
Check query_expr_offset_possible_outcome_equiv_congr.
Check query_expr_fetch_possible_outcome_equiv_congr.

Print Assumptions query_expr_possible_bag_outcome_context_boundary_congr.
Print Assumptions query_expr_possible_bag_outcome_context_boundary_final.
Print Assumptions query_expr_set_possible_bag_outcome_equiv.
Print Assumptions query_expr_natural_join_possible_bag_outcome_equiv.
Print Assumptions query_expr_cross_join_possible_bag_outcome_equiv.
Print Assumptions query_expr_join_possible_bag_outcome_equiv.
Print Assumptions query_expr_project_possible_bag_outcome_equiv.
Print Assumptions query_expr_row_map_possible_bag_outcome_equiv.
Print Assumptions query_expr_filter_possible_bag_outcome_equiv.
Print Assumptions query_expr_group_possible_bag_outcome_equiv.
Print Assumptions query_expr_grouping_sets_possible_bag_outcome_equiv.
Print Assumptions query_expr_window_possible_bag_outcome_equiv.
