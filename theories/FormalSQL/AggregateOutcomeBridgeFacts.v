(******************************************************************************)
(** Small value/error bridges from aggregate semantics to group outcomes.    **)
(******************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteSet FiniteBag FiniteCollection
  OrderedSet Env Formula Bool3 Projection SqlOutcome SqlQuerySyntax
  SqlQuerySemantics SqlErrorSemantics.
From Logos.FormalSQL Require Import
  AggregateRuntimeFacts GroupedFilterOutcomeFacts ProofAgentFacade TNullSyntax.
From Stdlib Require Import List Sorting.Permutation ZArith.

Import ListNotations.
Import Tuple.
Import NullValues.

Open Scope Z_scope.

(** COUNT-star observes the number of rows in a group both in its value and in
    its BIGINT overflow check.  The statement includes the aggregate-only and
    full expression check because grouping finalizes the former before HAVING
    and evaluates the latter only for a reached projection. *)
Lemma tnull_group_count_star_value_runtime_exact :
  forall env group_terms group,
    Interp.interp_aggterm TNull
      (Env.env_g TNull env (@Env.Group_By TNull group_terms) group)
      ACountStar =
      value_int64_checked (Z.of_nat (List.length group)) /\
    @eval_aggterm_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull env (@Env.Group_By TNull group_terms) group)
      ACountStar =
      int64_result_runtime_error (Z.of_nat (List.length group)) /\
    @eval_aggterm_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull env (@Env.Group_By TNull group_terms) group)
      ACountStar =
      int64_result_runtime_error (Z.of_nat (List.length group)).
Proof.
  intros env group_terms group.
  unfold ACountStar.
  cbn [Interp.interp_aggterm
    eval_aggterm_aggregate_runtime_error eval_aggterm_runtime_error
    FTerms.variables_ft].
  assert (Hempty :
    Fset.is_empty (A TNull) (Fset.empty (A TNull)) = true).
  { reflexivity. }
  rewrite !Hempty.
  unfold Env.env_g.
  cbn [Interp.unfold_env_slice
    NullValues.interp_aggregate NullValues.interp_aggregate_runtime_error
    NullValues.count_runtime_error NullValues.row_count
    NullValues.observation_values].
  split.
  - lazymatch goal with
    | |- Tuple.interp_aggregate TNull AggregateCountStar ?values = _ =>
        change
          (value_int64_checked (row_count values) =
           value_int64_checked (Z.of_nat (List.length group)))
    end.
    unfold row_count; repeat rewrite length_map; reflexivity.
  - split.
    + lazymatch goal with
      | |- count_runtime_error (observation_values ?observations) = _ =>
          change
            (count_runtime_error (observation_values observations) =
             int64_result_runtime_error (Z.of_nat (List.length group)))
      end.
      unfold count_runtime_error, row_count, observation_values.
      repeat rewrite length_map; reflexivity.
    + lazymatch goal with
      | |- count_runtime_error (observation_values ?observations) = _ =>
          change
            (count_runtime_error (observation_values observations) =
             int64_result_runtime_error (Z.of_nat (List.length group)))
      end.
      unfold count_runtime_error, row_count, observation_values.
      repeat rewrite length_map; reflexivity.
Qed.

(** Equal row cardinality is the complete COUNT-star value/local-error
    observation.  No in-range premise is needed: an out-of-range cardinality
    produces the same NULL placeholder and the same numeric error on both
    sides. *)
Theorem count_star_value_local_error_exact_of_equal_length :
  forall left right,
    List.length left = List.length right ->
    interp_aggregate AggregateCountStar left =
      interp_aggregate AggregateCountStar right /\
    aggregate_local_runtime_error AggregateCountStar left =
      aggregate_local_runtime_error AggregateCountStar right.
Proof.
  intros left right Hlength.
  split.
  - change
      (value_int64_checked (row_count left) =
       value_int64_checked (row_count right)).
    unfold row_count; now rewrite Hlength.
  - change (count_runtime_error left = count_runtime_error right).
    unfold count_runtime_error, row_count; now rewrite Hlength.
Qed.

(** Full COUNT-star observations also depend only on cardinality.  FormalSQL's
    private COUNT-star child is not an SQL expression, so its observation
    errors are intentionally ignored by the aggregate callback. *)
Theorem count_star_value_runtime_error_exact_of_equal_observation_length :
  forall left right,
    List.length left = List.length right ->
    interp_aggregate AggregateCountStar (observation_values left) =
      interp_aggregate AggregateCountStar (observation_values right) /\
    interp_aggregate_runtime_error AggregateCountStar left =
      interp_aggregate_runtime_error AggregateCountStar right.
Proof.
  intros left right Hlength.
  assert (Hvalues :
    List.length (observation_values left) =
    List.length (observation_values right)).
  { now rewrite !observation_values_length. }
  split.
  - exact (proj1
      (count_star_value_local_error_exact_of_equal_length
        (observation_values left) (observation_values right) Hvalues)).
  - rewrite !count_star_runtime_error_observations.
    exact (proj2
      (count_star_value_local_error_exact_of_equal_length
        (observation_values left) (observation_values right) Hvalues)).
Qed.

(** COUNT(expr) agrees exactly with COUNT-star only when every reached
    expression value is non-NULL.  This statement keeps DISTINCT out of the
    contract because duplicate elimination would change COUNT multiplicity. *)
Theorem count_star_count_all_nonnull_value_local_error_exact :
  forall star_values expression_values,
    List.length star_values = List.length expression_values ->
    Forall
      (fun value => NullValues.is_null_value value = false)
      expression_values ->
    interp_aggregate AggregateCountStar star_values =
      interp_aggregate
        (AggregateCall AggregateCount AggregateAll) expression_values /\
    aggregate_local_runtime_error AggregateCountStar star_values =
      aggregate_local_runtime_error
        (AggregateCall AggregateCount AggregateAll) expression_values.
Proof.
  intros star_values expression_values Hlength Hnonnull.
  pose proof
    (non_null_count_eq_length_of_Forall_nonnull expression_values Hnonnull)
    as Hcount.
  split.
  - change
      (value_int64_checked (row_count star_values) =
       value_int64_checked (non_null_count expression_values)).
    unfold row_count; now rewrite Hcount, Hlength.
  - change
      (count_runtime_error star_values =
       non_null_count_runtime_error expression_values).
    unfold count_runtime_error, non_null_count_runtime_error, row_count.
    now rewrite Hcount, Hlength.
Qed.

(** The expression form additionally evaluates every reached child.  Child
    safety is therefore explicit; once it holds, equal cardinality preserves
    both the successful BIGINT value and the overflow category. *)
Theorem count_star_count_all_nonnull_value_runtime_error_exact :
  forall star_observations expression_observations,
    List.length star_observations = List.length expression_observations ->
    Forall
      (fun observation =>
        fst observation = None /\
        NullValues.is_null_value (snd observation) = false)
      expression_observations ->
    interp_aggregate AggregateCountStar
      (observation_values star_observations) =
      interp_aggregate (AggregateCall AggregateCount AggregateAll)
        (observation_values expression_observations) /\
    interp_aggregate_runtime_error AggregateCountStar star_observations =
      interp_aggregate_runtime_error
        (AggregateCall AggregateCount AggregateAll)
        expression_observations.
Proof.
  intros star_observations expression_observations Hlength Hsafe_nonnull.
  assert (Hvalue_length :
    List.length (observation_values star_observations) =
    List.length (observation_values expression_observations)).
  { now rewrite !observation_values_length. }
  assert (Hnonnull :
    Forall
      (fun value => NullValues.is_null_value value = false)
      (observation_values expression_observations)).
  {
    clear Hlength Hvalue_length star_observations.
    unfold observation_values.
    induction Hsafe_nonnull as
      [|[error value] observations [Herror Hvalue] Hrest IH].
    - constructor.
    - cbn; constructor; [exact Hvalue|exact IH].
  }
  pose proof
    (count_star_count_all_nonnull_value_local_error_exact
      (observation_values star_observations)
      (observation_values expression_observations)
      Hvalue_length Hnonnull) as [Hvalue Hlocal].
  split; [exact Hvalue|].
  rewrite count_star_runtime_error_observations.
  rewrite aggregate_call_safe_children_reduce_to_local.
  - exact Hlocal.
  - apply first_observation_error_none_iff.
    rewrite Forall_forall.
    intros [error value] Hin; cbn.
    rewrite Forall_forall in Hsafe_nonnull.
    exact (proj1 (Hsafe_nonnull (error, value) Hin)).
Qed.

Section PredicateObservationTransport.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable symbol_runtime_error :
  Tuple.scalar_operator T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  Tuple.aggregate T ->
  list (option sql_runtime_error * Tuple.value T) ->
  option sql_runtime_error.
Variable value_is_null : Tuple.value T -> bool.

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** Predicate formulas have identical outcomes when their reached argument
    error and interpreted-value observations agree.  This is the small
    formula/HAVING seam used after aggregate value/error laws; it preserves
    SQL FALSE versus UNKNOWN in the successful Bool3 result. *)
Theorem formula_pred_outcome_equiv_of_argument_observations :
  forall left_env right_env predicate left_arguments right_arguments,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      left_arguments =
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      right_arguments ->
    map (@Interp.interp_aggterm T left_env) left_arguments =
    map (@Interp.interp_aggterm T right_env) right_arguments ->
    forall outcome,
      eval_formula left_env (FExpr_Pred predicate left_arguments) outcome <->
      eval_formula right_env (FExpr_Pred predicate right_arguments) outcome.
Proof.
  intros left_env right_env predicate left_arguments right_arguments
    Herror Hvalues outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EFormula_PredError.
    now rewrite <- Herror.
  - rewrite Hvalues.
    apply EFormula_PredSuccess.
    now rewrite <- Herror.
  - apply EFormula_PredError.
    now rewrite Herror.
  - rewrite <- Hvalues.
    apply EFormula_PredSuccess.
    now rewrite Herror.
Qed.

End PredicateObservationTransport.

(** Exact value/error observation of one aggregate term at one environment.
    This is deliberately below query syntax: clients discharge it from the
    operator-specific group evaluator bridge appropriate to their aggregate. *)
Definition aggterm_observation_at
    {T : Tuple.Rcd}
    (symbol_runtime_error :
      Tuple.scalar_operator T ->
      list (option sql_runtime_error * Tuple.value T) ->
      option sql_runtime_error)
    (aggregate_runtime_error :
      Tuple.aggregate T ->
      list (option sql_runtime_error * Tuple.value T) ->
      option sql_runtime_error)
    (env : Env.env T) (term : @aggterm T)
    (observation : option sql_runtime_error * Tuple.value T) : Prop :=
  @eval_aggterm_runtime_error T
    symbol_runtime_error aggregate_runtime_error env term =
      fst observation /\
  Interp.interp_aggterm T env term = snd observation.

(** A one-column COUNT-star projection.  Its alias is arbitrary; only the
    operator shape is fixed. *)
Definition tnull_count_star_select_list
    (output : Tuple.attribute TNull) : @_select_list TNull :=
  SelectList [SelectAs ACountStar output].

Lemma tnull_group_count_star_projection_eq_of_equal_length :
  forall left_env right_env left_group_terms right_group_terms
      left_group right_group output,
    List.length left_group = List.length right_group ->
    Oeset.compare (OTuple TNull)
      (group_projection left_env (tnull_count_star_select_list output)
        left_group_terms left_group)
      (group_projection right_env (tnull_count_star_select_list output)
        right_group_terms right_group) = Eq.
Proof.
  intros left_env right_env left_group_terms right_group_terms
    left_group right_group output Hlength.
  pose proof
    (tnull_group_count_star_value_runtime_exact
      left_env left_group_terms left_group) as [Hleft_value _].
  pose proof
    (tnull_group_count_star_value_runtime_exact
      right_env right_group_terms right_group) as [Hright_value _].
  unfold group_projection, tnull_count_star_select_list.
  apply tnull_projection_envs_eq_of_select_items.
  constructor.
  - split; [reflexivity|].
    change
      (Interp.interp_aggterm TNull
        (Env.env_g TNull left_env
          (@Env.Group_By TNull left_group_terms) left_group)
        ACountStar =
       Interp.interp_aggterm TNull
        (Env.env_g TNull right_env
          (@Env.Group_By TNull right_group_terms) right_group)
        ACountStar).
    rewrite Hleft_value, Hright_value, Hlength.
    reflexivity.
  - constructor.
Qed.

Section CountStarGroupOutcomeBridge.

Context {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A TNull).
Variable instance :
  relname -> Febag.bag (Fecol.CBag (Tuple.CTuple TNull)).

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome TNull relname basesort instance unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value).
Local Abbreviation eval_formula_aggregates :=
  (@eval_formula_expr_aggregate_runtime_error TNull relname
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome TNull relname basesort instance unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    NullValues.is_null_value).

(** Equal-cardinality groups with observationally equivalent HAVING formulas
    have the same COUNT-star scheduler observation.  The HAVING premises are
    separate because COUNT cardinality alone says nothing about an arbitrary
    predicate; [formula_pred_outcome_equiv_of_argument_observations] supplies
    them for predicate formulas. *)
Theorem tnull_count_star_group_observation_equiv_of_equal_length :
  forall left_env right_env left_group_terms right_group_terms
      left_having right_having left_group right_group output,
    List.length left_group = List.length right_group ->
    eval_formula_aggregates
      (Env.env_g TNull left_env
        (@Env.Group_By TNull left_group_terms) left_group)
      left_having =
    eval_formula_aggregates
      (Env.env_g TNull right_env
        (@Env.Group_By TNull right_group_terms) right_group)
      right_having ->
    (forall outcome,
      eval_formula
        (Env.env_g TNull left_env
          (@Env.Group_By TNull left_group_terms) left_group)
        left_having outcome <->
      eval_formula
        (Env.env_g TNull right_env
          (@Env.Group_By TNull right_group_terms) right_group)
        right_having outcome) ->
    @group_execution_observation_equiv TNull relname
      basesort instance unknown3
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      NullValues.is_null_value
      left_env (tnull_count_star_select_list output)
      left_group_terms left_having
      right_env (tnull_count_star_select_list output)
      right_group_terms right_having
      left_group right_group.
Proof.
  intros left_env right_env left_group_terms right_group_terms
    left_having right_having left_group right_group output
    Hlength Hhaving_aggregates Hhaving.
  pose proof
    (tnull_group_count_star_value_runtime_exact
      left_env left_group_terms left_group)
    as [Hleft_value [Hleft_aggregate Hleft_runtime]].
  pose proof
    (tnull_group_count_star_value_runtime_exact
      right_env right_group_terms right_group)
    as [Hright_value [Hright_aggregate Hright_runtime]].
  unfold group_execution_observation_equiv.
  split.
  - unfold tnull_count_star_select_list, SelectList, SelectAs.
    cbn [eval_select_list_aggregate_runtime_error
      eval_select_aggregate_runtime_error first_runtime_error first_error].
    change
      (first_error
        (@eval_aggterm_aggregate_runtime_error TNull
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          (Env.env_g TNull left_env
            (@Env.Group_By TNull left_group_terms) left_group)
          ACountStar) None =
       first_error
        (@eval_aggterm_aggregate_runtime_error TNull
          NullValues.interp_scalar_operator_runtime_error
          NullValues.interp_aggregate_runtime_error
          (Env.env_g TNull right_env
            (@Env.Group_By TNull right_group_terms) right_group)
          ACountStar) None).
    now rewrite Hleft_aggregate, Hright_aggregate, Hlength.
  - split; [exact Hhaving_aggregates|].
    split; [exact Hhaving|].
    split.
    + unfold tnull_count_star_select_list, SelectList, SelectAs.
      cbn [eval_select_list_runtime_error eval_select_runtime_error
        first_runtime_error first_error].
      change
        (first_error
          (@eval_aggterm_runtime_error TNull
            NullValues.interp_scalar_operator_runtime_error
            NullValues.interp_aggregate_runtime_error
            (Env.env_g TNull left_env
              (@Env.Group_By TNull left_group_terms) left_group)
            ACountStar) None =
         first_error
          (@eval_aggterm_runtime_error TNull
            NullValues.interp_scalar_operator_runtime_error
            NullValues.interp_aggregate_runtime_error
            (Env.env_g TNull right_env
              (@Env.Group_By TNull right_group_terms) right_group)
            ACountStar) None).
      now rewrite Hleft_runtime, Hright_runtime, Hlength.
    + now apply tnull_group_count_star_projection_eq_of_equal_length.
Qed.

(** Ordered Forall2 pairing preserves duplicate groups and the first
    COUNT/HAVING error.  It does not claim an exact ordered output row list:
    successful rows remain related only by FormalSQL's semantic row
    permutation, exactly as required by the existing group scheduler
    boundary. *)
Theorem tnull_count_star_groups_outcome_equiv_of_Forall2_observations :
  forall left_env right_env left_group_terms right_group_terms
      left_having right_having left_groups right_groups output,
    Forall2
      (fun left_group right_group =>
        List.length left_group = List.length right_group /\
        eval_formula_aggregates
          (Env.env_g TNull left_env
            (@Env.Group_By TNull left_group_terms) left_group)
          left_having =
        eval_formula_aggregates
          (Env.env_g TNull right_env
            (@Env.Group_By TNull right_group_terms) right_group)
          right_having /\
        forall outcome,
          eval_formula
            (Env.env_g TNull left_env
              (@Env.Group_By TNull left_group_terms) left_group)
            left_having outcome <->
          eval_formula
            (Env.env_g TNull right_env
              (@Env.Group_By TNull right_group_terms) right_group)
            right_having outcome)
      left_groups right_groups ->
    (exists outcome,
      eval_groups left_env (tnull_count_star_select_list output)
        left_group_terms left_having left_groups outcome) ->
    outcome_relation_equiv (Oeset.permut (OTuple TNull))
      (eval_groups left_env (tnull_count_star_select_list output)
        left_group_terms left_having left_groups)
      (eval_groups right_env (tnull_count_star_select_list output)
        right_group_terms right_having right_groups).
Proof.
  intros left_env right_env left_group_terms right_group_terms
    left_having right_having left_groups right_groups output
    Hobservations Hexists.
  eapply eval_groups_outcome_Forall2_congr; [|exact Hexists].
  clear Hexists.
  induction Hobservations as
    [|left_group right_group left_groups right_groups
       [Hlength [Haggregates Hhaving]] _ IH].
  - constructor.
  - constructor; [|exact IH].
    now apply tnull_count_star_group_observation_equiv_of_equal_length.
Qed.

(** TRUE HAVING is environment-independent, so equal group cardinalities are
    the only pointwise premise needed in this common specialization. *)
Corollary tnull_count_star_groups_true_outcome_equiv_of_Forall2_length :
  forall left_env right_env left_group_terms right_group_terms
      left_groups right_groups output,
    Forall2
      (fun left_group right_group =>
        List.length left_group = List.length right_group)
      left_groups right_groups ->
    (exists outcome,
      eval_groups left_env (tnull_count_star_select_list output)
        left_group_terms FExpr_True left_groups outcome) ->
    outcome_relation_equiv (Oeset.permut (OTuple TNull))
      (eval_groups left_env (tnull_count_star_select_list output)
        left_group_terms FExpr_True left_groups)
      (eval_groups right_env (tnull_count_star_select_list output)
        right_group_terms FExpr_True right_groups).
Proof.
  intros left_env right_env left_group_terms right_group_terms
    left_groups right_groups output Hlengths Hexists.
  apply tnull_count_star_groups_outcome_equiv_of_Forall2_observations;
    [|exact Hexists].
  clear Hexists.
  induction Hlengths as
    [|left_group right_group left_groups right_groups Hlength _ IH].
  - constructor.
  - constructor; [|exact IH].
    split; [exact Hlength|].
    split; [reflexivity|].
    intro outcome; split; intro Heval; inversion Heval; constructor.
Qed.

End CountStarGroupOutcomeBridge.
