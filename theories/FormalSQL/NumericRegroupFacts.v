(************************************************************************************)
(** Exact NUMERIC regrouping and duplicate-free UNION facts for SQL rewrites.      **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Lia List NArith QArith Qcanon SetoidList
  Sorting.Permutation ZArith.
From SQLFS Require Import ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet
  FlatData FTerms FTuples GenericInstance ListPermut ListSort OrderedSet Partition
  SqlBagAbstraction SqlErrorSemantics SqlOutcome SqlQueryFacts
  SqlQuerySemantics Values ValueNumeric.
From Logos.FormalSQL Require Import AggregateRuntimeFacts
  GroupedFilterOutcomeFacts GroupingRewriteFacts NumericDerivedFacts
  NumericFacts RelationalAlgebraFacts TNullSyntax.

Import ListNotations.
Import NullValues.
Import Tuple.

(** [numeric_add] is the exact binary operation induced by PostgreSQL's
    [sum(numeric)] finalizer, including NaN and both infinities. *)
Lemma numeric_add_associative : forall first second third,
  numeric_add (numeric_add first second) third =
  numeric_add first (numeric_add second third).
Proof.
intros [|first| |] [|second| |] [|third| |];
  cbn [numeric_add]; try reflexivity.
- f_equal; symmetry; apply Qcplus_assoc.
Qed.

Definition numeric_sum_state_reachable_invariant
    (state : numeric_sum_state) : Prop :=
  0 <= numeric_sum_finite_count state /\
  0 <= numeric_sum_nan_count state /\
  0 <= numeric_sum_pos_inf_count state /\
  0 <= numeric_sum_neg_inf_count state /\
  (numeric_sum_total_count state = 0 ->
   numeric_sum_finite_accumulator state = Q2Qc (inject_Z 0)).

Lemma numeric_sum_initial_reachable_invariant :
  numeric_sum_state_reachable_invariant numeric_sum_initial.
Proof.
unfold numeric_sum_state_reachable_invariant, numeric_sum_initial,
  numeric_sum_total_count, numeric_agg_total_count; cbn.
repeat split; try lia; reflexivity.
Qed.

Lemma numeric_sum_transition_preserves_reachable_invariant :
  forall state next,
    numeric_sum_state_reachable_invariant state ->
    numeric_sum_state_reachable_invariant
      (numeric_sum_transition state next).
Proof.
intros [finite_count nan_count pos_inf_count neg_inf_count accumulator]
  [|finite| |] Hvalid;
  cbv [numeric_sum_state_reachable_invariant numeric_sum_transition
    numeric_sum_total_count numeric_agg_total_count
    numeric_sum_finite_count numeric_sum_nan_count
    numeric_sum_pos_inf_count numeric_sum_neg_inf_count
    numeric_sum_finite_accumulator] in *;
  destruct Hvalid as
    [Hfinite [Hnan [Hpos [Hneg Hzero]]]];
  repeat split; try lia.
all: intros Hcount; exfalso; lia.
Qed.

Definition numeric_sum_option_add
    (current : option numeric) (next : numeric) : option numeric :=
  match current with
  | None => Some next
  | Some total => Some (numeric_add total next)
  end.

(** SUM of the nonempty per-group SUM results is exactly SUM of the flattened
    numeric inputs.  Empty groups contribute [None] and are omitted, matching
    SQL SUM's treatment of NULL subtotals.  The result covers finite values,
    NaN, and infinities because it relies only on exact [numeric_add]
    associativity. *)
Theorem numeric_sum_option_regroup_from : forall groups current,
  fold_left numeric_sum_option_add
    (flat_map
      (fun group =>
        match fold_left numeric_sum_option_add group None with
        | Some total => [total]
        | None => []
        end)
      groups)
    current =
  fold_left numeric_sum_option_add (concat groups) current.
Proof.
assert (Hsome : forall numbers total,
  fold_left numeric_sum_option_add numbers (Some total) =
  match fold_left numeric_sum_option_add numbers None with
  | Some subtotal => Some (numeric_add total subtotal)
  | None => Some total
  end).
{
  induction numbers as [|number numbers IH]; intro total; cbn.
  - reflexivity.
  - rewrite IH, (IH number).
    destruct (fold_left numeric_sum_option_add numbers None)
      as [subtotal |] eqn:Hfold; cbn.
    + f_equal; apply numeric_add_associative.
    + reflexivity.
}
assert (Haccumulator : forall numbers current,
  fold_left numeric_sum_option_add numbers current =
  match fold_left numeric_sum_option_add numbers None with
  | Some subtotal => numeric_sum_option_add current subtotal
  | None => current
  end).
{
  intros numbers [total |].
  - rewrite Hsome.
    destruct (fold_left numeric_sum_option_add numbers None); reflexivity.
  - remember (fold_left numeric_sum_option_add numbers None)
      as result eqn:Hresult.
    destruct result; reflexivity.
}
assert (Hregroup : forall groups current,
  fold_left numeric_sum_option_add
    (flat_map
      (fun group =>
        match fold_left numeric_sum_option_add group None with
        | Some total => [total]
        | None => []
        end)
      groups)
    current =
  fold_left numeric_sum_option_add (concat groups) current).
{
  induction groups as [|group groups IH]; intro current; cbn.
  - reflexivity.
  - rewrite !fold_left_app.
    destruct (fold_left numeric_sum_option_add group None)
      as [subtotal |] eqn:Hgroup; cbn.
    + rewrite (Haccumulator group current), Hgroup; cbn.
      apply IH.
    + rewrite (Haccumulator group current), Hgroup; cbn.
      apply IH.
}
intros groups current; apply Hregroup.
Qed.

Corollary numeric_sum_option_regroup : forall groups,
  fold_left numeric_sum_option_add
    (flat_map
      (fun group =>
        match fold_left numeric_sum_option_add group None with
        | Some total => [total]
        | None => []
        end)
      groups)
    None =
  fold_left numeric_sum_option_add (concat groups) None.
Proof.
intro groups; apply numeric_sum_option_regroup_from.
Qed.

Lemma numeric_sum_from_state_transition : forall state next,
  numeric_sum_state_reachable_invariant state ->
  numeric_sum_from_state (numeric_sum_transition state next) =
  numeric_sum_option_add (numeric_sum_from_state state) next.
Proof.
intros [finite_count nan_count pos_inf_count neg_inf_count accumulator]
  [|finite| |] Hvalid;
  cbv [numeric_sum_state_reachable_invariant
    numeric_sum_option_add numeric_sum_transition numeric_sum_from_state
    numeric_sum_total_count numeric_agg_total_count
    numeric_agg_special_result numeric_add
    numeric_sum_finite_count numeric_sum_nan_count
    numeric_sum_pos_inf_count numeric_sum_neg_inf_count
    numeric_sum_finite_accumulator] in *;
  destruct Hvalid as
    [Hfinite [Hnan [Hpos [Hneg Hzero]]]].
all: repeat match goal with
  | |- context [Z.eqb ?left ?right] =>
      destruct (Z.eqb left right) eqn:?; cbn
  | |- context [Z.ltb ?left ?right] =>
      destruct (Z.ltb left right) eqn:?; cbn
  end.
all: repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end.
all: repeat match goal with
  | Hzero : ?total = 0 -> _, Htotal : ?total = 0 |- _ =>
      specialize (Hzero Htotal)
  end.
all: try reflexivity; try lia; try (f_equal; ring).
all: assert (accumulator = Q2Qc (inject_Z 0)) as Haccumulator.
{ apply Hzero; lia. }
all: rewrite Haccumulator; f_equal; f_equal; cbn [inject_Z];
  apply Qcplus_0_l.
Qed.

Lemma numeric_sum_fold_option_add : forall numbers state,
  numeric_sum_state_reachable_invariant state ->
  numeric_sum_from_state
    (fold_left numeric_sum_transition numbers state) =
  fold_left numeric_sum_option_add numbers
    (numeric_sum_from_state state).
Proof.
induction numbers as [|number numbers IH]; intros state Hvalid; cbn.
- reflexivity.
- rewrite IH.
  + now rewrite numeric_sum_from_state_transition.
  + now apply numeric_sum_transition_preserves_reachable_invariant.
Qed.

Corollary numeric_sum_fold_from_initial : forall numbers,
  numeric_sum_from_state
    (fold_left numeric_sum_transition numbers numeric_sum_initial) =
  fold_left numeric_sum_option_add numbers None.
Proof.
intro numbers.
rewrite numeric_sum_fold_option_add.
- reflexivity.
- apply numeric_sum_initial_reachable_invariant.
Qed.

Lemma interp_sum_numeric_option_fold : forall observations,
  forallb is_numeric_value observations = true ->
  interp_sum_numeric observations =
  Value_numeric
    (fold_left numeric_sum_option_add (numeric_values observations) None).
Proof.
intros observations Hnumeric.
unfold interp_sum_numeric; rewrite Hnumeric, numeric_sum_fold_from_initial.
reflexivity.
Qed.

(** A singleton nullable NUMERIC SUM returns its sole observation exactly,
    including SQL NULL, NaN, and infinities. *)
Lemma interp_sum_numeric_singleton : forall number,
  interp_sum_numeric [Value_numeric number] = Value_numeric number.
Proof.
intros [number |]; [|reflexivity].
change
  (Value_numeric
    (numeric_sum_from_state
      (numeric_sum_transition numeric_sum_initial number)) =
   Value_numeric (Some number)).
rewrite numeric_sum_from_state_transition.
- reflexivity.
- apply numeric_sum_initial_reachable_invariant.
Qed.

(** The corresponding singleton runtime check is exact as well: a present
    result reports precisely its numeric result error, while SQL NULL is
    error-free. *)
Lemma sum_numeric_runtime_error_singleton : forall number,
  sum_numeric_runtime_error [Value_numeric number] =
  match number with
  | None => None
  | Some result => numeric_result_runtime_error result
  end.
Proof.
intros [number |]; [|reflexivity].
change
  (numeric_sum_state_runtime_error
    (numeric_sum_transition numeric_sum_initial number) =
   numeric_result_runtime_error number).
unfold numeric_sum_state_runtime_error.
rewrite numeric_sum_from_state_transition.
- reflexivity.
- apply numeric_sum_initial_reachable_invariant.
Qed.

Local Lemma numeric_observations_all_concat : forall groups,
  Forall
    (fun observations => forallb is_numeric_value observations = true)
    groups ->
  forallb is_numeric_value (concat groups) = true.
Proof.
intros groups Hall.
induction Hall as [|observations groups Hobservations Hgroups IH];
  cbn [concat].
- reflexivity.
- rewrite forallb_app, Hobservations, IH; reflexivity.
Qed.

Local Lemma numeric_values_app : forall left right,
  numeric_values (left ++ right) = numeric_values left ++ numeric_values right.
Proof.
intros left right.
induction left as [|observation left IH]; [reflexivity |].
destruct observation; cbn; try exact IH.
destruct o; cbn; now rewrite IH.
Qed.

Local Lemma numeric_values_concat : forall groups,
  numeric_values (concat groups) = concat (map numeric_values groups).
Proof.
intro groups.
induction groups as [|observations groups IH]; cbn [concat];
  [reflexivity |].
rewrite numeric_values_app, IH; reflexivity.
Qed.

(** Exact SQL-level NUMERIC regrouping.  [subtotals] may contain NULLs and
    special numeric values; the explicit [numeric_values] premise states that
    its present observations are exactly the nonempty per-group sums.  The
    conclusion preserves both the aggregate value and the precise numeric
    runtime-error category, unlike a value-only reassociation law. *)
Theorem interp_sum_numeric_regroup_value_runtime_exact :
  forall groups subtotals,
    Forall
      (fun observations => forallb is_numeric_value observations = true)
      groups ->
    forallb is_numeric_value subtotals = true ->
    numeric_values subtotals =
      flat_map
        (fun numbers =>
          match fold_left numeric_sum_option_add numbers None with
          | Some total => [total]
          | None => []
          end)
        (map numeric_values groups) ->
    interp_sum_numeric subtotals = interp_sum_numeric (concat groups) /\
    sum_numeric_runtime_error subtotals =
      sum_numeric_runtime_error (concat groups).
Proof.
intros groups subtotals Hgroups Hsubtotals Hnumeric_values.
pose proof (@numeric_observations_all_concat groups Hgroups) as Hconcat.
assert (Hfold :
  fold_left numeric_sum_option_add (numeric_values subtotals) None =
  fold_left numeric_sum_option_add (numeric_values (concat groups)) None).
{
  rewrite Hnumeric_values, numeric_values_concat.
  apply numeric_sum_option_regroup.
}
assert (Hstate :
  numeric_sum_from_state
    (fold_left numeric_sum_transition
      (numeric_values subtotals) numeric_sum_initial) =
  numeric_sum_from_state
    (fold_left numeric_sum_transition
      (numeric_values (concat groups)) numeric_sum_initial)).
{
  rewrite !numeric_sum_fold_from_initial.
  exact Hfold.
}
split.
- unfold interp_sum_numeric.
  rewrite Hsubtotals, Hconcat.
  now rewrite Hstate.
- unfold sum_numeric_runtime_error.
  rewrite Hsubtotals, Hconcat.
  unfold numeric_sum_state_runtime_error.
  now rewrite Hstate.
Qed.

(** The exact aggregate term covered by the evaluator-to-group bridge below.
    This is an operator-family description: neither a concrete column name nor
    a surrounding SELECT or query shape is fixed here. *)
Definition tnull_sum_numeric_dot_term (attribute : attribute TNull) :=
  AAggregate AggregateSumNumeric AggregateAll (Dot attribute).

(** The exact argument environments selected for one closed group.  Here
    [closed] means that the group environment has no correlated outer tail. *)
Definition tnull_closed_group_sum_numeric_dot_argument_envs
    (group_terms : list (@aggterm TNull))
    (group : list (tuple TNull))
    (attribute : attribute TNull) :=
  let group_env :=
    Env.env_g TNull nil (@Env.Group_By TNull group_terms) group in
  let aggregate_term := tnull_sum_numeric_dot_term attribute in
  let function_term := Dot attribute in
  let selected_env :=
    if Fset.is_empty (A TNull) (FTerms.variables_ft TNull function_term)
    then Some group_env
    else Interp.find_eval_env TNull group_env aggregate_term in
  match selected_env with
  | None | Some nil => nil
  | Some (slice :: outer_env) =>
      map (fun inner_slice => inner_slice :: outer_env)
        (Interp.unfold_env_slice TNull slice)
  end.

(** The observations passed by [eval_aggterm_aggregate_runtime_error] to the
    concrete NUMERIC SUM callback.  Keeping this definition definitionally
    aligned with the evaluator prevents clients from rebuilding its
    [find_eval_env]/[unfold_env_slice] schedule. *)
Definition tnull_closed_group_sum_numeric_dot_argument_observations
    (group_terms : list (@aggterm TNull))
    (group : list (tuple TNull))
    (attribute : attribute TNull) :=
  map
    (fun argument_env =>
      (@eval_funterm_runtime_error TNull
        NullValues.interp_scalar_operator_runtime_error
        argument_env (Dot attribute),
       Interp.interp_funterm TNull argument_env (Dot attribute)))
    (tnull_closed_group_sum_numeric_dot_argument_envs
      group_terms group attribute).

Definition tnull_closed_group_sum_numeric_dot_argument_values
    (group_terms : list (@aggterm TNull))
    (group : list (tuple TNull))
    (attribute : attribute TNull) :=
  map
    (fun argument_env =>
      Interp.interp_funterm TNull argument_env (Dot attribute))
    (tnull_closed_group_sum_numeric_dot_argument_envs
      group_terms group attribute).

Local Lemma tnull_sum_numeric_dot_observation_values :
  forall group_terms group attribute,
    NullValues.observation_values
      (tnull_closed_group_sum_numeric_dot_argument_observations
        group_terms group attribute) =
    tnull_closed_group_sum_numeric_dot_argument_values
      group_terms group attribute.
Proof.
intros group_terms group attribute.
unfold NullValues.observation_values,
  tnull_closed_group_sum_numeric_dot_argument_observations,
  tnull_closed_group_sum_numeric_dot_argument_values.
now rewrite map_map.
Qed.

Local Lemma tnull_sum_numeric_dot_value_observations :
  forall group_terms group attribute,
    Interp.interp_aggterm TNull
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
    NullValues.interp_sum_numeric
      (tnull_closed_group_sum_numeric_dot_argument_values
        group_terms group attribute).
Proof.
intros group_terms group attribute.
unfold tnull_closed_group_sum_numeric_dot_argument_values,
  tnull_closed_group_sum_numeric_dot_argument_envs,
  tnull_sum_numeric_dot_term, AAggregate.
reflexivity.
Qed.

Local Lemma tnull_sum_numeric_dot_runtime_observations :
  forall group_terms group attribute,
    @eval_aggterm_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
    NullValues.interp_aggregate_runtime_error
      (AggregateCall AggregateSumNumeric AggregateAll)
      (tnull_closed_group_sum_numeric_dot_argument_observations
        group_terms group attribute).
Proof.
intros group_terms group attribute.
unfold tnull_closed_group_sum_numeric_dot_argument_observations,
  tnull_closed_group_sum_numeric_dot_argument_envs,
  tnull_sum_numeric_dot_term, AAggregate.
reflexivity.
Qed.

Local Lemma tnull_dot_variables_nonempty : forall attribute,
  Fset.is_empty (A TNull)
    (FTerms.variables_ft TNull (Dot attribute)) = false.
Proof.
intro attribute; reflexivity.
Qed.

Local Lemma tnull_sum_numeric_dot_selects_closed_group :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Interp.find_eval_env TNull
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
    Some
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group).
Proof.
intros group_terms group attribute Hnonempty Hpresent.
case_eq (ListSort.quicksort (OTuple TNull) group).
- intro Hsorted.
  pose proof (ListSort.length_quicksort (OTuple TNull) group) as Hlength.
  rewrite Hsorted in Hlength.
  symmetry in Hlength.
  apply length_zero_iff_nil in Hlength.
  contradiction.
- intros first rest Hsorted.
  assert (Hfirst : attribute inS labels TNull first).
  {
    rewrite Forall_forall in Hpresent.
    apply Hpresent.
    apply (proj2 (ListSort.In_quicksort (OTuple TNull) group first)).
    change (In first (ListSort.quicksort (OTuple TNull) group)).
    rewrite Hsorted; now left.
  }
  unfold Env.env_g.
  rewrite Hsorted.
  assert (Hsuitable :
    Interp.is_a_suitable_env TNull (labels TNull first) nil
      (tnull_sum_numeric_dot_term attribute) = true).
  {
    unfold Interp.is_a_suitable_env, tnull_sum_numeric_dot_term,
      AAggregate.
    cbn [ATerms.is_built_upon_ag FTerms.is_built_upon_ft].
    rewrite Bool.Bool.orb_true_iff; right.
    unfold Dot.
    cbn [FTerms.is_built_upon_ft flat_map].
    rewrite FTerms.funterm_mem_true_iff.
    rewrite ATerms.in_extract_funterms, app_nil_r.
    apply
      (in_map
        (fun current : Tuple.attribute TNull =>
          @ATerms.A_Expr TNull (@FTerms.F_Dot TNull current))
        (Fset.elements (A TNull) (labels TNull first)) attribute).
    now apply Fset.mem_in_elements.
  }
  unfold Interp.find_eval_env at 1; fold Interp.find_eval_env.
  rewrite Hsuitable; reflexivity.
Qed.

Local Lemma tnull_sum_numeric_dot_singleton_observation :
  forall stored_labels row attribute,
    attribute inS labels TNull row ->
    (@eval_funterm_runtime_error TNull
       NullValues.interp_scalar_operator_runtime_error
       [(stored_labels, @Env.Group_Fine TNull, [row])]
       (Dot attribute),
     Interp.interp_funterm TNull
       [(stored_labels, @Env.Group_Fine TNull, [row])]
       (Dot attribute)) =
    (None, dot TNull row attribute).
Proof.
intros stored_labels row attribute Hpresent.
unfold Dot, Interp.interp_funterm, Interp.interp_dot.
cbn [eval_funterm_runtime_error].
rewrite ListSort.quicksort_1.
now rewrite Hpresent.
Qed.

(** For a nonempty logical group whose rows expose the referenced attribute,
    the evaluator passes exactly one error-free observation per row to
    [sum(numeric)] in the representative's actual order.  This is the
    key interface that hides [env_g], [find_eval_env], [unfold_env_slice], and
    the label-selection details from generated proofs. *)
Theorem tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Permutation
      (tnull_closed_group_sum_numeric_dot_argument_observations
        group_terms group attribute)
      (map
        (fun row =>
          (None, dot TNull row attribute))
        group).
Proof.
intros group_terms group attribute Hnonempty Hpresent.
pose proof
  (@tnull_sum_numeric_dot_selects_closed_group
    group_terms group attribute Hnonempty Hpresent) as Hselected.
unfold tnull_closed_group_sum_numeric_dot_argument_observations,
  tnull_closed_group_sum_numeric_dot_argument_envs.
rewrite tnull_dot_variables_nonempty, Hselected.
unfold Env.env_g.
case_eq (ListSort.quicksort (OTuple TNull) group).
- intro Hsorted.
  pose proof (ListSort.length_quicksort (OTuple TNull) group) as Hlength.
  rewrite Hsorted in Hlength.
  symmetry in Hlength.
  apply length_zero_iff_nil in Hlength; contradiction.
- intros first rest Hsorted.
  cbn.
  unfold Interp.unfold_env_slice.
  rewrite !map_map.
  apply Permutation_refl'.
  apply map_ext_in; intros row Hrow.
  apply
    (@tnull_sum_numeric_dot_singleton_observation
      (labels TNull first) row attribute).
  rewrite Forall_forall in Hpresent.
  now apply Hpresent.
Qed.

(** Direct evaluator bridge for one closed logical group.  It covers both the
    value interpreter and the aggregate-only runtime-error checker, so callers
    cannot prove a value reassociation while silently dropping a NUMERIC error
    category. *)
Theorem tnull_closed_group_sum_numeric_dot_value_runtime_exact :
  forall group_terms group attribute,
    group <> nil ->
    Forall
      (fun row => attribute inS labels TNull row)
      group ->
    Interp.interp_aggterm TNull
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
      NullValues.interp_sum_numeric
        (map (fun row => dot TNull row attribute) group) /\
    @eval_aggterm_aggregate_runtime_error TNull
      NullValues.interp_scalar_operator_runtime_error
      NullValues.interp_aggregate_runtime_error
      (Env.env_g TNull nil (@Env.Group_By TNull group_terms) group)
      (tnull_sum_numeric_dot_term attribute) =
      NullValues.sum_numeric_runtime_error
        (map (fun row => dot TNull row attribute) group).
Proof.
intros group_terms group attribute Hnonempty Hpresent.
pose proof
  (@tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows
    group_terms group attribute Hnonempty Hpresent) as Hobservations.
assert (Hvalues :
  Permutation
    (tnull_closed_group_sum_numeric_dot_argument_values
      group_terms group attribute)
    (map (fun row => dot TNull row attribute) group)).
{
  rewrite <- tnull_sum_numeric_dot_observation_values.
  unfold NullValues.observation_values.
  eapply Permutation_trans with
    (l' :=
      map snd
        (map
          (fun row => (None, dot TNull row attribute))
          group)).
  - now apply Permutation_map.
  - rewrite map_map; apply Permutation_refl.
}
assert (Hchildren :
  NullValues.first_observation_error
    (tnull_closed_group_sum_numeric_dot_argument_observations
      group_terms group attribute) = None).
{
  apply first_observation_error_none_iff.
  rewrite Forall_forall; intros observation Hobservation.
  assert (Hmapped : In observation
    (map (fun row => (None, dot TNull row attribute)) group)).
  { eapply Permutation_in; eauto. }
  apply in_map_iff in Hmapped.
  destruct Hmapped as [row [Hequal _]].
  now subst observation.
}
split.
- rewrite tnull_sum_numeric_dot_value_observations.
  exact (@NumericFacts.interp_sum_numeric_permutation _ _ Hvalues).
- rewrite tnull_sum_numeric_dot_runtime_observations.
  rewrite aggregate_call_safe_children_reduce_to_local.
  + cbn [NullValues.aggregate_local_runtime_error
      NullValues.aggregate_input_values].
    rewrite tnull_sum_numeric_dot_observation_values.
    exact (@NumericFacts.sum_numeric_runtime_error_permutation _ _ Hvalues).
  + exact Hchildren.
Qed.

(** A finite NUMERIC observation is an exact canonical rational.  These
    helpers make the common DECIMAL rollup proof independent of generated
    attributes and select-list names. *)
Definition finite_numeric_observation (number : Qc) : NullValues.value :=
  Value_numeric (Some (NumericFinite number)).

Definition finite_numeric_total (numbers : list Qc) : Qc :=
  fold_left Qcplus numbers (Q2Qc 0).

Fixpoint nonempty_finite_group_totals
    (groups : list (list Qc)) : list Qc :=
  match groups with
  | [] => []
  | [] :: rest => nonempty_finite_group_totals rest
  | group :: rest =>
      finite_numeric_total group :: nonempty_finite_group_totals rest
  end.

Lemma numeric_values_finite_observations : forall numbers,
  numeric_values (map finite_numeric_observation numbers) =
  map NumericFinite numbers.
Proof.
induction numbers as [|number numbers IH]; cbn; now rewrite ?IH.
Qed.

Lemma finite_observations_all_numeric : forall numbers,
  forallb is_numeric_value (map finite_numeric_observation numbers) = true.
Proof.
induction numbers as [|number numbers IH]; cbn; now rewrite ?IH.
Qed.

Lemma numeric_sum_finite_fold_state :
  forall numbers finite_count nan_count pos_inf_count neg_inf_count accumulator,
    fold_left numeric_sum_transition (map NumericFinite numbers)
      (NumericSumState finite_count nan_count pos_inf_count neg_inf_count
        accumulator) =
    NumericSumState
      (finite_count + Z.of_nat (length numbers))
      nan_count pos_inf_count neg_inf_count
      (fold_left Qcplus numbers accumulator).
Proof.
induction numbers as [|number numbers IH];
  intros finite_count nan_count pos_inf_count neg_inf_count accumulator; cbn.
- f_equal; lia.
- rewrite IH; f_equal; lia.
Qed.

Lemma interp_sum_finite_observations : forall numbers,
  interp_sum_numeric (map finite_numeric_observation numbers) =
  match numbers with
  | [] => Value_numeric None
  | _ => Value_numeric (Some (NumericFinite (finite_numeric_total numbers)))
  end.
Proof.
intro numbers.
unfold interp_sum_numeric.
rewrite finite_observations_all_numeric, numeric_values_finite_observations.
unfold numeric_sum_initial.
rewrite numeric_sum_finite_fold_state.
destruct numbers as [|number numbers]; cbn [numeric_sum_initial
  numeric_sum_from_state numeric_sum_total_count numeric_agg_total_count
  numeric_agg_special_result finite_numeric_total].
- reflexivity.
- cbn [length].
  unfold numeric_sum_from_state, numeric_sum_total_count,
    numeric_agg_total_count, numeric_agg_special_result.
  cbn.
  f_equal; apply f_equal; ring.
Qed.

Lemma interp_sum_numeric_values_extensional : forall left right,
  forallb is_numeric_value left = true ->
  forallb is_numeric_value right = true ->
  numeric_values left = numeric_values right ->
  interp_sum_numeric left = interp_sum_numeric right.
Proof.
intros left right Hleft Hright Hvalues.
unfold interp_sum_numeric; now rewrite Hleft, Hright, Hvalues.
Qed.

Lemma finite_numeric_total_from_accumulator : forall numbers accumulator,
  fold_left Qcplus numbers accumulator =
  Qcplus accumulator (finite_numeric_total numbers).
Proof.
unfold finite_numeric_total.
induction numbers as [|number numbers IH]; intro accumulator.
- cbn; symmetry; apply Qcplus_0_r.
- cbn.
  rewrite (IH (Qcplus accumulator number)), (IH (Qcplus (Q2Qc 0) number)).
  ring.
Qed.

Lemma nonempty_group_totals_flatten : forall groups,
  finite_numeric_total (nonempty_finite_group_totals groups) =
  finite_numeric_total (concat groups).
Proof.
induction groups as [|group groups IH]; [reflexivity|].
destruct group as [|number numbers]; cbn [nonempty_finite_group_totals];
  [exact IH|].
unfold finite_numeric_total at 1 3.
cbn [concat].
rewrite fold_left_app.
cbn.
rewrite
  (finite_numeric_total_from_accumulator
    (nonempty_finite_group_totals groups)
    (Qcplus (Q2Qc 0)
      (fold_left Qcplus numbers (Qcplus (Q2Qc 0) number)))),
  (finite_numeric_total_from_accumulator
    (concat groups)
    (fold_left Qcplus numbers (Qcplus (Q2Qc 0) number))).
rewrite IH; ring.
Qed.

Lemma grouped_finite_sums_all_numeric : forall groups,
  forallb is_numeric_value
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) = true.
Proof.
induction groups as [|group groups IH]; cbn; [reflexivity|].
rewrite interp_sum_finite_observations.
destruct group; cbn; exact IH.
Qed.

Lemma numeric_values_grouped_finite_sums : forall groups,
  numeric_values
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) =
  map NumericFinite (nonempty_finite_group_totals groups).
Proof.
induction groups as [|group groups IH]; cbn; [reflexivity|].
rewrite interp_sum_finite_observations.
destruct group; cbn; now rewrite IH.
Qed.

Lemma nonempty_group_totals_nil_iff : forall groups,
  nonempty_finite_group_totals groups = [] <-> concat groups = [].
Proof.
induction groups as [|group groups IH]; [cbn; tauto|].
destruct group as [|number numbers].
- cbn [nonempty_finite_group_totals]; exact IH.
- cbn [nonempty_finite_group_totals]; split; discriminate.
Qed.

(** Pure mathematical-value equality: SUM over nonempty finite group totals
    equals SUM over the flattened input. Empty and all-empty partitions retain
    SQL NULL behavior: inner NULL sums are ignored, and an entirely empty
    partition still produces NULL. This theorem does not establish equivalence
    of intermediate SQL evaluation. In particular, it supplies no runtime
    overflow/range-error or typmod preservation, no grouping or ordering
    equivalence, and no license to reassociate operations whose intermediate
    representability can differ; callers must prove those obligations at the
    appropriate outcome boundary. *)
Theorem interp_sum_numeric_finite_regroup : forall groups,
  interp_sum_numeric
    (map
      (fun group =>
        interp_sum_numeric (map finite_numeric_observation group))
      groups) =
  interp_sum_numeric
    (map finite_numeric_observation (concat groups)).
Proof.
intro groups.
transitivity
  (interp_sum_numeric
    (map finite_numeric_observation
      (nonempty_finite_group_totals groups))).
- apply interp_sum_numeric_values_extensional.
  + apply grouped_finite_sums_all_numeric.
  + apply finite_observations_all_numeric.
  + rewrite numeric_values_grouped_finite_sums,
      numeric_values_finite_observations; reflexivity.
- rewrite !interp_sum_finite_observations.
  pose proof (nonempty_group_totals_flatten groups) as Htotals.
  destruct (concat groups) as [|number numbers] eqn:Hconcat.
  + assert (nonempty_finite_group_totals groups = []) as Hempty.
    { apply (proj2 (nonempty_group_totals_nil_iff groups)); exact Hconcat. }
    now rewrite Hempty.
  + destruct (nonempty_finite_group_totals groups) as [|total totals]
      eqn:Hgroups.
    * exfalso.
      apply (proj1 (nonempty_group_totals_nil_iff groups)) in Hgroups.
      rewrite Hgroups in Hconcat; discriminate.
    * now rewrite Htotals.
Qed.

(** Bag-side hypotheses used to prove that a SQL DISTINCT node is inert.
    They are stated using FormalSQL's semantic tuple comparison, not Rocq's
    structural equality. *)
Section DuplicateFreeUnion.

Context {T : Tuple.Rcd}.

Local Definition bagT := Febag.bag (SqlQuerySemantics.BTupleT T).

Definition query_bag_duplicate_free (bag : bagT) : Prop :=
  forall row,
    (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row bag <= 1)%N.

Definition query_bags_disjoint (left right : bagT) : Prop :=
  forall row,
    Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left = 0%N \/
    Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right = 0%N.

(** UNION ALL exposes the sum of the two input multiplicities.  Keeping this
    as an occurrence law lets larger rewrites compose it without baking in a
    surrounding DISTINCT, filter, projection, or query tree. *)
Lemma query_set_union_occurrence_exact : forall left right row,
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row
    (query_set_bag Union left right) =
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right)%N.
Proof.
intros left right row.
unfold query_set_bag; cbn.
apply Febag.nb_occ_union.
Qed.

(** Semantic list duplicate-freedom transfers exactly to the finite-bag
    abstraction.  The relation is FormalSQL tuple equality, not Rocq
    structural equality. *)
Lemma query_bag_duplicate_free_of_rows_NoDupA : forall rows,
  NoDupA
    (fun first second => Oeset.compare (OTuple T) first second = Eq)
    rows ->
  query_bag_duplicate_free (rows_bag T rows).
Proof.
intros rows Hnodup row.
unfold query_bag_duplicate_free, rows_bag.
rewrite Febag.nb_occ_mk_bag.
rewrite (@oeset_nb_occ_of_NoDupA
  (tuple T) (OTuple T) rows Hnodup row).
destruct (Oeset.mem_bool (OTuple T) row rows); cbn; lia.
Qed.

(** Duplicate-freedom is proper under semantic bag equality. *)
Lemma query_bag_duplicate_free_transport : forall left right,
  bag_eq T left right ->
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right.
Proof.
intros left right Hbags Hleft.
unfold query_bag_duplicate_free in Hleft |- *.
intro row.
specialize (Hleft row).
pose proof
  ((proj1 (@bag_eq_iff_occurrences T left right) Hbags) row) as Hocc.
exact
  (eq_ind
    (Febag.nb_occ (Fecol.CBag (CTuple T)) row left)
    (fun count => (count <= 1)%N)
    Hleft
    (Febag.nb_occ (Fecol.CBag (CTuple T)) row right)
    Hocc).
Qed.

(** A successful global GROUP bag is duplicate-free independently of its
    SELECT list and HAVING predicate: global grouping has one logical group,
    so a successful group scheduler emits at most one row. *)
Section GlobalGroupDuplicateFree.

Context {relname : Type}.

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
Variable boolean_schedule :
  SqlQuerySyntax.boolean_site -> SqlQuerySyntax.boolean_evaluation_order.

Theorem eval_group_bag_global_success_duplicate_free :
  forall env select_list having input_bag output_bag,
    @eval_group_bag_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env select_list [] having input_bag
      (SqlSuccess output_bag) ->
    query_bag_duplicate_free output_bag.
Proof.
intros env select_list having input_bag output_bag Heval.
inversion Heval; subst.
match goal with
| Hkeys : SqlQuerySyntax.scalar_group_key_terms [] = Some ?group_terms |- _ =>
    cbn [SqlQuerySyntax.scalar_group_key_terms] in Hkeys;
    inversion Hkeys; subst group_terms
end.
eapply query_bag_duplicate_free_transport.
- apply query_same_rows_as_bag_iff_bag_eq; eassumption.
- apply query_bag_duplicate_free_of_rows_NoDupA.
  eapply (@eval_groups_global_success_NoDupA T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null boolean_schedule
    (fun first second =>
      Oeset.compare (OTuple T) first second = Eq)); eassumption.
Qed.

End GlobalGroupDuplicateFree.

Lemma query_bags_disjoint_sym : forall left right,
  query_bags_disjoint left right -> query_bags_disjoint right left.
Proof.
intros left right Hdisjoint row.
destruct (Hdisjoint row) as [Hleft | Hright]; [right | left]; assumption.
Qed.

Lemma query_set_union_duplicate_free : forall left right,
  query_bag_duplicate_free left ->
  query_bag_duplicate_free right ->
  query_bags_disjoint left right ->
  query_bag_duplicate_free (query_set_bag Union left right).
Proof.
intros left right Hleft Hright Hdisjoint row.
unfold query_bag_duplicate_free in Hleft, Hright.
unfold query_bags_disjoint in Hdisjoint.
unfold query_set_bag; cbn.
rewrite Febag.nb_occ_union.
change
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right <= 1)%N.
destruct (Hdisjoint row) as [Hzero | Hzero]; rewrite Hzero.
- rewrite N.add_0_l; apply Hright.
- rewrite N.add_0_r; apply Hleft.
Qed.

Lemma query_set_union_disjoint_right : forall first second third,
  query_bags_disjoint first third ->
  query_bags_disjoint second third ->
  query_bags_disjoint (query_set_bag Union first second) third.
Proof.
intros first second third Hfirst Hsecond row.
unfold query_bags_disjoint in Hfirst, Hsecond.
destruct (Hfirst row) as [Hfirst_zero | Hthird_zero];
  [|right; exact Hthird_zero].
destruct (Hsecond row) as [Hsecond_zero | Hthird_zero];
  [left | right; exact Hthird_zero].
unfold query_set_bag; cbn; rewrite Febag.nb_occ_union.
change
  (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row first +
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row second = 0)%N.
now rewrite Hfirst_zero, Hsecond_zero.
Qed.

Lemma query_distinct_bag_inert : forall bag,
  query_bag_duplicate_free bag ->
  bag_eq T (query_distinct_bag bag) bag.
Proof.
intros bag Hunique.
apply bag_eq_iff_occurrences; intro row.
unfold query_distinct_bag.
rewrite Febag.nb_occ_mk_bag.
change
  (Feset.nb_occ (Fecol.CSet (CTuple T)) row
    (Feset.mk_set (Fecol.CSet (CTuple T))
      (Febag.elements (SqlQuerySemantics.BTupleT T) bag)) =
   Febag.nb_occ (SqlQuerySemantics.BTupleT T) row bag).
rewrite Feset.nb_occ_alt, Feset.mem_mk_set.
rewrite <- Febag.mem_unfold, Febag.mem_nb_occ.
specialize (Hunique row).
destruct (Febag.nb_occ (SqlQuerySemantics.BTupleT T) row bag) as [|count];
  cbn in Hunique |- *; [reflexivity|].
assert (N.pos count = 1%N) by lia.
now rewrite H.
Qed.

(** DISTINCT maps every supported tuple to multiplicity one and every absent
    tuple to zero.  This is the single-operator occurrence contract; callers
    remain responsible for the child relation and runtime outcome. *)
Lemma query_distinct_bag_occurrence_exact : forall bag row,
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row
    (query_distinct_bag bag) =
  if Febag.mem (SqlQuerySemantics.BTupleT T) row bag then 1%N else 0%N.
Proof.
intros bag row.
unfold query_distinct_bag.
rewrite Febag.nb_occ_mk_bag.
change
  (Feset.nb_occ (Fecol.CSet (CTuple T)) row
    (Feset.mk_set (Fecol.CSet (CTuple T))
      (Febag.elements (SqlQuerySemantics.BTupleT T) bag)) =
   if Febag.mem (SqlQuerySemantics.BTupleT T) row bag
   then 1%N
   else 0%N).
rewrite Feset.nb_occ_alt, Feset.mem_mk_set.
rewrite <- Febag.mem_unfold.
reflexivity.
Qed.

(** Duplicate-free bags are equal once their semantic supports agree.  The
    duplicate-free premises turn every nonzero occurrence count into exactly
    one; no representative order or structural tuple equality is exposed. *)
Lemma query_duplicate_free_support_bag_eq :
  forall left right : bagT,
    query_bag_duplicate_free left ->
    query_bag_duplicate_free right ->
    (forall row,
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left = 0%N <->
      Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right = 0%N) ->
    bag_eq T left right.
Proof.
intros left right Hleft Hright Hsupport.
apply bag_eq_iff_occurrences; intro row.
specialize (Hleft row); specialize (Hright row); specialize (Hsupport row).
set (left_occ :=
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row left) in *.
set (right_occ :=
  Febag.nb_occ (SqlQuerySemantics.BTupleT T) row right) in *.
change (left_occ = right_occ).
destruct left_occ as [|left_count];
destruct right_occ as [|right_count].
- reflexivity.
- exfalso.
  pose proof (proj1 Hsupport eq_refl) as Hzero.
  discriminate Hzero.
- exfalso.
  pose proof (proj2 Hsupport eq_refl) as Hzero.
  discriminate Hzero.
- cbn in Hleft, Hright.
  assert (N.pos left_count = 1%N) by lia.
  assert (N.pos right_count = 1%N) by lia.
  congruence.
Qed.

End DuplicateFreeUnion.

(** Exact occurrence contract for one finite-bag filter.  The predicate must
    respect semantic tuple equality because the bag representation is
    quotient-facing. *)
Lemma query_bag_filter_occurrence_exact :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool)
      (bag : Febag.bag (SqlQuerySemantics.BTupleT T)),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    forall row,
      Febag.nb_occ (Fecol.CBag (CTuple T)) row
        (Febag.filter (Fecol.CBag (CTuple T)) keep bag) =
      if keep row
      then Febag.nb_occ (Fecol.CBag (CTuple T)) row bag
      else 0%N.
Proof.
intros T keep bag Hproper row.
rewrite Febag.nb_occ_filter.
- destruct (keep row); cbn;
    [now rewrite N.mul_1_r | now rewrite N.mul_0_r].
- intros first second _ Hequal; now apply Hproper.
Qed.

(** Filtering a duplicate-free bag preserves duplicate-freedom.  The
    predicate must respect semantic tuple equality because [Febag.filter]
    operates on the quotient-facing finite-bag interface. *)
Lemma query_bag_filter_duplicate_free :
  forall (T : Tuple.Rcd) (keep : tuple T -> bool)
      (bag : Febag.bag (SqlQuerySemantics.BTupleT T)),
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    query_bag_duplicate_free bag ->
    query_bag_duplicate_free
      (Febag.filter (Fecol.CBag (CTuple T)) keep bag).
Proof.
intros T keep bag Hproper Hunique row.
rewrite Febag.nb_occ_filter.
- destruct (keep row); cbn; [now rewrite N.mul_1_r | now rewrite N.mul_0_r].
- intros first second _ Hequal; now apply Hproper.
Qed.
