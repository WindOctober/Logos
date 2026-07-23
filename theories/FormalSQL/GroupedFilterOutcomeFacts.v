(******************************************************************************)
(** Outcome-exact grouped-key HAVING-conjunct pushdown facts.                 **)
(******************************************************************************)

From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula SqlAlgebra
  SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax.
From Logos.FormalSQL Require Import GroupingRewriteFacts.
From Stdlib Require Import Bool List.

Import ListNotations.
Import Tuple.

(** These contracts expose the two facts about a relational formula outcome
    which an outcome-preserving filter rewrite actually needs.  Existence is
    separate from exclusion of other observations because formula evaluation
    is relational (subqueries can have several legal outcomes). *)
Section FormulaContracts.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable contains_nulls : Tuple.tuple T -> bool.
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
  (@eval_formula_expr_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Definition formula_total_success_at
    (env : Env.env T) (formula : formula_expr T relname) : Prop :=
  (exists truth, eval_formula env formula (SqlSuccess truth)) /\
  (forall error, ~ eval_formula env formula (SqlError error)).

Definition formula_acceptance_exact_at
    (env : Env.env T) (formula : formula_expr T relname)
    (accepted : bool) : Prop :=
  (exists truth,
    eval_formula env formula (SqlSuccess truth) /\
    Bool.is_true (B T) truth = accepted) /\
  (forall truth,
    eval_formula env formula (SqlSuccess truth) ->
    Bool.is_true (B T) truth = accepted) /\
  (forall error, ~ eval_formula env formula (SqlError error)).

Lemma formula_acceptance_exact_total_success :
  forall env formula accepted,
    formula_acceptance_exact_at env formula accepted ->
    formula_total_success_at env formula.
Proof.
  intros env formula accepted
    [[truth [Htruth Haccepted]] [Hsuccess Herror]].
  split; [now exists truth|exact Herror].
Qed.

(** [FExpr_Conj And_F] is eager in FormalSQL: the right formula is evaluated
    after every successful left observation, even when the left observation
    is SQL-nontrue.  These lemmas retain that evaluation order explicitly. *)
Lemma formula_and_success_intro :
  forall env left right left_truth right_truth,
    eval_formula env left (SqlSuccess left_truth) ->
    eval_formula env right (SqlSuccess right_truth) ->
    eval_formula env (FExpr_Conj And_F left right)
      (SqlSuccess (Bool.andb (B T) left_truth right_truth)).
Proof.
  intros; now apply EFormula_ConjSuccess.
Qed.

Lemma formula_and_right_error_intro :
  forall env left right left_truth error,
    eval_formula env left (SqlSuccess left_truth) ->
    eval_formula env right (SqlError error) ->
    eval_formula env (FExpr_Conj And_F left right) (SqlError error).
Proof.
  intros env left right left_truth error Hleft Hright.
  eapply EFormula_ConjRightError with (left_truth := left_truth);
    eassumption.
Qed.

Lemma formula_and_true_left_outcome_exact :
  forall env left right,
    formula_acceptance_exact_at env left true ->
    forall outcome,
      eval_formula env (FExpr_Conj And_F left right) outcome <->
      eval_formula env right outcome.
Proof.
  intros env left right
    [[left_truth [Hleft Hleft_accept]] [Hleft_success Hleft_error]]
    outcome.
  assert (Hleft_true : left_truth = Bool.true (B T)).
  { apply (proj1 (Bool.true_is_true (B T) left_truth));
      exact Hleft_accept. }
  split; intro Heval.
  - inversion Heval; subst.
    + exfalso; eapply Hleft_error; eassumption.
    + assumption.
    + assert (Hobserved_true : left_truth0 = Bool.true (B T)).
      { apply (proj1 (Bool.true_is_true (B T) left_truth0));
          now apply Hleft_success. }
      subst left_truth0.
      cbn [interp_conj].
      rewrite Bool.andb_true_l; assumption.
  - destruct outcome as [right_truth|error].
    + replace right_truth with
        (Bool.andb (B T) left_truth right_truth).
      * eapply formula_and_success_intro; eassumption.
      * subst left_truth; now rewrite Bool.andb_true_l.
    + eapply formula_and_right_error_intro; eassumption.
Qed.

Lemma formula_and_total_success_at_intro :
  forall env left right,
    formula_total_success_at env left ->
    formula_total_success_at env right ->
    formula_total_success_at env (FExpr_Conj And_F left right).
Proof.
  intros env left right
    [[left_truth Hleft] Hleft_error]
    [[right_truth Hright] Hright_error].
  split.
  - exists (Bool.andb (B T) left_truth right_truth).
    now eapply formula_and_success_intro.
  - intros error Heval; inversion Heval; subst.
    + eapply Hleft_error; eassumption.
    + eapply Hright_error; eassumption.
Qed.

Lemma formula_and_left_nontrue_success_rejected :
  forall env left right truth,
    formula_acceptance_exact_at env left false ->
    eval_formula env (FExpr_Conj And_F left right) (SqlSuccess truth) ->
    Bool.is_true (B T) truth = false.
Proof.
  intros env left right truth
    [[left_truth [Hleft Hleft_accept]] [Hleft_success Hleft_error]] Heval.
  inversion Heval; subst.
  assert (Hobserved : Bool.is_true (B T) left_truth0 = false).
  { apply Hleft_success; eassumption. }
  cbn [interp_conj].
  rewrite Bool.is_true_andb, Hobserved; reflexivity.
Qed.

End FormulaContracts.

Arguments formula_total_success_at
  {T relname} basesort instance unknown contains_nulls symbol_runtime_error
  aggregate_runtime_error value_is_null env formula.
Arguments formula_acceptance_exact_at
  {T relname} basesort instance unknown contains_nulls symbol_runtime_error
  aggregate_runtime_error value_is_null env formula accepted.

(** The exact list-level bridge.  [keep] is the group-key decision computed
    by the lower filter.  [key_formula] is its HAVING-level FormulaExpr view.
    On groups rejected by [keep], the source still performs SELECT aggregate
    finalization and eagerly evaluates all of HAVING; the explicit safety
    premise is therefore essential.  Scalar SELECT runtime evaluation is not
    a premise: the operational semantics correctly skips it once HAVING is
    SQL-nontrue. *)
Section GroupedHavingBridge.

Context {T : Tuple.Rcd} {relname : Type}.

Variable basesort : relname -> Fset.set (Tuple.A T).
Variable instance : relname -> Febag.bag (Fecol.CBag (Tuple.CTuple T)).
Variable unknown : Bool.b (Tuple.B T).
Variable contains_nulls : Tuple.tuple T -> bool.
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
  (@eval_formula_expr_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_formula_aggregates :=
  (@eval_formula_expr_aggregate_runtime_error T relname
    symbol_runtime_error aggregate_runtime_error).
Local Abbreviation eval_select_aggregates :=
  (@eval_select_list_aggregate_runtime_error T
    symbol_runtime_error aggregate_runtime_error).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Definition group_env
    (env : Env.env T) (group_terms : list (@aggterm T))
    (group : list (tuple T)) : Env.env T :=
  env_g T env (@Group_By T group_terms) group.

Definition grouped_key_formula_contract
    (env : Env.env T) (group_terms : list (@aggterm T))
    (key_formula : formula_expr T relname)
    (groups : list (list (tuple T)))
    (keep : list (tuple T) -> bool) : Prop :=
  forall group,
    In group groups ->
    eval_formula_aggregates (group_env env group_terms group) key_formula =
      None /\
    formula_acceptance_exact_at
      basesort instance unknown contains_nulls symbol_runtime_error
      aggregate_runtime_error value_is_null
      (group_env env group_terms group) key_formula (keep group).

Definition skipped_group_runtime_safe
    (env : Env.env T) (select_list : _select_list T)
    (group_terms : list (@aggterm T))
    (rest_having : formula_expr T relname)
    (groups : list (list (tuple T)))
    (keep : list (tuple T) -> bool) : Prop :=
  forall group,
    In group groups ->
    keep group = false ->
    eval_select_aggregates (group_env env group_terms group) select_list = None /\
    eval_formula_aggregates (group_env env group_terms group) rest_having = None /\
    formula_total_success_at
      basesort instance unknown contains_nulls symbol_runtime_error
      aggregate_runtime_error value_is_null
      (group_env env group_terms group) rest_having.

Lemma grouped_key_formula_contract_tail :
  forall env group_terms key_formula group groups keep,
    grouped_key_formula_contract env group_terms key_formula
      (group :: groups) keep ->
    grouped_key_formula_contract env group_terms key_formula groups keep.
Proof.
  intros env group_terms key_formula group groups keep Hcontract other Hin.
  apply Hcontract; now right.
Qed.

Lemma skipped_group_runtime_safe_tail :
  forall env select_list group_terms rest_having group groups keep,
    skipped_group_runtime_safe env select_list group_terms rest_having
      (group :: groups) keep ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      groups keep.
Proof.
  intros env select_list group_terms rest_having group groups keep
    Hsafe other Hin.
  apply Hsafe; now right.
Qed.

Theorem eval_groups_having_key_conj_filter_exact :
  forall env select_list group_terms key_formula rest_having groups keep,
    grouped_key_formula_contract env group_terms key_formula groups keep ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      groups keep ->
    forall outcome,
      eval_groups env select_list group_terms
        (FExpr_Conj And_F key_formula rest_having) groups outcome <->
      eval_groups env select_list group_terms rest_having
        (filter keep groups) outcome.
Proof.
  intros env select_list group_terms key_formula rest_having groups.
  induction groups as [|group groups IH]; intros keep Hkey Hskip outcome.
  - cbn; split; intro Heval; inversion Heval; constructor.
  - assert (Hkey_head := Hkey group (or_introl eq_refl)).
    destruct Hkey_head as [Hkey_aggregates Hkey_exact].
    assert (Hkey_tail := grouped_key_formula_contract_tail
      env group_terms key_formula group groups keep Hkey).
    assert (Hskip_tail := skipped_group_runtime_safe_tail
      env select_list group_terms rest_having group groups keep Hskip).
    specialize (IH keep Hkey_tail Hskip_tail).
    destruct (keep group) eqn:Hkeep; cbn [filter]; rewrite Hkeep; cbn.
    + assert (Hformula : forall observed,
        eval_formula (group_env env group_terms group)
          (FExpr_Conj And_F key_formula rest_having) observed <->
        eval_formula (group_env env group_terms group)
          rest_having observed).
      {
        intro observed.
        now apply formula_and_true_left_outcome_exact.
      }
      assert (Haggregates :
        eval_formula_aggregates (group_env env group_terms group)
          (FExpr_Conj And_F key_formula rest_having) =
        eval_formula_aggregates (group_env env group_terms group)
          rest_having).
      {
        cbn [eval_formula_expr_aggregate_runtime_error].
        now rewrite Hkey_aggregates.
      }
      unfold group_env in Haggregates.
      split; intro Heval; inversion Heval; subst.
      * eapply EGroups_AggregateError; eassumption.
      * eapply EGroups_HavingAggregateError.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
      * eapply EGroups_HavingError.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
      * eapply EGroups_HavingFalse.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
        -- eassumption.
        -- apply (proj1 (IH _)); eassumption.
      * eapply EGroups_SelectError.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
      * eapply EGroups_SelectSuccess.
        -- eassumption.
        -- rewrite <- Haggregates; eassumption.
        -- apply (proj1 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
        -- apply (proj1 (IH _)); eassumption.
      * eapply EGroups_AggregateError; eassumption.
      * eapply EGroups_HavingAggregateError.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
      * eapply EGroups_HavingError.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
      * eapply EGroups_HavingFalse.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
        -- eassumption.
        -- apply (proj2 (IH _)); eassumption.
      * eapply EGroups_SelectError.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
      * eapply EGroups_SelectSuccess.
        -- eassumption.
        -- rewrite Haggregates; eassumption.
        -- apply (proj2 (Hformula _)); eassumption.
        -- eassumption.
        -- eassumption.
        -- apply (proj2 (IH _)); eassumption.
    + destruct (Hskip group (or_introl eq_refl) Hkeep) as
      [Hselect_aggregates
          [Hrest_aggregates
            Hrest_total]].
      pose proof (formula_acceptance_exact_total_success
        basesort instance unknown contains_nulls symbol_runtime_error
        aggregate_runtime_error value_is_null _ _ _ Hkey_exact)
        as Hkey_total.
      pose proof (formula_and_total_success_at_intro
        basesort instance unknown contains_nulls symbol_runtime_error
        aggregate_runtime_error value_is_null _ _ _
        Hkey_total Hrest_total)
        as Hconj_total.
      destruct Hconj_total as
        [[conj_truth Hconj_truth] Hconj_error].
      assert (Hconj_rejected :
        Bool.is_true (B T) conj_truth = false).
      {
        eapply formula_and_left_nontrue_success_rejected; eassumption.
      }
      assert (Haggregates :
        eval_formula_aggregates (group_env env group_terms group)
          (FExpr_Conj And_F key_formula rest_having) = None).
      {
        cbn [eval_formula_expr_aggregate_runtime_error].
        now rewrite Hkey_aggregates, Hrest_aggregates.
      }
      unfold group_env in Hselect_aggregates, Haggregates.
      split; intro Heval.
      * inversion Heval; subst.
        -- congruence.
        -- congruence.
        -- exfalso; eapply Hconj_error; eassumption.
        -- apply (proj1 (IH _)); eassumption.
        -- assert (Hrejected : Bool.is_true (B T) truth = false).
           { eapply formula_and_left_nontrue_success_rejected; eassumption. }
           congruence.
        -- assert (Hrejected : Bool.is_true (B T) truth = false).
           { eapply formula_and_left_nontrue_success_rejected; eassumption. }
           congruence.
      * eapply EGroups_HavingFalse.
        -- exact Hselect_aggregates.
        -- exact Haggregates.
        -- exact Hconj_truth.
        -- exact Hconj_rejected.
        -- apply (proj2 (IH _)); eassumption.
Qed.

(** The lower [Q_Sigma] predicate is the older bag-algebra [sql_formula],
    whereas HAVING uses [formula_expr].  This definition is exactly the
    Boolean decision in [SqlAlgebra.eval_query]'s [Q_Sigma] branch. *)
Definition bag_formula_row_keep
    (env : Env.env T)
    (formula : @sql_formula T (@query T relname))
    (row : tuple T) : bool :=
  Bool.is_true (B T)
    (@eval_sql_formula T (@query T relname) unknown contains_nulls
      (@eval_query T relname basesort instance unknown contains_nulls)
      (env_t T env row) formula).

Lemma first_runtime_error_filter_none :
  forall (A : Type) (check : A -> option sql_runtime_error) keep rows,
    first_runtime_error check rows = None ->
    first_runtime_error check (filter keep rows) = None.
Proof.
  intros A check keep rows.
  induction rows as [|value rows IH]; intro Hnone; cbn in *.
  - reflexivity.
  - destruct (check value) eqn:Hcheck; [discriminate|].
    destruct (keep value); cbn; rewrite ?Hcheck; now apply IH.
Qed.

(** A successful grouping-key pass remains successful after a lower filter;
    this is the key-runtime obligation needed when the list-level bridge is
    lifted to [eval_group_bag_outcome]. *)
Lemma group_keys_runtime_error_filter_none :
  forall env group_terms rows keep,
    @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
      env group_terms rows = None ->
    @group_keys_runtime_error T symbol_runtime_error aggregate_runtime_error
      env group_terms (filter keep rows) = None.
Proof.
  intros env group_terms rows keep Hnone.
  unfold group_keys_runtime_error in *.
  now apply first_runtime_error_filter_none.
Qed.

Lemma bag_sigma_eval_exact :
  forall env bag_formula input,
    @eval_query T relname basesort instance unknown contains_nulls env
      (Q_Sigma bag_formula input) =
    Febag.filter (Fecol.CBag (CTuple T))
      (bag_formula_row_keep env bag_formula)
      (@eval_query T relname basesort instance unknown contains_nulls env
        input).
Proof.
  reflexivity.
Qed.

(** The lower bag filter is runtime-total exactly when its child is total and
    every canonical input row passes the bag [Formula] runtime checker. *)
Lemma bag_sigma_runtime_error_none_iff :
  forall env bag_formula input,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env
      (Q_Sigma bag_formula input) = None <->
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env input = None /\
    first_runtime_error
      (fun row =>
        @eval_formula_runtime_error T relname symbol_runtime_error
          aggregate_runtime_error
          (@eval_query_runtime_error T relname basesort instance unknown
            contains_nulls symbol_runtime_error aggregate_runtime_error)
          (env_t T env row) bag_formula)
      (Febag.elements (Fecol.CBag (CTuple T))
        (@eval_query T relname basesort instance unknown contains_nulls env
          input)) = None.
Proof.
  intros env bag_formula input.
  cbn [eval_query_runtime_error].
  destruct (@eval_query_runtime_error T relname basesort instance unknown
    contains_nulls symbol_runtime_error aggregate_runtime_error env input);
    cbn; split; intro H.
  - discriminate.
  - destruct H as [H _]; discriminate.
  - now split.
  - now destruct H as [_ H].
Qed.

Definition grouped_key_keep
    (env : Env.env T) (group_terms : list (@aggterm T))
    (keep_key : list (value T) -> bool)
    (group : list (tuple T)) : bool :=
  match group with
  | nil => false
  | row :: _ => keep_key (query_grouping_key env group_terms row)
  end.

(** This is the explicit syntax/semantics bridge required by pushdown.

    - The first conjunct says that the actual bag [Formula] decision factors
      through the complete emitted grouping-key vector.  Consequently its
      truth is constant on every group; no attribute outside the key may be
      smuggled into the lower filter.
    - The second conjunct says that every legal HAVING [FormulaExpr]
      observation has exactly that TRUE/non-TRUE decision, excludes errors,
      is inhabited, and has no aggregate-finalization error.

    Neither conjunct assumes a query or group-evaluator equivalence. *)
Definition bag_formula_group_key_link
    (env : Env.env T) (group_terms : list (@aggterm T))
    (bag_formula : @sql_formula T (@query T relname))
    (key_formula : formula_expr T relname)
    (rows : list (tuple T))
    (keep_key : list (value T) -> bool) : Prop :=
  (forall row,
    In row rows ->
    bag_formula_row_keep env bag_formula row =
      keep_key (query_grouping_key env group_terms row)) /\
  grouped_key_formula_contract env group_terms key_formula
    (query_make_groups env rows group_terms)
    (grouped_key_keep env group_terms keep_key).

Lemma bag_formula_key_factorization_is_constant :
  forall env group_terms bag_formula rows keep_key left right,
    (forall row,
      In row rows ->
      bag_formula_row_keep env bag_formula row =
        keep_key (query_grouping_key env group_terms row)) ->
    In left rows ->
    In right rows ->
    query_grouping_key env group_terms left =
      query_grouping_key env group_terms right ->
    bag_formula_row_keep env bag_formula left =
      bag_formula_row_keep env bag_formula right.
Proof.
  intros env group_terms bag_formula rows keep_key left right
    Hfactor Hleft Hright Hkey.
  rewrite (Hfactor left Hleft), (Hfactor right Hright), Hkey.
  reflexivity.
Qed.

Lemma filter_extensional_on_members :
  forall (A : Type) (left right : A -> bool) rows,
    (forall value, In value rows -> left value = right value) ->
    filter left rows = filter right rows.
Proof.
  intros A left right rows Hsame.
  induction rows as [|value rows IH]; cbn.
  - reflexivity.
  - rewrite (Hsame value (or_introl eq_refl)).
    rewrite IH; [reflexivity|].
    intros other Hin; apply Hsame; now right.
Qed.

(** This corollary is ready to compose with the bag-level [Q_Sigma]
    evaluation.  The nonempty-key premise is semantically necessary: global
    aggregation over empty input creates one empty group, while filtering
    before grouping can remove all ordinary rows. *)
Theorem eval_groups_having_key_conj_after_bag_formula_filter_exact :
  forall env select_list group_terms key_formula rest_having rows
      bag_formula keep_key,
    group_terms <> nil ->
    bag_formula_group_key_link env group_terms bag_formula key_formula
      rows keep_key ->
    skipped_group_runtime_safe env select_list group_terms rest_having
      (query_make_groups env rows group_terms)
      (grouped_key_keep env group_terms keep_key) ->
    forall outcome,
      eval_groups env select_list group_terms
        (FExpr_Conj And_F key_formula rest_having)
        (query_make_groups env rows group_terms) outcome <->
      eval_groups env select_list group_terms rest_having
        (query_make_groups env
          (filter (bag_formula_row_keep env bag_formula) rows)
          group_terms) outcome.
Proof.
  intros env select_list group_terms key_formula rest_having rows
    bag_formula keep_key Hnonempty [Hfactor Hkey] Hskip outcome.
  assert (Hfilter :
    filter (bag_formula_row_keep env bag_formula) rows =
    filter
      (fun row => keep_key (query_grouping_key env group_terms row)) rows).
  {
    apply filter_extensional_on_members.
    exact Hfactor.
  }
  rewrite Hfilter.
  rewrite (query_make_groups_filter_by_key_exact
    T env group_terms rows keep_key Hnonempty).
  apply eval_groups_having_key_conj_filter_exact; assumption.
Qed.

End GroupedHavingBridge.
