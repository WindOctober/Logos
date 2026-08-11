(** Correlation-preserving membership/EXISTS composition. *)

Set Implicit Arguments.

From Stdlib Require Import List Lia.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance ListPermut OrderedSet Projection SqlBagAbstraction
  SqlErrorSemantics SqlOutcome SqlQueryContexts SqlQueryFacts
  SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts MembershipCompositionFacts OrderedQueryFacts
  PossibleOutcomeFacts RelationalAlgebraFacts SubqueryFacts.

Import ListNotations.
Import Tuple.

(******************************************************************************)
(** Correlated predicate decisions and native semi/anti-join sources.       **)
(******************************************************************************)

Section CorrelatedMembershipSources.

Context {T : Tuple.Rcd} {relname : Type}.

Lemma query_join_row_has_match_map :
  forall (matches : tuple T -> tuple T -> bool) left right_rows,
    query_join_row_has_match (map (matches left) right_rows) =
    existsb (matches left) right_rows.
Proof.
intros matches left right_rows.
induction right_rows as [|right right_rows IH]; cbn; [reflexivity|].
destruct (matches left right); cbn; [reflexivity|exact IH].
Qed.

Lemma query_join_source_rows_left_map :
  forall rows : list (tuple T),
    map (@query_join_source_row T) (map (@JoinSourceLeft T) rows) = rows.
Proof.
intro rows; induction rows as [|row rows IH]; cbn; [reflexivity|].
now rewrite IH.
Qed.

(** The native semi-join scheduler retains each matching left occurrence
    exactly once.  The equation is stronger than a support statement: input
    order and duplicate multiplicity are both preserved. *)
Lemma query_join_semi_sources_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) left_rows right_rows,
    query_join_sources T QueryJoinSemi left_rows right_rows
      (map (fun left => map (matches left) right_rows) left_rows) =
    map (@JoinSourceLeft T)
      (filter (fun left => existsb (matches left) right_rows) left_rows).
Proof.
intros matches left_rows; induction left_rows as [|left left_rows IH];
  intro right_rows;
  cbn -[query_join_row_has_match].
- reflexivity.
- unfold query_join_sources in IH.
  assert (IHleft :
    query_join_left_sources T QueryJoinSemi left_rows right_rows
      (map (fun current => map (matches current) right_rows) left_rows) =
    map (@JoinSourceLeft T)
      (filter (fun current => existsb (matches current) right_rows)
        left_rows)).
  {
    rewrite <- IH.
    symmetry; apply app_nil_r.
  }
  rewrite query_join_row_has_match_map, IHleft.
  destruct (existsb (matches left) right_rows); cbn; now rewrite app_nil_r.
Qed.

(** The native anti-join scheduler retains each left occurrence for which no
    join-condition comparison is TRUE.  This is directly suitable for
    [NOT EXISTS].  It is suitable for [NOT IN] only after a separate theorem
    rules out UNKNOWN contamination. *)
Lemma query_join_anti_sources_boolean_matrix :
  forall (matches : tuple T -> tuple T -> bool) left_rows right_rows,
    query_join_sources T QueryJoinAnti left_rows right_rows
      (map (fun left => map (matches left) right_rows) left_rows) =
    map (@JoinSourceLeft T)
      (filter
        (fun left => negb (existsb (matches left) right_rows)) left_rows).
Proof.
intros matches left_rows; induction left_rows as [|left left_rows IH];
  intro right_rows;
  cbn -[query_join_row_has_match].
- reflexivity.
- unfold query_join_sources in IH.
  assert (IHleft :
    query_join_left_sources T QueryJoinAnti left_rows right_rows
      (map (fun current => map (matches current) right_rows) left_rows) =
    map (@JoinSourceLeft T)
      (filter
        (fun current => negb (existsb (matches current) right_rows))
        left_rows)).
  {
    rewrite <- IH.
    symmetry; apply app_nil_r.
  }
  rewrite query_join_row_has_match_map, IHleft.
  destruct (existsb (matches left) right_rows); cbn; now rewrite app_nil_r.
Qed.

End CorrelatedMembershipSources.

(******************************************************************************)
(** Exact correlated scalar acceptance lifted to row-list execution.        **)
(******************************************************************************)

Section CorrelatedMembershipRows.

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

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation scalar_exact :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** One pointwise contract covers correlated [IN], [EXISTS], [NOT EXISTS],
    and NULL-safe [NOT IN].  [retain] is identity for semi-join and Boolean
    negation for anti-join.  Correlation is explicit in [env_t]: each left
    occurrence receives its own outer-row environment. *)
Definition correlated_filter_join_acceptance_exact_at
    (env : Env.env T)
    (formula : scalar_expr T relname ScalarResultBoolean)
    (right_rows : list (tuple T))
    (matches : tuple T -> tuple T -> bool)
    (retain : bool -> bool) (left_rows : list (tuple T)) : Prop :=
  forall left,
    In left left_rows ->
    scalar_exact (env_t T env left) formula
      (retain (existsb (matches left) right_rows)).

(** A correlated predicate whose exact filter decision is existence of a
    matching right row executes exactly like the occurrence-preserving native
    semi-join source scheduler.  Scalar/subquery errors cannot disappear:
    their exclusion is part of every exact acceptance premise. *)
Theorem eval_filter_rows_correlated_semijoin_sources_exact :
  forall env formula left_rows right_rows matches outcome,
    correlated_filter_join_acceptance_exact_at
      env formula right_rows matches (fun matched => matched) left_rows ->
    eval_filter_rows env formula left_rows outcome <->
    outcome =
      SqlSuccess
        (map (@query_join_source_row T)
          (query_join_sources T QueryJoinSemi left_rows right_rows
            (map (fun left => map (matches left) right_rows) left_rows))).
Proof.
intros env formula left_rows right_rows matches outcome Hexact.
rewrite query_join_semi_sources_boolean_matrix.
rewrite query_join_source_rows_left_map.
change
  (eval_filter_rows env formula left_rows outcome <->
   outcome = SqlSuccess
      (filter (fun left => existsb (matches left) right_rows) left_rows)).
apply eval_filter_rows_acceptance_exact.
intros row Hrow; exact (Hexact row Hrow).
Qed.

(** Anti-join is the same composition with the no-match decision.  This
    theorem does not derive the decision from [NOT IN]; callers must use the
    NULL-aware bridge below (or establish the exact contract independently). *)
Theorem eval_filter_rows_correlated_antijoin_sources_exact :
  forall env formula left_rows right_rows matches outcome,
    correlated_filter_join_acceptance_exact_at
      env formula right_rows matches negb left_rows ->
    eval_filter_rows env formula left_rows outcome <->
    outcome =
      SqlSuccess
        (map (@query_join_source_row T)
          (query_join_sources T QueryJoinAnti left_rows right_rows
            (map (fun left => map (matches left) right_rows) left_rows))).
Proof.
intros env formula left_rows right_rows matches outcome Hexact.
rewrite query_join_anti_sources_boolean_matrix.
rewrite query_join_source_rows_left_map.
change
  (eval_filter_rows env formula left_rows outcome <->
   outcome = SqlSuccess
      (filter
        (fun left => negb (existsb (matches left) right_rows)) left_rows)).
apply eval_filter_rows_acceptance_exact.
intros row Hrow; exact (Hexact row Hrow).
Qed.

End CorrelatedMembershipRows.

(******************************************************************************)
(** Constructor-specific exact contracts for IN, EXISTS, and their negation. *)
(******************************************************************************)

Section CorrelatedMembershipContracts.

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
Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation scalar_exact :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** Fixed-environment [IN] to semi-join acceptance.  The successful child may
    expose multiple legal row representatives; [Hfixed] requires all of them
    to agree only on TRUE acceptance, so FALSE and UNKNOWN remain distinct
    internally but are both rejected by WHERE. *)
Theorem scalar_expr_correlated_in_semijoin_acceptance_exact :
  forall env arguments subquery
      (right_rows : list (tuple T)) (matches : tuple T -> bool),
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs (query_expr_outputs subquery)) rows) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      existsb
        (fun row => Bool.is_true (B T)
          (@in_row_truth T relname unknown value_is_null
            values subquery row)) rows =
      existsb matches right_rows) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_exact env (SExpr_In arguments subquery)
      (existsb matches right_rows).
Proof.
intros env arguments subquery right_rows matches Harguments Hquery
  Houtputs Hfixed Hargument_errors Hquery_errors.
eapply scalar_expr_in_acceptance_exact
  with (accept := fun values row =>
    Bool.is_true (B T)
      (@in_row_truth T relname unknown value_is_null values subquery row)).
- exact Harguments.
- exact Hquery.
- exact Houtputs.
- intros values Hvalues row; reflexivity.
- exact Hfixed.
- exact Hargument_errors.
- exact Hquery_errors.
Qed.

(** EXISTS is intrinsically two-valued.  This direct acceptance form avoids
    demanding ordinary target-list outcomes from the subquery: the native
    EXISTS evaluator is the authoritative observation. *)
Theorem scalar_expr_correlated_exists_semijoin_acceptance_exact :
  forall env subquery
      (right_rows : list (tuple T)) (matches : tuple T -> bool),
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      Bool.is_true (B T) truth = existsb matches right_rows) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_exact env (SExpr_Exists subquery) (existsb matches right_rows).
Proof.
intros env subquery right_rows matches
  [truth Htruth] Hfixed Herrors.
unfold scalar_expr_acceptance_exact_at.
split.
- exists truth; split; [now apply EScalar_ExistsSuccess|now apply Hfixed].
- split.
  + intros observed Hobserved.
    apply eval_scalar_boolean_exists_success_iff in Hobserved.
    now apply Hfixed.
  + intros error Herror.
    apply eval_scalar_boolean_exists_error_iff in Herror.
    now apply (Herrors error).
Qed.

(** NOT EXISTS composes with anti-join because EXISTS never produces UNKNOWN.
    The emptiness premise is stated using the native EXISTS truth rather than
    ordinary subquery rows, preserving dead-target and error behavior. *)
Theorem scalar_expr_correlated_not_exists_antijoin_acceptance_exact :
  forall env subquery
      (right_rows : list (tuple T)) (matches : tuple T -> bool),
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty (negb (existsb matches right_rows))) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_exact env (SExpr_Not (SExpr_Exists subquery))
      (negb (existsb matches right_rows)).
Proof.
intros env subquery right_rows matches Hsuccess Hfixed Herrors.
now apply scalar_expr_not_exists_acceptance_exact.
Qed.

End CorrelatedMembershipContracts.

(** The PostgreSQL Bool3 instance needs an explicit no-UNKNOWN condition for
    NOT IN.  A true target match must correspond to a TRUE membership row;
    when no target match exists, every membership comparison must be FALSE.
    This is precisely the extra contract that plain anti-join lacks. *)
Section TNullNotInAntijoinContract.

Context {relname : Type}.

Variable basesort : relname -> Fset.set (A TNull).
Variable instance : relname -> Febag.bag (Fecol.CBag (CTuple TNull)).
Variable symbol_runtime_error :
  scalar_operator TNull ->
  list (option sql_runtime_error * value TNull) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate TNull ->
  list (option sql_runtime_error * value TNull) ->
  option sql_runtime_error.
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error NullValues.is_null_value
    boolean_schedule).
Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome TNull relname basesort instance unknown3
    symbol_runtime_error aggregate_runtime_error NullValues.is_null_value
    boolean_schedule).

Theorem tnull_scalar_expr_correlated_not_in_antijoin_acceptance_exact :
  forall env arguments subquery
      (right_rows : list (tuple TNull))
      (matches : tuple TNull -> bool),
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      if existsb matches right_rows
      then exists row,
        In row (@query_canonical_rows TNull rows) /\
        @in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery row = true3
      else Forall
        (fun row =>
          @in_row_truth TNull relname unknown3 NullValues.is_null_value
            values subquery row = false3)
        (@query_canonical_rows TNull rows)) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown3 symbol_runtime_error
      aggregate_runtime_error NullValues.is_null_value boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery))
      (negb (existsb matches right_rows)).
Proof.
intros env arguments subquery right_rows matches Harguments Hquery
  Hcases Hargument_errors Hquery_errors.
destruct (existsb matches right_rows) eqn:Hmatches; cbn [negb].
- eapply tnull_scalar_expr_not_in_rejects_exact_of_true_match;
    eassumption.
- eapply tnull_scalar_expr_not_in_accepts_exact_of_all_false;
    eassumption.
Qed.

End TNullNotInAntijoinContract.

(******************************************************************************)
(** Full scheduled and possible-outcome lifting across Filter and Join.      **)
(******************************************************************************)

Section CorrelatedFilterJoinOutcomes.

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

(** Scheduled constructor lift.  The right input is explicit because Filter
    does not otherwise evaluate it: requiring one success and excluding its
    errors prevents decorrelation from introducing an eager target-only error.
    The local continuation contract contains correlated scalar/subquery,
    Bool3 acceptance, join-condition, projection, bag, and local-error
    transport, but no child-query plumbing. *)
Theorem query_expr_correlated_filter_join_relation_transport :
  forall schedule env source_formula input kind target_predicate
      matched_select left_select right_select right row_rel,
    (exists right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows)) ->
    (forall error,
      ~ @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env right (SqlError error)) ->
    (forall left_rows right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows) ->
      outcome_relation_transport (Forall2 row_rel)
        (@eval_filter_rows_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env source_formula left_rows)
        (@query_join_rows_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env kind target_predicate matched_select left_select
          right_select left_rows right_rows)) ->
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter source_formula input))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Join kind target_predicate
          matched_select left_select right_select input right)).
Proof.
intros schedule env source_formula input kind target_predicate
  matched_select left_select right_select right row_rel
  [default_right Hdefault_right] Hright_safe Hlocal.
split.
- intros source_rows Hsource.
  apply eval_query_expr_filter_success_iff in Hsource.
  destruct Hsource as [left_rows [Hleft Hfilter]].
  destruct (proj1 (Hlocal left_rows default_right Hdefault_right)
    source_rows Hfilter) as [target_rows [Htarget Hrows]].
  exists target_rows; split; [|exact Hrows].
  destruct Htarget as [output_bag [Hbag Houtput]].
  eapply EQuery_JoinSuccess; eassumption.
- split.
  + intros target_rows Htarget.
    apply eval_query_expr_join_success_iff in Htarget.
    destruct Htarget as
      [left_rows [right_rows [output_bag
        [Hleft [Hright [Hbag Houtput]]]]]].
    destruct (proj1 (proj2 (Hlocal left_rows right_rows Hright))
      target_rows (ex_intro _ output_bag (conj Hbag Houtput)))
      as [source_rows [Hfilter Hrows]].
    exists source_rows; split; [|exact Hrows].
    eapply EQuery_FilterRows; eassumption.
  + intro error; split; intro Herror.
    * apply eval_query_expr_filter_error_iff in Herror.
      destruct Herror as [Hleft | [left_rows [Hleft Hfilter]]].
      -- now apply EQuery_JoinLeftError.
      -- pose proof (proj1
           ((proj2 (proj2
             (Hlocal left_rows default_right Hdefault_right))) error)
           Hfilter) as Hbag.
         eapply EQuery_JoinBagError; eassumption.
    * apply eval_query_expr_join_error_iff in Herror.
      destruct Herror as
        [Hleft |
         [left_rows [Hleft
           [Hright_error | [right_rows [Hright Hbag]]]]]].
      -- now apply EQuery_FilterChildError.
      -- exfalso; exact (Hright_safe error Hright_error).
      -- pose proof (proj2
           ((proj2 (proj2
             (Hlocal left_rows right_rows Hright))) error)
           Hbag) as Hfilter.
         eapply EQuery_FilterRows; eassumption.
Qed.

(** Compact all-schedule contract shared by semi-join, anti-join, and the
    generic Join form.  It records the extra right child required after
    decorrelation and the operator-local outcome transport, but deliberately
    does not prescribe how an IN/EXISTS formula proves that transport. *)
Definition correlated_filter_join_possible_outcome_contract
    (env : Env.env T)
    (source_formula : scalar_expr T relname ScalarResultBoolean)
    (kind : query_join_kind)
    (target_predicate : scalar_expr T relname ScalarResultBoolean)
    (matched_select left_select right_select : query_select_list T relname)
    (right : query_expr T relname)
    (row_rel : tuple T -> tuple T -> Prop) : Prop :=
  forall schedule,
    (exists right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows)) /\
    (forall error,
      ~ @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env right (SqlError error)) /\
    forall left_rows right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows) ->
      outcome_relation_transport (Forall2 row_rel)
        (@eval_filter_rows_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env source_formula left_rows)
        (@query_join_rows_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env kind target_predicate matched_select left_select
          right_select left_rows right_rows).

(** Public all-schedule lift.  Correlated environments remain inside the
    local contract, while the theorem handles union over schedules and
    possible-outcome inhabitation once. *)
Theorem query_expr_correlated_filter_join_possible_outcome_related :
  forall env source_formula input kind target_predicate
      matched_select left_select right_select right row_rel,
    correlated_filter_join_possible_outcome_contract env source_formula kind
      target_predicate matched_select left_select right_select right row_rel ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_related T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (Forall2 row_rel)
      (QExpr_Filter source_formula input)
      (QExpr_Join kind target_predicate
        matched_select left_select right_select input right).
Proof.
intros env source_formula input kind target_predicate
  matched_select left_select right_select right row_rel Hcontract Hinhabited.
unfold query_expr_possible_outcome_related,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_of_left_inhabited_transport;
  [exact Hinhabited|].
apply outcome_relation_transport_exists_same_index.
intro schedule.
destruct (Hcontract schedule) as [Hsuccess [Hsafe Hlocal]].
now apply query_expr_correlated_filter_join_relation_transport.
Qed.

(** Instantiating the row relation with semantic tuple equality recovers the
    ordinary ordered possible-outcome equivalence consumed by generated
    top-level theorems. *)
Corollary query_expr_correlated_filter_join_possible_outcome_equiv :
  forall env source_formula input kind target_predicate
      matched_select left_select right_select right,
    query_expr_outputs (QExpr_Filter source_formula input) =
      query_expr_outputs
        (QExpr_Join kind target_predicate
          matched_select left_select right_select input right) ->
    correlated_filter_join_possible_outcome_contract env source_formula kind
      target_predicate matched_select left_select right_select right
      (fun left right => Oeset.compare (OTuple T) left right = Eq) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter source_formula input)
      (QExpr_Join kind target_predicate
        matched_select left_select right_select input right).
Proof.
intros env source_formula input kind target_predicate matched_select
  left_select right_select right Houtputs Hcontract Hinhabited.
apply query_expr_possible_outcome_equiv_of_Forall2_rows;
  [exact Houtputs|].
eapply query_expr_correlated_filter_join_possible_outcome_related;
  eassumption.
Qed.

(** Named specializations keep agent search at the SQL rewrite boundary while
    sharing the same proof and contracts. *)
Corollary query_expr_correlated_filter_semijoin_possible_outcome_related :
  forall env source_formula input target_predicate
      matched_select left_select right_select right row_rel,
    correlated_filter_join_possible_outcome_contract env source_formula
      QueryJoinSemi target_predicate matched_select left_select right_select
      right row_rel ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_related T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (Forall2 row_rel)
      (QExpr_Filter source_formula input)
      (QExpr_Join QueryJoinSemi target_predicate
        matched_select left_select right_select input right).
Proof.
intros; eapply query_expr_correlated_filter_join_possible_outcome_related;
  eassumption.
Qed.

Corollary query_expr_correlated_filter_antijoin_possible_outcome_related :
  forall env source_formula input target_predicate
      matched_select left_select right_select right row_rel,
    correlated_filter_join_possible_outcome_contract env source_formula
      QueryJoinAnti target_predicate matched_select left_select right_select
      right row_rel ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter source_formula input) outcome) ->
    @query_expr_possible_outcome_related T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (Forall2 row_rel)
      (QExpr_Filter source_formula input)
      (QExpr_Join QueryJoinAnti target_predicate
        matched_select left_select right_select input right).
Proof.
intros; eapply query_expr_correlated_filter_join_possible_outcome_related;
  eassumption.
Qed.

End CorrelatedFilterJoinOutcomes.
