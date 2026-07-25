(************************************************************************************)
(** Reusable facts for FormalSQL's exact ordered query-outcome semantics.          **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Arith PeanoNat NArith Lia Sorting.Permutation.
From SQLFS Require Import
  ListPermut OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
  SqlOutcome SqlErrorSemantics SqlOrder SqlListFacts SqlBagAbstraction SqlQuerySyntax
  SqlQuerySemantics SqlQueryFacts SqlQueryContexts.
From Logos.FormalSQL Require Import
  QueryCardinality RelationalAlgebraFacts AggregateRuntimeFacts
  GroupedFilterOutcomeFacts.

Import Tuple.
Import ListNotations.

(** Exact row-list equality is preserved by the two list slices used by SQL
    OFFSET and FETCH. *)

Lemma ordered_rows_equiv_skipn :
  forall (T : Tuple.Rcd) count (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (skipn count left) (skipn count right).
Proof.
intros T count.
induction count as [|count IH]; intros left right Hequiv.
- exact Hequiv.
- destruct left as [|left_head left_tail];
    destruct right as [|right_head right_tail];
    unfold ordered_rows_equiv, mk_oelists in *; cbn in *;
    try discriminate; try reflexivity.
  destruct (Oeset.compare (OTuple T) left_head right_head);
    try discriminate.
  apply IH.
  exact Hequiv.
Qed.

Lemma ordered_rows_equiv_firstn :
  forall (T : Tuple.Rcd) count (left right : list (tuple T)),
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (firstn count left) (firstn count right).
Proof.
intros T count.
induction count as [|count IH]; intros left right Hequiv.
- unfold ordered_rows_equiv, mk_oelists; reflexivity.
- destruct left as [|left_head left_tail];
    destruct right as [|right_head right_tail];
    unfold ordered_rows_equiv, mk_oelists in *; cbn in *;
    try discriminate; try reflexivity.
  destruct (Oeset.compare (OTuple T) left_head right_head);
    try discriminate.
  apply IH.
  exact Hequiv.
Qed.

Section ExactQueries.

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

Local Abbreviation query_equiv :=
  (@query_expr_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_global_typed_outcome_equiv :=
  (@query_expr_global_typed_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_safe :=
  (query_expr_runtime_safe basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation success_bags :=
  (query_success_bags basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** A lightweight contract for row properties of every successful concrete
    observation of a query.  It deliberately says nothing about errors or
    query inhabitation: those remain separate outcome obligations. *)
Definition query_success_Forall
    (env : Env.env T) (query : query_expr T relname)
    (property : tuple T -> Prop) : Prop :=
  forall rows,
    eval_query env query (SqlSuccess rows) ->
    Forall property rows.

(** An inhabited error-free query relation necessarily contains a successful
    observation.  This small bridge is useful for relational evaluators: it
    does not assume that evaluation is deterministic, and it does not turn an
    error into a value. *)
Lemma query_expr_has_success_of_runtime_safe_and_outcome :
  forall env query,
    query_safe env query ->
    (exists outcome, eval_query env query outcome) ->
    query_has_success env query.
Proof.
intros env query Hsafe [[rows | error] Houtcome].
- now exists rows.
- exfalso; exact (Hsafe error Houtcome).
Qed.

(** The safe exact equivalence and error-preserving exact equivalence
    interfaces have the expected algebraic structure. *)

Lemma query_expr_equiv_refl_safe :
  forall env query,
    query_safe env query ->
    query_has_success env query ->
    query_equiv env query query.
Proof.
intros env query Hsafe Hsuccess.
split; [reflexivity |].
unfold query_expr_observation_equiv.
apply successful_relation_equiv_refl.
- apply ordered_rows_equiv_refl.
- exact Hsuccess.
- exact Hsafe.
Qed.

Lemma query_expr_outcome_equiv_refl :
  forall env query,
    (exists outcome, eval_query env query outcome) ->
    query_outcome_equiv env query query.
Proof.
intros env query Houtcome.
split; [reflexivity |].
unfold query_expr_outcome_observation_equiv.
apply outcome_relation_equiv_refl.
- apply ordered_rows_equiv_refl.
- exact Houtcome.
Qed.

(** Pointwise equality of the complete evaluation relation is a direct
    introduction rule for error-preserving query equivalence.  This avoids
    repeatedly rebuilding the success witnesses, ordered reflexivity, and
    error correspondence after a constructor-level normalization proof. *)
Lemma query_expr_outcome_equiv_of_eval_iff :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists outcome, eval_query env left outcome) ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    query_outcome_equiv env left right.
Proof.
intros env left right Houtputs Hleft Heval.
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- exact Hleft.
- destruct Hleft as [outcome Houtcome].
  exists outcome; now apply (proj1 (Heval outcome)).
- intros left_rows Hrows.
  exists left_rows; split.
  + now apply (proj1 (Heval (SqlSuccess left_rows))).
  + apply ordered_rows_equiv_refl.
- intros right_rows Hrows.
  exists right_rows; split.
  + now apply (proj2 (Heval (SqlSuccess right_rows))).
  + apply ordered_rows_equiv_refl.
- intro error; apply Heval.
Qed.

(** Global typed raw-outcome equivalence is the compositional interface used
    by query contexts.  Once either side is known to expose an outcome, it
    discharges the fixed-environment error-preserving equivalence directly. *)
Lemma query_expr_outcome_equiv_of_global_typed :
  forall env left right,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    (exists outcome, eval_query env left outcome) ->
    query_outcome_equiv env left right.
Proof.
intros env left right [Houtputs Heval] Houtcome.
apply query_expr_outcome_equiv_of_eval_iff; [exact Houtputs | exact Houtcome |].
exact (Heval env).
Qed.

(** Bag-closed equivalence can preserve exact SQL errors without proving both
    sides runtime-safe.  The possible successful bags and error categories are
    kept as separate premises so an error-only relation cannot be discharged
    vacuously. *)
Theorem query_bag_closed_outcome_equiv_of_success_bags :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    BagClosed T
      (fun rows => eval_query env first (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query env second (SqlSuccess rows)) ->
    (exists outcome, eval_query env first outcome) ->
    (exists outcome, eval_query env second outcome) ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    (forall error,
      eval_query env first (SqlError error) <->
      eval_query env second (SqlError error)) ->
    query_outcome_equiv env first second.
Proof.
intros env first second Houtputs Hfirst_closed Hsecond_closed
  Hfirst_outcome Hsecond_outcome Hbags Herrors.
apply (proj2
  (@query_bag_closed_typed_outcome_equiv_iff_possible_bag_equiv
    T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null
    env first second Hfirst_closed Hsecond_closed)).
split; [exact Houtputs |].
unfold query_possible_bag_outcome_equiv.
apply outcome_relation_equiv_intro.
- destruct Hfirst_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess (rows_bag T rows)); cbn.
    exists rows; split; [exact Houtcome | apply bag_eq_refl].
  + now exists (SqlError error).
- destruct Hsecond_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess (rows_bag T rows)); cbn.
    exists rows; split; [exact Houtcome | apply bag_eq_refl].
  + now exists (SqlError error).
- intros left_bag Hleft_bag.
  exists left_bag; split.
  + exact (proj1 (Hbags left_bag) Hleft_bag).
  + apply bag_eq_refl.
- intros right_bag Hright_bag.
  exists right_bag; split.
  + exact (proj2 (Hbags right_bag) Hright_bag).
  + apply bag_eq_refl.
- intro error; cbn; apply Herrors.
Qed.

(** Direct reset constructors provide the semantic closure premises
    automatically.  Other constructors may call the general theorem only
    when a separate conditional closure theorem applies. *)
Corollary query_bag_reset_outcome_equiv_of_success_bags :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_order_behavior first = BagReset ->
    query_expr_order_behavior second = BagReset ->
    (exists outcome, eval_query env first outcome) ->
    (exists outcome, eval_query env second outcome) ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    (forall error,
      eval_query env first (SqlError error) <->
      eval_query env second (SqlError error)) ->
    query_outcome_equiv env first second.
Proof.
intros env first second Houtputs Hfirst_reset Hsecond_reset
  Hfirst_outcome Hsecond_outcome Hbags Herrors.
apply query_bag_closed_outcome_equiv_of_success_bags; try assumption.
- now apply query_bag_reset_sound.
- now apply query_bag_reset_sound.
Qed.

(** Exact left-to-right error propagation for set operations.  A right-child
    error is observable only after the left child has produced a success. *)
Lemma eval_query_expr_set_error_iff :
  forall env operation left right error,
    eval_query env (QExpr_Set operation left right) (SqlError error) <->
    eval_query env left (SqlError error) \/
    exists left_rows,
      eval_query env left (SqlSuccess left_rows) /\
      eval_query env right (SqlError error).
Proof.
intros env operation left right error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hleft | [left_rows [Hleft Hright]]].
  + now apply EQuery_SetLeftError.
  + eapply EQuery_SetRightError; eassumption.
Qed.

(** CROSS JOIN has the same child-error schedule as other binary reset
    operators: the right child is reached only after a left success. *)
Lemma eval_query_expr_cross_join_error_iff :
  forall env left right error,
    eval_query env (QExpr_CrossJoin left right) (SqlError error) <->
    eval_query env left (SqlError error) \/
    exists left_rows,
      eval_query env left (SqlSuccess left_rows) /\
      eval_query env right (SqlError error).
Proof.
intros env left right error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hleft | [left_rows [Hleft Hright]]].
  + now apply EQuery_CrossJoinLeftError.
  + eapply EQuery_CrossJoinRightError; eassumption.
Qed.

(** Runtime safety composes through binary bag-reset operators without
    weakening their left-to-right error schedule. *)
Lemma query_expr_set_runtime_safe :
  forall env operation left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_Set operation left right).
Proof.
intros env operation left right Hleft Hright error Herror.
apply eval_query_expr_set_error_iff in Herror.
destruct Herror as [Herror | [left_rows [_ Herror]]].
- exact (Hleft error Herror).
- exact (Hright error Herror).
Qed.

Lemma query_expr_cross_join_runtime_safe :
  forall env left right,
    query_safe env left ->
    query_safe env right ->
    query_safe env (QExpr_CrossJoin left right).
Proof.
intros env left right Hleft Hright error Herror.
apply eval_query_expr_cross_join_error_iff in Herror.
destruct Herror as [Herror | [left_rows [_ Herror]]].
- exact (Hleft error Herror).
- exact (Hright error Herror).
Qed.

(** Successful child witnesses construct successful parent witnesses.  These
    lemmas preserve multiplicities through the authoritative finite-bag
    operators and choose only one legal ordered representative. *)
Lemma query_expr_set_has_success :
  forall env operation left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_Set operation left right).
Proof.
intros env operation left right [left_rows Hleft] [right_rows Hright].
exists
  (Febag.elements (Fecol.CBag (CTuple T))
    (query_set_bag_function operation left right
      (rows_bag T left_rows) (rows_bag T right_rows))).
eapply EQuery_SetSuccess; [exact Hleft | exact Hright |].
apply query_elements_same_rows_as_bag.
Qed.

Lemma query_expr_cross_join_has_success :
  forall env left right,
    query_has_success env left ->
    query_has_success env right ->
    query_has_success env (QExpr_CrossJoin left right).
Proof.
intros env left right [left_rows Hleft] [right_rows Hright].
exists
  (Febag.elements (Fecol.CBag (CTuple T))
    (query_cross_join_bag
      (rows_bag T left_rows) (rows_bag T right_rows))).
eapply EQuery_CrossJoinSuccess; [exact Hleft | exact Hright |].
apply query_elements_same_rows_as_bag.
Qed.

(** Inhabitation also composes when either child fails.  Error constructors
    are selected in the evaluator's exact left-to-right order. *)
Lemma query_expr_set_has_outcome :
  forall env operation left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_Set operation left right) outcome.
Proof.
intros env operation left right
  [[left_rows | left_error] Hleft]
  [[right_rows | right_error] Hright].
- exists
    (SqlSuccess
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_set_bag_function operation left right
          (rows_bag T left_rows) (rows_bag T right_rows)))).
  eapply EQuery_SetSuccess; [exact Hleft | exact Hright |].
  apply query_elements_same_rows_as_bag.
- exists (SqlError right_error); eapply EQuery_SetRightError; eassumption.
- exists (SqlError left_error); now apply EQuery_SetLeftError.
- exists (SqlError left_error); now apply EQuery_SetLeftError.
Qed.

Lemma query_expr_cross_join_has_outcome :
  forall env left right,
    (exists outcome, eval_query env left outcome) ->
    (exists outcome, eval_query env right outcome) ->
    exists outcome, eval_query env (QExpr_CrossJoin left right) outcome.
Proof.
intros env left right
  [[left_rows | left_error] Hleft]
  [[right_rows | right_error] Hright].
- exists
    (SqlSuccess
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_cross_join_bag
          (rows_bag T left_rows) (rows_bag T right_rows)))).
  eapply EQuery_CrossJoinSuccess; [exact Hleft | exact Hright |].
  apply query_elements_same_rows_as_bag.
- exists (SqlError right_error); eapply EQuery_CrossJoinRightError; eassumption.
- exists (SqlError left_error); now apply EQuery_CrossJoinLeftError.
- exists (SqlError left_error); now apply EQuery_CrossJoinLeftError.
Qed.

(** Fixed-environment child outcome equivalences compose through the
    order-insensitive set-operation reset.  Corresponding output sorts,
    parent inhabitation, possible success bags, and short-circuit errors are
    all derived from the two exact child relations. *)
Lemma query_expr_set_outcome_equiv_congr :
  forall env operation left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
Proof.
intros env operation left left' right right' Hleft Hright.
pose proof
  (query_expr_outcome_equiv_implies_success_bags Hleft)
  as Hleft_bags.
pose proof
  (query_expr_outcome_equiv_implies_success_bags Hright)
  as Hright_bags.
destruct Hleft as
  [Hleft_outputs
    [Hleft_source_outcome
      [Hleft_target_outcome
        [Hleft_forward [Hleft_backward Hleft_errors]]]]].
destruct Hright as
  [Hright_outputs
    [Hright_source_outcome
      [Hright_target_outcome
        [Hright_forward [Hright_backward Hright_errors]]]]].
apply query_bag_reset_outcome_equiv_of_success_bags.
- exact Hleft_outputs.
- reflexivity.
- reflexivity.
- destruct Hleft_source_outcome as [[left_rows | error] Hleft_outcome].
  + destruct Hright_source_outcome as [[right_rows | error] Hright_outcome].
    * exists
        (SqlSuccess
          (Febag.elements (Fecol.CBag (CTuple T))
            (query_set_bag_function operation left right
              (rows_bag T left_rows) (rows_bag T right_rows)))).
      eapply EQuery_SetSuccess.
      -- exact Hleft_outcome.
      -- exact Hright_outcome.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError error).
      eapply EQuery_SetRightError; eassumption.
  + exists (SqlError error).
    now apply EQuery_SetLeftError.
- destruct Hleft_target_outcome as [[left_rows | error] Hleft_outcome].
  + destruct Hright_target_outcome as [[right_rows | error] Hright_outcome].
    * exists
        (SqlSuccess
          (Febag.elements (Fecol.CBag (CTuple T))
            (query_set_bag_function operation left' right'
              (rows_bag T left_rows) (rows_bag T right_rows)))).
      eapply EQuery_SetSuccess.
      -- exact Hleft_outcome.
      -- exact Hright_outcome.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError error).
      eapply EQuery_SetRightError; eassumption.
  + exists (SqlError error).
    now apply EQuery_SetLeftError.
- apply query_set_success_bags_congr.
  + now apply query_expr_outputs_eq_sort_eq.
  + now apply query_expr_outputs_eq_sort_eq.
  + exact Hleft_bags.
  + exact Hright_bags.
- intro error; split; intro Heval.
  + apply eval_query_expr_set_error_iff in Heval.
    apply eval_query_expr_set_error_iff.
    destruct Heval as
      [Hleft_error | [left_rows [Hleft_success Hright_error]]].
    * left; now apply (proj1 (Hleft_errors error)).
    * right.
      destruct (Hleft_forward left_rows Hleft_success)
        as [target_left_rows [Htarget_left _]].
      exists target_left_rows; split; [exact Htarget_left |].
      now apply (proj1 (Hright_errors error)).
  + apply eval_query_expr_set_error_iff in Heval.
    apply eval_query_expr_set_error_iff.
    destruct Heval as
      [Hleft_error | [left_rows [Hleft_success Hright_error]]].
    * left; now apply (proj2 (Hleft_errors error)).
    * right.
      destruct (Hleft_backward left_rows Hleft_success)
        as [source_left_rows [Hsource_left _]].
      exists source_left_rows; split; [exact Hsource_left |].
      now apply (proj2 (Hright_errors error)).
Qed.

(** Fixed-environment child outcome equivalences also compose through CROSS
    JOIN's bag reset.  Exact appended output order and SQL error categories
    remain observable even though successful row order is reset. *)
Lemma query_expr_cross_join_outcome_equiv_congr :
  forall env left left' right right',
    query_outcome_equiv env left left' ->
    query_outcome_equiv env right right' ->
    query_outcome_equiv env
      (QExpr_CrossJoin left right)
      (QExpr_CrossJoin left' right').
Proof.
intros env left left' right right' Hleft Hright.
pose proof
  (query_expr_outcome_equiv_implies_success_bags Hleft)
  as Hleft_bags.
pose proof
  (query_expr_outcome_equiv_implies_success_bags Hright)
  as Hright_bags.
destruct Hleft as
  [Hleft_outputs
    [Hleft_source_outcome
      [Hleft_target_outcome
        [Hleft_forward [Hleft_backward Hleft_errors]]]]].
destruct Hright as
  [Hright_outputs
    [Hright_source_outcome
      [Hright_target_outcome
        [Hright_forward [Hright_backward Hright_errors]]]]].
apply query_bag_reset_outcome_equiv_of_success_bags.
- cbn [query_expr_outputs].
  now rewrite Hleft_outputs, Hright_outputs.
- reflexivity.
- reflexivity.
- destruct Hleft_source_outcome as [[left_rows | error] Hleft_outcome].
  + destruct Hright_source_outcome as [[right_rows | error] Hright_outcome].
    * exists
        (SqlSuccess
          (Febag.elements (Fecol.CBag (CTuple T))
            (query_cross_join_bag
              (rows_bag T left_rows) (rows_bag T right_rows)))).
      eapply EQuery_CrossJoinSuccess.
      -- exact Hleft_outcome.
      -- exact Hright_outcome.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError error).
      eapply EQuery_CrossJoinRightError; eassumption.
  + exists (SqlError error).
    now apply EQuery_CrossJoinLeftError.
- destruct Hleft_target_outcome as [[left_rows | error] Hleft_outcome].
  + destruct Hright_target_outcome as [[right_rows | error] Hright_outcome].
    * exists
        (SqlSuccess
          (Febag.elements (Fecol.CBag (CTuple T))
            (query_cross_join_bag
              (rows_bag T left_rows) (rows_bag T right_rows)))).
      eapply EQuery_CrossJoinSuccess.
      -- exact Hleft_outcome.
      -- exact Hright_outcome.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError error).
      eapply EQuery_CrossJoinRightError; eassumption.
  + exists (SqlError error).
    now apply EQuery_CrossJoinLeftError.
- apply query_cross_join_actual_success_bags_congr.
  + exact Hleft_bags.
  + exact Hright_bags.
- intro error; split; intro Heval.
  + apply eval_query_expr_cross_join_error_iff in Heval.
    apply eval_query_expr_cross_join_error_iff.
    destruct Heval as
      [Hleft_error | [left_rows [Hleft_success Hright_error]]].
    * left; now apply (proj1 (Hleft_errors error)).
    * right.
      destruct (Hleft_forward left_rows Hleft_success)
        as [target_left_rows [Htarget_left _]].
      exists target_left_rows; split; [exact Htarget_left |].
      now apply (proj1 (Hright_errors error)).
  + apply eval_query_expr_cross_join_error_iff in Heval.
    apply eval_query_expr_cross_join_error_iff.
    destruct Heval as
      [Hleft_error | [left_rows [Hleft_success Hright_error]]].
    * left; now apply (proj2 (Hleft_errors error)).
    * right.
      destruct (Hleft_backward left_rows Hleft_success)
        as [source_left_rows [Hsource_left _]].
      exists source_left_rows; split; [exact Hsource_left |].
      now apply (proj2 (Hright_errors error)).
Qed.

(** WHERE predicates need preserve only runtime errors and the TRUE/non-TRUE
    acceptance decision.  FALSE and UNKNOWN may differ without changing the
    filtered relation. *)
Lemma query_expr_filter_outcome_equiv_of_global_acceptance :
  forall env left_formula right_formula input,
    @formula_expr_global_filter_outcome_equiv T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null left_formula right_formula ->
    (exists outcome,
      eval_query env (QExpr_Filter left_formula input) outcome) ->
    query_outcome_equiv env
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input).
Proof.
intros env left_formula right_formula input Hformula Houtcome.
apply query_expr_outcome_equiv_of_global_typed; [|exact Houtcome].
apply query_expr_filter_global_typed_acceptance_congr.
- exact Hformula.
- apply query_expr_global_typed_outcome_equiv_refl.
Qed.

(** HAVING substitution additionally preserves aggregate-finalization
    observations, exactly as required by the grouping evaluator. *)
Lemma query_expr_group_outcome_equiv_of_global_having :
  forall env select_list group_terms left_having right_having input,
    @formula_expr_global_group_outcome_equiv T relname basesort instance
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null left_having right_having ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms left_having input) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms left_having input)
      (QExpr_Group select_list group_terms right_having input).
Proof.
intros env select_list group_terms left_having right_having input
  Hhaving Houtcome.
apply query_expr_outcome_equiv_of_global_typed; [|exact Houtcome].
apply query_expr_group_global_typed_congr.
- exact Hhaving.
- apply query_expr_global_typed_outcome_equiv_refl.
Qed.

(** An exact child outcome equivalence transports through an unchanged GROUP
    node at the raw evaluation-relation boundary.  Successful child lists may
    choose different representatives, so the grouped bag observation is
    transported through their semantic bag equality.  Child and group errors
    retain the evaluator's original scheduling. *)
Lemma eval_query_expr_group_outcome_iff_of_child_outcome_equiv :
  forall env select_list group_terms having left right,
    query_outcome_equiv env left right ->
    forall outcome,
      eval_query env
        (QExpr_Group select_list group_terms having left) outcome <->
      eval_query env
        (QExpr_Group select_list group_terms having right) outcome.
Proof.
intros env select_list group_terms having left right
  [_ [_ [_ [Hforward [Hbackward Herrors]]]]] outcome.
destruct outcome as [output | error].
- rewrite !eval_query_expr_group_success_iff.
  split.
  + intros [left_rows [output_bag [Hleft [Hgroup Houtput]]]].
    destruct (Hforward left_rows Hleft)
      as [right_rows [Hright Hrows]].
    exists right_rows, output_bag.
    split; [exact Hright |].
    split; [|exact Houtput].
    eapply eval_group_bag_outcome_input_transport.
    * exact (ordered_rows_equiv_implies_bag_eq Hrows).
    * exact Hgroup.
  + intros [right_rows [output_bag [Hright [Hgroup Houtput]]]].
    destruct (Hbackward right_rows Hright)
      as [left_rows [Hleft Hrows]].
    exists left_rows, output_bag.
    split; [exact Hleft |].
    split; [|exact Houtput].
    eapply eval_group_bag_outcome_input_transport.
    * exact (bag_eq_sym (ordered_rows_equiv_implies_bag_eq Hrows)).
    * exact Hgroup.
- rewrite !eval_query_expr_group_error_iff.
  split.
  + intros [Hchild_error | [left_rows [Hleft Hgroup]]].
    * left; now apply (proj1 (Herrors error)).
    * right.
      destruct (Hforward left_rows Hleft)
        as [right_rows [Hright Hrows]].
      exists right_rows; split; [exact Hright |].
      eapply eval_group_bag_outcome_input_transport.
      -- exact (ordered_rows_equiv_implies_bag_eq Hrows).
      -- exact Hgroup.
  + intros [Hchild_error | [right_rows [Hright Hgroup]]].
    * left; now apply (proj2 (Herrors error)).
    * right.
      destruct (Hbackward right_rows Hright)
        as [left_rows [Hleft Hrows]].
      exists left_rows; split; [exact Hleft |].
      eapply eval_group_bag_outcome_input_transport.
      -- exact (bag_eq_sym (ordered_rows_equiv_implies_bag_eq Hrows)).
      -- exact Hgroup.
Qed.

(** The raw relation transport above needs only one parent-outcome witness to
    recover the complete fixed-environment outcome equivalence.  In
    particular, the child equivalence supplies the corresponding right-parent
    witness; no separate right inhabitation premise is needed. *)
Lemma query_expr_group_outcome_equiv_congr :
  forall env select_list group_terms having left right,
    query_outcome_equiv env left right ->
    (exists outcome,
      eval_query env
        (QExpr_Group select_list group_terms having left) outcome) ->
    query_outcome_equiv env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
Proof.
intros env select_list group_terms having left right Hchild Houtcome.
apply query_expr_outcome_equiv_of_eval_iff.
- reflexivity.
- exact Houtcome.
- apply eval_query_expr_group_outcome_iff_of_child_outcome_equiv.
  exact Hchild.
Qed.

(** Error-preserving equivalence can be narrowed to the success-only
    interface only when success and safety are established explicitly. *)

Lemma query_expr_equiv_of_outcome_equiv_safe :
  forall env left right,
    query_outcome_equiv env left right ->
    query_safe env left ->
    query_safe env right ->
    query_has_success env left ->
    query_equiv env left right.
Proof.
intros env left right
  [Houtputs [_ [_ [Hforward [Hbackward _]]]]]
  Hleft_safe Hright_safe Hsuccess.
split; [exact Houtputs |].
unfold query_expr_observation_equiv, successful_relation_equiv.
split; [exact Hsuccess |].
split; [exact Hleft_safe |].
split; [exact Hright_safe |].
split; [exact Hforward | exact Hbackward].
Qed.

Lemma query_expr_equiv_sym :
  forall env left right,
    query_equiv env left right ->
    query_equiv env right left.
Proof.
intros env left right
  [Houtputs [Hsuccess [Hleft_safe [Hright_safe [Hforward Hbackward]]]]].
split; [now symmetry |].
unfold query_expr_observation_equiv, successful_relation_equiv.
split.
- destruct Hsuccess as [left_rows Hleft].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright _]].
  now exists right_rows.
- split; [exact Hright_safe |].
  split; [exact Hleft_safe |].
  split.
  + intros right_rows Hright.
    destruct (Hbackward right_rows Hright)
      as [left_rows [Hleft Hrows]].
    exists left_rows; split; [exact Hleft |].
    now apply ordered_rows_equiv_sym.
  + intros left_rows Hleft.
    destruct (Hforward left_rows Hleft)
      as [right_rows [Hright Hrows]].
    exists right_rows; split; [exact Hright |].
    now apply ordered_rows_equiv_sym.
Qed.

Lemma query_expr_equiv_trans :
  forall env first second third,
    query_equiv env first second ->
    query_equiv env second third ->
    query_equiv env first third.
Proof.
intros env first second third
  [Hfirst_outputs
    [Hsuccess [Hfirst_safe [Hsecond_safe [Hfirst_forward Hfirst_backward]]]]]
  [Hsecond_outputs
    [_ [_ [Hthird_safe [Hsecond_forward Hsecond_backward]]]]].
split; [now transitivity (query_expr_outputs second) |].
unfold query_expr_observation_equiv, successful_relation_equiv.
split; [exact Hsuccess |].
split; [exact Hfirst_safe |].
split; [exact Hthird_safe |].
split.
- intros first_rows Hfirst.
  destruct (Hfirst_forward first_rows Hfirst)
    as [second_rows [Hsecond Hfirst_rows]].
  destruct (Hsecond_forward second_rows Hsecond)
    as [third_rows [Hthird Hsecond_rows]].
  exists third_rows; split; [exact Hthird |].
  eapply ordered_rows_equiv_trans;
    [exact Hfirst_rows | exact Hsecond_rows].
- intros third_rows Hthird.
  destruct (Hsecond_backward third_rows Hthird)
    as [second_rows [Hsecond Hsecond_rows]].
  destruct (Hfirst_backward second_rows Hsecond)
    as [first_rows [Hfirst Hfirst_rows]].
  exists first_rows; split; [exact Hfirst |].
  eapply ordered_rows_equiv_trans;
    [exact Hfirst_rows | exact Hsecond_rows].
Qed.

Lemma query_expr_outcome_equiv_sym :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env right left.
Proof.
intros env left right
  [Houtputs [Hleft [Hright [Hforward [Hbackward Herrors]]]]].
split; [now symmetry |].
unfold query_expr_outcome_observation_equiv, outcome_relation_equiv.
split; [exact Hright |].
split; [exact Hleft |].
split.
- intros right_rows Hright_rows.
  destruct (Hbackward right_rows Hright_rows)
    as [left_rows [Hleft_rows Hrows]].
  exists left_rows; split; [exact Hleft_rows |].
  now apply ordered_rows_equiv_sym.
- split.
  + intros left_rows Hleft_rows.
    destruct (Hforward left_rows Hleft_rows)
      as [right_rows [Hright_rows Hrows]].
    exists right_rows; split; [exact Hright_rows |].
    now apply ordered_rows_equiv_sym.
  + intro error; symmetry; apply Herrors.
Qed.

Lemma query_expr_outcome_equiv_trans :
  forall env first second third,
    query_outcome_equiv env first second ->
    query_outcome_equiv env second third ->
    query_outcome_equiv env first third.
Proof.
intros env first second third
  [Hfirst_outputs
    [Hfirst_outcome [_ [Hfirst_forward [Hfirst_backward Hfirst_errors]]]]]
  [Hsecond_outputs
    [_ [Hthird_outcome [Hsecond_forward [Hsecond_backward Hsecond_errors]]]]].
split; [now transitivity (query_expr_outputs second) |].
unfold query_expr_outcome_observation_equiv, outcome_relation_equiv.
split; [exact Hfirst_outcome |].
split; [exact Hthird_outcome |].
split.
- intros first_rows Hfirst.
  destruct (Hfirst_forward first_rows Hfirst)
    as [second_rows [Hsecond Hfirst_rows]].
  destruct (Hsecond_forward second_rows Hsecond)
    as [third_rows [Hthird Hsecond_rows]].
  exists third_rows; split; [exact Hthird |].
  eapply ordered_rows_equiv_trans;
    [exact Hfirst_rows | exact Hsecond_rows].
- split.
  + intros third_rows Hthird.
    destruct (Hsecond_backward third_rows Hthird)
      as [second_rows [Hsecond Hsecond_rows]].
    destruct (Hfirst_backward second_rows Hsecond)
      as [first_rows [Hfirst Hfirst_rows]].
    exists first_rows; split; [exact Hfirst |].
    eapply ordered_rows_equiv_trans;
      [exact Hfirst_rows | exact Hsecond_rows].
  + intro error.
    destruct (Hfirst_errors error) as [Hfirst_error Hfirst_error_back].
    destruct (Hsecond_errors error) as [Hsecond_error Hsecond_error_back].
    split.
    * intro H; apply Hsecond_error, Hfirst_error, H.
    * intro H; apply Hfirst_error_back, Hsecond_error_back, H.
Qed.

(** Raw global equivalence is reusable in either direction and composes before
    or after substitution into any typed query context. *)

Lemma query_expr_global_outcome_equiv_sym :
  forall left right,
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null left right ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null right left.
Proof.
intros left right Hequiv env outcome.
destruct (Hequiv env outcome) as [Hforward Hbackward].
split; [exact Hbackward | exact Hforward].
Qed.

Lemma query_expr_global_outcome_equiv_trans :
  forall first second third,
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null first second ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null second third ->
    query_expr_global_outcome_equiv basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null first third.
Proof.
intros first second third Hfirst Hsecond env outcome.
destruct (Hfirst env outcome) as [Hfirst_forward Hfirst_backward].
destruct (Hsecond env outcome) as [Hsecond_forward Hsecond_backward].
split.
- intro H; apply Hsecond_forward, Hfirst_forward, H.
- intro H; apply Hfirst_backward, Hsecond_backward, H.
Qed.

Lemma query_expr_global_typed_outcome_equiv_sym :
  forall left right,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null left right ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null right left.
Proof.
intros left right [Houtputs Hequiv].
split; [now symmetry |].
now apply query_expr_global_outcome_equiv_sym.
Qed.

Lemma query_expr_global_typed_outcome_equiv_trans :
  forall first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null first third.
Proof.
intros first second third [Hfirst_outputs Hfirst] [Hsecond_outputs Hsecond].
split; [now transitivity (query_expr_outputs second) |].
eapply query_expr_global_outcome_equiv_trans;
  [exact Hfirst | exact Hsecond].
Qed.

Lemma query_expr_context_global_equiv_chain :
  forall context first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      symbol_runtime_error aggregate_runtime_error
      value_is_null
      (plug_query_expr_context context first)
      (plug_query_expr_context context third).
Proof.
intros context first second third Hfirst Hsecond.
eapply query_expr_global_typed_outcome_equiv_trans with
  (second := plug_query_expr_context context second).
- now apply query_expr_context_global_congr.
- now apply query_expr_context_global_congr.
Qed.

(** Exact inversion rules for the order-preserving projection and selection
    nodes complement the reset-node inversion rules in SqlQueryFacts. *)

Lemma eval_query_expr_project_success_iff :
  forall env select_list input output,
    eval_query env (QExpr_Project select_list input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list input_rows = SqlSuccess output.
Proof.
intros env select_list input output; split; intro Heval.
- inversion Heval; subst.
  exists input_rows; split; [assumption | reflexivity].
- destruct Heval as [input_rows [Hinput Hproject]].
  rewrite <- Hproject.
  now apply EQuery_ProjectRows.
Qed.

Lemma eval_query_expr_project_error_iff :
  forall env select_list input error,
    eval_query env (QExpr_Project select_list input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list input_rows = SqlError error.
Proof.
intros env select_list input error; split; intro Heval.
- inversion Heval; subst.
  + left; assumption.
  + right; exists input_rows; split; [assumption | reflexivity].
- destruct Heval as [Hchild | [input_rows [Hinput Hproject]]].
  + now apply EQuery_ProjectChildError.
  + rewrite <- Hproject.
    now apply EQuery_ProjectRows.
Qed.

Lemma eval_query_expr_filter_success_iff :
  forall env formula input output,
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) <->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlSuccess output).
Proof.
intros env formula input output; split; intro Heval.
- inversion Heval; subst.
  exists input_rows; split; assumption.
- destruct Heval as [input_rows [Hinput Hfilter]].
  eapply EQuery_FilterRows; [exact Hinput | exact Hfilter].
Qed.

(** Lift the accepted-row property rule through a successful [QExpr_Filter]
    observation.  This is the bridge from formula semantics to row facts used
    by later projections. *)
Lemma eval_query_expr_filter_success_Forall_accepted :
  forall env formula input output (property : tuple T -> Prop),
    (forall input_rows row truth,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row) formula (SqlSuccess truth) ->
      Bool.is_true (B T) truth = true ->
      property row) ->
    eval_query env (QExpr_Filter formula input) (SqlSuccess output) ->
    Forall property output.
Proof.
intros env formula input output property Hproperty Houtput.
apply eval_query_expr_filter_success_iff in Houtput.
destruct Houtput as [input_rows [Hinput Hfilter]].
eapply filter_rows_success_Forall_accepted; [|exact Hfilter].
intros row truth Hin Hformula Htrue.
exact (Hproperty input_rows row truth Hinput Hin Hformula Htrue).
Qed.

(** Successful projection transports a polymorphic row property through its
    pointwise projection map.  No global SELECT-list safety premise is needed:
    the successful parent observation already certifies every reached row. *)
Lemma query_expr_project_success_Forall :
  forall env select_list input
      (input_property output_property : tuple T -> Prop),
    query_success_Forall env input input_property ->
    (forall row,
      input_property row ->
      output_property
        (projection T (env_t T env row) (@Select_List T select_list))) ->
    query_success_Forall env
      (QExpr_Project select_list input) output_property.
Proof.
intros env select_list input input_property output_property
  Hinput Hprojection output Houtput.
apply eval_query_expr_project_success_iff in Houtput.
destruct Houtput as [input_rows [Hrows Hproject]].
eapply project_rows_success_Forall.
- exact (Hinput input_rows Hrows).
- exact Hprojection.
- exact Hproject.
Qed.

(** Filtering preserves every property already known for all successful child
    rows.  This is an exact-list boundary, so no semantic-properness premise is
    necessary: the filter can only retain the original row occurrences. *)
Lemma query_expr_filter_success_Forall :
  forall env formula input (property : tuple T -> Prop),
    query_success_Forall env input property ->
    query_success_Forall env (QExpr_Filter formula input) property.
Proof.
intros env formula input property Hinput output Houtput.
apply eval_query_expr_filter_success_iff in Houtput.
destruct Houtput as [input_rows [Hrows Hfilter]].
eapply filter_rows_success_Forall;
  [exact Hfilter | exact (Hinput input_rows Hrows)].
Qed.

(** UNORDERED may choose any concrete representative of the child's bag.
    Hence the property must respect semantic tuple equality; the underlying
    [query_same_rows_as_bag] witnesses preserve every duplicate occurrence. *)
Lemma query_expr_unordered_success_Forall :
  forall env input (property : tuple T -> Prop),
    tuple_property_semantic_invariant property ->
    query_success_Forall env input property ->
    query_success_Forall env (QExpr_Unordered input) property.
Proof.
intros env input property Hproper Hinput output Houtput.
apply eval_query_expr_unordered_success_iff in Houtput.
destruct Houtput as [input_rows [Hrows Hbag]].
eapply query_same_rows_as_bag_Forall_transport.
- exact Hproper.
- apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl.
- exact Hbag.
- exact (Hinput input_rows Hrows).
Qed.

(** UNION ALL combines the complete multiplicities of both successful child
    observations.  The explicit sort premise rules out FormalSQL's
    ill-sorted empty-bag branch; semantic properness permits the evaluator to
    choose any representative of the resulting union bag. *)
Lemma query_expr_union_success_Forall :
  forall env left right (property : tuple T -> Prop),
    query_expr_sort left =S= query_expr_sort right ->
    tuple_property_semantic_invariant property ->
    query_success_Forall env left property ->
    query_success_Forall env right property ->
    query_success_Forall env (QExpr_Set Union left right) property.
Proof.
intros env left right property Hsort Hproper Hleft Hright output Houtput.
apply eval_query_expr_set_success_iff in Houtput.
destruct Houtput as
  [left_rows [right_rows [Hleft_rows [Hright_rows Houtput]]]].
assert (Hrepresentative :
  query_same_rows_as_bag (left_rows ++ right_rows)
    (query_set_bag_function Union left right
      (rows_bag T left_rows) (rows_bag T right_rows))).
{
  unfold query_set_bag_function; rewrite Hsort.
  apply query_same_rows_as_bag_iff_occurrences; intro row.
  rewrite Oeset.nb_occ_app.
  unfold query_set_bag, Febag.interp_set_op; cbn.
  rewrite Febag.nb_occ_union, 2 rows_bag_occ; reflexivity.
}
eapply query_same_rows_as_bag_Forall_transport.
- exact Hproper.
- exact Hrepresentative.
- exact Houtput.
- rewrite Forall_app; split.
  + exact (Hleft left_rows Hleft_rows).
  + exact (Hright right_rows Hright_rows).
Qed.

(** CROSS JOIN resets order after constructing its pure finite-bag result.
    Callers provide the polymorphic property for the canonical representative
    of that pure cross bag; this lemma performs only the generic evaluator and
    semantic-representative transport, without encoding any particular joined
    attribute or rewrite pattern. *)
Lemma query_expr_cross_join_success_Forall :
  forall env left right (property : tuple T -> Prop),
    tuple_property_semantic_invariant property ->
    (forall left_rows right_rows,
      eval_query env left (SqlSuccess left_rows) ->
      eval_query env right (SqlSuccess right_rows) ->
      Forall property
        (Febag.elements (Fecol.CBag (CTuple T))
          (query_cross_join_bag
            (rows_bag T left_rows) (rows_bag T right_rows)))) ->
    query_success_Forall env (QExpr_CrossJoin left right) property.
Proof.
intros env left right property Hproper Hcross output Houtput.
apply eval_query_expr_cross_join_success_iff in Houtput.
destruct Houtput as
  [left_rows [right_rows [Hleft_rows [Hright_rows Houtput]]]].
eapply query_same_rows_as_bag_Forall_transport.
- exact Hproper.
- apply query_elements_same_rows_as_bag.
- exact Houtput.
- exact (Hcross left_rows right_rows Hleft_rows Hright_rows).
Qed.

Lemma eval_query_expr_filter_error_iff :
  forall env formula input error,
    eval_query env (QExpr_Filter formula input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlError error).
Proof.
intros env formula input error; split; intro Heval.
- inversion Heval; subst.
  + left; assumption.
  + right; exists input_rows; split; assumption.
- destruct Heval as [Hchild | [input_rows [Hinput Hfilter]]].
  + now apply EQuery_FilterChildError.
  + eapply EQuery_FilterRows; [exact Hinput | exact Hfilter].
Qed.

(** Filtering a finite row list is inhabited whenever evaluating the formula
    is inhabited on every row that can be reached.  A head formula error is
    returned immediately; successful heads retain the exact tail outcome, so
    this theorem neither assumes safety nor replaces [SqlError] by an empty
    result. *)
Lemma eval_filter_rows_has_outcome_of_formula_total :
  forall env formula rows,
    (forall row,
      In row rows ->
      exists outcome,
        @eval_formula_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          (env_t T env row) formula outcome) ->
    exists outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env formula rows outcome.
Proof.
intros env formula rows Htotal.
induction rows as [|row rows IH].
- exists (SqlSuccess nil); constructor.
- destruct (Htotal row (or_introl eq_refl)) as
    [[truth | error] Hhead].
  + destruct IH as [tail Htail].
    { intros other Hother; apply Htotal; now right. }
    exists (@filter_cons_outcome T truth row tail).
    eapply EFilterRows_Cons; eassumption.
  + exists (SqlError error); now apply EFilterRows_HeadError.
Qed.

(** Query-level wrapper for the preceding list traversal.  The child error
    branch is propagated without demanding formula evaluation; formula
    totality is required only for rows of an actual successful child
    observation. *)
Lemma query_expr_filter_has_outcome_of_formula_total :
  forall env formula input,
    (forall input_rows,
      eval_query env input (SqlSuccess input_rows) ->
      forall row,
        In row input_rows ->
        exists outcome,
          @eval_formula_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            (env_t T env row) formula outcome) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Filter formula input) outcome.
Proof.
intros env formula input Htotal [[rows | error] Hinput].
- destruct
  (eval_filter_rows_has_outcome_of_formula_total
      (env := env) (formula := formula) rows
      (Htotal rows Hinput)) as [outcome Hfilter].
  exists outcome; eapply EQuery_FilterRows; eassumption.
- exists (SqlError error); now apply EQuery_FilterChildError.
Qed.

(** Exact formula-acceptance contracts expose a filter as finite-bag
    filtering without choosing a privileged child-list representative.  The
    predicate properness premise is necessary because successful bags are
    quotiented by semantic tuple equality rather than Leibniz equality. *)
Theorem query_filter_success_bags_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    rel_equiv
      (success_bags env (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
Proof.
intros env formula input keep Hproper Hexact output; split.
- intros [output_rows [Houtput Houtput_bag]].
  apply eval_query_expr_filter_success_iff in Houtput.
  destruct Houtput as [input_rows [Hinput Hfilter]].
  pose proof
    (proj1
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows keep
        (fun row _ => Hexact row) (SqlSuccess output_rows)) Hfilter)
    as Heq.
  inversion Heq; subst output_rows.
  exists (rows_bag T input_rows); split.
  + exists input_rows; split; [exact Hinput | apply bag_eq_refl].
  + pose proof
      (@query_same_rows_as_bag_filter T keep input_rows
        (rows_bag T input_rows) Hproper) as Hfiltered.
    assert (Hself :
      query_same_rows_as_bag input_rows (rows_bag T input_rows)).
    { apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl. }
    specialize (Hfiltered Hself).
    apply query_same_rows_as_bag_iff_bag_eq in Hfiltered.
    eapply bag_eq_trans;
      [apply bag_eq_sym; exact Hfiltered | exact Houtput_bag].
- intros [input_bag [[input_rows [Hinput Hinput_bag]] Houtput_bag]].
  exists (List.filter keep input_rows); split.
  + apply eval_query_expr_filter_success_iff.
    exists input_rows; split; [exact Hinput |].
    apply
      (proj2
        (@eval_filter_rows_acceptance_exact T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env formula input_rows keep
          (fun row _ => Hexact row)
          (SqlSuccess (List.filter keep input_rows)))).
    reflexivity.
  + assert (Hsame : query_same_rows_as_bag input_rows input_bag).
    { apply query_same_rows_as_bag_iff_bag_eq; exact Hinput_bag. }
    pose proof
      (@query_same_rows_as_bag_filter T keep input_rows input_bag
        Hproper Hsame) as Hfiltered.
    apply query_same_rows_as_bag_iff_bag_eq in Hfiltered.
    eapply bag_eq_trans; [exact Hfiltered | exact Houtput_bag].
Qed.

(** If every row of every successful child observation has an exact
    acceptance contract, filtering introduces no SQL runtime-error category.
    Child errors are still propagated unchanged. *)
Theorem query_filter_error_iff_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall input_rows row,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros env formula input keep Hexact error.
rewrite eval_query_expr_filter_error_iff.
split.
- intros [Hchild | [input_rows [Hinput Hlocal]]]; [exact Hchild |].
  pose proof
    (proj1
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows keep
        (fun row Hin => Hexact input_rows row Hinput Hin)
        (SqlError error)) Hlocal) as Habsurd.
  discriminate Habsurd.
- intro Hchild; now left.
Qed.

(** A total exact acceptance contract turns every successful child
    observation into a successful filter observation.  Keeping the child
    success premise explicit makes this constructor usable without assuming
    global query inhabitation or runtime safety. *)
Lemma query_expr_filter_has_success_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    query_has_success env input ->
    query_has_success env (QExpr_Filter formula input).
Proof.
intros env formula input keep Hexact [rows Hrows].
exists (List.filter keep rows).
apply eval_query_expr_filter_success_iff.
exists rows; split; [exact Hrows |].
apply
  (proj2
    (@eval_filter_rows_acceptance_exact T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env formula rows keep (fun row _ => Hexact row)
      (SqlSuccess (List.filter keep rows)))).
reflexivity.
Qed.

(** Exact proper filtering preserves functionality of possible successful
    bags.  The properness premise is stated independently because finite bags
    quotient rows by [OTuple] equality, while [keep] is an ordinary Rocq
    function. *)
Theorem query_filter_success_bags_functional_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Filter formula input) first ->
      success_bags env (QExpr_Filter formula input) second ->
      bag_eq T first second.
Proof.
intros env formula input keep Hproper Hexact Hfunctional
  first second Hfirst Hsecond.
pose proof
  (proj1
    (@query_filter_success_bags_exact
      env formula input keep Hproper Hexact first) Hfirst)
  as [first_input [Hfirst_input Hfirst_filter]].
pose proof
  (proj1
    (@query_filter_success_bags_exact
      env formula input keep Hproper Hexact second) Hsecond)
  as [second_input [Hsecond_input Hsecond_filter]].
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst_filter |].
eapply bag_eq_trans.
- apply bag_filter_congr_on_support.
  + exact (Hfunctional first_input second_input
      Hfirst_input Hsecond_input).
  + intros left right _ Hequal; exact (Hproper left right Hequal).
- exact Hsecond_filter.
Qed.

(** Pointwise filtering preserves ordered SQL row equality when its decision
    depends only on the visible tuple. *)
Lemma ordered_rows_equiv_filter :
  forall (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    forall left right,
      ordered_rows_equiv T left right ->
      ordered_rows_equiv T
        (List.filter keep left) (List.filter keep right).
Proof.
intros keep Hproper left.
induction left as [|left_row left_rows IH];
  intros [|right_row right_rows] Hequiv;
  unfold ordered_rows_equiv, mk_oelists in *; cbn in *;
  try discriminate; try reflexivity.
case_eq (Oeset.compare (OTuple T) left_row right_row);
  intro Hrow; rewrite Hrow in Hequiv; try discriminate.
pose proof (Hproper left_row right_row Hrow) as Hkeep.
destruct (keep left_row) eqn:Hleft;
destruct (keep right_row) eqn:Hright;
  try discriminate Hkeep; cbn.
- rewrite Hrow.
  now apply IH.
- now apply IH.
Qed.

(** Exact proper filtering preserves bag closure.  Closure is stated at the
    SQL observation boundary: a requested representative is recovered by an
    actually evaluated list that is [ordered_rows_equiv], rather than by
    forcing the evaluator to construct the same hidden tuple representation. *)
Theorem query_expr_filter_bag_closed_exact :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_acceptance_exact_at
        basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null
        (env_t T env row) formula (keep row)) ->
    BagClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_Filter formula input) (SqlSuccess rows)).
Proof.
intros env formula input keep Hproper Hexact Hclosed desired Hpossible.
unfold alpha in Hpossible.
destruct Hpossible as [observed [Hobserved Hobserved_bag]].
apply eval_query_expr_filter_success_iff in Hobserved.
destruct Hobserved as [input_rows [Hinput Hfilter]].
pose proof
  (proj1
    (@eval_filter_rows_acceptance_exact T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env formula input_rows keep
      (fun row _ => Hexact row) (SqlSuccess observed)) Hfilter)
  as Hobserved_exact.
injection Hobserved_exact as Hobserved_rows.
rewrite Hobserved_rows in Hobserved_bag.
assert (Hself : query_same_rows_as_bag input_rows
  (rows_bag T input_rows)).
{ apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl. }
pose proof
  (@query_same_rows_as_bag_filter T keep input_rows
    (rows_bag T input_rows) Hproper Hself) as Hfiltered.
assert (Hdesired : query_same_rows_as_bag desired
  (Febag.filter (Fecol.CBag (CTuple T)) keep
    (rows_bag T input_rows))).
{
  apply query_same_rows_as_bag_iff_bag_eq.
  apply query_same_rows_as_bag_iff_bag_eq in Hfiltered.
  eapply (@bag_eq_trans T
    (rows_bag T desired)
    (rows_bag T (List.filter keep input_rows))).
  - exact (@bag_eq_sym T _ _ Hobserved_bag).
  - exact Hfiltered.
}
destruct
  (@query_same_rows_as_filtered_bag_preimage T desired
    (rows_bag T input_rows) keep Hproper Hdesired)
  as [desired_input [Hdesired_input Hdesired_filter]].
apply query_same_rows_as_bag_iff_bag_eq in Hdesired_input.
assert (Hinput_possible :
  alpha T
    (fun rows => eval_query env input (SqlSuccess rows))
    (rows_bag T desired_input)).
{
  unfold alpha.
  exists input_rows; split; [exact Hinput |].
  now apply bag_eq_sym.
}
destruct (Hclosed desired_input Hinput_possible)
  as [actual_input [Hactual_input Hinput_ordered]].
exists (List.filter keep actual_input); split.
- apply eval_query_expr_filter_success_iff.
  exists actual_input; split; [exact Hactual_input |].
  apply
    (proj2
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula actual_input keep
        (fun row _ => Hexact row)
        (SqlSuccess (List.filter keep actual_input)))).
  reflexivity.
- rewrite <- Hdesired_filter.
  now apply ordered_rows_equiv_filter.
Qed.

(** Bag-reset/window error inversions retain the exact child or local
    runtime-error source.  In particular, rank embedding failure is the
    modeled numeric range error; window item errors retain their SQL error
    category and legal shared peer ordering. *)

Lemma eval_query_expr_distinct_error_iff :
  forall env input error,
    eval_query env (QExpr_Distinct input) (SqlError error) <->
    eval_query env input (SqlError error).
Proof.
intros env input error; split; intro Heval.
- inversion Heval; subst; assumption.
- now apply EQuery_DistinctChildError.
Qed.

(** DISTINCT is raw-outcome inert at a reset boundary when duplicate
    elimination leaves every possible child bag unchanged.  The reset
    transport is used directly; ordinary [BagClosed] deliberately promises
    only an observationally equivalent representative and is not strong
    enough for this exact context-congruence result. *)
Theorem query_expr_distinct_global_typed_inert_reset :
  forall input,
    query_expr_order_behavior input = BagReset ->
    (forall env bag,
      query_success_bags basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null
        env input bag ->
      bag_eq T (query_distinct_bag bag) bag) ->
    query_global_typed_outcome_equiv (QExpr_Distinct input) input.
Proof.
intros input Hreset Hinert.
split; [reflexivity |].
intros env [rows | error].
- split; intro Heval.
  + apply eval_query_expr_distinct_success_iff in Heval.
    destruct Heval as [input_rows [Hinput Hrows]].
    apply query_same_rows_as_bag_iff_bag_eq in Hrows.
    assert (Hbags : bag_eq T
      (rows_bag T input_rows) (rows_bag T rows)).
    {
      apply bag_eq_sym.
      eapply bag_eq_trans; [exact Hrows |].
      apply (Hinert env (rows_bag T input_rows)).
      unfold query_success_bags, alpha.
      exists input_rows; split; [exact Hinput | apply bag_eq_refl].
    }
    eapply query_bag_reset_success_transport; eassumption.
  + apply eval_query_expr_distinct_success_iff.
    exists rows; split; [exact Heval |].
    apply query_same_rows_as_bag_iff_bag_eq.
    apply bag_eq_sym.
    apply (Hinert env (rows_bag T rows)).
    unfold query_success_bags, alpha.
    exists rows; split; [exact Heval | apply bag_eq_refl].
- apply eval_query_expr_distinct_error_iff.
Qed.

Lemma eval_query_expr_rank_error_iff :
  forall env partition_keys order_keys rank_attribute rank_value input error,
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlError error) <->
    eval_query env input (SqlError error) \/
    (error = DataException NumericValueOutOfRange /\
     exists input_rows,
       eval_query env input (SqlSuccess input_rows) /\
       @query_rank_rows_outcome T value_is_null
         partition_keys order_keys rank_attribute rank_value
         (query_rank_bag_rows (query_rows_bag input_rows))
         (query_rank_bag_rows (query_rows_bag input_rows)) = None).
Proof.
intros env partition_keys order_keys rank_attribute rank_value input error.
split; intro Heval.
- inversion Heval; subst.
  + left; assumption.
  + right; split; [reflexivity |].
    exists input_rows; split; assumption.
- destruct Heval as [Hchild | [-> [input_rows [Hinput Hrank]]]].
  + now apply EQuery_RankChildError.
  + eapply EQuery_RankValueError; eassumption.
Qed.

Lemma eval_query_expr_window_error_iff :
  forall env partition_keys order_keys items input error,
    eval_query env
      (QExpr_Window partition_keys order_keys items input)
      (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows ordered_input,
      eval_query env input (SqlSuccess input_rows) /\
      order_by_rows value_is_null (partition_keys ++ order_keys)
        (query_rank_bag_rows (query_rows_bag input_rows)) ordered_input /\
      @query_window_rows_outcome T symbol_runtime_error
        aggregate_runtime_error value_is_null env partition_keys items
        None 0 nil ordered_input = Some (SqlError error).
Proof.
intros env partition_keys order_keys items input error; split; intro Heval.
- inversion Heval; subst; eauto 8.
- destruct Heval as
    [Hchild |
     [input_rows [ordered_input [Hinput [Horder Hwindow]]]]].
  + now apply EQuery_WindowChildError.
  + eapply EQuery_WindowRowsError with
      (input_rows := input_rows) (ordered_rows := ordered_input);
      eassumption.
Qed.

(** OFFSET and FETCH are exact deterministic list slices.  These laws retain
    runtime errors and therefore hold before any safety assumption. *)

Lemma eval_query_expr_offset_zero_iff :
  forall env input outcome,
    eval_query env (QExpr_Offset 0 input) outcome <->
    eval_query env input outcome.
Proof.
intros env input [output | error].
- split; intro Heval.
  + apply eval_query_expr_offset_success_iff in Heval.
    destruct Heval as [input_rows [Hinput Houtput]].
    cbn in Houtput; now subst output.
  + apply eval_query_expr_offset_success_iff.
    exists output; split; [exact Heval | reflexivity].
- apply eval_query_expr_offset_error_iff.
Qed.

Lemma eval_query_expr_fetch_zero_success_iff :
  forall env input output,
    eval_query env (QExpr_Fetch 0 input) (SqlSuccess output) <->
    output = nil /\ query_has_success env input.
Proof.
intros env input output; split; intro Heval.
- apply eval_query_expr_fetch_success_iff in Heval.
  destruct Heval as [input_rows [Hinput Houtput]].
  split; [exact Houtput | now exists input_rows].
- destruct Heval as [-> [input_rows Hinput]].
  apply eval_query_expr_fetch_success_iff.
  exists input_rows; split; [exact Hinput | reflexivity].
Qed.

(** Under safety and success-inhabitation, FETCH 0 erases every semantic
    distinction between equal-typed children.  Safety is essential because
    child errors are still observable before the slice is applied. *)
Theorem query_expr_fetch_zero_annihilator_outcome_equiv_safe :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_safe env left ->
    query_safe env right ->
    query_has_success env left ->
    query_has_success env right ->
    query_outcome_equiv env
      (QExpr_Fetch 0 left) (QExpr_Fetch 0 right).
Proof.
intros env left right Houtputs Hleft_safe Hright_safe
  [left_rows Hleft_success] [right_rows Hright_success].
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- exists (SqlSuccess nil).
  now apply EQuery_FetchSuccess with (input_rows := left_rows).
- exists (SqlSuccess nil).
  now apply EQuery_FetchSuccess with (input_rows := right_rows).
- intros output Houtput.
  apply eval_query_expr_fetch_zero_success_iff in Houtput.
  destruct Houtput as [-> _].
  exists nil; split.
  + now apply EQuery_FetchSuccess with (input_rows := right_rows).
  + apply ordered_rows_equiv_refl.
- intros output Houtput.
  apply eval_query_expr_fetch_zero_success_iff in Houtput.
  destruct Houtput as [-> _].
  exists nil; split.
  + now apply EQuery_FetchSuccess with (input_rows := left_rows).
  + apply ordered_rows_equiv_refl.
- intro error; rewrite 2 eval_query_expr_fetch_error_iff.
  split; intro Herror.
  + exfalso; now apply (Hleft_safe error).
  + exfalso; now apply (Hright_safe error).
Qed.

Lemma eval_query_expr_offset_offset_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Offset outer (QExpr_Offset inner input)) outcome <->
    eval_query env (QExpr_Offset (outer + inner) input) outcome.
Proof.
intros env outer inner input [output | error].
- split; intro Heval.
  + apply eval_query_expr_offset_success_iff in Heval.
    destruct Heval as [middle [Hmiddle Houtput]].
    apply eval_query_expr_offset_success_iff in Hmiddle.
    destruct Hmiddle as [input_rows [Hinput Hmiddle]].
    apply eval_query_expr_offset_success_iff.
    exists input_rows; split; [exact Hinput |].
    subst middle output; apply skipn_skipn.
  + apply eval_query_expr_offset_success_iff in Heval.
    destruct Heval as [input_rows [Hinput Houtput]].
    apply eval_query_expr_offset_success_iff.
    exists (skipn inner input_rows); split.
    * apply eval_query_expr_offset_success_iff.
      exists input_rows; split; [exact Hinput | reflexivity].
    * subst output; symmetry; apply skipn_skipn.
- split; intro Heval.
  + apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_offset_error_iff; exact Heval.
  + apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_offset_error_iff.
    apply eval_query_expr_offset_error_iff; exact Heval.
Qed.

Lemma eval_query_expr_fetch_fetch_iff :
  forall env outer inner input outcome,
    eval_query env (QExpr_Fetch outer (QExpr_Fetch inner input)) outcome <->
    eval_query env (QExpr_Fetch (Nat.min outer inner) input) outcome.
Proof.
intros env outer inner input [output | error].
- split; intro Heval.
  + apply eval_query_expr_fetch_success_iff in Heval.
    destruct Heval as [middle [Hmiddle Houtput]].
    apply eval_query_expr_fetch_success_iff in Hmiddle.
    destruct Hmiddle as [input_rows [Hinput Hmiddle]].
    apply eval_query_expr_fetch_success_iff.
    exists input_rows; split; [exact Hinput |].
    subst middle output; apply firstn_firstn.
  + apply eval_query_expr_fetch_success_iff in Heval.
    destruct Heval as [input_rows [Hinput Houtput]].
    apply eval_query_expr_fetch_success_iff.
    exists (firstn inner input_rows); split.
    * apply eval_query_expr_fetch_success_iff.
      exists input_rows; split; [exact Hinput | reflexivity].
    * subst output; symmetry; apply firstn_firstn.
- split; intro Heval.
  + apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff; exact Heval.
  + apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff.
    apply eval_query_expr_fetch_error_iff; exact Heval.
Qed.

Lemma eval_query_expr_offset_fetch_comm_iff :
  forall env offset count input outcome,
    eval_query env
      (QExpr_Offset offset (QExpr_Fetch count input)) outcome <->
    eval_query env
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)) outcome.
Proof.
intros env offset count input [output | error].
- split; intro Heval.
  + apply eval_query_expr_offset_success_iff in Heval.
    destruct Heval as [middle [Hmiddle Houtput]].
    apply eval_query_expr_fetch_success_iff in Hmiddle.
    destruct Hmiddle as [input_rows [Hinput Hmiddle]].
    apply eval_query_expr_fetch_success_iff.
    exists (skipn offset input_rows); split.
    * apply eval_query_expr_offset_success_iff.
      exists input_rows; split; [exact Hinput | reflexivity].
    * subst middle output; apply skipn_firstn_comm.
  + apply eval_query_expr_fetch_success_iff in Heval.
    destruct Heval as [middle [Hmiddle Houtput]].
    apply eval_query_expr_offset_success_iff in Hmiddle.
    destruct Hmiddle as [input_rows [Hinput Hmiddle]].
    apply eval_query_expr_offset_success_iff.
    exists (firstn count input_rows); split.
    * apply eval_query_expr_fetch_success_iff.
      exists input_rows; split; [exact Hinput | reflexivity].
    * subst middle output; symmetry; apply skipn_firstn_comm.
- split; intro Heval.
  + apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff.
    apply eval_query_expr_offset_error_iff; exact Heval.
  + apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_offset_error_iff.
    apply eval_query_expr_fetch_error_iff; exact Heval.
Qed.

Lemma eval_query_expr_fetch_offset_comm_iff :
  forall env count offset input outcome,
    eval_query env
      (QExpr_Fetch count (QExpr_Offset offset input)) outcome <->
    eval_query env
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)) outcome.
Proof.
intros env count offset input [output | error].
- split; intro Heval.
  + apply eval_query_expr_fetch_success_iff in Heval.
    destruct Heval as [middle [Hmiddle Houtput]].
    apply eval_query_expr_offset_success_iff in Hmiddle.
    destruct Hmiddle as [input_rows [Hinput Hmiddle]].
    apply eval_query_expr_offset_success_iff.
    exists (firstn (offset + count) input_rows); split.
    * apply eval_query_expr_fetch_success_iff.
      exists input_rows; split; [exact Hinput | reflexivity].
    * subst middle output; apply firstn_skipn_comm.
  + apply eval_query_expr_offset_success_iff in Heval.
    destruct Heval as [middle [Hmiddle Houtput]].
    apply eval_query_expr_fetch_success_iff in Hmiddle.
    destruct Hmiddle as [input_rows [Hinput Hmiddle]].
    apply eval_query_expr_fetch_success_iff.
    exists (skipn offset input_rows); split.
    * apply eval_query_expr_offset_success_iff.
      exists input_rows; split; [exact Hinput | reflexivity].
    * subst middle output; symmetry; apply firstn_skipn_comm.
- split; intro Heval.
  + apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_offset_error_iff.
    apply eval_query_expr_fetch_error_iff; exact Heval.
  + apply eval_query_expr_offset_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff in Heval.
    apply eval_query_expr_fetch_error_iff.
    apply eval_query_expr_offset_error_iff; exact Heval.
Qed.

Lemma eval_query_expr_offset_success_length :
  forall env offset input output,
    eval_query env (QExpr_Offset offset input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows - offset.
Proof.
intros env offset input output Heval.
apply eval_query_expr_offset_success_iff in Heval.
destruct Heval as [input_rows [Hinput Houtput]].
exists input_rows; split; [exact Hinput |].
subst output; apply length_skipn.
Qed.

Lemma eval_query_expr_fetch_success_length :
  forall env count input output,
    eval_query env (QExpr_Fetch count input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = Nat.min count (length input_rows).
Proof.
intros env count input output Heval.
apply eval_query_expr_fetch_success_iff in Heval.
destruct Heval as [input_rows [Hinput Houtput]].
exists input_rows; split; [exact Hinput |].
subst output; apply length_firstn.
Qed.

(** ORDER BY retains the complete input bag while constraining only the legal
    ordered representatives. *)

Lemma eval_query_expr_order_by_success_occurrences :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      forall row,
        Oeset.nb_occ (OTuple T) row output =
        Oeset.nb_occ (OTuple T) row input_rows.
Proof.
intros env keys input output Heval.
apply eval_query_expr_order_by_success_iff in Heval.
destruct Heval as [input_rows [Hinput [Hsame _]]].
exists input_rows; split; [exact Hinput |].
pose proof
  (proj1 (@query_same_rows_as_bag_iff_occurrences
    T output (query_rows_bag input_rows)) Hsame) as Hocc.
intro row.
specialize (Hocc row).
unfold query_rows_bag, SqlQuerySemantics.BTupleT in Hocc.
rewrite Febag.nb_occ_mk_bag in Hocc.
exact Hocc.
Qed.

Lemma eval_query_expr_order_by_success_length :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      length output = length input_rows.
Proof.
intros env keys input output Heval.
apply eval_query_expr_order_by_success_iff in Heval.
destruct Heval as [input_rows [Hinput [Hsame _]]].
exists input_rows; split; [exact Hinput |].
unfold query_same_rows_as_bag, query_rows_bag,
  SqlQuerySemantics.BTupleT in Hsame.
pose proof
  (Febag.cardinal_eq (Fecol.CBag (CTuple T))
    (Febag.mk_bag (Fecol.CBag (CTuple T)) output)
    (Febag.mk_bag (Fecol.CBag (CTuple T)) input_rows) Hsame) as Hcardinal.
rewrite 2 Febag.cardinal_mk_bag in Hcardinal.
now apply Nat2N.inj in Hcardinal.
Qed.

Lemma eval_query_expr_order_by_success_ordered :
  forall env keys input output,
    eval_query env (QExpr_OrderBy keys input) (SqlSuccess output) ->
    ordered_rows value_is_null keys output.
Proof.
intros env keys input output Heval.
apply eval_query_expr_order_by_success_iff in Heval.
destruct Heval as [input_rows [_ [_ Hordered]]].
exact Hordered.
Qed.

(** A bag representative with at most one row has only one semantic ordering.
    This is the precise boundary at which a cardinality proof can erase an
    ORDER BY without assuming anything about physical row order. *)
Lemma query_same_rows_as_bag_length_le_one_ordered_equiv :
  forall left right,
    @query_same_rows_as_bag T left (query_rows_bag right) ->
    (length right <= 1)%nat ->
    ordered_rows_equiv T left right.
Proof.
intros left right Hsame Hlength.
assert (Hright : @query_same_rows_as_bag T right (query_rows_bag right)).
{ unfold query_same_rows_as_bag; apply Febag.equal_refl. }
pose proof (query_same_rows_as_bag_length Hsame Hright) as Hlengths.
destruct right as [|right_head right_tail].
- destruct left as [|left_head left_tail]; [apply ordered_rows_equiv_refl |].
  cbn in Hlengths; discriminate.
- destruct right_tail as [|right_second right_tail].
  + destruct left as [|left_head left_tail].
    * cbn in Hlengths; discriminate.
    * destruct left_tail as [|left_second left_tail].
      -- pose proof
           (proj1
             (query_same_rows_as_bag_iff_occurrences
               T [left_head] (query_rows_bag [right_head])) Hsame left_head)
           as Hocc.
         unfold query_rows_bag, SqlQuerySemantics.BTupleT in Hocc.
         rewrite Febag.nb_occ_mk_bag in Hocc.
         cbn in Hocc.
         rewrite Oeset.compare_eq_refl in Hocc.
         destruct (Oeset.compare (OTuple T) left_head right_head) eqn:Hcompare;
           try discriminate.
         unfold ordered_rows_equiv, mk_oelists; cbn.
         now rewrite Hcompare.
      -- cbn in Hlengths; discriminate.
  + cbn in Hlength; lia.
Qed.

(** ORDER BY is observationally redundant for a query whose every successful
    outcome contains at most one row.  Child errors are preserved exactly. *)
Theorem query_expr_order_by_outcome_equiv_of_success_length_le_one :
  forall env keys input,
    (exists outcome, eval_query env input outcome) ->
    (forall rows,
      eval_query env input (SqlSuccess rows) ->
      (length rows <= 1)%nat) ->
    query_outcome_equiv env (QExpr_OrderBy keys input) input.
Proof.
intros env keys input Houtcome Hbound.
assert (Hordered_outcome :
  exists outcome, eval_query env (QExpr_OrderBy keys input) outcome).
{
  destruct Houtcome as [[rows | error] Heval].
  - destruct (@order_by_rows_has_observation T value_is_null keys rows)
      as [output [Hsame Hordered]].
    exists (SqlSuccess output).
    apply eval_query_expr_order_by_success_iff.
    exists rows; repeat split; assumption.
  - exists (SqlError error).
    now apply eval_query_expr_order_by_error_iff.
}
apply query_expr_outcome_equiv_of_observations.
- reflexivity.
- exact Hordered_outcome.
- exact Houtcome.
- intros output Heval.
  apply eval_query_expr_order_by_success_iff in Heval.
  destruct Heval as [input_rows [Hinput [Hsame _]]].
  exists input_rows; split; [exact Hinput |].
  now apply query_same_rows_as_bag_length_le_one_ordered_equiv;
    [exact Hsame | apply Hbound].
- intros input_rows Hinput.
  destruct (@order_by_rows_has_observation T value_is_null keys input_rows)
    as [output [Hsame Hordered]].
  exists output; split.
  + apply eval_query_expr_order_by_success_iff.
    exists input_rows; repeat split; assumption.
  + now apply query_same_rows_as_bag_length_le_one_ordered_equiv;
      [exact Hsame | apply Hbound].
- intro error; apply eval_query_expr_order_by_error_iff.
Qed.

(** A nested ORDER BY exposes only the outer key order.  The inner sort still
    must produce a legal representative, but it neither changes the input bag
    nor hides a child runtime error. *)

Lemma eval_query_expr_order_by_order_by_iff :
  forall env outer_keys inner_keys input outcome,
    eval_query env
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input)) outcome <->
    eval_query env (QExpr_OrderBy outer_keys input) outcome.
Proof.
intros env outer_keys inner_keys input [output | error].
- split; intro Heval.
  + apply eval_query_expr_order_by_success_iff in Heval.
    destruct Heval as
      [middle [Hmiddle [Houtput_bag Houtput_ordered]]].
    apply eval_query_expr_order_by_success_iff in Hmiddle.
    destruct Hmiddle as
      [input_rows [Hinput [Hmiddle_bag _]]].
    apply eval_query_expr_order_by_success_iff.
    exists input_rows; split; [exact Hinput |].
    split; [| exact Houtput_ordered].
    eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput_bag.
    * now apply query_same_rows_as_bag_iff_bag_eq in Hmiddle_bag.
  + apply eval_query_expr_order_by_success_iff in Heval.
    destruct Heval as
      [input_rows [Hinput [Houtput_bag Houtput_ordered]]].
    destruct
      (@order_by_rows_has_observation T value_is_null inner_keys input_rows)
      as [middle [Hmiddle_bag Hmiddle_ordered]].
    apply eval_query_expr_order_by_success_iff.
    exists middle; split.
    * apply eval_query_expr_order_by_success_iff.
      exists input_rows; repeat split; assumption.
    * split; [| exact Houtput_ordered].
      eapply query_same_rows_as_bag_bag_transport.
      -- exact Houtput_bag.
      -- apply bag_eq_sym.
         now apply query_same_rows_as_bag_iff_bag_eq in Hmiddle_bag.
- split; intro Heval.
  + apply eval_query_expr_order_by_error_iff in Heval.
    apply eval_query_expr_order_by_error_iff in Heval.
    now apply eval_query_expr_order_by_error_iff.
  + apply eval_query_expr_order_by_error_iff in Heval.
    apply eval_query_expr_order_by_error_iff.
    now apply eval_query_expr_order_by_error_iff.
Qed.

(** Context-ready forms of the exact slicing and ordering rewrites.  These
    preserve the ordered output schema and every runtime outcome, so they may
    be passed directly to [query_expr_context_global_congr]. *)

Lemma query_expr_offset_zero_global_typed_equiv :
  forall input,
    query_global_typed_outcome_equiv (QExpr_Offset 0 input) input.
Proof.
intro input; split; [reflexivity |].
intros env outcome; apply eval_query_expr_offset_zero_iff.
Qed.

Lemma query_expr_offset_offset_global_typed_equiv :
  forall outer inner input,
    query_global_typed_outcome_equiv
      (QExpr_Offset outer (QExpr_Offset inner input))
      (QExpr_Offset (outer + inner) input).
Proof.
intros outer inner input; split; [reflexivity |].
intros env outcome; apply eval_query_expr_offset_offset_iff.
Qed.

Lemma query_expr_fetch_fetch_global_typed_equiv :
  forall outer inner input,
    query_global_typed_outcome_equiv
      (QExpr_Fetch outer (QExpr_Fetch inner input))
      (QExpr_Fetch (Nat.min outer inner) input).
Proof.
intros outer inner input; split; [reflexivity |].
intros env outcome; apply eval_query_expr_fetch_fetch_iff.
Qed.

Lemma query_expr_offset_fetch_global_typed_equiv :
  forall offset count input,
    query_global_typed_outcome_equiv
      (QExpr_Offset offset (QExpr_Fetch count input))
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)).
Proof.
intros offset count input; split; [reflexivity |].
intros env outcome; apply eval_query_expr_offset_fetch_comm_iff.
Qed.

Lemma query_expr_fetch_offset_global_typed_equiv :
  forall count offset input,
    query_global_typed_outcome_equiv
      (QExpr_Fetch count (QExpr_Offset offset input))
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)).
Proof.
intros count offset input; split; [reflexivity |].
intros env outcome; apply eval_query_expr_fetch_offset_comm_iff.
Qed.

Lemma query_expr_order_by_order_by_global_typed_equiv :
  forall outer_keys inner_keys input,
    query_global_typed_outcome_equiv
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input))
      (QExpr_OrderBy outer_keys input).
Proof.
intros outer_keys inner_keys input; split; [reflexivity |].
intros env outcome; apply eval_query_expr_order_by_order_by_iff.
Qed.

(** Fixed-environment error-preserving congruence uses extensional ordered-row
    equality rather than Rocq list equality.  Bag resets cross the explicit
    list-to-bag bridge; slices preserve positional equality directly. *)

Lemma query_expr_distinct_outcome_equiv_congr :
  forall env left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros env left right
  [Houtputs
    [Hleft_outcome
      [Hright_outcome [Hforward [Hbackward Herrors]]]]].
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- destruct Hleft_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_distinct_bag (query_rows_bag rows)))).
    eapply EQuery_DistinctSuccess; [exact Houtcome |].
    apply query_elements_same_rows_as_bag.
  + exists (SqlError error).
    now apply EQuery_DistinctChildError.
- destruct Hright_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_distinct_bag (query_rows_bag rows)))).
    eapply EQuery_DistinctSuccess; [exact Houtcome |].
    apply query_elements_same_rows_as_bag.
  + exists (SqlError error).
    now apply EQuery_DistinctChildError.
- intros output Houtput.
  apply eval_query_expr_distinct_success_iff in Houtput.
  destruct Houtput as [left_rows [Hleft Houtput]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists output; split.
  + apply eval_query_expr_distinct_success_iff.
    exists right_rows; split; [exact Hright |].
    eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput.
    * apply query_distinct_bag_congr.
      exact (ordered_rows_equiv_implies_bag_eq Hrows).
  + apply ordered_rows_equiv_refl.
- intros output Houtput.
  apply eval_query_expr_distinct_success_iff in Houtput.
  destruct Houtput as [right_rows [Hright Houtput]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists output; split.
  + apply eval_query_expr_distinct_success_iff.
    exists left_rows; split; [exact Hleft |].
    eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput.
    * apply query_distinct_bag_congr.
      apply bag_eq_sym.
      exact (ordered_rows_equiv_implies_bag_eq Hrows).
  + apply ordered_rows_equiv_refl.
- intro error.
  rewrite 2 eval_query_expr_distinct_error_iff.
  apply Herrors.
Qed.

Lemma query_expr_order_by_outcome_equiv_congr :
  forall env keys left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
Proof.
intros env keys left right
  [Houtputs
    [Hleft_outcome
      [Hright_outcome [Hforward [Hbackward Herrors]]]]].
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- destruct Hleft_outcome as [[rows | error] Houtcome].
  + destruct (@order_by_rows_has_observation T value_is_null keys rows)
      as [output Horder].
    exists (SqlSuccess output).
    now apply EQuery_OrderBySuccess with rows.
  + exists (SqlError error).
    now apply EQuery_OrderByChildError.
- destruct Hright_outcome as [[rows | error] Houtcome].
  + destruct (@order_by_rows_has_observation T value_is_null keys rows)
      as [output Horder].
    exists (SqlSuccess output).
    now apply EQuery_OrderBySuccess with rows.
  + exists (SqlError error).
    now apply EQuery_OrderByChildError.
- intros output Houtput.
  apply eval_query_expr_order_by_success_iff in Houtput.
  destruct Houtput as
    [left_rows [Hleft [Houtput_bag Houtput_ordered]]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists output; split.
  + apply eval_query_expr_order_by_success_iff.
    exists right_rows; split; [exact Hright |].
    split; [| exact Houtput_ordered].
    eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput_bag.
    * exact (ordered_rows_equiv_implies_bag_eq Hrows).
  + apply ordered_rows_equiv_refl.
- intros output Houtput.
  apply eval_query_expr_order_by_success_iff in Houtput.
  destruct Houtput as
    [right_rows [Hright [Houtput_bag Houtput_ordered]]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists output; split.
  + apply eval_query_expr_order_by_success_iff.
    exists left_rows; split; [exact Hleft |].
    split; [| exact Houtput_ordered].
    eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput_bag.
    * apply bag_eq_sym.
      exact (ordered_rows_equiv_implies_bag_eq Hrows).
  + apply ordered_rows_equiv_refl.
- intro error.
  rewrite 2 eval_query_expr_order_by_error_iff.
  apply Herrors.
Qed.

Lemma query_expr_offset_outcome_equiv_congr :
  forall env offset left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
Proof.
intros env offset left right
  [Houtputs
    [Hleft_outcome
      [Hright_outcome [Hforward [Hbackward Herrors]]]]].
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- destruct Hleft_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess (skipn offset rows)).
    now apply EQuery_OffsetSuccess.
  + exists (SqlError error).
    now apply EQuery_OffsetChildError.
- destruct Hright_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess (skipn offset rows)).
    now apply EQuery_OffsetSuccess.
  + exists (SqlError error).
    now apply EQuery_OffsetChildError.
- intros output Houtput.
  apply eval_query_expr_offset_success_iff in Houtput.
  destruct Houtput as [left_rows [Hleft ->]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists (skipn offset right_rows); split.
  + now apply EQuery_OffsetSuccess.
  + now apply ordered_rows_equiv_skipn.
- intros output Houtput.
  apply eval_query_expr_offset_success_iff in Houtput.
  destruct Houtput as [right_rows [Hright ->]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists (skipn offset left_rows); split.
  + now apply EQuery_OffsetSuccess.
  + now apply ordered_rows_equiv_skipn.
- intro error.
  rewrite 2 eval_query_expr_offset_error_iff.
  apply Herrors.
Qed.

Lemma query_expr_fetch_outcome_equiv_congr :
  forall env count left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
Proof.
intros env count left right
  [Houtputs
    [Hleft_outcome
      [Hright_outcome [Hforward [Hbackward Herrors]]]]].
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- destruct Hleft_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess (firstn count rows)).
    now apply EQuery_FetchSuccess.
  + exists (SqlError error).
    now apply EQuery_FetchChildError.
- destruct Hright_outcome as [[rows | error] Houtcome].
  + exists (SqlSuccess (firstn count rows)).
    now apply EQuery_FetchSuccess.
  + exists (SqlError error).
    now apply EQuery_FetchChildError.
- intros output Houtput.
  apply eval_query_expr_fetch_success_iff in Houtput.
  destruct Houtput as [left_rows [Hleft ->]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists (firstn count right_rows); split.
  + now apply EQuery_FetchSuccess.
  + now apply ordered_rows_equiv_firstn.
- intros output Houtput.
  apply eval_query_expr_fetch_success_iff in Houtput.
  destruct Houtput as [right_rows [Hright ->]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists (firstn count left_rows); split.
  + now apply EQuery_FetchSuccess.
  + now apply ordered_rows_equiv_firstn.
- intro error.
  rewrite 2 eval_query_expr_fetch_error_iff.
  apply Herrors.
Qed.

Lemma query_expr_rank_outcome_equiv_congr :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    query_outcome_equiv env left right ->
    query_outcome_equiv env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value right).
Proof.
intros env partition_keys order_keys rank_attribute rank_value left right
  [Houtputs
    [Hleft_outcome
      [Hright_outcome [Hforward [Hbackward Herrors]]]]].
apply query_expr_outcome_equiv_of_observations.
- cbn [query_expr_outputs]; now rewrite Houtputs.
- destruct Hleft_outcome as [[rows | error] Houtcome].
  + destruct
      (@query_rank_rows_outcome T value_is_null
        partition_keys order_keys rank_attribute rank_value
        (query_rank_bag_rows (query_rows_bag rows))
        (query_rank_bag_rows (query_rows_bag rows)))
      as [ranked_rows |] eqn:Hrank.
    * exists (SqlSuccess
        (Febag.elements (Fecol.CBag (CTuple T))
          (query_rows_bag ranked_rows))).
      eapply EQuery_RankSuccess with
        (input_rows := rows) (ranked_rows := ranked_rows).
      -- exact Houtcome.
      -- exact Hrank.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError (DataException NumericValueOutOfRange)).
      eapply EQuery_RankValueError with (input_rows := rows);
        [exact Houtcome | exact Hrank].
  + exists (SqlError error).
    now apply EQuery_RankChildError.
- destruct Hright_outcome as [[rows | error] Houtcome].
  + destruct
      (@query_rank_rows_outcome T value_is_null
        partition_keys order_keys rank_attribute rank_value
        (query_rank_bag_rows (query_rows_bag rows))
        (query_rank_bag_rows (query_rows_bag rows)))
      as [ranked_rows |] eqn:Hrank.
    * exists (SqlSuccess
        (Febag.elements (Fecol.CBag (CTuple T))
          (query_rows_bag ranked_rows))).
      eapply EQuery_RankSuccess with
        (input_rows := rows) (ranked_rows := ranked_rows).
      -- exact Houtcome.
      -- exact Hrank.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError (DataException NumericValueOutOfRange)).
      eapply EQuery_RankValueError with (input_rows := rows);
        [exact Houtcome | exact Hrank].
  + exists (SqlError error).
    now apply EQuery_RankChildError.
- intros output Houtput.
  apply eval_query_expr_rank_success_iff in Houtput.
  destruct Houtput as
    [left_rows [output_bag [Hleft [Hrank Houtput_bag]]]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  assert (Hinput_bags :
    bag_eq T (rows_bag T left_rows) (rows_bag T right_rows)).
  { exact (ordered_rows_equiv_implies_bag_eq Hrows). }
  pose proof
    (query_rank_bag_relation_extensional
      value_is_null partition_keys order_keys rank_attribute rank_value
      Hinput_bags (bag_eq_refl T output_bag)) as Htransport.
  exists output; split.
  + apply eval_query_expr_rank_success_iff.
    exists right_rows, output_bag; repeat split; try assumption.
    now apply (proj1 Htransport).
  + apply ordered_rows_equiv_refl.
- intros output Houtput.
  apply eval_query_expr_rank_success_iff in Houtput.
  destruct Houtput as
    [right_rows [output_bag [Hright [Hrank Houtput_bag]]]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  assert (Hinput_bags :
    bag_eq T (rows_bag T right_rows) (rows_bag T left_rows)).
  {
    apply bag_eq_sym.
    exact (ordered_rows_equiv_implies_bag_eq Hrows).
  }
  pose proof
    (query_rank_bag_relation_extensional
      value_is_null partition_keys order_keys rank_attribute rank_value
      Hinput_bags (bag_eq_refl T output_bag)) as Htransport.
  exists output; split.
  + apply eval_query_expr_rank_success_iff.
    exists left_rows, output_bag; repeat split; try assumption.
    now apply (proj1 Htransport).
  + apply ordered_rows_equiv_refl.
- intro error; split; intro Herror.
  + apply eval_query_expr_rank_error_iff in Herror.
    apply eval_query_expr_rank_error_iff.
    destruct Herror as
      [Hchild | [Hkind [left_rows [Hleft Hrank]]]].
    * left; now apply (proj1 (Herrors error)).
    * right; split; [exact Hkind |].
      destruct (Hforward left_rows Hleft)
        as [right_rows [Hright Hrows]].
      exists right_rows; split; [exact Hright |].
      pose proof
        (query_rank_bag_rows_eq
          (ordered_rows_equiv_implies_bag_eq Hrows)) as Hcanonical.
      change
        (query_rank_bag_rows (query_rows_bag left_rows) =
         query_rank_bag_rows (query_rows_bag right_rows)) in Hcanonical.
      now rewrite <- Hcanonical.
  + apply eval_query_expr_rank_error_iff in Herror.
    apply eval_query_expr_rank_error_iff.
    destruct Herror as
      [Hchild | [Hkind [right_rows [Hright Hrank]]]].
    * left; now apply (proj2 (Herrors error)).
    * right; split; [exact Hkind |].
      destruct (Hbackward right_rows Hright)
        as [left_rows [Hleft Hrows]].
      exists left_rows; split; [exact Hleft |].
      pose proof
        (query_rank_bag_rows_eq
          (ordered_rows_equiv_implies_bag_eq Hrows)) as Hcanonical.
      change
        (query_rank_bag_rows (query_rows_bag left_rows) =
         query_rank_bag_rows (query_rows_bag right_rows)) in Hcanonical.
      now rewrite Hcanonical.
Qed.

Lemma query_expr_window_outcome_equiv_congr :
  forall env partition_keys order_keys items left right,
    query_outcome_equiv env left right ->
    (exists outcome,
      eval_query env
        (QExpr_Window partition_keys order_keys items left) outcome) ->
    (exists outcome,
      eval_query env
        (QExpr_Window partition_keys order_keys items right) outcome) ->
    query_outcome_equiv env
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
Proof.
intros env partition_keys order_keys items left right
  [Houtputs
    [_ [_ [Hforward [Hbackward Herrors]]]]]
  Hleft_outcome Hright_outcome.
apply query_expr_outcome_equiv_of_observations.
- cbn [query_expr_outputs]; now rewrite Houtputs.
- exact Hleft_outcome.
- exact Hright_outcome.
- intros output Houtput.
  apply eval_query_expr_window_success_iff in Houtput.
  destruct Houtput as
    [left_rows [output_bag [Hleft [Hwindow Houtput_bag]]]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  assert (Hinput_bags :
    bag_eq T (rows_bag T left_rows) (rows_bag T right_rows)).
  { exact (ordered_rows_equiv_implies_bag_eq Hrows). }
  pose proof
    (query_window_bag_relation_extensional
      symbol_runtime_error aggregate_runtime_error value_is_null
      env partition_keys order_keys items
      Hinput_bags (bag_eq_refl T output_bag)) as Htransport.
  exists output; split.
  + apply eval_query_expr_window_success_iff.
    exists right_rows, output_bag; repeat split; try assumption.
    now apply (proj1 Htransport).
  + apply ordered_rows_equiv_refl.
- intros output Houtput.
  apply eval_query_expr_window_success_iff in Houtput.
  destruct Houtput as
    [right_rows [output_bag [Hright [Hwindow Houtput_bag]]]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  assert (Hinput_bags :
    bag_eq T (rows_bag T right_rows) (rows_bag T left_rows)).
  {
    apply bag_eq_sym.
    exact (ordered_rows_equiv_implies_bag_eq Hrows).
  }
  pose proof
    (query_window_bag_relation_extensional
      symbol_runtime_error aggregate_runtime_error value_is_null
      env partition_keys order_keys items
      Hinput_bags (bag_eq_refl T output_bag)) as Htransport.
  exists output; split.
  + apply eval_query_expr_window_success_iff.
    exists left_rows, output_bag; repeat split; try assumption.
    now apply (proj1 Htransport).
  + apply ordered_rows_equiv_refl.
- intro error; split; intro Herror.
  + apply eval_query_expr_window_error_iff in Herror.
    apply eval_query_expr_window_error_iff.
    destruct Herror as
      [Hchild |
       [left_rows [ordered_input [Hleft [Horder Hwindow]]]]].
    * left; now apply (proj1 (Herrors error)).
    * right.
      destruct (Hforward left_rows Hleft)
        as [right_rows [Hright Hrows]].
      exists right_rows, ordered_input; split; [exact Hright |].
      pose proof
        (query_rank_bag_rows_eq
          (ordered_rows_equiv_implies_bag_eq Hrows)) as Hcanonical.
      change
        (query_rank_bag_rows (query_rows_bag left_rows) =
         query_rank_bag_rows (query_rows_bag right_rows)) in Hcanonical.
      split.
      -- now rewrite <- Hcanonical.
      -- exact Hwindow.
  + apply eval_query_expr_window_error_iff in Herror.
    apply eval_query_expr_window_error_iff.
    destruct Herror as
      [Hchild |
       [right_rows [ordered_input [Hright [Horder Hwindow]]]]].
    * left; now apply (proj2 (Herrors error)).
    * right.
      destruct (Hbackward right_rows Hright)
        as [left_rows [Hleft Hrows]].
      exists left_rows, ordered_input; split; [exact Hleft |].
      pose proof
        (query_rank_bag_rows_eq
          (ordered_rows_equiv_implies_bag_eq Hrows)) as Hcanonical.
      change
        (query_rank_bag_rows (query_rows_bag left_rows) =
         query_rank_bag_rows (query_rows_bag right_rows)) in Hcanonical.
      split.
      -- now rewrite Hcanonical.
      -- exact Hwindow.
Qed.

(** Success-only packages keep operator-local failures explicit.  ORDER BY
    cannot add an error; rank/window callers must separately prove that their
    embedding or window-item computations are safe and have a success. *)

Lemma query_expr_order_by_equiv_congr :
  forall env keys left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
Proof.
intros env keys left right Hchild.
pose proof
  (query_expr_order_by_outcome_equiv_congr keys
    (query_expr_equiv_implies_outcome_equiv Hchild)) as Houtcome.
destruct Hchild as
  [_ [Hsuccess [Hleft_safe [Hright_safe _]]]].
apply query_expr_equiv_of_outcome_equiv_safe.
- exact Houtcome.
- intros error Herror.
  apply eval_query_expr_order_by_error_iff in Herror.
  exact (Hleft_safe error Herror).
- intros error Herror.
  apply eval_query_expr_order_by_error_iff in Herror.
  exact (Hright_safe error Herror).
- destruct Hsuccess as [rows Hrows].
  now apply eval_query_expr_order_by_has_success with rows.
Qed.

Lemma query_expr_rank_equiv_congr_safe :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    query_equiv env left right ->
    query_safe env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left) ->
    query_safe env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value right) ->
    query_has_success env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left) ->
    query_equiv env
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank
        partition_keys order_keys rank_attribute rank_value right).
Proof.
intros env partition_keys order_keys rank_attribute rank_value left right
  [Houtputs [_ [_ [_ [Hforward Hbackward]]]]]
  Hleft_safe Hright_safe Hsuccess.
apply query_bag_reset_equiv_of_success_bags_safe.
- cbn [query_expr_outputs]; now rewrite Houtputs.
- reflexivity.
- reflexivity.
- apply query_rank_success_bags_congr.
  now apply query_success_bags_of_success_rel_equiv.
- exact Hleft_safe.
- exact Hright_safe.
- exact Hsuccess.
Qed.

Lemma query_expr_window_equiv_congr_safe :
  forall env partition_keys order_keys items left right,
    query_equiv env left right ->
    query_safe env (QExpr_Window partition_keys order_keys items left) ->
    query_safe env (QExpr_Window partition_keys order_keys items right) ->
    query_has_success env
      (QExpr_Window partition_keys order_keys items left) ->
    query_equiv env
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
Proof.
intros env partition_keys order_keys items left right
  [Houtputs [_ [_ [_ [Hforward Hbackward]]]]]
  Hleft_safe Hright_safe Hsuccess.
apply query_bag_reset_equiv_of_success_bags_safe.
- cbn [query_expr_outputs]; now rewrite Houtputs.
- reflexivity.
- reflexivity.
- apply query_window_success_bags_congr.
  now apply query_success_bags_of_success_rel_equiv.
- exact Hleft_safe.
- exact Hright_safe.
- exact Hsuccess.
Qed.

(** Fixed-environment exact equivalence is substitutive through deterministic
    slicing, because slicing respects ordered row equality. *)

Lemma query_expr_offset_equiv_congr :
  forall env offset left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
Proof.
intros env offset left right
  [Houtputs [Hsuccess [Hleft_safe [Hright_safe [Hforward Hbackward]]]]].
split; [exact Houtputs |].
unfold query_expr_observation_equiv, successful_relation_equiv.
split.
- destruct Hsuccess as [rows Hrows].
  exists (skipn offset rows).
  now apply EQuery_OffsetSuccess.
- split.
  + intros error Heval.
    apply eval_query_expr_offset_error_iff in Heval.
    now apply (Hleft_safe error).
  + split.
    * intros error Heval.
      apply eval_query_expr_offset_error_iff in Heval.
      now apply (Hright_safe error).
    * split.
      -- intros output Houtput.
         apply eval_query_expr_offset_success_iff in Houtput.
         destruct Houtput as [left_rows [Hleft Houtput]].
         destruct (Hforward left_rows Hleft)
           as [right_rows [Hright Hrows]].
         exists (skipn offset right_rows); split.
         ++ now apply EQuery_OffsetSuccess.
         ++ subst output; now apply ordered_rows_equiv_skipn.
      -- intros output Houtput.
         apply eval_query_expr_offset_success_iff in Houtput.
         destruct Houtput as [right_rows [Hright Houtput]].
         destruct (Hbackward right_rows Hright)
           as [left_rows [Hleft Hrows]].
         exists (skipn offset left_rows); split.
         ++ now apply EQuery_OffsetSuccess.
         ++ subst output; now apply ordered_rows_equiv_skipn.
Qed.

Lemma query_expr_fetch_equiv_congr :
  forall env count left right,
    query_equiv env left right ->
    query_equiv env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
Proof.
intros env count left right
  [Houtputs [Hsuccess [Hleft_safe [Hright_safe [Hforward Hbackward]]]]].
split; [exact Houtputs |].
unfold query_expr_observation_equiv, successful_relation_equiv.
split.
- destruct Hsuccess as [rows Hrows].
  exists (firstn count rows).
  now apply EQuery_FetchSuccess.
- split.
  + intros error Heval.
    apply eval_query_expr_fetch_error_iff in Heval.
    now apply (Hleft_safe error).
  + split.
    * intros error Heval.
      apply eval_query_expr_fetch_error_iff in Heval.
      now apply (Hright_safe error).
    * split.
      -- intros output Houtput.
         apply eval_query_expr_fetch_success_iff in Houtput.
         destruct Houtput as [left_rows [Hleft Houtput]].
         destruct (Hforward left_rows Hleft)
           as [right_rows [Hright Hrows]].
         exists (firstn count right_rows); split.
         ++ now apply EQuery_FetchSuccess.
         ++ subst output; now apply ordered_rows_equiv_firstn.
      -- intros output Houtput.
         apply eval_query_expr_fetch_success_iff in Houtput.
         destruct Houtput as [right_rows [Hright Houtput]].
         destruct (Hbackward right_rows Hright)
           as [left_rows [Hleft Hrows]].
         exists (firstn count left_rows); split.
         ++ now apply EQuery_FetchSuccess.
         ++ subst output; now apply ordered_rows_equiv_firstn.
Qed.

(** A row predicate that has exactly the successful observation TRUE on every
    input row is an identity filter.  Requiring exact outcome uniqueness, not
    merely the existence of a TRUE derivation, preserves runtime errors for
    formula expressions containing subqueries. *)
Lemma eval_filter_rows_always_true_iff :
  forall env formula rows,
    (forall row,
      In row rows ->
      forall outcome,
        @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null (env_t T env row) formula outcome <->
        outcome = SqlSuccess (Bool.true (B T))) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env formula rows outcome <->
      outcome = SqlSuccess rows.
Proof.
intros env formula rows Hformula.
induction rows as [|row rows IH]; intro outcome.
- split; intro Heval.
  + inversion Heval; reflexivity.
  + subst outcome; constructor.
- assert (Hhead := Hformula row (or_introl eq_refl)).
  assert (Htail : forall row',
    In row' rows ->
    forall observed,
      @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null (env_t T env row') formula observed <->
      observed = SqlSuccess (Bool.true (B T))).
  {
    intros row' Hin; apply Hformula; now right.
  }
  specialize (IH Htail).
  split; intro Heval.
  + inversion Heval; subst.
    * apply Hhead in H3; discriminate.
    * apply Hhead in H2; inversion H2; subst truth.
      apply IH in H4; subst tail.
      unfold filter_cons_outcome.
      destruct (Bool.is_true (B T) (Bool.true (B T))) eqn:Htrue.
      -- reflexivity.
      -- rewrite Bool.true_is_true_alt in Htrue; discriminate.
  + subst outcome.
    replace (SqlSuccess (row :: rows)) with
      (@filter_cons_outcome T (Bool.true (B T)) row (SqlSuccess rows)).
    * eapply EFilterRows_Cons.
      -- apply Hhead; reflexivity.
      -- apply IH; reflexivity.
    * unfold filter_cons_outcome.
      now rewrite Bool.true_is_true_alt.
Qed.

Theorem query_expr_filter_outcome_equiv_of_always_true :
  forall env formula input,
    (exists outcome, eval_query env input outcome) ->
    (forall rows,
      eval_query env input (SqlSuccess rows) ->
      forall row,
        In row rows ->
        forall outcome,
          @eval_formula_expr_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error
            value_is_null (env_t T env row) formula outcome <->
          outcome = SqlSuccess (Bool.true (B T))) ->
    query_outcome_equiv env (QExpr_Filter formula input) input.
Proof.
intros env formula input Hinhabited Hformula.
apply query_expr_outcome_equiv_of_observations.
- reflexivity.
- destruct Hinhabited as [[rows | error] Heval].
  + exists (SqlSuccess rows).
    eapply EQuery_FilterRows; [exact Heval |].
    apply eval_filter_rows_always_true_iff with (rows := rows).
    * now apply Hformula.
    * reflexivity.
  + exists (SqlError error); now apply EQuery_FilterChildError.
- exact Hinhabited.
- intros output Houtput.
  apply eval_query_expr_filter_success_iff in Houtput.
  destruct Houtput as [input_rows [Hinput Hfilter]].
  apply (eval_filter_rows_always_true_iff
    (env := env) (formula := formula)) in Hfilter.
  + inversion Hfilter; subst output.
    exists input_rows; split; [exact Hinput |].
    apply ordered_rows_equiv_refl.
  + now apply Hformula.
- intros input_rows Hinput.
  exists input_rows; split.
  + eapply EQuery_FilterRows; [exact Hinput |].
    apply eval_filter_rows_always_true_iff with (rows := input_rows).
    * now apply Hformula.
    * reflexivity.
  + apply ordered_rows_equiv_refl.
- intro error; split; intro Herror.
  + apply eval_query_expr_filter_error_iff in Herror.
    destruct Herror as [Hchild | [rows [Hinput Hfilter]]]; [exact Hchild |].
    apply (eval_filter_rows_always_true_iff
      (env := env) (formula := formula)) in Hfilter.
    * discriminate.
    * now apply Hformula.
  + now apply EQuery_FilterChildError.
Qed.

(** Pull an arbitrary relational permutation of a mapped list back to a
    permutation of its source.  No injectivity premise is needed: each mapped
    occurrence retains one source occurrence, even when several sources map
    to equivalent outputs. *)
Lemma relational_permutation_map_inv :
  forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) output input,
    _permut R output (map f input) ->
    exists reordered,
      Permutation input reordered /\
      Forall2 R output (map f reordered).
Proof.
intros A B R f output.
induction output as [|head output IH]; intros input Hpermut.
- destruct input as [|item input].
  + exists nil; split; constructor.
  + inversion Hpermut.
- destruct (_permut_inv_left_strong
    (R := R) (l2 := map f input) head nil output Hpermut)
    as [mapped [prefix [suffix [Hhead [Hmap Htail]]]]].
  destruct (map_eq_app _ _ _ _ Hmap)
    as [before [after [Hinput [Hprefix Hafter]]]].
  destruct (map_eq_cons _ _ Hafter)
    as [item [rest [Hmapped [Hsuffix Hrest]]]].
  subst input prefix mapped suffix after.
  simpl in Htail; rewrite <- map_app in Htail.
  destruct (IH (before ++ rest) Htail)
    as [reordered [Hreordered Hrows]].
  exists (item :: reordered); split.
  + eapply Permutation_trans.
    * apply Permutation_sym, Permutation_middle.
    * now apply perm_skip.
  + simpl; now constructor.
Qed.

Lemma ordered_rows_equiv_of_Forall2 :
  forall left right,
    Forall2
      (fun left_row right_row =>
        Oeset.compare (OTuple T) left_row right_row = Eq)
      left right ->
    ordered_rows_equiv T left right.
Proof.
intros left right Hrows.
induction Hrows; unfold ordered_rows_equiv, mk_oelists in *; cbn.
- reflexivity.
- now rewrite H.
Qed.

(** Pointwise projection preserves exact ordered-row equivalence.  Tuple
    representations may differ, so the proof goes through [projection_eq]
    rather than Rocq equality. *)
Lemma ordered_rows_equiv_map_projection :
  forall env select_list left right,
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        left)
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        right).
Proof.
intros env select_list left.
induction left as [|left_row left_rows IH];
  intros [|right_row right_rows] Hequiv;
  unfold ordered_rows_equiv, mk_oelists in *; cbn in *;
  try discriminate; try reflexivity.
case_eq (Oeset.compare (OTuple T) left_row right_row);
  intro Hrow; rewrite Hrow in Hequiv; try discriminate.
assert (Hprojection :
  projection T (env_t T env left_row) (@Select_List T select_list) =t=
  projection T (env_t T env right_row) (@Select_List T select_list)).
{ apply projection_eq, env_t_eq_2; exact Hrow. }
change
  (comparelA (Oeset.compare (OTuple T))
    (projection T (env_t T env left_row) (@Select_List T select_list) ::
      map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        left_rows)
    (projection T (env_t T env right_row) (@Select_List T select_list) ::
      map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        right_rows) = Eq).
rewrite comparelA_unfold, Hprojection.
now apply IH.
Qed.

(** Two different projection maps preserve ordered equality when their
    outputs agree pointwise on the rows under consideration. *)
Lemma ordered_rows_equiv_map_two_projections :
  forall env left_select right_select rows,
    (forall row,
      In row rows ->
      Oeset.compare (OTuple T)
        (projection T (env_t T env row) (@Select_List T left_select))
        (projection T (env_t T env row) (@Select_List T right_select)) = Eq) ->
    ordered_rows_equiv T
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T left_select))
        rows)
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T right_select))
        rows).
Proof.
intros env left_select right_select rows Hrows.
apply ordered_rows_equiv_of_Forall2.
induction rows as [|row rows IH].
- constructor.
- constructor.
  + apply Hrows; now left.
  + apply IH. intros other Hother; apply Hrows; now right.
Qed.

(** Error-free projection of an ordered input is the pointwise projection in
    exactly the same order. *)
Lemma project_rows_outcome_all_safe :
  forall env select_list rows,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows =
    SqlSuccess
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows).
Proof.
intros env select_list rows Hsafe.
induction rows as [|row rows IH]; cbn.
- reflexivity.
- rewrite Hsafe, IH; reflexivity.
Qed.

(** Local SELECT-list safety preserves an explicitly witnessed successful
    child observation. *)
Lemma query_expr_project_has_success_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_has_success env input ->
    query_has_success env (QExpr_Project select_list input).
Proof.
intros env select_list input Hsafe [rows Hrows].
exists
  (map
    (fun row =>
      projection T (env_t T env row) (@Select_List T select_list))
    rows).
apply eval_query_expr_project_success_iff.
exists rows; split; [exact Hrows |].
now apply project_rows_outcome_all_safe.
Qed.

(** Under the same local SELECT-list safety premise, projection introduces no
    new error category and propagates child errors exactly. *)
Lemma eval_query_expr_project_error_iff_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    forall error,
      eval_query env (QExpr_Project select_list input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros env select_list input Hsafe error.
rewrite eval_query_expr_project_error_iff.
split.
- intros [Hchild | [rows [_ Hlocal]]]; [exact Hchild |].
  rewrite
    (@project_rows_outcome_all_safe
      env select_list rows Hsafe) in Hlocal.
  discriminate.
- intro Hchild; now left.
Qed.

(** A pointwise runtime-safe SELECT list adds no error to its child. *)
Lemma query_expr_project_runtime_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_safe env input ->
    query_safe env (QExpr_Project select_list input).
Proof.
intros env select_list input Hselect Hinput error Herror.
apply (proj1
  (eval_query_expr_project_error_iff_safe
    env select_list input Hselect error)) in Herror.
exact (Hinput error Herror).
Qed.

(** The same local-safety premise lifts any child outcome to a parent
    outcome.  Child errors remain errors; only a successful child invokes the
    already-proved pointwise projection constructor. *)
Lemma query_expr_project_has_outcome_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    (exists outcome, eval_query env input outcome) ->
    exists outcome, eval_query env (QExpr_Project select_list input) outcome.
Proof.
intros env select_list input Hselect [[rows | error] Hinput].
- destruct
    (query_expr_project_has_success_safe
      (env := env) (input := input) select_list
      Hselect (ex_intro _ rows Hinput))
    as [output Houtput].
  now exists (SqlSuccess output).
- exists (SqlError error); now apply EQuery_ProjectChildError.
Qed.

(** Different SELECT lists over the same child are outcome-equivalent when
    they expose the same ordered output schema, cannot fail locally, and map
    every row of every successful child observation to an equivalent tuple. *)
Theorem query_expr_project_select_lists_outcome_equiv_safe :
  forall env left_select right_select input,
    select_list_outputs left_select = select_list_outputs right_select ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) left_select = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) right_select = None) ->
    (forall input_rows row,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      Oeset.compare (OTuple T)
        (projection T (env_t T env row) (@Select_List T left_select))
        (projection T (env_t T env row) (@Select_List T right_select)) = Eq) ->
    (exists outcome, eval_query env input outcome) ->
    query_outcome_equiv env
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
Proof.
intros env left_select right_select input Houtputs Hleft_safe Hright_safe
  Hrows Hinput_outcome.
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- destruct Hinput_outcome as [[input_rows|error] Hinput].
  + exists (SqlSuccess
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T left_select))
        input_rows)).
    rewrite <- (@project_rows_outcome_all_safe
      env left_select input_rows Hleft_safe).
    now apply EQuery_ProjectRows.
  + exists (SqlError error). now apply EQuery_ProjectChildError.
- destruct Hinput_outcome as [[input_rows|error] Hinput].
  + exists (SqlSuccess
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T right_select))
        input_rows)).
    rewrite <- (@project_rows_outcome_all_safe
      env right_select input_rows Hright_safe).
    now apply EQuery_ProjectRows.
  + exists (SqlError error). now apply EQuery_ProjectChildError.
- intros output Houtput.
  apply eval_query_expr_project_success_iff in Houtput.
  destruct Houtput as [input_rows [Hinput Hproject]].
  rewrite (@project_rows_outcome_all_safe
    env left_select input_rows Hleft_safe) in Hproject.
  inversion Hproject; subst output.
  exists
    (map
      (fun row =>
        projection T (env_t T env row) (@Select_List T right_select))
      input_rows); split.
  + apply eval_query_expr_project_success_iff.
    exists input_rows; split; [exact Hinput|].
    now apply project_rows_outcome_all_safe.
  + apply ordered_rows_equiv_map_two_projections.
    intros row Hin; now apply (Hrows input_rows row Hinput Hin).
- intros output Houtput.
  apply eval_query_expr_project_success_iff in Houtput.
  destruct Houtput as [input_rows [Hinput Hproject]].
  rewrite (@project_rows_outcome_all_safe
    env right_select input_rows Hright_safe) in Hproject.
  inversion Hproject; subst output.
  exists
    (map
      (fun row =>
        projection T (env_t T env row) (@Select_List T left_select))
      input_rows); split.
  + apply eval_query_expr_project_success_iff.
    exists input_rows; split; [exact Hinput|].
    now apply project_rows_outcome_all_safe.
  + apply ordered_rows_equiv_map_two_projections.
    intros row Hin; now apply (Hrows input_rows row Hinput Hin).
- intro error; split; intro Herror.
  + apply eval_query_expr_project_error_iff in Herror.
    apply eval_query_expr_project_error_iff.
    destruct Herror as [Hchild|[rows [Hchild Hlocal]]].
    * now left.
    * rewrite (@project_rows_outcome_all_safe
        env left_select rows Hleft_safe) in Hlocal.
      discriminate.
  + apply eval_query_expr_project_error_iff in Herror.
    apply eval_query_expr_project_error_iff.
    destruct Herror as [Hchild|[rows [Hchild Hlocal]]].
    * now left.
    * rewrite (@project_rows_outcome_all_safe
        env right_select rows Hright_safe) in Hlocal.
      discriminate.
Qed.

(** Mapping a representative list and mapping its bag produce the same bag.
    Projection properness for [OTuple] equality is the only semantic premise. *)
Lemma projected_rows_same_as_mapped_bag :
  forall env select_list rows bag,
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows)
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        bag).
Proof.
intros env select_list rows bag Hrows.
apply query_same_rows_as_bag_iff_bag_eq.
unfold bag_eq, rows_bag.
rewrite Febag.map_unfold, Febag.nb_occ_equal.
intro output_row; rewrite 2 Febag.nb_occ_mk_bag.
apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
- intros left right Hequal; apply projection_eq, env_t_eq_2; exact Hequal.
- intro row; apply Oeset.permut_nb_occ, Oeset.nb_occ_permut.
  intro input_row.
  rewrite <- Febag.nb_occ_elements.
  unfold query_same_rows_as_bag, query_rows_bag in Hrows.
  rewrite Febag.nb_occ_equal in Hrows.
  specialize (Hrows input_row).
  now rewrite Febag.nb_occ_mk_bag in Hrows.
Qed.

(** Every ordered representative of a mapped bag has a source-bag
    representative whose pointwise projection is ordered-row equivalent to
    it.  This is the non-injective direction needed by the exact/bag bridge. *)
Lemma mapped_bag_rows_have_projection_preimage :
  forall env select_list bag output,
    query_same_rows_as_bag output
      (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        bag) ->
    exists input_rows,
      query_same_rows_as_bag input_rows bag /\
      ordered_rows_equiv T output
        (map
          (fun row =>
            projection T (env_t T env row) (@Select_List T select_list))
          input_rows).
Proof.
intros env select_list bag output Houtput.
assert (Hpermut :
  Oeset.permut (OTuple T) output
    (map
      (fun row =>
        projection T (env_t T env row) (@Select_List T select_list))
      (Febag.elements (Fecol.CBag (CTuple T)) bag))).
{
  apply Oeset.nb_occ_permut; intro row.
  unfold query_same_rows_as_bag, query_rows_bag in Houtput.
  rewrite Febag.nb_occ_equal in Houtput.
  specialize (Houtput row).
  rewrite Febag.nb_occ_mk_bag in Houtput.
  rewrite Febag.map_unfold, Febag.nb_occ_mk_bag in Houtput.
  exact Houtput.
}
destruct (relational_permutation_map_inv
  (fun row =>
    projection T (env_t T env row) (@Select_List T select_list))
  (output := output)
  (Febag.elements (Fecol.CBag (CTuple T)) bag)
  Hpermut)
  as [input_rows [Hinput_permut Hrows]].
exists input_rows; split.
- eapply query_same_rows_as_bag_bag_transport.
  + now apply permutation_same_rows_as_bag.
  + unfold query_rows_bag, bag_eq.
    rewrite Febag.nb_occ_equal; intro row.
    rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_elements.
    symmetry; now apply permutation_preserves_oeset_occurrences.
- now apply ordered_rows_equiv_of_Forall2.
Qed.

(** The possible successful bag produced by a projection is the multiplicity-
    preserving bag map of one possible child bag. *)
Definition query_project_bag
    (env : Env.env T) (select_list : @_select_list T)
    (input : Febag.bag (Fecol.CBag (CTuple T))) :=
  Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
    (fun row =>
      projection T (env_t T env row) (@Select_List T select_list))
    input.

Theorem query_project_success_bags_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    rel_equiv
      (success_bags env (QExpr_Project select_list input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T (query_project_bag env select_list input_bag) output).
Proof.
intros env select_list input Hsafe output; split; intro Houtput.
- unfold success_bags, query_success_bags, alpha in Houtput.
  destruct Houtput as [output_rows [Heval Hrows]].
  apply eval_query_expr_project_success_iff in Heval.
  destruct Heval as [input_rows [Hinput Hproject]].
  rewrite (@project_rows_outcome_all_safe
    env select_list input_rows Hsafe) in Hproject.
  inversion Hproject; subst output_rows.
  exists (rows_bag T input_rows); split.
  + unfold success_bags, query_success_bags, alpha.
    exists input_rows; split; [exact Hinput | apply bag_eq_refl].
  + assert (Hmapped : query_same_rows_as_bag
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        input_rows)
      (query_project_bag env select_list (rows_bag T input_rows))).
    { unfold query_project_bag.
      apply projected_rows_same_as_mapped_bag.
      apply query_same_rows_as_bag_iff_bag_eq; apply bag_eq_refl. }
    apply query_same_rows_as_bag_iff_bag_eq in Hmapped.
    apply query_same_rows_as_bag_iff_bag_eq in Hrows.
    eapply bag_eq_trans; [apply bag_eq_sym; exact Hmapped | exact Hrows].
- destruct Houtput as [input_bag [Hinput Hbag]].
  unfold success_bags, query_success_bags, alpha in Hinput |- *.
  destruct Hinput as [input_rows [Heval Hrows]].
  exists
    (map
      (fun row =>
        projection T (env_t T env row) (@Select_List T select_list))
      input_rows).
  split.
  + apply eval_query_expr_project_success_iff.
    exists input_rows; split; [exact Heval |].
    now apply project_rows_outcome_all_safe.
  + apply query_same_rows_as_bag_iff_bag_eq.
    assert (Hmapped : query_same_rows_as_bag
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        input_rows)
      (query_project_bag env select_list input_bag)).
    { unfold query_project_bag.
      now apply projected_rows_same_as_mapped_bag. }
    apply query_same_rows_as_bag_iff_bag_eq in Hmapped.
    eapply bag_eq_trans; [exact Hmapped | exact Hbag].
Qed.

(** A locally safe projection preserves bag closure.  It retains the order of
    the actual child witness, while projection properness transports the
    child's ordered row equality to the requested output order. *)
Theorem query_expr_project_bag_closed_safe :
  forall env select_list input,
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    BagClosed T
      (fun rows => eval_query env input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows =>
        eval_query env (QExpr_Project select_list input) (SqlSuccess rows)).
Proof.
intros env select_list input Hsafe Hclosed desired Hpossible.
pose proof
  (proj1
    (@query_project_success_bags_safe
      env select_list input Hsafe (rows_bag T desired)) Hpossible)
  as [input_bag [Hinput_bag Hmapped]].
assert (Hdesired : query_same_rows_as_bag desired
  (query_project_bag env select_list input_bag)).
{
  apply query_same_rows_as_bag_iff_bag_eq.
  now apply bag_eq_sym.
}
destruct
  (@mapped_bag_rows_have_projection_preimage
    env select_list input_bag desired Hdesired)
  as [input_rows [Hinput_rows Hordered]].
unfold success_bags, query_success_bags, alpha in Hinput_bag.
destruct Hinput_bag as [old_rows [Hold_rows Hold_bag]].
apply query_same_rows_as_bag_iff_bag_eq in Hinput_rows.
assert (Htransport : bag_eq T
  (rows_bag T old_rows) (rows_bag T input_rows)).
{
  eapply bag_eq_trans; [exact Hold_bag |].
  now apply bag_eq_sym.
}
assert (Hinput_possible :
  alpha T
    (fun rows => eval_query env input (SqlSuccess rows))
    (rows_bag T input_rows)).
{
  unfold alpha.
  exists old_rows; now split.
}
destruct (Hclosed input_rows Hinput_possible)
  as [actual_input [Hactual_input Hinput_ordered]].
exists
  (map
    (fun row =>
      projection T (env_t T env row) (@Select_List T select_list))
    actual_input).
split.
- apply eval_query_expr_project_success_iff.
  exists actual_input; split; [exact Hactual_input |].
  now apply project_rows_outcome_all_safe.
- eapply ordered_rows_equiv_trans; [exact Hordered |].
  now apply ordered_rows_equiv_map_projection.
Qed.

(** Possible projected bags determine full ordered projection equivalence
    when each child is bag-closed and each SELECT list is locally safe.  This
    is the list-sensitive counterpart of the bag-reset bridge above: output
    schema, parent inhabitation, and exact SQL errors remain explicit. *)
Theorem query_expr_project_outcome_equiv_of_success_bags_safe_closed :
  forall env left_select right_select left_input right_input,
    query_expr_outputs (QExpr_Project left_select left_input) =
      query_expr_outputs (QExpr_Project right_select right_input) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) left_select = None) ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) right_select = None) ->
    BagClosed T
      (fun rows => eval_query env left_input (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query env right_input (SqlSuccess rows)) ->
    rel_equiv
      (success_bags env (QExpr_Project left_select left_input))
      (success_bags env (QExpr_Project right_select right_input)) ->
    (exists outcome,
      eval_query env (QExpr_Project left_select left_input) outcome) ->
    (exists outcome,
      eval_query env (QExpr_Project right_select right_input) outcome) ->
    (forall error,
      eval_query env (QExpr_Project left_select left_input)
        (SqlError error) <->
      eval_query env (QExpr_Project right_select right_input)
        (SqlError error)) ->
    query_outcome_equiv env
      (QExpr_Project left_select left_input)
      (QExpr_Project right_select right_input).
Proof.
intros env left_select right_select left_input right_input
  Houtputs Hleft_safe Hright_safe Hleft_closed Hright_closed Hbags
  Hleft_outcome Hright_outcome Herrors.
apply query_bag_closed_outcome_equiv_of_success_bags.
- exact Houtputs.
- now apply query_expr_project_bag_closed_safe.
- now apply query_expr_project_bag_closed_safe.
- exact Hleft_outcome.
- exact Hright_outcome.
- exact Hbags.
- exact Herrors.
Qed.

Lemma query_project_bag_congr :
  forall env select_list left right,
    bag_eq T left right ->
    bag_eq T
      (query_project_bag env select_list left)
      (query_project_bag env select_list right).
Proof.
intros env select_list left right Hbags.
unfold query_project_bag.
apply (RelationalAlgebraFacts.query_bag_map_congr (T := T)); [|exact Hbags].
intros first second Hequal.
apply projection_eq, env_t_eq_2; exact Hequal.
Qed.

(** Base tables have one possible successful bag modulo [bag_eq]. *)
Theorem query_table_success_bags_functional :
  forall env outputs table first second,
    success_bags env (QExpr_Table outputs table) first ->
    success_bags env (QExpr_Table outputs table) second ->
    bag_eq T first second.
Proof.
intros env outputs table first second Hfirst Hsecond.
unfold success_bags, query_success_bags, alpha in Hfirst, Hsecond.
destruct Hfirst as [first_rows [Hfirst_eval Hfirst_bag]].
destruct Hsecond as [second_rows [Hsecond_eval Hsecond_bag]].
apply eval_query_expr_table_success_iff in Hfirst_eval.
apply eval_query_expr_table_success_iff in Hsecond_eval.
apply query_same_rows_as_bag_iff_bag_eq in Hfirst_eval, Hfirst_bag,
  Hsecond_eval, Hsecond_bag.
eapply bag_eq_trans.
- eapply bag_eq_trans;
    [apply bag_eq_sym; exact Hfirst_bag | exact Hfirst_eval].
- apply bag_eq_sym.
  eapply bag_eq_trans;
    [apply bag_eq_sym; exact Hsecond_bag | exact Hsecond_eval].
Qed.

(** Exact safe equivalence for right distribution.  Possible-bag
    functionality is explicit because the target evaluates [left] twice. *)
Theorem query_expr_cross_join_union_right_equiv_safe :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    query_safe env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_safe env
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)) ->
    query_has_success env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_equiv env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
Proof.
intros env left first second Hsource_sort Htarget_sort Hfunctional
  Hsource_safe Htarget_safe Hsource_success.
apply query_bag_reset_equiv_of_success_bags_safe.
- reflexivity.
- reflexivity.
- reflexivity.
- now apply query_cross_join_union_right_success_bags.
- exact Hsource_safe.
- exact Htarget_safe.
- exact Hsource_success.
Qed.

Theorem query_expr_cross_join_union_right_outcome_equiv_safe :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall left_bag left_bag',
      success_bags env left left_bag ->
      success_bags env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    query_safe env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_safe env
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)) ->
    query_has_success env
      (QExpr_CrossJoin left (QExpr_Set Union first second)) ->
    query_outcome_equiv env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
Proof.
intros env left first second Hsource_sort Htarget_sort Hfunctional
  Hsource_safe Htarget_safe Hsource_success.
apply query_expr_equiv_implies_outcome_equiv.
now apply query_expr_cross_join_union_right_equiv_safe.
Qed.

(** A locally safe projection is congruent for fixed-environment,
    error-preserving query equivalence.  This local rule is intentionally
    separate from the global context rule: schema constraints commonly justify
    a child rewrite only for the current database instance. *)
Theorem query_expr_project_outcome_equiv_congr_safe :
  forall env select_list left right,
    query_outcome_equiv env left right ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_outcome_equiv env
      (QExpr_Project select_list left)
      (QExpr_Project select_list right).
Proof.
intros env select_list left right
  [_ [Hleft_outcome [Hright_outcome
    [Hforward [Hbackward Herrors]]]]] Hselect_safe.
apply query_expr_outcome_equiv_of_observations.
- reflexivity.
- destruct Hleft_outcome as [[left_rows|left_error] Hleft].
  + exists (SqlSuccess
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        left_rows)).
    rewrite <- (@project_rows_outcome_all_safe
      env select_list left_rows Hselect_safe).
    now apply EQuery_ProjectRows.
  + exists (SqlError left_error).
    now apply EQuery_ProjectChildError.
- destruct Hright_outcome as [[right_rows|right_error] Hright].
  + exists (SqlSuccess
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        right_rows)).
    rewrite <- (@project_rows_outcome_all_safe
      env select_list right_rows Hselect_safe).
    now apply EQuery_ProjectRows.
  + exists (SqlError right_error).
    now apply EQuery_ProjectChildError.
- intros left_output Hleft.
  apply eval_query_expr_project_success_iff in Hleft.
  destruct Hleft as [left_rows [Hleft Hproject_left]].
  rewrite (@project_rows_outcome_all_safe
    env select_list left_rows Hselect_safe) in Hproject_left.
  inversion Hproject_left; subst left_output.
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists
    (map
      (fun row =>
        projection T (env_t T env row) (@Select_List T select_list))
      right_rows); split.
  + apply eval_query_expr_project_success_iff.
    exists right_rows; split; [exact Hright |].
    now apply project_rows_outcome_all_safe.
  + now apply ordered_rows_equiv_map_projection.
- intros right_output Hright.
  apply eval_query_expr_project_success_iff in Hright.
  destruct Hright as [right_rows [Hright Hproject_right]].
  rewrite (@project_rows_outcome_all_safe
    env select_list right_rows Hselect_safe) in Hproject_right.
  inversion Hproject_right; subst right_output.
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists
    (map
      (fun row =>
        projection T (env_t T env row) (@Select_List T select_list))
      left_rows); split.
  + apply eval_query_expr_project_success_iff.
    exists left_rows; split; [exact Hleft |].
    now apply project_rows_outcome_all_safe.
  + now apply ordered_rows_equiv_map_projection.
- intro error; split; intro Herror.
  + apply eval_query_expr_project_error_iff in Herror.
    apply eval_query_expr_project_error_iff.
    destruct Herror as [Hchild | [rows [Hchild Hlocal]]].
    * left; now apply (proj1 (Herrors error)).
    * rewrite (@project_rows_outcome_all_safe
        env select_list rows Hselect_safe) in Hlocal.
      discriminate.
  + apply eval_query_expr_project_error_iff in Herror.
    apply eval_query_expr_project_error_iff.
    destruct Herror as [Hchild | [rows [Hchild Hlocal]]].
    * left; now apply (proj2 (Herrors error)).
    * rewrite (@project_rows_outcome_all_safe
        env select_list rows Hselect_safe) in Hlocal.
      discriminate.
Qed.

(** Successful projection observations determine their output list
    pointwise even when another input row could have raised an error.  This
    is deliberately weaker than global SELECT-list safety: the successful
    premise already records that every row actually projected cleanly. *)
Lemma project_rows_success_exact :
  forall env select_list rows output,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows = SqlSuccess output ->
    output =
      map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        rows.
Proof.
intros env select_list rows.
induction rows as [|row rows IH]; intro output; cbn.
- intro Houtput; now injection Houtput.
- destruct
    (@eval_select_list_runtime_error T symbol_runtime_error
      aggregate_runtime_error (env_t T env row) select_list)
    as [error |] eqn:Hrow; [discriminate |].
  destruct
    (@project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows)
    as [rest | error] eqn:Hrest; [|discriminate].
  intro Houtput; injection Houtput as Houtput; subst output.
  f_equal; exact (IH rest eq_refl).
Qed.

(** Possible-success-bag functionality is preserved by projection without a
    global runtime-safety premise.  Only successful observations are being
    compared, so [project_rows_success_exact] supplies the exact pointwise
    maps on both sides. *)
Theorem query_project_success_bags_functional :
  forall env select_list input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Project select_list input) first ->
      success_bags env (QExpr_Project select_list input) second ->
      bag_eq T first second.
Proof.
intros env select_list input Hfunctional first second Hfirst Hsecond.
unfold success_bags, query_success_bags, alpha in Hfirst, Hsecond.
destruct Hfirst as [first_rows [Hfirst_eval Hfirst_bag]].
destruct Hsecond as [second_rows [Hsecond_eval Hsecond_bag]].
apply eval_query_expr_project_success_iff in Hfirst_eval.
apply eval_query_expr_project_success_iff in Hsecond_eval.
destruct Hfirst_eval as
  [first_input [Hfirst_input Hfirst_project]].
destruct Hsecond_eval as
  [second_input [Hsecond_input Hsecond_project]].
apply project_rows_success_exact in Hfirst_project.
apply project_rows_success_exact in Hsecond_project.
subst first_rows second_rows.
assert (Hfirst_child : success_bags env input (rows_bag T first_input)).
{
  unfold success_bags, query_success_bags, alpha.
  exists first_input; split; [exact Hfirst_input | apply bag_eq_refl].
}
assert (Hsecond_child : success_bags env input (rows_bag T second_input)).
{
  unfold success_bags, query_success_bags, alpha.
  exists second_input; split; [exact Hsecond_input | apply bag_eq_refl].
}
assert (Hfirst_map :
  bag_eq T
    (rows_bag T
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        first_input))
    (query_project_bag env select_list (rows_bag T first_input))).
{
  apply query_same_rows_as_bag_iff_bag_eq.
  apply projected_rows_same_as_mapped_bag.
  apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl.
}
assert (Hsecond_map :
  bag_eq T
    (rows_bag T
      (map
        (fun row =>
          projection T (env_t T env row) (@Select_List T select_list))
        second_input))
    (query_project_bag env select_list (rows_bag T second_input))).
{
  apply query_same_rows_as_bag_iff_bag_eq.
  apply projected_rows_same_as_mapped_bag.
  apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl.
}
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst_bag |].
eapply bag_eq_trans; [exact Hfirst_map |].
eapply bag_eq_trans.
- apply query_project_bag_congr.
  exact (Hfunctional _ _ Hfirst_child Hsecond_child).
- eapply bag_eq_trans; [apply bag_eq_sym; exact Hsecond_map |].
  exact Hsecond_bag.
Qed.

(** Set operations preserve possible-success-bag functionality whenever both
    children do.  The statement covers all modeled set operations; no UNION
    associativity or duplicate-freedom premise is smuggled into the rule. *)
Theorem query_set_success_bags_functional :
  forall env operation left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Set operation left right) first ->
      success_bags env (QExpr_Set operation left right) second ->
      bag_eq T first second.
Proof.
intros env operation left right Hleft Hright first second Hfirst Hsecond.
apply (proj1
  (@query_set_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env operation left right first)) in Hfirst.
apply (proj1
  (@query_set_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env operation left right second)) in Hsecond.
unfold lift_possible_bag_binary in Hfirst, Hsecond.
destruct Hfirst as
  [left_first [right_first [Hleft_first [Hright_first Hfirst]]]].
destruct Hsecond as
  [left_second [right_second [Hleft_second [Hright_second Hsecond]]]].
unfold query_set_bag_relation, binary_bag_graph in Hfirst, Hsecond.
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst |].
eapply bag_eq_trans.
- apply query_set_bag_function_congr.
  + exact (Hleft _ _ Hleft_first Hleft_second).
  + exact (Hright _ _ Hright_first Hright_second).
- exact Hsecond.
Qed.

(** CROSS JOIN preserves possible-success-bag functionality compositionally.
    Multiplicities are retained through [query_cross_join_bag_congr]. *)
Theorem query_cross_join_success_bags_functional :
  forall env left right,
    (forall first second,
      success_bags env left first ->
      success_bags env left second ->
      bag_eq T first second) ->
    (forall first second,
      success_bags env right first ->
      success_bags env right second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_CrossJoin left right) first ->
      success_bags env (QExpr_CrossJoin left right) second ->
      bag_eq T first second.
Proof.
intros env left right Hleft Hright first second Hfirst Hsecond.
apply (proj1
  (@query_cross_join_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env left right first)) in Hfirst.
apply (proj1
  (@query_cross_join_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env left right second)) in Hsecond.
unfold lift_possible_bag_binary in Hfirst, Hsecond.
destruct Hfirst as
  [left_first [right_first [Hleft_first [Hright_first Hfirst]]]].
destruct Hsecond as
  [left_second [right_second [Hleft_second [Hright_second Hsecond]]]].
unfold query_cross_join_bag_relation, binary_bag_graph in Hfirst, Hsecond.
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst |].
eapply bag_eq_trans.
- apply query_cross_join_bag_congr.
  + exact (Hleft _ _ Hleft_first Hleft_second).
  + exact (Hright _ _ Hright_first Hright_second).
- exact Hsecond.
Qed.

(** DISTINCT preserves possible-success-bag functionality without assuming
    that it is inert: both observations apply the same duplicate-elimination
    function to equivalent child bags. *)
Theorem query_distinct_success_bags_functional :
  forall env input,
    (forall first second,
      success_bags env input first ->
      success_bags env input second ->
      bag_eq T first second) ->
    forall first second,
      success_bags env (QExpr_Distinct input) first ->
      success_bags env (QExpr_Distinct input) second ->
      bag_eq T first second.
Proof.
intros env input Hinput first second Hfirst Hsecond.
apply (proj1
  (@query_distinct_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env input first)) in Hfirst.
apply (proj1
  (@query_distinct_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env input second)) in Hsecond.
unfold lift_possible_bag_unary in Hfirst, Hsecond.
destruct Hfirst as [input_first [Hinput_first Hfirst]].
destruct Hsecond as [input_second [Hinput_second Hsecond]].
unfold query_distinct_bag_relation, unary_bag_graph in Hfirst, Hsecond.
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst |].
eapply bag_eq_trans.
- apply query_distinct_bag_congr.
  exact (Hinput _ _ Hinput_first Hinput_second).
- exact Hsecond.
Qed.
End ExactQueries.
