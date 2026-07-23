(************************************************************************************)
(** Reusable facts for FormalSQL's exact ordered query-outcome semantics.          **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Arith PeanoNat NArith Lia Sorting.Permutation.
From SQLFS Require Import
  ListPermut OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
  SqlAlgebra SqlOutcome SqlErrorSemantics SqlOrder SqlListFacts SqlBagAbstraction SqlQuerySyntax
  SqlQuerySemantics SqlQueryFacts SqlQueryContexts.
From Logos.FormalSQL Require Import RelationalAlgebraFacts.

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
Variable contains_nulls : tuple T -> bool.
Variable symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value T) ->
  option sql_runtime_error.
Variable value_is_null : value T -> bool.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_equiv :=
  (@query_expr_equiv T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_outcome_equiv :=
  (@query_expr_outcome_equiv T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_global_typed_outcome_equiv :=
  (@query_expr_global_typed_outcome_equiv T relname basesort instance unknown
    contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_safe :=
  (query_expr_runtime_safe basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation query_has_success :=
  (query_expr_has_success basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

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
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    (exists outcome, eval_query env left outcome) ->
    query_outcome_equiv env left right.
Proof.
intros env left right [Houtputs Heval] Houtcome.
apply query_expr_outcome_equiv_of_eval_iff; [exact Houtputs | exact Houtcome |].
exact (Heval env).
Qed.

(** WHERE predicates need preserve only runtime errors and the TRUE/non-TRUE
    acceptance decision.  FALSE and UNKNOWN may differ without changing the
    filtered relation. *)
Lemma query_expr_filter_outcome_equiv_of_global_acceptance :
  forall env left_formula right_formula input,
    @formula_expr_global_filter_outcome_equiv T relname basesort instance
      unknown contains_nulls symbol_runtime_error aggregate_runtime_error
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
      unknown contains_nulls symbol_runtime_error aggregate_runtime_error
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

(** A safe deterministic bag evaluator always supplies the canonical ordered
    representative required by the exact observation layer. *)
Lemma query_expr_bag_has_success_of_runtime_error_none :
  forall env outputs query,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    query_has_success env (QExpr_Bag outputs query).
Proof.
intros env outputs query Hsafe.
exists
  (Febag.elements (Fecol.CBag (CTuple T))
    (@SqlAlgebra.eval_query T relname basesort instance unknown contains_nulls
      env query)).
apply eval_query_expr_bag_success_iff.
exists (@SqlAlgebra.eval_query T relname basesort instance unknown contains_nulls
  env query).
split.
- unfold eval_query_outcome; now rewrite Hsafe.
- unfold query_same_rows_as_bag, query_rows_bag.
  apply Febag.elements_mk_bag.
Qed.

(** The same bag-level safety fact excludes every exact-layer error outcome. *)
Lemma query_expr_bag_runtime_safe_of_runtime_error_none :
  forall env outputs query,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    query_safe env (QExpr_Bag outputs query).
Proof.
intros env outputs query Hsafe error Herror.
apply eval_query_expr_bag_error_iff in Herror.
unfold eval_query_outcome in Herror.
now rewrite Hsafe in Herror.
Qed.

Corollary query_expr_bag_safe_success_of_runtime_error_none :
  forall env outputs query,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env query = None ->
    query_safe env (QExpr_Bag outputs query) /\
    query_has_success env (QExpr_Bag outputs query).
Proof.
intros env outputs query Hsafe; split.
- now apply query_expr_bag_runtime_safe_of_runtime_error_none.
- now apply query_expr_bag_has_success_of_runtime_error_none.
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
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null left right ->
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null right left.
Proof.
intros left right Hequiv env outcome.
destruct (Hequiv env outcome) as [Hforward Hbackward].
split; [exact Hbackward | exact Hforward].
Qed.

Lemma query_expr_global_outcome_equiv_trans :
  forall first second third,
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null first second ->
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null second third ->
    query_expr_global_outcome_equiv basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null first third.
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
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null left right ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null right left.
Proof.
intros left right [Houtputs Hequiv].
split; [now symmetry |].
now apply query_expr_global_outcome_equiv_sym.
Qed.

Lemma query_expr_global_typed_outcome_equiv_trans :
  forall first second third,
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
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
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null first second ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
      value_is_null second third ->
    query_expr_global_typed_outcome_equiv basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error
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
      @eval_filter_rows_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null env formula input_rows (SqlSuccess output).
Proof.
intros env formula input output; split; intro Heval.
- inversion Heval; subst.
  exists input_rows; split; assumption.
- destruct Heval as [input_rows [Hinput Hfilter]].
  eapply EQuery_FilterRows; [exact Hinput | exact Hfilter].
Qed.

Lemma eval_query_expr_filter_error_iff :
  forall env formula input error,
    eval_query env (QExpr_Filter formula input) (SqlError error) <->
    eval_query env input (SqlError error) \/
    exists input_rows,
      eval_query env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
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
apply query_bag_effect_equiv_of_success_bags_safe.
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
apply query_bag_effect_equiv_of_success_bags_safe.
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
        @eval_formula_expr_outcome T relname basesort instance unknown
          contains_nulls symbol_runtime_error aggregate_runtime_error
          value_is_null (env_t T env row) formula outcome <->
        outcome = SqlSuccess (Bool.true (B T))) ->
    forall outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
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
      @eval_formula_expr_outcome T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
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
          @eval_formula_expr_outcome T relname basesort instance unknown
            contains_nulls symbol_runtime_error aggregate_runtime_error
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

Lemma first_runtime_error_all_none :
  forall (A : Type) (check : A -> option sql_runtime_error) values,
    (forall value, In value values -> check value = None) ->
    first_runtime_error check values = None.
Proof.
intros A check values Hnone.
induction values as [|value values IH]; cbn.
- reflexivity.
- rewrite Hnone by now left.
  rewrite IH; [reflexivity |].
  intros item Hin; apply Hnone; now right.
Qed.

Lemma bag_projection_runtime_error_none :
  forall env select_list input,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env input = None ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env
      (@Q_Pi T relname select_list input) = None.
Proof.
intros env select_list input Hinput Hselect.
cbn [eval_query_runtime_error].
rewrite Hinput; cbn.
apply first_runtime_error_all_none.
intros row _; apply Hselect.
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

(** The exact order-preserving projection over a permutation-closed compact
    bag subtree agrees with compact [Q_Pi] whenever neither the child nor any
    projected row can fail.  The proof does not assume projection injectivity:
    [mapped_bag_rows_have_projection_preimage] preserves each occurrence. *)
Theorem query_expr_project_bag_equiv_safe :
  forall env input_outputs select_list input,
    @eval_query_runtime_error T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error env input = None ->
    (forall row,
      @eval_select_list_runtime_error T symbol_runtime_error
        aggregate_runtime_error (env_t T env row) select_list = None) ->
    query_equiv env
      (QExpr_Project select_list (QExpr_Bag input_outputs input))
      (QExpr_Bag (select_list_outputs select_list)
        (@Q_Pi T relname select_list input)).
Proof.
intros env input_outputs select_list input Hinput_safe Hselect_safe.
pose proof (bag_projection_runtime_error_none
  env select_list input Hinput_safe Hselect_safe) as Hprojection_safe.
set (input_bag :=
  @SqlAlgebra.eval_query T relname basesort instance unknown contains_nulls
    env input).
set (project_row := fun row =>
  projection T (env_t T env row) (@Select_List T select_list)).
apply query_expr_equiv_of_ordered_observations.
- reflexivity.
- exists (map project_row
    (Febag.elements (Fecol.CBag (CTuple T)) input_bag)).
  unfold project_row.
  pose proof (@project_rows_outcome_all_safe env select_list
    (Febag.elements (Fecol.CBag (CTuple T)) input_bag)
    Hselect_safe) as Hproject.
  assert (Hchild :
    eval_query env (QExpr_Bag input_outputs input)
      (SqlSuccess
        (Febag.elements (Fecol.CBag (CTuple T)) input_bag))).
  {
    eapply EQuery_BagSuccess with (bag := input_bag).
    - unfold eval_query_outcome; rewrite Hinput_safe; reflexivity.
    - apply query_elements_same_rows_as_bag.
  }
  assert (Heval :
    eval_query env (QExpr_Project select_list (QExpr_Bag input_outputs input))
      (@project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list
        (Febag.elements (Fecol.CBag (CTuple T)) input_bag))).
  { now apply EQuery_ProjectRows. }
  rewrite Hproject in Heval; exact Heval.
- intros error Herror.
  apply eval_query_expr_project_error_iff in Herror.
  destruct Herror as [Hchild | [rows [Hchild Hlocal]]].
  + apply eval_query_expr_bag_error_iff in Hchild.
    unfold eval_query_outcome in Hchild; rewrite Hinput_safe in Hchild.
    discriminate.
  + rewrite (@project_rows_outcome_all_safe
      env select_list rows Hselect_safe) in Hlocal.
    discriminate.
- intros error Herror.
  apply eval_query_expr_bag_error_iff in Herror.
  unfold eval_query_outcome in Herror; rewrite Hprojection_safe in Herror.
  discriminate.
- intros left_rows Hleft.
  apply eval_query_expr_project_success_iff in Hleft.
  destruct Hleft as [input_rows [Hchild Hproject]].
  apply eval_query_expr_bag_success_iff in Hchild.
  destruct Hchild as [observed_bag [Houtcome Hinput_rows]].
  unfold eval_query_outcome in Houtcome; rewrite Hinput_safe in Houtcome.
  inversion Houtcome; subst observed_bag.
  rewrite (@project_rows_outcome_all_safe
    env select_list input_rows Hselect_safe) in Hproject.
  inversion Hproject; subst left_rows.
  exists (map project_row input_rows); split.
  + apply eval_query_expr_bag_success_iff.
    exists (Febag.map (Fecol.CBag (CTuple T)) (Fecol.CBag (CTuple T))
      project_row input_bag); split.
    * unfold eval_query_outcome; rewrite Hprojection_safe.
      rewrite (@eval_query_unfold T relname basesort instance unknown
        contains_nulls env (@Q_Pi T relname select_list input)).
      reflexivity.
    * now apply projected_rows_same_as_mapped_bag.
  + apply ordered_rows_equiv_refl.
- intros right_rows Hright.
  apply eval_query_expr_bag_success_iff in Hright.
  destruct Hright as [observed_bag [Houtcome Hright_rows]].
  unfold eval_query_outcome in Houtcome; rewrite Hprojection_safe in Houtcome.
  rewrite (@eval_query_unfold T relname basesort instance unknown
    contains_nulls env (@Q_Pi T relname select_list input)) in Houtcome.
  inversion Houtcome; subst observed_bag.
  destruct (mapped_bag_rows_have_projection_preimage
    env select_list input_bag (output := right_rows) Hright_rows)
    as [input_rows [Hinput_rows Hordered]].
  exists (map project_row input_rows); split.
  + unfold project_row.
    pose proof (@project_rows_outcome_all_safe
      env select_list input_rows Hselect_safe) as Hproject.
    assert (Hchild :
      eval_query env (QExpr_Bag input_outputs input)
        (SqlSuccess input_rows)).
    {
      eapply EQuery_BagSuccess with (bag := input_bag).
      - unfold eval_query_outcome; rewrite Hinput_safe; reflexivity.
      - exact Hinput_rows.
    }
    assert (Heval :
      eval_query env
        (QExpr_Project select_list (QExpr_Bag input_outputs input))
        (@project_rows_outcome T symbol_runtime_error aggregate_runtime_error
          env select_list input_rows)).
    { now apply EQuery_ProjectRows. }
    rewrite Hproject in Heval; exact Heval.
  + now apply ordered_rows_equiv_sym.
Qed.

End ExactQueries.
