(** Reusable inversion and composition facts for predicate subqueries. *)

Set Implicit Arguments.

From Stdlib Require Import Bool List Sorting.Permutation.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula FTuples
  ListPermut OrderedSet SqlErrorSemantics SqlOutcome
  SqlBagAbstraction SqlQueryContexts SqlQueryFacts SqlQuerySemantics SqlQuerySyntax
  SqlQueryWellFormed.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts RelationalAlgebraFacts ScalarPredicateFacts.

Import ListNotations.
Import Tuple.

(** Three-valued quantifier results.  These state the exact UNKNOWN boundary
    without collapsing UNKNOWN into FALSE as a WHERE consumer would. *)

Lemma interp_exists_quant_not_true_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    Bool.existsb Bool3 interpretation values <> true3 <->
    Forall (fun value => interpretation value <> true3) values.
Proof.
  intros A interpretation values; split.
  - intro Hresult; rewrite Forall_forall.
    intros value Hvalue Htrue; apply Hresult.
    apply (proj2 (Bool.existsb_exists_true Bool3 interpretation values)).
    exists value; now split.
  - intros Hall Hresult; rewrite Forall_forall in Hall.
    apply (proj1 (Bool.existsb_exists_true Bool3
      interpretation values)) in Hresult.
    destruct Hresult as [value [Hvalue Htrue]].
    exact (Hall value Hvalue Htrue).
Qed.

Lemma interp_forall_quant_not_false_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    Bool.forallb Bool3 interpretation values <> false3 <->
    Forall (fun value => interpretation value <> false3) values.
Proof.
  intros A interpretation values; split.
  - intro Hresult; rewrite Forall_forall.
    intros value Hvalue Hfalse; apply Hresult.
    apply (proj2 (Bool.forallb_forall_false Bool3
      interpretation values)).
    exists value; now split.
  - intros Hall Hresult; rewrite Forall_forall in Hall.
    apply (proj1 (Bool.forallb_forall_false Bool3
      interpretation values)) in Hresult.
    destruct Hresult as [value [Hvalue Hfalse]].
    exact (Hall value Hvalue Hfalse).
Qed.

Lemma interp_exists_quant_unknown_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    interp_quant Bool3 Exists_F interpretation values = unknown3 <->
    Exists (fun value => interpretation value = unknown3) values /\
    Forall (fun value => interpretation value <> true3) values.
Proof.
  intros A interpretation values; induction values as [|head tail IH].
  - cbn [interp_quant]; split.
    + discriminate.
    + intros [Hexists _]; inversion Hexists.
  - change
      (orb3 (interpretation head)
        (Bool.existsb Bool3 interpretation tail) = unknown3 <->
       Exists (fun value => interpretation value = unknown3) (head :: tail) /\
       Forall (fun value => interpretation value <> true3) (head :: tail)).
    rewrite orb3_unknown_iff, IH.
    rewrite interp_exists_quant_not_true_iff.
    split.
    + intros [Hunknown [Hhead_safe Htail_safe]].
      destruct Hunknown as [Hhead | [Htail Htail_safe']].
      * split.
        -- constructor; exact Hhead.
        -- constructor; assumption.
      * split.
        -- now constructor 2.
        -- constructor; assumption.
    + intros [Hexists Hall].
      inversion Hall as [|? ? Hhead_safe Htail_safe]; subst.
      inversion Hexists as [? ? Hhead | ? ? Htail]; subst.
      * split.
        -- left; exact Hhead.
        -- now split.
      * split.
        -- right; now split.
        -- now split.
Qed.

Lemma interp_forall_quant_unknown_iff :
  forall (A : Type) (interpretation : A -> bool3) values,
    interp_quant Bool3 Forall_F interpretation values = unknown3 <->
    Exists (fun value => interpretation value = unknown3) values /\
    Forall (fun value => interpretation value <> false3) values.
Proof.
  intros A interpretation values; induction values as [|head tail IH].
  - cbn [interp_quant]; split.
    + discriminate.
    + intros [Hexists _]; inversion Hexists.
  - change
      (andb3 (interpretation head)
        (Bool.forallb Bool3 interpretation tail) = unknown3 <->
       Exists (fun value => interpretation value = unknown3) (head :: tail) /\
       Forall (fun value => interpretation value <> false3) (head :: tail)).
    rewrite andb3_unknown_iff, IH.
    rewrite interp_forall_quant_not_false_iff.
    split.
    + intros [Hunknown [Hhead_safe Htail_safe]].
      destruct Hunknown as [Hhead | [Htail Htail_safe']].
      * split.
        -- constructor; exact Hhead.
        -- constructor; assumption.
      * split.
        -- now constructor 2.
        -- constructor; assumption.
    + intros [Hexists Hall].
      inversion Hall as [|? ? Hhead_safe Htail_safe]; subst.
      inversion Hexists as [? ? Hhead | ? ? Htail]; subst.
      * split.
        -- left; exact Hhead.
        -- now split.
      * split.
        -- right; now split.
        -- now split.
Qed.

Lemma interp_quant_empty : forall (B : Bool.Rcd) which_quantifier
    (A : Type) (interpretation : A -> Bool.b B),
  interp_quant B which_quantifier interpretation [] =
  match which_quantifier with
  | Forall_F => Bool.true B
  | Exists_F => Bool.false B
  end.
Proof.
  intros B [|] A interpretation; reflexivity.
Qed.

Definition rows_empty_decision {A : Type} (rows : list A) : bool :=
  match rows with
  | nil => true
  | _ :: _ => false
  end.

(** Relational permutation preserves emptiness even when the two lists have
    different element types.  No equality or functionality property of [R]
    is needed for this shape-only observation. *)
Lemma rows_empty_decision_rel_permut :
  forall (A B : Type) (R : A -> B -> Prop) left right,
    _permut R left right ->
    rows_empty_decision left = rows_empty_decision right.
Proof.
  intros A B R left right Hpermut.
  induction Hpermut as [|left_row right_row tail prefix suffix
    Hrelated Htail IH].
  - reflexivity.
  - destruct prefix; reflexivity.
Qed.

Corollary rows_empty_decision_oeset_permut :
  forall (A : Type) (order : Oeset.Rcd A) left right,
    Oeset.permut order left right ->
    rows_empty_decision left = rows_empty_decision right.
Proof.
  intros A order left right Hpermut.
  now apply rows_empty_decision_rel_permut with
    (R := fun first second => Oeset.compare order first second = Eq).
Qed.

(** The ordinary list [existsb] respects a relational permutation only when
    its predicates are proper for the relation.  The heterogeneous statement
    makes that obligation explicit instead of silently replacing [R] by
    Leibniz equality. *)
Lemma existsb_rel_permut :
  forall (A B : Type) (R : A -> B -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      left_predicate left_value = right_predicate right_value) ->
    _permut R left right ->
    existsb left_predicate left = existsb right_predicate right.
Proof.
  intros A B R left_predicate right_predicate left right Hproper Hpermut.
  induction Hpermut as [|left_value right_value tail prefix suffix
    Hrelated Htail IH].
  - reflexivity.
  - cbn [existsb].
    rewrite (Hproper left_value right_value Hrelated), IH.
    rewrite 2 existsb_app.
    cbn [existsb].
    rewrite Bool.Bool.orb_assoc.
    rewrite (Bool.Bool.orb_comm
      (right_predicate right_value) (existsb right_predicate prefix)).
    symmetry; apply Bool.Bool.orb_assoc.
Qed.

(** Boolean existence depends on relational support, not multiplicity.  This
    is intentionally weaker than permutation: it is suitable only after a
    consumer has reduced observations to an existence decision. *)
Lemma existsb_support_rel :
  forall (A B : Type) (R : A -> B -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      left_predicate left_value = right_predicate right_value) ->
    list_support_rel R left right ->
    existsb left_predicate left = existsb right_predicate right.
Proof.
  intros A B R left_predicate right_predicate left right
    Hproper [Hforward Hbackward].
  destruct (existsb left_predicate left) eqn:Hleft,
    (existsb right_predicate right) eqn:Hright; try reflexivity.
  - apply existsb_exists in Hleft.
    destruct Hleft as [left_value [Hleft_value Haccepted]].
    destruct (Hforward left_value Hleft_value) as
      [right_value [Hright_value Hrelated]].
    assert (Hright_accepted : right_predicate right_value = true).
    { rewrite <- (Hproper left_value right_value Hrelated).
      exact Haccepted. }
    assert (Hexists : existsb right_predicate right = true).
    { apply existsb_exists.
      exists right_value; now split. }
    congruence.
  - apply existsb_exists in Hright.
    destruct Hright as [right_value [Hright_value Haccepted]].
    destruct (Hbackward right_value Hright_value) as
      [left_value [Hleft_value Hrelated]].
    assert (Hleft_accepted : left_predicate left_value = true).
    { rewrite (Hproper left_value right_value Hrelated).
      exact Haccepted. }
    assert (Hexists : existsb left_predicate left = true).
    { apply existsb_exists.
      exists left_value; now split. }
    congruence.
Qed.

Section PredicateSubquerySemantics.

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

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_scalar_value :=
  (@eval_scalar_value_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_scalar_values :=
  (@eval_scalar_values_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_scalar_operands :=
  (@eval_scalar_boolean_operands_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** Exact three-valued scalar observation at one environment.  This is
    deliberately stronger than [scalar_expr_acceptance_exact_at]: a consumer that
    applies SQL [NOT] must distinguish FALSE from UNKNOWN even though both are
    rejected by a filter.  The explicit no-error component also prevents an
    apparent truth equality from hiding a reachable runtime failure. *)
Definition scalar_expr_truth_exact_at
    (env : Env.env T)
    (expression : scalar_expr T relname ScalarResultBoolean)
    (expected : Bool.b (B T)) : Prop :=
  eval_scalar_boolean env expression (SqlSuccess expected) /\
  (forall truth,
    eval_scalar_boolean env expression (SqlSuccess truth) -> truth = expected) /\
  (forall error, ~ eval_scalar_boolean env expression (SqlError error)).

Lemma scalar_expr_truth_exact_acceptance_exact :
  forall env formula expected,
    scalar_expr_truth_exact_at env formula expected ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env formula
      (Bool.is_true (B T) expected).
Proof.
intros env formula expected [Hexists [Hsuccess Herror]].
unfold scalar_expr_acceptance_exact_at.
split.
- exists expected; now split.
- split.
  + intros truth Htruth; now rewrite (Hsuccess truth Htruth).
  + exact Herror.
Qed.

(** Exact truth, rather than mere filter acceptance, composes through SQL
    negation.  In particular, an UNKNOWN child remains UNKNOWN. *)
Theorem scalar_expr_not_truth_exact :
  forall env formula expected,
    scalar_expr_truth_exact_at env formula expected ->
    scalar_expr_truth_exact_at env (SExpr_Not formula)
      (Bool.negb (B T) expected).
Proof.
intros env formula expected [Hexists [Hsuccess Herror]].
unfold scalar_expr_truth_exact_at.
split.
- now apply EScalar_NotSuccess.
- split.
  + intros truth Htruth; inversion Htruth; subst.
    now rewrite (Hsuccess _ H1).
  + intros error Hnot_error; inversion Hnot_error; subst.
    eapply Herror; eassumption.
Qed.

Corollary scalar_expr_not_acceptance_exact :
  forall env formula expected,
    scalar_expr_truth_exact_at env formula expected ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Not formula)
      (Bool.is_true (B T) (Bool.negb (B T) expected)).
Proof.
intros env formula expected Hexact.
apply scalar_expr_truth_exact_acceptance_exact.
now apply scalar_expr_not_truth_exact.
Qed.

(** Raw evaluation-relation equality for one expression at two correlated
    environments.  Unlike [query_expr_outcome_equiv], the query relation below
    deliberately asks for the same concrete successful row list; constructor
    lemmas that cannot justify that strength must expose an extra premise. *)
Definition scalar_expr_env_outcome_equiv
    {kind : scalar_result_kind} (left_env right_env : Env.env T)
    (expression : scalar_expr T relname kind) : Prop :=
  match kind as result_kind return
      scalar_expr T relname result_kind -> Prop with
  | ScalarResultValue => fun value_expression => forall outcome,
      eval_scalar_value left_env value_expression outcome <->
      eval_scalar_value right_env value_expression outcome
  | ScalarResultBoolean => fun boolean_expression => forall outcome,
      eval_scalar_boolean left_env boolean_expression outcome <->
      eval_scalar_boolean right_env boolean_expression outcome
  end expression.

Definition query_expr_env_outcome_equiv
    (left_env right_env : Env.env T) (query : query_expr T relname) : Prop :=
  forall outcome,
    eval_query left_env query outcome <->
    eval_query right_env query outcome.

Lemma eval_scalar_boolean_operands_env_congr :
  forall left_env right_env operation expressions,
    Forall
      (scalar_expr_env_outcome_equiv left_env right_env) expressions ->
    forall outcome,
      eval_scalar_operands left_env operation expressions outcome <->
      eval_scalar_operands right_env operation expressions outcome.
Proof.
intros left_env right_env operation expressions Hequiv.
induction Hequiv as [|expression expressions Hexpression _ IH];
  intro outcome; split; intro Heval; inversion Heval; subst.
- constructor.
- constructor.
- apply EScalarBooleanOperands_HeadError.
  now apply (proj1 (Hexpression _)).
- eapply EScalarBooleanOperands_HeadDecides.
  + eapply (proj1 (Hexpression _)); eassumption.
  + eassumption.
- eapply EScalarBooleanOperands_Continue.
  + eapply (proj1 (Hexpression _)); eassumption.
  + eassumption.
  + now apply (proj1 (IH _)).
- apply EScalarBooleanOperands_HeadError.
  now apply (proj2 (Hexpression _)).
- eapply EScalarBooleanOperands_HeadDecides.
  + eapply (proj2 (Hexpression _)); eassumption.
  + eassumption.
- eapply EScalarBooleanOperands_Continue.
  + eapply (proj2 (Hexpression _)); eassumption.
  + eassumption.
  + now apply (proj2 (IH _)).
Qed.

(** A flattened Boolean expression preserves the exact scheduled operand
    relation.  The schedule is shared across both environments, so this fact
    retains every left/right-first error outcome instead of assuming a fixed
    conjunction order. *)
Lemma scalar_expr_conj_list_env_congr :
  forall left_env right_env site_rows operation expressions,
    Forall
      (scalar_expr_env_outcome_equiv left_env right_env) expressions ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_ConjList site_rows operation expressions).
Proof.
intros left_env right_env site_rows operation expressions Hequiv outcome.
assert (Hscheduled :
  Forall (scalar_expr_env_outcome_equiv left_env right_env)
    (schedule_boolean_operands boolean_schedule site_rows expressions)).
{
  rewrite Forall_forall in Hequiv |- *.
  intros expression Hin.
  apply Hequiv.
  eapply Permutation_in; [|exact Hin].
  apply Permutation_sym, schedule_boolean_operands_permutation.
}
split; intro Heval; inversion Heval; subst; apply EScalar_ConjList.
- now apply (proj1
    (@eval_scalar_boolean_operands_env_congr
      left_env right_env operation
      (schedule_boolean_operands boolean_schedule site_rows expressions)
      Hscheduled _)).
- now apply (proj2
    (@eval_scalar_boolean_operands_env_congr
      left_env right_env operation
      (schedule_boolean_operands boolean_schedule site_rows expressions)
      Hscheduled _)).
Qed.

Lemma scalar_expr_not_env_congr :
  forall left_env right_env formula,
    scalar_expr_env_outcome_equiv left_env right_env formula ->
    scalar_expr_env_outcome_equiv left_env right_env (SExpr_Not formula).
Proof.
  intros left_env right_env formula Hformula outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EScalar_NotError. now apply (proj1 (Hformula _)).
  - apply EScalar_NotSuccess. now apply (proj1 (Hformula _)).
  - apply EScalar_NotError. now apply (proj2 (Hformula _)).
  - apply EScalar_NotSuccess. now apply (proj2 (Hformula _)).
Qed.

Lemma scalar_expr_pred_env_congr_safe :
  forall left_env right_env predicate arguments,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_Pred predicate arguments).
Proof.
intros left_env right_env predicate arguments Harguments outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_PredArgumentsError.
  now apply (proj1 (Harguments _)).
- apply EScalar_PredSuccess.
  now apply (proj1 (Harguments _)).
- apply EScalar_PredArgumentsError.
  now apply (proj2 (Harguments _)).
- apply EScalar_PredSuccess.
  now apply (proj2 (Harguments _)).
Qed.

Lemma query_expr_table_env_congr :
  forall left_env right_env attributes relation,
    query_expr_env_outcome_equiv left_env right_env
      (@QExpr_Table T relname attributes relation).
Proof.
  intros left_env right_env attributes relation outcome.
  split; intro Heval; inversion Heval; subst; constructor; assumption.
Qed.

Lemma query_expr_cross_join_env_congr :
  forall left_env right_env left right,
    query_expr_env_outcome_equiv left_env right_env left ->
    query_expr_env_outcome_equiv left_env right_env right ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_CrossJoin left right).
Proof.
  intros left_env right_env left right Hleft Hright outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EQuery_CrossJoinLeftError. now apply (proj1 (Hleft _)).
  - eapply EQuery_CrossJoinRightError.
    + match goal with
      | H : eval_query left_env left _ |- _ =>
          exact (proj1 (Hleft _) H)
      end.
    + match goal with
      | H : eval_query left_env right _ |- _ =>
          exact (proj1 (Hright _) H)
      end.
  - eapply EQuery_CrossJoinSuccess.
    + match goal with
      | H : eval_query left_env left _ |- _ =>
          exact (proj1 (Hleft _) H)
      end.
    + match goal with
      | H : eval_query left_env right _ |- _ =>
          exact (proj1 (Hright _) H)
      end.
    + eassumption.
  - apply EQuery_CrossJoinLeftError. now apply (proj2 (Hleft _)).
  - eapply EQuery_CrossJoinRightError.
    + match goal with
      | H : eval_query right_env left _ |- _ =>
          exact (proj2 (Hleft _) H)
      end.
    + match goal with
      | H : eval_query right_env right _ |- _ =>
          exact (proj2 (Hright _) H)
      end.
  - eapply EQuery_CrossJoinSuccess.
    + match goal with
      | H : eval_query right_env left _ |- _ =>
          exact (proj2 (Hleft _) H)
      end.
    + match goal with
      | H : eval_query right_env right _ |- _ =>
          exact (proj2 (Hright _) H)
      end.
    + eassumption.
Qed.

Lemma eval_filter_rows_env_congr :
  forall left_env right_env formula,
    (forall row,
      scalar_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    forall rows outcome,
      eval_filter_rows left_env formula rows outcome <->
      eval_filter_rows right_env formula rows outcome.
Proof.
  intros left_env right_env formula Hformula rows.
  induction rows as [|row rows IH]; intro outcome.
  - split; intro Heval; inversion Heval; constructor.
  - split; intro Heval; inversion Heval; subst.
    + apply EFilterRows_HeadError. now apply (proj1 (Hformula row _)).
    + apply EFilterRows_Cons.
      * now apply (proj1 (Hformula row _)).
      * now apply (proj1 (IH _)).
    + apply EFilterRows_HeadError. now apply (proj2 (Hformula row _)).
    + apply EFilterRows_Cons.
      * now apply (proj2 (Hformula row _)).
      * now apply (proj2 (IH _)).
Qed.

Lemma query_expr_filter_env_congr :
  forall left_env right_env formula input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      scalar_expr_env_outcome_equiv
        (Env.env_t T left_env row) (Env.env_t T right_env row) formula) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Filter formula input).
Proof.
  intros left_env right_env formula input Hinput Hformula outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EQuery_FilterChildError. now apply (proj1 (Hinput _)).
  - eapply EQuery_FilterRows.
    + match goal with
      | H : eval_query left_env input _ |- _ =>
          exact (proj1 (Hinput _) H)
      end.
    + eapply (proj1
        (eval_filter_rows_env_congr
          (left_env := left_env) (right_env := right_env)
          (formula := formula) Hformula _ _)).
      eassumption.
  - apply EQuery_FilterChildError. now apply (proj2 (Hinput _)).
  - eapply EQuery_FilterRows.
    + match goal with
      | H : eval_query right_env input _ |- _ =>
          exact (proj2 (Hinput _) H)
      end.
    + eapply (proj2
        (eval_filter_rows_env_congr
          (left_env := left_env) (right_env := right_env)
          (formula := formula) Hformula _ _)).
      eassumption.
Qed.

Definition quantified_row_truth
    (which_predicate : predicate T) (values : list (value T))
    (subquery : query_expr T relname)
    (row : tuple T) : Bool.b (B T) :=
  interp_predicate T which_predicate
    (values ++
      @query_row_output_values T (query_expr_outputs subquery) row).

Definition quantified_rows_truth
    (which_quantifier : quantifier) (which_predicate : predicate T)
    (values : list (value T))
    (subquery : query_expr T relname) (rows : list (tuple T)) : Bool.b (B T) :=
  interp_quant (B T) which_quantifier
    (quantified_row_truth which_predicate values subquery)
    (query_canonical_rows rows).

(** A quantified predicate observes a successful child only through its
    finite bag of rows and the pointwise truth function.  The support property
    allows a caller to state exactly the schema/presence facts under which that
    truth function respects semantic tuple equality. *)
Theorem quantified_rows_truth_congr_of_bag_eq :
  forall which_quantifier which_predicate values subquery left right
      (property : tuple T -> Prop),
    @bag_eq T (query_rows_bag left) (query_rows_bag right) ->
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      (property first <-> property second)) ->
    Forall property (query_canonical_rows left) ->
    (forall left_row right_row,
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      property left_row ->
      quantified_row_truth which_predicate values subquery left_row =
      quantified_row_truth which_predicate values subquery right_row) ->
    quantified_rows_truth which_quantifier which_predicate values
      subquery left =
    quantified_rows_truth which_quantifier which_predicate values
      subquery right.
Proof.
  intros which_quantifier which_predicate values subquery
    left right property Hbags Hproperty Hleft Hrow.
  unfold quantified_rows_truth.
  apply (Formula.interp_quant_eq (B T) (OTuple T)).
  - eapply query_same_rows_as_bag_permut_between with
      (bag := query_rows_bag left).
    + apply query_canonical_rows_same_as_bag.
      apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl.
    + eapply query_same_rows_as_bag_bag_transport.
      * apply query_canonical_rows_same_as_bag.
        apply query_same_rows_as_bag_iff_bag_eq, bag_eq_refl.
      * exact (bag_eq_sym Hbags).
  - intros left_row right_row Hmember Hequal.
    apply Hrow; [exact Hequal|].
    rewrite Forall_forall in Hleft.
    destruct (proj1
      (@Oeset.mem_bool_true_iff (tuple T) (OTuple T)
        left_row (query_canonical_rows left)) Hmember)
      as [member [Hrelated Hin]].
    apply (proj2 (Hproperty left_row member Hrelated)).
    exact (Hleft member Hin).
Qed.

Definition in_row_truth
    (values : list (value T)) (subquery : query_expr T relname)
    (row : tuple T) : Bool.b (B T) :=
  @query_value_lists_equal T unknown value_is_null values
    (@query_row_output_values T (query_expr_outputs subquery) row).

Definition in_rows_truth
    (values : list (value T)) (subquery : query_expr T relname)
    (rows : list (tuple T)) : Bool.b (B T) :=
  interp_quant (B T) Exists_F
    (in_row_truth values subquery)
    (query_canonical_rows rows).

(** Reading an output column is extensional only on rows that actually carry
    that output.  Admissibility of an executable query provides this boundary;
    keeping it explicit makes raw helper lemmas fail closed for malformed row
    lists instead of treating an out-of-schema [dot] as meaningful SQL data. *)
Definition query_row_has_outputs
    (outputs : list (attribute T)) (row : tuple T) : Prop :=
  forall output, In output outputs -> output inS labels T row.

Lemma query_row_has_outputs_congr :
  forall outputs left right,
    Oeset.compare (OTuple T) left right = Eq ->
    query_row_has_outputs outputs left ->
    query_row_has_outputs outputs right.
Proof.
intros outputs left right Hequal Houtputs output Houtput.
rewrite tuple_eq in Hequal.
destruct Hequal as [Hlabels _].
rewrite <- (Fset.mem_eq_2 _ _ _ Hlabels).
now apply Houtputs.
Qed.

Lemma query_row_output_values_congr :
  forall outputs left right,
    query_row_has_outputs outputs left ->
    Oeset.compare (OTuple T) left right = Eq ->
    @query_row_output_values T outputs left =
    @query_row_output_values T outputs right.
Proof.
intros outputs left right Houtputs Hequal.
rewrite tuple_eq in Hequal.
destruct Hequal as [_ Hvalues].
unfold query_row_output_values.
induction outputs as [|output outputs IH]; [reflexivity|].
cbn; f_equal.
- apply Hvalues, Houtputs; now left.
- apply IH. intros current Hcurrent.
  apply Houtputs; now right.
Qed.

Lemma in_row_truth_congr :
  forall values subquery left right,
    query_row_has_outputs (query_expr_outputs subquery) left ->
    Oeset.compare (OTuple T) left right = Eq ->
    in_row_truth values subquery left = in_row_truth values subquery right.
Proof.
intros values subquery left right Houtputs Hequal.
unfold in_row_truth.
now rewrite (@query_row_output_values_congr
  (query_expr_outputs subquery) left right Houtputs Hequal).
Qed.

Lemma relational_permut_Forall_backward :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop) (Q : B -> Prop)
      left right,
    (forall left_value right_value,
      R left_value right_value -> Q right_value -> P left_value) ->
    _permut R left right ->
    Forall Q right ->
    Forall P left.
Proof.
intros A B R P Q left right Hproper Hpermut.
induction Hpermut as
  [|left_value right_value tail prefix suffix Hrelated Htail IH];
  intro Hall.
- constructor.
- constructor.
  + apply (Hproper left_value right_value Hrelated).
    rewrite Forall_forall in Hall.
    apply Hall, in_or_app; right; now left.
  + apply IH.
    rewrite Forall_forall in Hall |- *.
    intros value Hvalue.
    apply Hall.
    apply in_app_iff in Hvalue; apply in_app_iff.
    destruct Hvalue as [Hprefix | Hsuffix].
    * now left.
    * right; now right.
Qed.

Lemma query_canonical_rows_has_outputs :
  forall outputs rows,
    Forall (query_row_has_outputs outputs) rows ->
    Forall (query_row_has_outputs outputs) (query_canonical_rows rows).
Proof.
intros outputs rows Hrows.
eapply relational_permut_Forall_backward.
- intros left right Hequal Hright.
  eapply query_row_has_outputs_congr; [|exact Hright].
  rewrite Oeset.compare_lt_gt, CompOpp_iff.
  exact Hequal.
- eapply query_same_rows_as_bag_permut_between
    with (bag := query_rows_bag rows).
  + apply query_canonical_rows_same_as_bag.
    unfold query_same_rows_as_bag; apply Febag.equal_refl.
  + unfold query_same_rows_as_bag; apply Febag.equal_refl.
- exact Hrows.
Qed.

(** [IN] is three-valued, but a filtering consumer observes only whether its
    result is exactly TRUE.  If [accept] describes that decision for each
    candidate row, the decision over the canonical bag representative is the
    ordinary Boolean existence test over the original row list.  In
    particular, FALSE and UNKNOWN both remain non-accepting here; this lemma
    intentionally does not identify their underlying [Bool3] results. *)
Lemma existsb_rel_permut_with_left_property :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      P left_value ->
      left_predicate left_value = right_predicate right_value) ->
    _permut R left right ->
    Forall P left ->
    existsb left_predicate left = existsb right_predicate right.
Proof.
intros A B R P left_predicate right_predicate left right Hproper Hpermut.
induction Hpermut as
  [|left_value right_value tail prefix suffix Hrelated Htail IH];
  intro Hall.
- reflexivity.
- inversion Hall as [|? ? Hleft Htail_property]; subst.
  cbn [existsb].
  rewrite (Hproper left_value right_value Hrelated Hleft),
    (IH Htail_property), 2 existsb_app.
  cbn [existsb].
  rewrite Bool.Bool.orb_assoc.
  rewrite (Bool.Bool.orb_comm
    (right_predicate right_value) (existsb right_predicate prefix)).
  symmetry; apply Bool.Bool.orb_assoc.
Qed.

Lemma existsb_support_rel_with_left_property :
  forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop)
      (left_predicate : A -> bool) (right_predicate : B -> bool) left right,
    (forall left_value right_value,
      R left_value right_value ->
      P left_value ->
      left_predicate left_value = right_predicate right_value) ->
    list_support_rel R left right ->
    Forall P left ->
    existsb left_predicate left = existsb right_predicate right.
Proof.
intros A B R P left_predicate right_predicate left right
  Hproper [Hforward Hbackward] Hall.
destruct (existsb left_predicate left) eqn:Hleft,
  (existsb right_predicate right) eqn:Hright; try reflexivity.
- apply existsb_exists in Hleft.
  destruct Hleft as [left_value [Hleft_value Haccepted]].
  destruct (Hforward left_value Hleft_value) as
    [right_value [Hright_value Hrelated]].
  assert (Hproperty : P left_value).
  { rewrite Forall_forall in Hall; now apply Hall. }
  assert (Hright_accepted : right_predicate right_value = true).
  { rewrite <- (Hproper left_value right_value Hrelated Hproperty).
    exact Haccepted. }
  assert (Hexists : existsb right_predicate right = true).
  { apply existsb_exists; exists right_value; now split. }
  congruence.
- apply existsb_exists in Hright.
  destruct Hright as [right_value [Hright_value Haccepted]].
  destruct (Hbackward right_value Hright_value) as
    [left_value [Hleft_value Hrelated]].
  assert (Hproperty : P left_value).
  { rewrite Forall_forall in Hall; now apply Hall. }
  assert (Hleft_accepted : left_predicate left_value = true).
  { rewrite (Hproper left_value right_value Hrelated Hproperty).
    exact Haccepted. }
  assert (Hexists : existsb left_predicate left = true).
  { apply existsb_exists; exists left_value; now split. }
  congruence.
Qed.

Lemma in_rows_acceptance_existsb :
  forall values subquery rows (accept : tuple T -> bool),
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) rows ->
    (forall row,
      Bool.is_true (B T) (in_row_truth values subquery row) = accept row) ->
    Bool.is_true (B T) (in_rows_truth values subquery rows) =
    existsb accept rows.
Proof.
  intros values subquery rows accept Houtputs Haccept.
  assert (His_true_orb : forall left right,
    Bool.is_true (B T) (Bool.orb (B T) left right) =
    Datatypes.orb
      (Bool.is_true (B T) left) (Bool.is_true (B T) right)).
  {
    intros left right.
    rewrite BasicFacts.eq_bool_iff, !Bool.Bool.orb_true_iff,
      !Bool.true_is_true, Bool.orb_true_iff.
    intuition.
  }
  assert (His_true_exists : forall candidates,
    Bool.is_true (B T)
      (Bool.existsb (B T) (in_row_truth values subquery) candidates) =
    existsb
      (fun row =>
        Bool.is_true (B T) (in_row_truth values subquery row))
      candidates).
  {
    induction candidates as [|row candidates IH].
    - cbn [Bool.existsb List.existsb].
      destruct (Bool.is_true (B T) (Bool.false (B T))) eqn:Hfalse;
        [|reflexivity].
      apply Bool.true_is_true in Hfalse.
      exfalso; apply (Bool.true_diff_false (B T)); now symmetry.
    - cbn [Bool.existsb List.existsb].
      now rewrite His_true_orb, IH.
  }
  pose proof (query_canonical_rows_has_outputs Houtputs) as Hcanonical.
  unfold in_rows_truth, interp_quant.
  rewrite His_true_exists.
  eapply existsb_rel_permut_with_left_property; [| |exact Hcanonical].
  - intros left right Hequal Hleft_outputs.
    rewrite <- (Haccept right).
    apply f_equal.
    exact (@in_row_truth_congr values subquery left right
      Hleft_outputs Hequal).
  - eapply query_same_rows_as_bag_permut_between
      with (bag := query_rows_bag rows).
    + apply query_canonical_rows_same_as_bag.
      unfold query_same_rows_as_bag; apply Febag.equal_refl.
    + unfold query_same_rows_as_bag; apply Febag.equal_refl.
Qed.

(** At an [IN] filter boundary, duplicate insertion/removal is sound whenever
    both row presentations have the same support up to semantic tuple
    equality.  This theorem does not equate the underlying FALSE and UNKNOWN
    Bool3 results and does not claim bag or order equivalence. *)
Theorem in_rows_acceptance_support_rel :
  forall values subquery left right,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) left ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) right ->
    list_support_rel
      (fun first second =>
        Oeset.compare (OTuple T) first second = Eq)
      left right ->
    Bool.is_true (B T) (in_rows_truth values subquery left) =
    Bool.is_true (B T) (in_rows_truth values subquery right).
Proof.
  intros values subquery left right Hleft_outputs Hright_outputs Hsupport.
  assert (Hleft :
    Bool.is_true (B T) (in_rows_truth values subquery left) =
    existsb
      (fun row => Bool.is_true (B T) (in_row_truth values subquery row))
      left).
  { apply in_rows_acceptance_existsb; [exact Hleft_outputs|].
    intros; reflexivity. }
  assert (Hright :
    Bool.is_true (B T) (in_rows_truth values subquery right) =
    existsb
      (fun row => Bool.is_true (B T) (in_row_truth values subquery row))
      right).
  { apply in_rows_acceptance_existsb; [exact Hright_outputs|].
    intros; reflexivity. }
  rewrite Hleft, Hright.
  eapply existsb_support_rel_with_left_property;
    [|exact Hsupport|exact Hleft_outputs].
  intros first second Hequal.
  intro Hfirst_outputs.
  apply f_equal.
  exact (@in_row_truth_congr values subquery first second
    Hfirst_outputs Hequal).
Qed.

(** Membership acceptance distributes over concatenated candidate supports.
    Duplicates on either side remain irrelevant only to this Boolean
    acceptance observation; the theorem makes no statement about subquery
    evaluation order or errors that produce the candidate lists. *)
Theorem in_rows_acceptance_append :
  forall values subquery left right,
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) left ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery)) right ->
    Bool.is_true (B T)
      (in_rows_truth values subquery (left ++ right)) =
    Datatypes.orb
      (Bool.is_true (B T) (in_rows_truth values subquery left))
      (Bool.is_true (B T) (in_rows_truth values subquery right)).
Proof.
  intros values subquery left right Hleft Hright.
  assert (Haccept : forall rows,
    Forall (query_row_has_outputs (query_expr_outputs subquery)) rows ->
    Bool.is_true (B T) (in_rows_truth values subquery rows) =
    existsb
      (fun row => Bool.is_true (B T) (in_row_truth values subquery row))
      rows).
  { intros rows Hrows; apply in_rows_acceptance_existsb; [exact Hrows|].
    intros; reflexivity. }
  assert (Happend :
    Forall (query_row_has_outputs (query_expr_outputs subquery))
      (left ++ right)).
  { now apply Forall_app. }
  rewrite (Haccept (left ++ right) Happend),
    (Haccept left Hleft), (Haccept right Hright), existsb_app.
  reflexivity.
Qed.

(** Two list representatives of the same finite bag agree on emptiness.  The
    proof goes through exact occurrence equality and [Oeset.permut], retaining
    the multiplicity carried by [query_same_rows_as_bag]. *)
Lemma query_same_rows_as_bag_empty_decision :
  forall first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    rows_empty_decision first = rows_empty_decision second.
Proof.
  intros first second bag Hfirst Hsecond.
  unfold query_same_rows_as_bag in Hfirst, Hsecond.
  assert (Hbags :
    @query_rows_bag T first =BE= @query_rows_bag T second).
  {
    eapply Febag.equal_trans.
    - exact Hfirst.
    - now apply Febag.equal_sym.
  }
  apply rows_empty_decision_oeset_permut with (order := OTuple T).
  apply Oeset.nb_occ_permut; intro row.
  unfold query_rows_bag in Hbags.
  rewrite Febag.nb_occ_equal in Hbags.
  specialize (Hbags row).
  now rewrite 2 Febag.nb_occ_mk_bag in Hbags.
Qed.

Lemma quantified_rows_exists_true_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Exists_F which_predicate values subquery rows =
      Bool.true (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth which_predicate values subquery row =
          Bool.true (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.existsb_exists_true.
Qed.

Lemma quantified_rows_exists_false_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Exists_F which_predicate values subquery rows =
      Bool.false (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth which_predicate values subquery row =
          Bool.false (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.existsb_exists_false.
Qed.

Lemma quantified_rows_forall_true_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Forall_F which_predicate values subquery rows =
      Bool.true (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth which_predicate values subquery row =
          Bool.true (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.forallb_forall_true.
Qed.

Lemma quantified_rows_forall_false_iff :
  forall which_predicate values subquery rows,
    quantified_rows_truth Forall_F which_predicate values subquery rows =
      Bool.false (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth which_predicate values subquery row =
          Bool.false (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.forallb_forall_false.
Qed.

Lemma in_rows_true_iff : forall values subquery rows,
  in_rows_truth values subquery rows = Bool.true (B T) <->
  exists row,
    In row (query_canonical_rows rows) /\
    in_row_truth values subquery row = Bool.true (B T).
Proof.
  intros; unfold in_rows_truth, interp_quant.
  apply Bool.existsb_exists_true.
Qed.

Lemma in_rows_false_iff : forall values subquery rows,
  in_rows_truth values subquery rows = Bool.false (B T) <->
  forall row,
    In row (query_canonical_rows rows) ->
    in_row_truth values subquery row = Bool.false (B T).
Proof.
  intros; unfold in_rows_truth, interp_quant.
  apply Bool.existsb_exists_false.
Qed.

Lemma query_canonical_rows_empty :
  @query_canonical_rows T [] = [].
Proof.
  unfold query_canonical_rows, query_rows_bag; cbn [Febag.mk_bag].
  apply Febag.elements_empty.
Qed.

(** The scalar-subquery constructor observes the complete ordered child list:
    zero rows produce the caller-supplied typed NULL, one row produces its sole
    output value, and two or more rows produce [CardinalityViolation]. *)
Lemma eval_scalar_value_subquery_outcome_iff :
  forall env result_type null_value subquery outcome,
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery) outcome <->
    value_is_null null_value = true /\
    exists query_outcome,
      eval_query env subquery query_outcome /\
      @scalar_subquery_value_outcome T null_value
        (query_expr_outputs subquery) query_outcome = outcome.
Proof.
intros env result_type null_value subquery outcome; split.
- intro Heval; inversion Heval; subst.
  split; [assumption|].
  match goal with
  | Hquery : eval_query env subquery ?query_outcome |- _ =>
      exists query_outcome; split; [exact Hquery|reflexivity]
  end.
- intros [Hnull [query_outcome [Hquery Houtcome]]].
  rewrite <- Houtcome.
  now apply EScalar_Subquery.
Qed.

Lemma eval_scalar_value_subquery_child_error :
  forall env result_type null_value subquery error,
    value_is_null null_value = true ->
    eval_query env subquery (SqlError error) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery) (SqlError error).
Proof.
intros env result_type null_value subquery error Hnull Hquery.
replace (SqlError error) with
  (@scalar_subquery_value_outcome T null_value
    (query_expr_outputs subquery) (SqlError error)) by reflexivity.
apply EScalar_Subquery; assumption.
Qed.

Lemma eval_scalar_value_subquery_empty :
  forall env result_type null_value subquery,
    value_is_null null_value = true ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery)
      (SqlSuccess null_value).
Proof.
intros env result_type null_value subquery Hnull Hquery.
replace (SqlSuccess null_value) with
  (@scalar_subquery_value_outcome T null_value
    (query_expr_outputs subquery) (SqlSuccess [])) by reflexivity.
apply EScalar_Subquery; assumption.
Qed.

Lemma eval_scalar_value_subquery_singleton :
  forall env result_type null_value subquery output row,
    query_expr_outputs subquery = [output] ->
    value_is_null null_value = true ->
    eval_query env subquery (SqlSuccess [row]) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery)
      (SqlSuccess (dot T row output)).
Proof.
intros env result_type null_value subquery output row
  Houtputs Hnull Hquery.
replace (SqlSuccess (dot T row output)) with
  (@scalar_subquery_value_outcome T null_value
    (query_expr_outputs subquery) (SqlSuccess [row])).
- apply EScalar_Subquery; assumption.
- now rewrite Houtputs.
Qed.

Lemma eval_scalar_value_subquery_cardinality_violation :
  forall env result_type null_value subquery first second rest,
    value_is_null null_value = true ->
    eval_query env subquery (SqlSuccess (first :: second :: rest)) ->
    eval_scalar_value env
      (SExpr_Subquery result_type null_value subquery)
      (SqlError CardinalityViolation).
Proof.
intros env result_type null_value subquery first second rest Hnull Hquery.
replace (SqlError CardinalityViolation) with
  (@scalar_subquery_value_outcome T null_value
    (query_expr_outputs subquery)
    (SqlSuccess (first :: second :: rest))) by reflexivity.
apply EScalar_Subquery; assumption.
Qed.

Lemma eval_scalar_boolean_quant_error_iff :
  forall env which_quantifier which_predicate arguments subquery error,
    eval_scalar_boolean env
      (SExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlError error) <->
    eval_scalar_values env arguments (SqlError error) \/
    exists values,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlError error).
Proof.
  intros env which_quantifier which_predicate arguments subquery error; split.
  - intro Heval; inversion Heval; subst.
    + now left.
    + right; exists values; now split.
  - intros [Harguments | [values [Harguments Hsubquery]]].
    + now apply EScalar_QuantArgumentsError.
    + eapply EScalar_QuantSubqueryError; eassumption.
Qed.

Lemma eval_scalar_boolean_quant_success_iff :
  forall env which_quantifier which_predicate arguments subquery truth,
    eval_scalar_boolean env
      (SExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlSuccess truth) <->
    exists values rows,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = quantified_rows_truth which_quantifier which_predicate
        values subquery rows.
Proof.
  intros env which_quantifier which_predicate arguments subquery truth; split.
  - intro Heval; inversion Heval; subst.
    exists values, rows; repeat split; try assumption; reflexivity.
  - intros [values [rows [Harguments [Hsubquery ->]]]].
    eapply EScalar_QuantSuccess; eassumption.
Qed.

(** If every successful observation of a quantified subquery yields one fixed
    Bool3 result, and neither its arguments nor the subquery can fail, the
    enclosing predicate has an exact SQL-TRUE acceptance decision.  FALSE and
    UNKNOWN remain distinct in [fixed_truth]; only the final filter decision is
    projected through [Bool.is_true]. *)
Theorem scalar_expr_quant_acceptance_exact_of_fixed_truth :
  forall env quantifier predicate arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      quantified_rows_truth quantifier predicate values
        subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Quant quantifier predicate arguments subquery)
      (Bool.is_true (B T) fixed_truth).
Proof.
  intros env quantifier predicate arguments subquery fixed_truth
    [values Hvalues] [rows Hrows] Hfixed Hargument_errors Hquery_errors.
  unfold scalar_expr_acceptance_exact_at.
  split.
  - exists fixed_truth; split.
    + apply eval_scalar_boolean_quant_success_iff.
      exists values, rows; repeat split; try assumption.
      symmetry; now apply Hfixed.
    + reflexivity.
  - split.
    + intros truth Htruth.
      apply eval_scalar_boolean_quant_success_iff in Htruth.
      destruct Htruth as
        [observed_values [observed_rows
          [Hobserved_values [Hobserved_rows ->]]]].
      now rewrite (Hfixed observed_values observed_rows
        Hobserved_values Hobserved_rows).
    + intros error Herror.
      apply eval_scalar_boolean_quant_error_iff in Herror.
      destruct Herror as
        [Hargument_error | [observed_values [_ Hsubquery_error]]].
      * now apply (Hargument_errors error).
      * now apply (Hquery_errors error).
Qed.

Lemma eval_scalar_boolean_quant_forall_empty :
  forall env which_predicate arguments subquery values,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_boolean env
      (SExpr_Quant Forall_F which_predicate arguments subquery)
      (SqlSuccess (Bool.true (B T))).
Proof.
  intros env which_predicate arguments subquery values Harguments Hsubquery.
  apply eval_scalar_boolean_quant_success_iff.
  exists values, []; repeat split; try assumption.
  unfold quantified_rows_truth; rewrite query_canonical_rows_empty.
  reflexivity.
Qed.

Lemma eval_scalar_boolean_quant_exists_empty :
  forall env which_predicate arguments subquery values,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_boolean env
      (SExpr_Quant Exists_F which_predicate arguments subquery)
      (SqlSuccess (Bool.false (B T))).
Proof.
  intros env which_predicate arguments subquery values Harguments Hsubquery.
  apply eval_scalar_boolean_quant_success_iff.
  exists values, []; repeat split; try assumption.
  unfold quantified_rows_truth; rewrite query_canonical_rows_empty.
  reflexivity.
Qed.

Lemma eval_scalar_boolean_in_error_iff :
  forall env arguments subquery error,
    eval_scalar_boolean env (SExpr_In arguments subquery) (SqlError error) <->
    eval_scalar_values env arguments (SqlError error) \/
    exists values,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlError error).
Proof.
  intros env arguments subquery error; split.
  - intro Heval; inversion Heval; subst.
    + now left.
    + right; exists values; now split.
  - intros [Harguments | [values [Harguments Hsubquery]]].
    + now apply EScalar_InArgumentsError.
    + eapply EScalar_InSubqueryError; eassumption.
Qed.

Lemma eval_scalar_boolean_in_success_iff :
  forall env arguments subquery truth,
    eval_scalar_boolean env (SExpr_In arguments subquery) (SqlSuccess truth) <->
    exists values rows,
      eval_scalar_values env arguments (SqlSuccess values) /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = in_rows_truth values subquery rows.
Proof.
  intros env arguments subquery truth; split.
  - intro Heval; inversion Heval; subst.
    exists values, rows; repeat split; try assumption; reflexivity.
  - intros [values [rows [Harguments [Hsubquery ->]]]].
    eapply EScalar_InSuccess; eassumption.
Qed.

Lemma eval_scalar_boolean_in_empty :
  forall env arguments subquery values,
    eval_scalar_values env arguments (SqlSuccess values) ->
    eval_query env subquery (SqlSuccess []) ->
    eval_scalar_boolean env (SExpr_In arguments subquery)
      (SqlSuccess (Bool.false (B T))).
Proof.
  intros env arguments subquery values Harguments Hsubquery.
  apply eval_scalar_boolean_in_success_iff.
  exists values, []; repeat split; try assumption.
  unfold in_rows_truth; rewrite query_canonical_rows_empty.
  reflexivity.
Qed.

(** Exact [IN] truth from relationally evaluated typed arguments and a fixed
    three-valued result for every successful argument/child observation.  The
    child may expose any legal representative of its bag; callers must prove
    that [in_rows_truth] agrees across all of them. *)
Theorem scalar_expr_in_truth_exact :
  forall env arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth values subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_truth_exact_at env (SExpr_In arguments subquery) fixed_truth.
Proof.
intros env arguments subquery fixed_truth
  [values Hvalues] [rows Hrows] Hfixed Hargument_errors Hquery_errors.
unfold scalar_expr_truth_exact_at.
split.
- apply eval_scalar_boolean_in_success_iff.
  exists values, rows; repeat split; try assumption.
  symmetry; now apply Hfixed.
- split.
  + intros truth Htruth.
    apply eval_scalar_boolean_in_success_iff in Htruth.
    destruct Htruth as
      [observed_values [observed_rows
        [Hobserved_values [Hobserved_rows ->]]]].
    now apply Hfixed.
  + intros error Herror.
    apply eval_scalar_boolean_in_error_iff in Herror.
    destruct Herror as
      [Hargument_error | [observed_values [_ Hsubquery_error]]].
    * now apply (Hargument_errors error).
    * now apply (Hquery_errors error).
Qed.

(** Filter-level [IN] acceptance can be weaker than exact Bool3 truth: FALSE
    and UNKNOWN may vary across legal child observations as long as neither is
    accepted.  Tuple-valued membership and duplicate occurrences remain in
    [in_row_truth] and [existsb]; no Rocq equality or set collapse is used. *)
Theorem scalar_expr_in_acceptance_exact :
  forall env arguments subquery
      (accept : list (value T) -> tuple T -> bool) accepted,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      Forall
        (query_row_has_outputs (query_expr_outputs subquery)) rows) ->
    (forall values,
      eval_scalar_values env arguments (SqlSuccess values) ->
      forall row,
        Bool.is_true (B T) (in_row_truth values subquery row) =
        accept values row) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      existsb (accept values) rows = accepted) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_In arguments subquery) accepted.
Proof.
intros env arguments subquery accept accepted
  [values Hvalues] [rows Hrows] Houtputs Haccept Hfixed
  Hargument_errors Hquery_errors.
unfold scalar_expr_acceptance_exact_at.
split.
- exists (in_rows_truth values subquery rows); split.
  + apply eval_scalar_boolean_in_success_iff.
    exists values, rows; repeat split; try assumption; reflexivity.
  + rewrite (@in_rows_acceptance_existsb
      values subquery rows (accept values) (Houtputs rows Hrows)
      (Haccept values Hvalues)).
    now apply Hfixed.
- split.
  + intros truth Htruth.
    apply eval_scalar_boolean_in_success_iff in Htruth.
    destruct Htruth as
      [observed_values [observed_rows
        [Hobserved_values [Hobserved_rows ->]]]].
    rewrite (@in_rows_acceptance_existsb
      observed_values subquery observed_rows (accept observed_values)
      (Houtputs observed_rows Hobserved_rows)
      (Haccept observed_values Hobserved_values)).
    now apply Hfixed.
  + intros error Herror.
    apply eval_scalar_boolean_in_error_iff in Herror.
    destruct Herror as
      [Hargument_error | [observed_values [_ Hsubquery_error]]].
    * now apply (Hargument_errors error).
    * now apply (Hquery_errors error).
Qed.

(** [NOT IN] cannot be obtained by complementing the filter-acceptance bit of
    [IN]: SQL [NOT UNKNOWN] is still UNKNOWN.  This interface therefore
    requires the stronger fixed-truth premise and applies negation before
    projecting through [Bool.is_true]. *)
Theorem scalar_expr_not_in_acceptance_exact_of_fixed_truth :
  forall env arguments subquery fixed_truth,
    (exists values,
      eval_scalar_values env arguments (SqlSuccess values)) ->
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall values rows,
      eval_scalar_values env arguments (SqlSuccess values) ->
      eval_query env subquery (SqlSuccess rows) ->
      in_rows_truth values subquery rows = fixed_truth) ->
    (forall error, ~ eval_scalar_values env arguments (SqlError error)) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Not (SExpr_In arguments subquery))
      (Bool.is_true (B T) (Bool.negb (B T) fixed_truth)).
Proof.
intros env arguments subquery fixed_truth
  Harguments Hsuccess Hfixed Hargument_errors Hquery_errors.
apply scalar_expr_not_acceptance_exact.
now apply scalar_expr_in_truth_exact.
Qed.

Lemma eval_scalar_boolean_exists_error_iff : forall env subquery error,
  eval_scalar_boolean env (SExpr_Exists subquery) (SqlError error) <->
  eval_exists env subquery (SqlError error).
Proof.
  intros env subquery error; split.
  - intro Heval; inversion Heval; assumption.
  - intro Hsubquery; now apply EScalar_ExistsError.
Qed.

Lemma eval_scalar_boolean_exists_success_iff : forall env subquery truth,
  eval_scalar_boolean env (SExpr_Exists subquery) (SqlSuccess truth) <->
  eval_exists env subquery (SqlSuccess truth).
Proof.
  intros env subquery truth; split.
  - intro Heval; inversion Heval; assumption.
  - intro Hexists; now apply EScalar_ExistsSuccess.
Qed.

(** Cross-environment congruence for EXISTS uses the native existential
    observation.  Ordinary row outcomes are intentionally not substitutive:
    target-list expressions may be dead only to EXISTS. *)
Lemma eval_scalar_boolean_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    forall outcome,
      eval_scalar_boolean left_env (SExpr_Exists subquery) outcome <->
      eval_scalar_boolean right_env (SExpr_Exists subquery) outcome.
Proof.
  intros left_env right_env subquery Hquery [truth|error].
  - rewrite 2 eval_scalar_boolean_exists_success_iff; apply Hquery.
  - rewrite 2 eval_scalar_boolean_exists_error_iff; apply Hquery.
Qed.

(** Constructor-level form of [eval_scalar_boolean_exists_env_congr], suitable
    for structural congruence proofs over the typed scalar syntax. *)
Lemma scalar_expr_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_exists left_env subquery outcome <->
      eval_exists right_env subquery outcome) ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_Exists subquery).
Proof.
  intros left_env right_env subquery Hquery outcome.
  now apply eval_scalar_boolean_exists_env_congr.
Qed.

(** A typed IN expression is stable across correlated environments when both
    its relational argument evaluator and its query child expose exactly the
    same outcomes.  This includes argument-side scalar-subquery errors. *)
Lemma eval_scalar_boolean_in_env_congr_safe :
  forall left_env right_env arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_scalar_boolean left_env (SExpr_In arguments subquery) outcome <->
      eval_scalar_boolean right_env (SExpr_In arguments subquery) outcome.
Proof.
intros left_env right_env arguments subquery Harguments Hquery outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_InArgumentsError.
  now apply (proj1 (Harguments _)).
- eapply EScalar_InSubqueryError.
  + eapply (proj1 (Harguments _)); eassumption.
  + eapply (proj1 (Hquery _)); eassumption.
- eapply EScalar_InSuccess.
  + eapply (proj1 (Harguments _)); eassumption.
  + eapply (proj1 (Hquery _)); eassumption.
- apply EScalar_InArgumentsError.
  now apply (proj2 (Harguments _)).
- eapply EScalar_InSubqueryError.
  + eapply (proj2 (Harguments _)); eassumption.
  + eapply (proj2 (Hquery _)); eassumption.
- eapply EScalar_InSuccess.
  + eapply (proj2 (Harguments _)); eassumption.
  + eapply (proj2 (Hquery _)); eassumption.
Qed.

(** Constructor-level form of [eval_scalar_boolean_in_env_congr_safe]. *)
Lemma scalar_expr_in_env_congr_safe :
  forall left_env right_env arguments subquery,
    (forall outcome,
      eval_scalar_values left_env arguments outcome <->
      eval_scalar_values right_env arguments outcome) ->
    query_expr_env_outcome_equiv left_env right_env subquery ->
    scalar_expr_env_outcome_equiv left_env right_env
      (SExpr_In arguments subquery).
Proof.
  intros left_env right_env arguments subquery Harguments Hquery outcome.
  now apply eval_scalar_boolean_in_env_congr_safe.
Qed.

Lemma eval_scalar_boolean_exists_false_iff : forall env subquery,
  eval_scalar_boolean env (SExpr_Exists subquery)
    (SqlSuccess (Bool.false (B T))) <->
  eval_exists env subquery (SqlSuccess (Bool.false (B T))).
Proof.
  intros env subquery; split.
  - now apply eval_scalar_boolean_exists_success_iff.
  - now apply eval_scalar_boolean_exists_success_iff.
Qed.

Lemma eval_scalar_boolean_exists_true_iff : forall env subquery,
  eval_scalar_boolean env (SExpr_Exists subquery)
    (SqlSuccess (Bool.true (B T))) <->
  eval_exists env subquery (SqlSuccess (Bool.true (B T))).
Proof.
  intros env subquery; split.
  - now apply eval_scalar_boolean_exists_success_iff.
  - now apply eval_scalar_boolean_exists_success_iff.
Qed.

Local Lemma false_is_not_true :
  Bool.is_true (B T) (Bool.false (B T)) = false.
Proof.
  apply Bool.not_true_iff_false.
  intro Htrue.
  apply (Bool.true_diff_false (B T)).
  symmetry.
  now apply (proj1 (Bool.true_is_true (B T) (Bool.false (B T)))).
Qed.

(** The two-valued result of [EXISTS] expressed from the structural emptiness
    decision of a successful child observation. *)
Definition exists_truth_from_empty (empty : bool) : Bool.b (B T) :=
  if empty then Bool.false (B T) else Bool.true (B T).

Lemma exists_truth_from_empty_negation_acceptance :
  forall empty,
    Bool.is_true (B T)
      (Bool.negb (B T) (exists_truth_from_empty empty)) = empty.
Proof.
intro empty; destruct empty; unfold exists_truth_from_empty.
- rewrite Bool.negb_false; apply Bool.true_is_true_alt.
- rewrite Bool.negb_true; apply false_is_not_true.
Qed.

(** [EXISTS] has an exact two-valued truth whenever all native existential
    observations agree and the existential observation cannot fail.  This is
    intentionally stated over [eval_exists], because ordinary row evaluation
    may demand target expressions that are dead to EXISTS. *)
Theorem scalar_expr_exists_truth_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_expr_truth_exact_at env (SExpr_Exists subquery)
      (exists_truth_from_empty empty).
Proof.
intros env subquery empty [truth Htruth] Hfixed Herrors.
unfold scalar_expr_truth_exact_at.
split.
- pose proof (Hfixed truth Htruth) as Hequal; subst truth.
  now apply EScalar_ExistsSuccess.
- split.
  + intros observed Hobserved.
    apply eval_scalar_boolean_exists_success_iff in Hobserved.
    now apply Hfixed.
  + intros error Herror.
    apply eval_scalar_boolean_exists_error_iff in Herror.
    now apply (Herrors error).
Qed.

(** Unlike [NOT IN], [NOT EXISTS] is two-valued.  Its exact acceptance bit is
    therefore precisely the child's emptiness decision. *)
Theorem scalar_expr_not_exists_acceptance_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Not (SExpr_Exists subquery)) empty.
Proof.
intros env subquery empty Hsuccess Hemptiness Herrors.
pose proof
  (scalar_expr_not_acceptance_exact
    (scalar_expr_exists_truth_exact (env := env) (subquery := subquery)
      empty Hsuccess Hemptiness Herrors)) as Hexact.
rewrite exists_truth_from_empty_negation_acceptance in Hexact.
exact Hexact.
Qed.

(** EXISTS depends only on whether a successful child observation is empty.
    Successful observations may otherwise differ, but they must all agree on
    emptiness at this fixed (possibly correlated) environment.  Inhabitation
    and no-error are explicit so the exact scalar contract is not vacuous. *)
Theorem scalar_expr_exists_acceptance_exact :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null boolean_schedule env
      (SExpr_Exists subquery) (Datatypes.negb empty).
Proof.
  intros env subquery empty Hsuccess Hfixed Herror.
  pose proof
    (scalar_expr_truth_exact_acceptance_exact
      (scalar_expr_exists_truth_exact (env := env) (subquery := subquery)
        empty Hsuccess Hfixed Herror)) as Hexact.
  destruct empty; cbn [exists_truth_from_empty Datatypes.negb] in *.
  - rewrite false_is_not_true in Hexact; exact Hexact.
  - rewrite Bool.true_is_true_alt in Hexact; exact Hexact.
Qed.

(** Fixed-environment congruence is the useful correlated-query interface:
    [env] may already be extended with an outer row. *)

Lemma eval_scalar_boolean_quant_subquery_congr :
  forall env which_quantifier which_predicate arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_scalar_boolean env
        (SExpr_Quant which_quantifier which_predicate arguments left) outcome <->
      eval_scalar_boolean env
        (SExpr_Quant which_quantifier which_predicate arguments right) outcome.
Proof.
  intros env which_quantifier which_predicate arguments left right
    Houtputs Hequiv outcome; split; intro Heval; inversion Heval; subst.
  - now apply EScalar_QuantArgumentsError.
  - eapply EScalar_QuantSubqueryError; [eassumption|].
    now apply (proj1 (Hequiv (SqlError error))).
  - rewrite Houtputs.
    eapply EScalar_QuantSuccess; [eassumption|].
    now apply (proj1 (Hequiv (SqlSuccess rows))).
  - now apply EScalar_QuantArgumentsError.
  - eapply EScalar_QuantSubqueryError; [eassumption|].
    now apply (proj2 (Hequiv (SqlError error))).
  - rewrite <- Houtputs.
    eapply EScalar_QuantSuccess; [eassumption|].
    now apply (proj2 (Hequiv (SqlSuccess rows))).
Qed.

Lemma eval_scalar_boolean_in_subquery_congr :
  forall env arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_scalar_boolean env (SExpr_In arguments left) outcome <->
      eval_scalar_boolean env (SExpr_In arguments right) outcome.
Proof.
  intros env arguments left right Houtputs Hequiv outcome; split; intro Heval;
    inversion Heval; subst.
  - now apply EScalar_InArgumentsError.
  - eapply EScalar_InSubqueryError; [eassumption|].
    now apply (proj1 (Hequiv (SqlError error))).
  - rewrite Houtputs.
    eapply EScalar_InSuccess; [eassumption|].
    now apply (proj1 (Hequiv (SqlSuccess rows))).
  - now apply EScalar_InArgumentsError.
  - eapply EScalar_InSubqueryError; [eassumption|].
    now apply (proj2 (Hequiv (SqlError error))).
  - rewrite <- Houtputs.
    eapply EScalar_InSuccess; [eassumption|].
    now apply (proj2 (Hequiv (SqlSuccess rows))).
Qed.

Lemma eval_scalar_boolean_exists_subquery_congr :
  forall env left right,
    (forall outcome,
      eval_exists env left outcome <-> eval_exists env right outcome) ->
    forall outcome,
      eval_scalar_boolean env (SExpr_Exists left) outcome <->
      eval_scalar_boolean env (SExpr_Exists right) outcome.
Proof.
  intros env left right Hequiv outcome; split; intro Heval;
    inversion Heval; subst.
  - apply EScalar_ExistsError.
    now apply (proj1 (Hequiv (SqlError error))).
  - apply EScalar_ExistsSuccess.
    now apply (proj1 (Hequiv (SqlSuccess truth))).
  - apply EScalar_ExistsError.
    now apply (proj2 (Hequiv (SqlError error))).
  - apply EScalar_ExistsSuccess.
    now apply (proj2 (Hequiv (SqlSuccess truth))).
Qed.

Section TypedSubqueryAdmissibility.

Variable leaf_has_type : type T -> @aggterm T -> Prop.
Variable call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Variable predicate_has_types : predicate T -> list (type T) -> Prop.
Variable rank_type boolean_type : type T.

Lemma scalar_expr_quant_admissible_iff :
  forall phase which_quantifier which_predicate arguments subquery,
    @scalar_expr_admissible T relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase ScalarResultBoolean
      (SExpr_Quant which_quantifier which_predicate arguments subquery) <->
    scalar_phase_allows_subquery phase = true /\
    prop_forall
      (@scalar_expr_admissible T relname basesort
        leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type value_is_null phase ScalarResultValue)
      arguments /\
    @query_expr_admissible T relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null subquery /\
    arguments <> nil /\
    length arguments = length (query_expr_outputs subquery) /\
    length arguments + length (query_expr_outputs subquery) =
      predicate_arity T which_predicate /\
    predicate_has_types which_predicate
      (map scalar_expr_type arguments ++
       map (type_of_attribute T) (query_expr_outputs subquery)).
Proof.
  intros; reflexivity.
Qed.

Lemma scalar_expr_in_admissible_iff : forall phase arguments subquery,
  @scalar_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null phase ScalarResultBoolean
    (SExpr_In arguments subquery) <->
  scalar_phase_allows_subquery phase = true /\
  prop_forall
    (@scalar_expr_admissible T relname basesort
      leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type value_is_null phase ScalarResultValue)
    arguments /\
  @query_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null subquery /\
  scalar_expr_in_positionally_aligned arguments
    (query_expr_outputs subquery).
Proof.
  intros; reflexivity.
Qed.

Lemma scalar_expr_exists_admissible_iff : forall phase subquery,
  @scalar_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null phase ScalarResultBoolean
    (SExpr_Exists subquery) <->
  scalar_phase_allows_subquery phase = true /\
  @query_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null subquery.
Proof.
  intros; reflexivity.
Qed.

Lemma scalar_expr_subquery_admissible_iff :
  forall phase result_type null_value subquery,
  @scalar_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null phase ScalarResultValue
    (SExpr_Subquery result_type null_value subquery) <->
  scalar_phase_allows_subquery phase = true /\
  @query_expr_admissible T relname basesort
    leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type value_is_null subquery /\
  value_is_null null_value = true /\
  type_of_value T null_value = result_type /\
  match query_expr_outputs subquery with
  | output :: nil => type_of_attribute T output = result_type
  | _ => False
  end.
Proof.
  intros; reflexivity.
Qed.

End TypedSubqueryAdmissibility.

Lemma eval_scalar_value_context_correlated_congr :
  forall (context : @scalar_expr_context T relname ScalarResultValue)
      left right outer_env outer_row outcome,
    @query_expr_global_demand_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (scalar_expr_context_demand context) left right ->
    eval_scalar_value (env_t T outer_env outer_row)
      (plug_scalar_expr_context context left) outcome <->
    eval_scalar_value (env_t T outer_env outer_row)
      (plug_scalar_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  exact (@scalar_expr_context_global_congr T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule ScalarResultValue context left right Hequiv
    (env_t T outer_env outer_row) outcome).
Qed.

Lemma eval_scalar_boolean_context_correlated_congr :
  forall (context : @scalar_expr_context T relname ScalarResultBoolean)
      left right outer_env outer_row outcome,
    @query_expr_global_demand_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (scalar_expr_context_demand context) left right ->
    eval_scalar_boolean (env_t T outer_env outer_row)
      (plug_scalar_expr_context context left) outcome <->
    eval_scalar_boolean (env_t T outer_env outer_row)
      (plug_scalar_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  exact (@scalar_expr_context_global_congr T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule ScalarResultBoolean context left right Hequiv
    (env_t T outer_env outer_row) outcome).
Qed.

Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_demand_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule (query_expr_context_demand context) left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  exact (proj2 (@query_expr_context_global_congr T relname basesort instance
    unknown symbol_runtime_error aggregate_runtime_error
    value_is_null boolean_schedule context left right Hequiv)
    (env_t T outer_env outer_row) outcome).
Qed.

End PredicateSubquerySemantics.
