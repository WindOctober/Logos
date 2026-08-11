(******************************************************************************)
(** Public query laws for the union of outcomes over all Boolean schedules. **)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
  SqlOutcome SqlErrorSemantics SqlListFacts SqlBagAbstraction SqlQuerySyntax
  SqlQuerySemantics SqlQueryFacts SqlQueryContexts SqlQueryRenameTransport.
From Logos.FormalSQL Require Import
  OrderedQueryFacts GroupedFilterOutcomeFacts.

Import Tuple.
Import ListNotations.

(** Bidirectional transport is the relational part of
    [outcome_relation_equiv], without either nonemptiness obligation.  Keeping
    it separate is useful for syntax constructors: a parent witness supplies
    inhabitation, while the operator proof only has to transport successes and
    preserve every observable error category. *)
Definition outcome_relation_transport {A B : Type}
    (value_rel : A -> B -> Prop)
    (left : sql_outcome A -> Prop) (right : sql_outcome B -> Prop) : Prop :=
  (forall left_value,
    left (SqlSuccess left_value) ->
    exists right_value,
      right (SqlSuccess right_value) /\ value_rel left_value right_value) /\
  (forall right_value,
    right (SqlSuccess right_value) ->
    exists left_value,
      left (SqlSuccess left_value) /\ value_rel left_value right_value) /\
  (forall error, left (SqlError error) <-> right (SqlError error)).

Lemma outcome_relation_equiv_of_left_inhabited_transport :
  forall (A : Type) (value_rel : A -> A -> Prop)
      (left right : sql_outcome A -> Prop),
    (exists outcome, left outcome) ->
    outcome_relation_transport value_rel left right ->
    outcome_relation_equiv value_rel left right.
Proof.
intros A value_rel left right Hleft [Hforward [Hbackward Herrors]].
apply outcome_relation_equiv_intro.
- exact Hleft.
- destruct Hleft as [[left_value|error] Houtcome].
  + destruct (Hforward left_value Houtcome)
      as [right_value [Hright _]].
    now exists (SqlSuccess right_value).
  + exists (SqlError error); now apply (proj1 (Herrors error)).
- exact Hforward.
- exact Hbackward.
- exact Herrors.
Qed.

Lemma outcome_relation_equiv_value_relation_morphism :
  forall (A : Type) (left_rel right_rel : A -> A -> Prop)
      (left right : sql_outcome A -> Prop),
    (forall left_value right_value,
      left_rel left_value right_value <->
      right_rel left_value right_value) ->
    outcome_relation_equiv left_rel left right ->
    outcome_relation_equiv right_rel left right.
Proof.
intros A left_rel right_rel left right Hrel
  [Hleft [Hright [Hforward [Hbackward Herrors]]]].
apply outcome_relation_equiv_intro; try assumption.
- intros left_value Hleft_value.
  destruct (Hforward left_value Hleft_value) as
    [right_value [Hright_value Hrelated]].
  exists right_value; split; [exact Hright_value|].
  now apply (proj1 (Hrel left_value right_value)).
- intros right_value Hright_value.
  destruct (Hbackward right_value Hright_value) as
    [left_value [Hleft_value Hrelated]].
  exists left_value; split; [exact Hleft_value|].
  now apply (proj1 (Hrel left_value right_value)).
Qed.

(** Reverse a heterogeneous-looking relation on one carrier without requiring
    it to be symmetric.  This is the direction needed when a constructor's
    backward traversal reuses its forward transport theorem. *)
Lemma outcome_relation_equiv_flip :
  forall (A : Type) (value_rel : A -> A -> Prop)
      (left right : sql_outcome A -> Prop),
    outcome_relation_equiv value_rel left right ->
    outcome_relation_equiv (fun right_value left_value =>
      value_rel left_value right_value) right left.
Proof.
intros A value_rel left right
  [Hleft [Hright [Hforward [Hbackward Herrors]]]].
apply outcome_relation_equiv_intro.
- exact Hright.
- exact Hleft.
- exact Hbackward.
- exact Hforward.
- intro error; symmetry; apply Herrors.
Qed.

Lemma outcome_equiv_flip_relation :
  forall (A : Type) (value_rel : A -> A -> Prop) left right,
    outcome_equiv value_rel left right ->
    outcome_equiv
      (fun right_value left_value => value_rel left_value right_value)
      right left.
Proof.
intros A value_rel [left_value|left_error] [right_value|right_error];
  cbn; intro Hrelated; try contradiction.
- exact Hrelated.
- now symmetry.
Qed.

Lemma outcome_relation_transport_flip :
  forall (A : Type) (value_rel : A -> A -> Prop)
      (left right : sql_outcome A -> Prop),
    outcome_relation_transport value_rel left right ->
    outcome_relation_transport (fun right_value left_value =>
      value_rel left_value right_value) right left.
Proof.
intros A value_rel left right [Hforward [Hbackward Herrors]].
split; [exact Hbackward|].
split; [exact Hforward|].
intro error; symmetry; apply Herrors.
Qed.

Lemma Forall2_relation_flip :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    Forall2 relation left right ->
    Forall2 (fun right_value left_value =>
      relation left_value right_value) right left.
Proof.
intros A relation left right Hrelated.
induction Hrelated; constructor; assumption.
Qed.

Lemma outcome_relation_transport_Forall2_flip :
  forall (A : Type) (relation : A -> A -> Prop)
      (left right : sql_outcome (list A) -> Prop),
    outcome_relation_transport (Forall2 relation) left right ->
    outcome_relation_transport
      (Forall2 (fun right_value left_value =>
        relation left_value right_value)) right left.
Proof.
intros A relation left right [Hforward [Hbackward Herrors]].
split.
- intros right_values Hright.
  destruct (Hbackward right_values Hright) as
    [left_values [Hleft Hrelated]].
  exists left_values; split; [exact Hleft|].
  now apply Forall2_relation_flip.
- split.
  + intros left_values Hleft.
    destruct (Hforward left_values Hleft) as
      [right_values [Hright Hrelated]].
    exists right_values; split; [exact Hright|].
    now apply Forall2_relation_flip.
  + intro error; symmetry; apply Herrors.
Qed.

Lemma outcome_relation_transport_exists_same_index :
  forall (Index A : Type) (value_rel : A -> A -> Prop)
      (left right : Index -> sql_outcome A -> Prop),
    (forall index,
      outcome_relation_transport value_rel (left index) (right index)) ->
    outcome_relation_transport value_rel
      (fun outcome => exists index, left index outcome)
      (fun outcome => exists index, right index outcome).
Proof.
intros Index A value_rel left right Hall.
split.
- intros left_value [index Hleft].
  destruct (Hall index) as [Hforward _].
  destruct (Hforward left_value Hleft) as
    [right_value [Hright Hrelated]].
  exists right_value; split; [now exists index|exact Hrelated].
- split.
  + intros right_value [index Hright].
    destruct (Hall index) as [_ [Hbackward _]].
    destruct (Hbackward right_value Hright) as
      [left_value [Hleft Hrelated]].
    exists left_value; split; [now exists index|exact Hrelated].
  + intro error; split; intros [index Herror]; exists index.
    * now apply (proj1 ((proj2 (proj2 (Hall index))) error)).
    * now apply (proj2 ((proj2 (proj2 (Hall index))) error)).
Qed.

(** These relation lemmas are independent of SQL syntax.  They make the
    quantifier change from one scheduled relation to the union of all
    scheduled relations explicit, so no proof can silently promote a theorem
    about one Boolean schedule to a public SQL certificate. *)

Lemma successful_relation_equiv_transport_iff :
  forall (A : Type) (value_equiv : A -> A -> Prop)
      (left left' right right' : sql_outcome A -> Prop),
    successful_relation_equiv value_equiv left right ->
    (forall outcome, left outcome <-> left' outcome) ->
    (forall outcome, right outcome <-> right' outcome) ->
    successful_relation_equiv value_equiv left' right'.
Proof.
intros A value_equiv left left' right right'
  [Hsuccess [Hleft_safe [Hright_safe [Hforward Hbackward]]]]
  Hleft_iff Hright_iff.
apply successful_relation_equiv_intro.
- destruct Hsuccess as [value Hvalue].
  exists value; now apply (proj1 (Hleft_iff _)).
- intros error Herror.
  apply (proj2 (Hleft_iff _)) in Herror.
  now apply (Hleft_safe error).
- intros error Herror.
  apply (proj2 (Hright_iff _)) in Herror.
  now apply (Hright_safe error).
- intros left_value Hleft'.
  apply (proj2 (Hleft_iff _)) in Hleft'.
  destruct (Hforward left_value Hleft')
    as [right_value [Hright Hequiv]].
  exists right_value; split;
    [now apply (proj1 (Hright_iff _))|exact Hequiv].
- intros right_value Hright'.
  apply (proj2 (Hright_iff _)) in Hright'.
  destruct (Hbackward right_value Hright')
    as [left_value [Hleft Hequiv]].
  exists left_value; split;
    [now apply (proj1 (Hleft_iff _))|exact Hequiv].
Qed.

Lemma outcome_relation_equiv_implies_successful_relation_equiv_safe :
  forall (A : Type) (value_equiv : A -> A -> Prop)
      (left right : sql_outcome A -> Prop),
    outcome_relation_equiv value_equiv left right ->
    (exists value, left (SqlSuccess value)) ->
    (forall error, ~ left (SqlError error)) ->
    (forall error, ~ right (SqlError error)) ->
    successful_relation_equiv value_equiv left right.
Proof.
intros A value_equiv left right
  [_ [_ [Hforward [Hbackward _]]]] Hsuccess Hleft_safe Hright_safe.
now apply successful_relation_equiv_intro.
Qed.

Lemma outcome_relation_equiv_transport_iff :
  forall (A : Type) (value_equiv : A -> A -> Prop)
      (left left' right right' : sql_outcome A -> Prop),
    outcome_relation_equiv value_equiv left right ->
    (forall outcome, left outcome <-> left' outcome) ->
    (forall outcome, right outcome <-> right' outcome) ->
    outcome_relation_equiv value_equiv left' right'.
Proof.
intros A value_equiv left left' right right'
  [Hleft [Hright [Hforward [Hbackward Herrors]]]]
  Hleft_iff Hright_iff.
apply outcome_relation_equiv_intro.
- destruct Hleft as [outcome Houtcome].
  exists outcome; now apply (proj1 (Hleft_iff outcome)).
- destruct Hright as [outcome Houtcome].
  exists outcome; now apply (proj1 (Hright_iff outcome)).
- intros left_value Hleft'.
  apply (proj2 (Hleft_iff (SqlSuccess left_value))) in Hleft'.
  destruct (Hforward left_value Hleft')
    as [right_value [Hright_value Hequiv]].
  exists right_value; split;
    [now apply (proj1 (Hright_iff _))|exact Hequiv].
- intros right_value Hright'.
  apply (proj2 (Hright_iff (SqlSuccess right_value))) in Hright'.
  destruct (Hbackward right_value Hright')
    as [left_value [Hleft_value Hequiv]].
  exists left_value; split;
    [now apply (proj1 (Hleft_iff _))|exact Hequiv].
- intro error; split; intro Herror.
  + apply (proj2 (Hleft_iff _)) in Herror.
    apply (proj1 (Hright_iff _)).
    now apply (proj1 (Herrors error)).
  + apply (proj2 (Hright_iff _)) in Herror.
    apply (proj1 (Hleft_iff _)).
    now apply (proj2 (Herrors error)).
Qed.

Theorem outcome_relation_equiv_exists_schedule_transport :
  forall (Schedule A : Type) (default_schedule : Schedule)
      (value_equiv : A -> A -> Prop)
      (left right : Schedule -> sql_outcome A -> Prop),
    (forall left_schedule,
      exists right_schedule,
        outcome_relation_equiv value_equiv
          (left left_schedule) (right right_schedule)) ->
    (forall right_schedule,
      exists left_schedule,
        outcome_relation_equiv value_equiv
          (left left_schedule) (right right_schedule)) ->
    outcome_relation_equiv value_equiv
      (fun outcome => exists schedule, left schedule outcome)
      (fun outcome => exists schedule, right schedule outcome).
Proof.
intros Schedule A default_schedule value_equiv left right
  Hforward_schedule Hbackward_schedule.
apply outcome_relation_equiv_intro.
- destruct (Hforward_schedule default_schedule)
    as [right_schedule [Hleft _]].
  destruct Hleft as [outcome Houtcome].
  now exists outcome, default_schedule.
- destruct (Hbackward_schedule default_schedule)
    as [left_schedule [_ [Hright _]]].
  destruct Hright as [outcome Houtcome].
  now exists outcome, default_schedule.
- intros left_value [left_schedule Hleft].
  destruct (Hforward_schedule left_schedule)
    as [right_schedule [_ [_ [Hforward _]]]].
  destruct (Hforward left_value Hleft)
    as [right_value [Hright Hequiv]].
  exists right_value; split; [now exists right_schedule|exact Hequiv].
- intros right_value [right_schedule Hright].
  destruct (Hbackward_schedule right_schedule)
    as [left_schedule [_ [_ [_ [Hbackward _]]]]].
  destruct (Hbackward right_value Hright)
    as [left_value [Hleft Hequiv]].
  exists left_value; split; [now exists left_schedule|exact Hequiv].
- intro error; split.
  + intros [left_schedule Hleft].
    destruct (Hforward_schedule left_schedule)
      as [right_schedule [_ [_ [_ [_ Herrors]]]]].
    exists right_schedule; now apply (proj1 (Herrors error)).
  + intros [right_schedule Hright].
    destruct (Hbackward_schedule right_schedule)
      as [left_schedule [_ [_ [_ [_ Herrors]]]]].
    exists left_schedule; now apply (proj2 (Herrors error)).
Qed.

Section PublicPossibleOutcomes.

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

(** Relation-parametric public observations deliberately omit schema equality.
    This is the reusable transport layer for heterogeneous operators; ordinary
    query equivalence is recovered by instantiating [rows_rel] with
    [ordered_rows_equiv] and proving the endpoint signatures equal. *)
Definition query_expr_possible_outcome_related
    (env : Env.env T) (rows_rel : list (tuple T) -> list (tuple T) -> Prop)
    (left right : query_expr T relname) : Prop :=
  outcome_relation_equiv rows_rel
    (@eval_query_expr_possible_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env left)
    (@eval_query_expr_possible_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null env right).

(** A local scalar-value contract may relate different expressions evaluated
    in different environments.  It is deliberately evaluator-level: all
    successful values are related in both directions and every runtime-error
    category is preserved.  This is the scalar analogue of the row contracts
    used below by Project and Filter. *)
Definition scalar_value_observation_related_at
    (schedule : boolean_site -> boolean_evaluation_order)
    (left_env : Env.env T)
    (left_expression : scalar_expr T relname ScalarResultValue)
    (right_env : Env.env T)
    (right_expression : scalar_expr T relname ScalarResultValue)
    (value_rel : value T -> value T -> Prop) : Prop :=
  outcome_relation_equiv value_rel
    (@eval_scalar_value_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      left_env left_expression)
    (@eval_scalar_value_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      right_env right_expression).

(** Pointwise contract for the deterministic callback carried by RowMap. *)
Definition row_map_observation_related_at
    (left_map : tuple T -> sql_outcome (tuple T)) (left_row : tuple T)
    (right_map : tuple T -> sql_outcome (tuple T)) (right_row : tuple T)
    (output_rel : tuple T -> tuple T -> Prop) : Prop :=
  outcome_equiv output_rel (left_map left_row) (right_map right_row).

(** A deterministic RowMap transports any positional input-row relation when
    its callbacks preserve the requested output relation.  The recursive
    definition returns the first callback error, so exact error categories are
    retained rather than hidden behind list mapping. *)
Lemma row_map_rows_outcome_relation :
  forall left_map right_map left_rows right_rows row_rel output_rel,
    Forall2 row_rel left_rows right_rows ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      row_map_observation_related_at
        left_map left_row right_map right_row output_rel) ->
    outcome_equiv (Forall2 output_rel)
      (@row_map_rows_outcome T left_map left_rows)
      (@row_map_rows_outcome T right_map right_rows).
Proof.
intros left_map right_map left_rows right_rows row_rel output_rel Hrows.
induction Hrows as
  [|left_row right_row left_rows right_rows Hrow Hrows IH]; intro Hpoint.
- constructor.
- cbn [row_map_rows_outcome].
  pose proof (Hpoint left_row right_row Hrow) as Hhead.
  unfold row_map_observation_related_at in Hhead.
  destruct (left_map left_row) as [left_output|left_error];
    destruct (right_map right_row) as [right_output|right_error];
    cbn in Hhead |- *; try contradiction.
  + specialize (IH Hpoint).
    destruct (row_map_rows_outcome left_map left_rows)
      as [left_outputs|left_tail_error];
      destruct (row_map_rows_outcome right_map right_rows)
      as [right_outputs|right_tail_error];
      cbn in IH |- *; try contradiction.
    * now constructor.
    * exact IH.
  + exact Hhead.
Qed.

(** Structural forward traversal for a scalar SELECT/argument list.  The
    theorem preserves positional multiplicity and the first reached error;
    it does not model the evaluator as a pure [map]. *)
Lemma eval_scalar_values_relation_forward :
  forall schedule left_env left_expressions left_outcome,
    @eval_scalar_values_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      left_env left_expressions left_outcome ->
    forall right_env right_expressions value_rel,
      Forall2
        (fun left_expression right_expression =>
          scalar_value_observation_related_at schedule
            left_env left_expression right_env right_expression value_rel)
        left_expressions right_expressions ->
      exists right_outcome,
        @eval_scalar_values_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          right_env right_expressions right_outcome /\
        outcome_equiv (Forall2 value_rel) left_outcome right_outcome.
Proof.
intros schedule left_env left_expressions left_outcome Heval.
induction Heval as
  [left_env
  |left_env left_expression left_expressions error Hleft_head
  |left_env left_expression left_expressions left_value left_tail
      Hleft_head Hleft_tail IHtail];
  intros right_env right_expressions value_rel Hexpressions.
- inversion Hexpressions; subst.
  exists (SqlSuccess nil); split; [constructor|constructor].
- inversion Hexpressions as
    [|left_head right_head left_tail right_tail Hhead Htail]; subst.
  unfold scalar_value_observation_related_at in Hhead.
  destruct Hhead as [_ [_ [_ [_ Herrors]]]].
  exists (SqlError error); split.
  + apply EScalarValues_HeadError.
    now apply (proj1 (Herrors error)).
  + reflexivity.
- inversion Hexpressions as
    [|left_head right_head left_tail_exprs right_tail_exprs Hhead Htail];
    subst.
  unfold scalar_value_observation_related_at in Hhead.
  destruct Hhead as [_ [_ [Hforward _]]].
  destruct (Hforward left_value Hleft_head) as
    [right_value [Hright_head Hvalue]].
  destruct (IHtail right_env right_tail_exprs value_rel Htail) as
    [right_tail [Hright_tail Hrelated_tail]].
  exists (@scalar_value_cons_outcome T right_value right_tail); split.
  + eapply EScalarValues_Cons; eassumption.
  + destruct left_tail as [left_values|left_error];
      destruct right_tail as [right_values|right_error];
      cbn [scalar_value_cons_outcome] in Hrelated_tail |- *;
      try contradiction.
    * now constructor.
    * exact Hrelated_tail.
Qed.

(** Bidirectional relation-parametric lifting for scalar value lists.  This
    is reusable by predicate calls, SELECT lists, aggregate inputs, and
    window arguments; callers prove only the per-expression contracts. *)
Theorem eval_scalar_values_relation_transport :
  forall schedule left_env left_expressions
      right_env right_expressions value_rel,
    Forall2
      (fun left_expression right_expression =>
        scalar_value_observation_related_at schedule
          left_env left_expression right_env right_expression value_rel)
      left_expressions right_expressions ->
    outcome_relation_transport (Forall2 value_rel)
      (@eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env left_expressions)
      (@eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        right_env right_expressions).
Proof.
intros schedule left_env left_expressions right_env right_expressions
  value_rel Hexpressions.
assert (Hexpressions_flip :
  Forall2
    (fun right_expression left_expression =>
      scalar_value_observation_related_at schedule
        right_env right_expression left_env left_expression
        (fun right_value left_value => value_rel left_value right_value))
    right_expressions left_expressions).
{
  induction Hexpressions as
    [|left_expression right_expression lefts rights Hhead Htail IH].
  - constructor.
  - constructor; [|exact IH].
    unfold scalar_value_observation_related_at in *.
    now apply outcome_relation_equiv_flip.
}
split.
- intros left_values Hleft.
  destruct (@eval_scalar_values_relation_forward
    schedule left_env left_expressions (SqlSuccess left_values) Hleft
    right_env right_expressions value_rel Hexpressions) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_values|right_error]; cbn in Hrelated.
  + exists right_values; now split.
  + contradiction.
- split.
  + intros right_values Hright.
    destruct (@eval_scalar_values_relation_forward
      schedule right_env right_expressions (SqlSuccess right_values) Hright
      left_env left_expressions
      (fun right_value left_value => value_rel left_value right_value)
      Hexpressions_flip) as [observed [Hobserved Hrelated]].
    destruct observed as [left_values|left_error]; cbn in Hrelated.
    * exists left_values; split; [exact Hobserved|].
      now apply Forall2_relation_flip in Hrelated.
    * contradiction.
  + intro error; split; intro Herror.
    * destruct (@eval_scalar_values_relation_forward
        schedule left_env left_expressions (SqlError error) Herror
        right_env right_expressions value_rel Hexpressions) as
        [observed [Hobserved Hrelated]].
      destruct observed as [right_values|right_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst right_error.
    * destruct (@eval_scalar_values_relation_forward
        schedule right_env right_expressions (SqlError error) Herror
        left_env left_expressions
        (fun right_value left_value => value_rel left_value right_value)
        Hexpressions_flip) as [observed [Hobserved Hrelated]].
      destruct observed as [left_values|left_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst left_error.
Qed.

(** Apply a scalar operator after its argument-list observation.  This is only
    the sequencing already present in [EScalar_CallArgumentsError] and
    [EScalar_CallSuccess]; keeping it explicit lets operator-local value/error
    facts compose without reopening the scalar evaluator. *)
Definition scalar_call_apply_outcome
    (operator : scalar_operator T)
    (arguments : sql_outcome (list (value T))) : sql_outcome (value T) :=
  match arguments with
  | SqlSuccess values =>
      @scalar_call_value_outcome T symbol_runtime_error operator values
  | SqlError error => SqlError error
  end.

Lemma eval_scalar_value_call_outcome_iff :
  forall schedule env result_type operator arguments outcome,
    @eval_scalar_value_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env (SExpr_Call result_type operator arguments) outcome <->
    exists argument_outcome,
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env arguments argument_outcome /\
      scalar_call_apply_outcome operator argument_outcome = outcome.
Proof.
intros schedule env result_type operator arguments outcome; split.
- intro Heval; inversion Heval; subst.
  + exists (SqlError error); now split.
  + exists (SqlSuccess values); now split.
- intros [[values | error] [Harguments Houtcome]]; cbn in Houtcome.
  + rewrite <- Houtcome; now apply EScalar_CallSuccess.
  + rewrite <- Houtcome; now apply EScalar_CallArgumentsError.
Qed.

(** The complete local contract for two scalar operators.  The operators and
    represented values may differ; corresponding argument lists must produce
    related successful values and exactly the same SQL runtime-error category.
    Range, typmod, NULL, and provenance facts are intentionally kept outside
    this definition and are used only to establish its semantic premise. *)
Definition scalar_call_local_observation_related
    (left_operator right_operator : scalar_operator T)
    (argument_rel result_rel : value T -> value T -> Prop) : Prop :=
  forall left_values right_values,
    Forall2 argument_rel left_values right_values ->
    outcome_equiv result_rel
      (@scalar_call_value_outcome T symbol_runtime_error
        left_operator left_values)
      (@scalar_call_value_outcome T symbol_runtime_error
        right_operator right_values).

Lemma scalar_call_expression_relation_forward :
  forall schedule left_env left_result_type left_operator left_arguments
      right_env right_result_type right_operator right_arguments
      argument_rel result_rel,
    outcome_relation_transport (Forall2 argument_rel)
      (@eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env left_arguments)
      (@eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        right_env right_arguments) ->
    scalar_call_local_observation_related
      left_operator right_operator argument_rel result_rel ->
    forall left_outcome,
      @eval_scalar_value_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env (SExpr_Call left_result_type left_operator left_arguments)
        left_outcome ->
      exists right_outcome,
        @eval_scalar_value_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          right_env
          (SExpr_Call right_result_type right_operator right_arguments)
          right_outcome /\
        outcome_equiv result_rel left_outcome right_outcome.
Proof.
intros schedule left_env left_result_type left_operator left_arguments
  right_env right_result_type right_operator right_arguments
  argument_rel result_rel
  [Harguments_forward [_ Hargument_errors]] Hlocal
  left_outcome Hleft.
apply eval_scalar_value_call_outcome_iff in Hleft.
destruct Hleft as [[left_values | left_error]
  [Hleft_arguments Hleft_outcome]].
- destruct (Harguments_forward left_values Hleft_arguments) as
    [right_values [Hright_arguments Hvalues]].
  pose proof (Hlocal left_values right_values Hvalues) as Hresult.
  exists (@scalar_call_value_outcome T symbol_runtime_error
    right_operator right_values); split.
  + apply eval_scalar_value_call_outcome_iff.
    exists (SqlSuccess right_values); now split.
  + now rewrite <- Hleft_outcome.
- assert (Hright_arguments :
    @eval_scalar_values_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      right_env right_arguments (SqlError left_error)).
  { now apply (proj1 (Hargument_errors left_error)). }
  exists (SqlError left_error); split.
  + apply eval_scalar_value_call_outcome_iff.
    exists (SqlError left_error); now split.
  + now rewrite <- Hleft_outcome.
Qed.

(** Bidirectional evaluator-level Scalar Outcome Bridge.  It preserves child
    argument errors, operator-local errors, NULL payloads through [result_rel],
    and successful values in one interface. *)
Theorem scalar_call_expression_relation_transport :
  forall schedule left_env left_result_type left_operator left_arguments
      right_env right_result_type right_operator right_arguments
      argument_rel result_rel,
    outcome_relation_transport (Forall2 argument_rel)
      (@eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env left_arguments)
      (@eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        right_env right_arguments) ->
    scalar_call_local_observation_related
      left_operator right_operator argument_rel result_rel ->
    outcome_relation_transport result_rel
      (@eval_scalar_value_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env (SExpr_Call left_result_type left_operator left_arguments))
      (@eval_scalar_value_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        right_env
          (SExpr_Call right_result_type right_operator right_arguments)).
Proof.
intros schedule left_env left_result_type left_operator left_arguments
  right_env right_result_type right_operator right_arguments
  argument_rel result_rel Harguments Hlocal.
pose proof (outcome_relation_transport_Forall2_flip Harguments)
  as Harguments_flip.
assert (Hlocal_flip : scalar_call_local_observation_related
  right_operator left_operator
  (fun right_value left_value => argument_rel left_value right_value)
  (fun right_value left_value => result_rel left_value right_value)).
{
  intros right_values left_values Hvalues.
  apply outcome_equiv_flip_relation.
  apply Hlocal.
  now apply Forall2_relation_flip in Hvalues.
}
split.
- intros left_value Hleft.
  destruct (scalar_call_expression_relation_forward
    (left_result_type := left_result_type)
    (left_operator := left_operator) (right_operator := right_operator)
    right_result_type Harguments Hlocal Hleft) as
    [[right_value | right_error] [Hright Hrelated]];
    cbn in Hrelated; [eauto|contradiction].
- split.
  + intros right_value Hright.
    destruct (scalar_call_expression_relation_forward
      (left_result_type := right_result_type)
      (left_operator := right_operator) (right_operator := left_operator)
      left_result_type Harguments_flip Hlocal_flip Hright) as
      [[left_value | left_error] [Hleft Hrelated]];
      cbn in Hrelated; [eauto|contradiction].
  + intro error; split; intro Herror.
    * destruct (scalar_call_expression_relation_forward
        (left_result_type := left_result_type)
        (left_operator := left_operator) (right_operator := right_operator)
        right_result_type Harguments Hlocal Herror) as
        [[right_value | right_error] [Hright Hrelated]];
        cbn in Hrelated; [contradiction|now subst right_error].
    * destruct (scalar_call_expression_relation_forward
        (left_result_type := right_result_type)
        (left_operator := right_operator) (right_operator := left_operator)
        left_result_type Harguments_flip Hlocal_flip Herror) as
        [[left_value | left_error] [Hleft Hrelated]];
        cbn in Hrelated; [contradiction|now subst left_error].
Qed.

(** Reachable-argument safety corollary.  It does not require an operator to
    be globally total: only argument lists that the expression can actually
    produce must have no local error. *)
Lemma scalar_call_expression_runtime_safe_of_reachable_local_safe :
  forall schedule env result_type operator arguments,
    (forall error,
      ~ @eval_scalar_values_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env arguments (SqlError error)) ->
    (forall values,
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env arguments (SqlSuccess values) ->
      forall error,
        @scalar_call_value_outcome T symbol_runtime_error operator values <>
          SqlError error) ->
    forall error,
      ~ @eval_scalar_value_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env (SExpr_Call result_type operator arguments) (SqlError error).
Proof.
intros schedule env result_type operator arguments
  Harguments_safe Hlocal_safe error Heval.
apply eval_scalar_value_call_outcome_iff in Heval.
destruct Heval as [[values | argument_error]
  [Harguments Houtcome]].
- exact (Hlocal_safe values Harguments error Houtcome).
- inversion Houtcome; subst argument_error.
  exact (Harguments_safe error Harguments).
Qed.

Lemma query_expr_possible_outcome_equiv_of_related :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_expr_possible_outcome_related env (@ordered_rows_equiv T) left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Houtputs Hrelated.
now split.
Qed.

(** Final bridge for the common positional-row relation emitted by Project and
    Filter transport.  Static output-signature equality remains explicit. *)
Lemma query_expr_possible_outcome_equiv_of_Forall2_rows :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_expr_possible_outcome_related env
      (Forall2
        (fun left_row right_row =>
          Oeset.compare (OTuple T) left_row right_row = Eq))
      left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Houtputs Hrelated.
apply query_expr_possible_outcome_equiv_of_related; [exact Houtputs|].
unfold query_expr_possible_outcome_related in *.
eapply outcome_relation_equiv_value_relation_morphism; [|exact Hrelated].
intros left_rows right_rows; symmetry.
apply ordered_rows_equiv_iff_Forall2.
Qed.

(** Per-row projection contract.  Successful scalar value lists are related
    only through the rows ultimately constructed by the two SELECT lists;
    every scalar error category is preserved by [outcome_relation_equiv]. *)
Definition project_row_observation_related_at
    (schedule : boolean_site -> boolean_evaluation_order)
    (left_env : Env.env T) (left_select : @query_select_list T relname)
    (left_row : tuple T)
    (right_env : Env.env T) (right_select : @query_select_list T relname)
    (right_row : tuple T)
    (output_rel : tuple T -> tuple T -> Prop) : Prop :=
  outcome_relation_equiv
    (fun left_values right_values =>
      output_rel
        (@project_row T relname left_select left_values)
        (@project_row T relname right_select right_values))
    (@eval_scalar_values_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      (env_t T left_env left_row) (map fst left_select))
    (@eval_scalar_values_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      (env_t T right_env right_row) (map fst right_select)).

(** One-directional structural induction for Project.  Positional [Forall2]
    preserves list order and multiplicity; the scalar contract preserves the
    first reached error instead of treating projection as a pure [map]. *)
Lemma eval_project_rows_relation_forward :
  forall schedule left_env left_select left_rows left_outcome,
    @eval_project_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      left_env left_select left_rows left_outcome ->
    forall right_env right_select right_rows row_rel output_rel,
      Forall2 row_rel left_rows right_rows ->
      (forall left_row right_row,
        row_rel left_row right_row ->
        project_row_observation_related_at schedule
          left_env left_select left_row
          right_env right_select right_row output_rel) ->
      exists right_outcome,
        @eval_project_rows_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          right_env right_select right_rows right_outcome /\
        outcome_equiv (Forall2 output_rel) left_outcome right_outcome.
Proof.
intros schedule left_env left_select left_rows left_outcome Heval.
induction Heval as
  [left_env left_select
  |left_env left_select left_row left_rows error Hleft_scalar
  |left_env left_select left_row left_rows left_values left_tail
      Hleft_scalar Hleft_tail IHtail];
  intros right_env right_select right_rows row_rel output_rel
    Hrows Hpoint.
- inversion Hrows; subst.
  exists (SqlSuccess nil); split; [constructor|constructor].
- inversion Hrows as
    [|left_head right_head left_tail_rows right_tail_rows Hrow Hrest]; subst.
  pose proof (Hpoint left_row right_head Hrow) as Hlocal.
  destruct Hlocal as [_ [_ [_ [_ Herrors]]]].
  exists (SqlError error); split.
  + apply EProjectRows_HeadError.
    now apply (proj1 (Herrors error)).
  + reflexivity.
- inversion Hrows as
    [|left_head right_head left_tail_rows right_tail_rows Hrow Hrest]; subst.
  pose proof (Hpoint left_row right_head Hrow) as Hlocal.
  destruct Hlocal as [_ [_ [Hforward _]]].
  destruct (Hforward left_values Hleft_scalar) as
    [right_values [Hright_scalar Hhead]].
  destruct (IHtail right_env right_select right_tail_rows
    row_rel output_rel Hrest Hpoint) as
    [right_tail [Hright_tail Htail]].
  exists
    (@project_cons_outcome T
      (@project_row T relname right_select right_values) right_tail).
  split.
  + eapply EProjectRows_Cons; eassumption.
  + destruct left_tail as [left_rows'|left_error];
      destruct right_tail as [right_rows'|right_error];
      cbn [project_cons_outcome] in Htail |- *; try contradiction.
    * now constructor.
    * exact Htail.
Qed.

(** Bidirectional evaluator-level Project transport.  No tuple equality,
    schema identity, or concrete SELECT shape is built into this theorem. *)
Theorem eval_project_rows_relation_transport :
  forall schedule left_env left_select left_rows
      right_env right_select right_rows row_rel output_rel,
    Forall2 row_rel left_rows right_rows ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      project_row_observation_related_at schedule
        left_env left_select left_row
        right_env right_select right_row output_rel) ->
    outcome_relation_transport (Forall2 output_rel)
      (@eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env left_select left_rows)
      (@eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        right_env right_select right_rows).
Proof.
intros schedule left_env left_select left_rows
  right_env right_select right_rows row_rel output_rel Hrows Hpoint.
assert (Hrows_flip :
  Forall2 (fun right_row left_row => row_rel left_row right_row)
    right_rows left_rows).
{ now apply Forall2_relation_flip. }
assert (Hpoint_flip : forall right_row left_row,
  (fun right_row left_row => row_rel left_row right_row)
      right_row left_row ->
  project_row_observation_related_at schedule
    right_env right_select right_row
    left_env left_select left_row
    (fun right_output left_output => output_rel left_output right_output)).
{
  intros right_row left_row Hrow.
  unfold project_row_observation_related_at.
  apply outcome_relation_equiv_flip.
  now apply Hpoint.
}
split.
- intros left_output Hleft.
  destruct (@eval_project_rows_relation_forward
    schedule left_env left_select left_rows (SqlSuccess left_output) Hleft
    right_env right_select right_rows row_rel output_rel Hrows Hpoint) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists right_output; now split.
  + contradiction.
- split.
  + intros right_output Hright.
    destruct (@eval_project_rows_relation_forward
      schedule right_env right_select right_rows (SqlSuccess right_output)
      Hright left_env left_select left_rows
      (fun right_row left_row => row_rel left_row right_row)
      (fun right_output left_output => output_rel left_output right_output)
      Hrows_flip Hpoint_flip) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_output|left_error]; cbn in Hrelated.
    * exists left_output; split; [exact Hobserved|].
      now apply Forall2_relation_flip in Hrelated.
    * contradiction.
  + intro error; split; intro Herror.
    * destruct (@eval_project_rows_relation_forward
        schedule left_env left_select left_rows (SqlError error) Herror
        right_env right_select right_rows row_rel output_rel Hrows Hpoint) as
        [observed [Hobserved Hrelated]].
      destruct observed as [right_output|right_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst right_error.
    * destruct (@eval_project_rows_relation_forward
        schedule right_env right_select right_rows (SqlError error) Herror
        left_env left_select left_rows
        (fun right_row left_row => row_rel left_row right_row)
        (fun right_output left_output => output_rel left_output right_output)
        Hrows_flip Hpoint_flip) as
        [observed [Hobserved Hrelated]].
      destruct observed as [left_output|left_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst left_error.
Qed.

(** Constructor-level RowMap transport.  Output attribute lists are metadata
    and therefore may differ at this relation layer; a final query-equivalence
    theorem must still prove the endpoint signatures equal. *)
Lemma query_expr_row_map_relation_forward :
  forall schedule env
      left_outputs left_map left_input
      right_outputs right_map right_input row_rel output_rel,
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_input)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_input) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      row_map_observation_related_at
        left_map left_row right_map right_row output_rel) ->
    forall left_outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_RowMap left_outputs left_map left_input) left_outcome ->
      exists right_outcome,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env (QExpr_RowMap right_outputs right_map right_input) right_outcome /\
        outcome_equiv (Forall2 output_rel) left_outcome right_outcome.
Proof.
intros schedule env left_outputs left_map left_input
  right_outputs right_map right_input row_rel output_rel
  [Hchild_forward [_ Hchild_errors]] Hpoint left_outcome Hleft.
inversion Hleft; subst.
- exists (SqlError error); split; [|reflexivity].
  apply EQuery_RowMapChildError.
  match goal with
  | Herror : context [eval_query_expr_outcome] |- _ =>
      now apply (proj1 (Hchild_errors error)) in Herror
  end.
- match goal with
  | Hchild : context [eval_query_expr_outcome] |- _ =>
      destruct (Hchild_forward _ Hchild) as
        [right_rows [Hright_child Hrows]];
      exists (@row_map_rows_outcome T right_map right_rows); split;
      [now apply EQuery_RowMapRows|]
  end.
  now apply row_map_rows_outcome_relation with (row_rel := row_rel).
Qed.

Theorem query_expr_row_map_relation_transport :
  forall schedule env
      left_outputs left_map left_input
      right_outputs right_map right_input row_rel output_rel,
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_input)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_input) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      row_map_observation_related_at
        left_map left_row right_map right_row output_rel) ->
    outcome_relation_transport (Forall2 output_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_RowMap left_outputs left_map left_input))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_RowMap right_outputs right_map right_input)).
Proof.
intros schedule env left_outputs left_map left_input
  right_outputs right_map right_input row_rel output_rel Hchild Hpoint.
pose proof (outcome_relation_transport_Forall2_flip Hchild) as Hchild_flip.
assert (Hpoint_flip : forall right_row left_row,
  (fun right_row left_row => row_rel left_row right_row)
      right_row left_row ->
  row_map_observation_related_at right_map right_row left_map left_row
    (fun right_output left_output => output_rel left_output right_output)).
{
  intros right_row left_row Hrow.
  unfold row_map_observation_related_at.
  apply outcome_equiv_flip_relation.
  now apply Hpoint.
}
split.
- intros left_output Hleft.
  destruct (@query_expr_row_map_relation_forward
    schedule env left_outputs left_map left_input
    right_outputs right_map right_input row_rel output_rel
    Hchild Hpoint (SqlSuccess left_output) Hleft) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists right_output; now split.
  + contradiction.
- split.
  + intros right_output Hright.
    destruct (@query_expr_row_map_relation_forward
      schedule env right_outputs right_map right_input
      left_outputs left_map left_input
      (fun right_row left_row => row_rel left_row right_row)
      (fun right_output left_output => output_rel left_output right_output)
      Hchild_flip Hpoint_flip (SqlSuccess right_output) Hright) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_output|left_error]; cbn in Hrelated.
    * exists left_output; split; [exact Hobserved|].
      now apply Forall2_relation_flip in Hrelated.
    * contradiction.
  + intro error; split; intro Herror.
    * destruct (@query_expr_row_map_relation_forward
        schedule env left_outputs left_map left_input
        right_outputs right_map right_input row_rel output_rel
        Hchild Hpoint (SqlError error) Herror) as
        [observed [Hobserved Hrelated]].
      destruct observed as [right_output|right_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst right_error.
    * destruct (@query_expr_row_map_relation_forward
        schedule env right_outputs right_map right_input
        left_outputs left_map left_input
        (fun right_row left_row => row_rel left_row right_row)
        (fun right_output left_output => output_rel left_output right_output)
        Hchild_flip Hpoint_flip (SqlError error) Herror) as
        [observed [Hobserved Hrelated]].
      destruct observed as [left_output|left_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst left_error.
Qed.

(** One-directional Filter traversal under an arbitrary positional row
    relation.  [filter_scalar_observation_equiv_at] compares SQL acceptance
    (TRUE versus non-TRUE) and exact errors, rather than requiring equal Bool3
    payloads. *)
Lemma eval_filter_rows_relation_forward :
  forall schedule left_env left_formula left_rows left_outcome,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      left_env left_formula left_rows left_outcome ->
    forall right_env right_formula right_rows row_rel,
      Forall2 row_rel left_rows right_rows ->
      (forall left_row right_row,
        row_rel left_row right_row ->
        @filter_scalar_observation_equiv_at T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          (env_t T left_env left_row) left_formula
          (env_t T right_env right_row) right_formula) ->
      exists right_outcome,
        @eval_filter_rows_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          right_env right_formula right_rows right_outcome /\
        outcome_equiv (Forall2 row_rel) left_outcome right_outcome.
Proof.
intros schedule left_env left_formula left_rows left_outcome Heval.
induction Heval as
  [left_env left_formula
  |left_env left_formula left_row left_rows error Hleft_formula
  |left_env left_formula left_row left_rows left_truth left_tail
      Hleft_formula Hleft_tail IHtail];
  intros right_env right_formula right_rows row_rel Hrows Hpoint.
- inversion Hrows; subst.
  exists (SqlSuccess nil); split; [constructor|constructor].
- inversion Hrows as
    [|left_head right_head left_tail_rows right_tail_rows Hrow Hrest]; subst.
  pose proof (Hpoint left_row right_head Hrow) as Hlocal.
  destruct Hlocal as [_ [_ Herrors]].
  exists (SqlError error); split.
  + apply EFilterRows_HeadError.
    now apply (proj1 (Herrors error)).
  + reflexivity.
- inversion Hrows as
    [|left_head right_head left_tail_rows right_tail_rows Hrow Hrest]; subst.
  pose proof (Hpoint left_row right_head Hrow) as Hlocal.
  destruct Hlocal as [Hforward _].
  destruct (Hforward left_truth Hleft_formula) as
    [right_truth [Hright_formula Haccept]].
  destruct (IHtail right_env right_formula right_tail_rows
    row_rel Hrest Hpoint) as [right_tail [Hright_tail Htail]].
  exists (@filter_cons_outcome T right_truth right_head right_tail); split.
  + eapply EFilterRows_Cons; eassumption.
  + destruct left_tail as [left_rows'|left_error];
      destruct right_tail as [right_rows'|right_error];
      cbn in Htail |- *; try contradiction.
    * unfold filter_cons_outcome.
      destruct (Bool.is_true (B T) left_truth) eqn:Hleft;
        destruct (Bool.is_true (B T) right_truth) eqn:Hright;
        try discriminate Haccept; cbn.
      -- now constructor.
      -- exact Htail.
    * exact Htail.
Qed.

Theorem eval_filter_rows_relation_transport :
  forall schedule left_env left_formula left_rows
      right_env right_formula right_rows row_rel,
    Forall2 row_rel left_rows right_rows ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      @filter_scalar_observation_equiv_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        (env_t T left_env left_row) left_formula
        (env_t T right_env right_row) right_formula) ->
    outcome_relation_transport (Forall2 row_rel)
      (@eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        left_env left_formula left_rows)
      (@eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        right_env right_formula right_rows).
Proof.
intros schedule left_env left_formula left_rows
  right_env right_formula right_rows row_rel Hrows Hpoint.
assert (Hrows_flip :
  Forall2 (fun right_row left_row => row_rel left_row right_row)
    right_rows left_rows).
{ now apply Forall2_relation_flip. }
assert (Hpoint_flip : forall right_row left_row,
  (fun right_row left_row => row_rel left_row right_row)
      right_row left_row ->
  @filter_scalar_observation_equiv_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule
    (env_t T right_env right_row) right_formula
    (env_t T left_env left_row) left_formula).
{
  intros right_row left_row Hrow.
  apply filter_scalar_observation_equiv_at_sym.
  now apply Hpoint.
}
split.
- intros left_output Hleft.
  destruct (@eval_filter_rows_relation_forward
    schedule left_env left_formula left_rows (SqlSuccess left_output) Hleft
    right_env right_formula right_rows row_rel Hrows Hpoint) as
    [observed [Hobserved Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists right_output; now split.
  + contradiction.
- split.
  + intros right_output Hright.
    destruct (@eval_filter_rows_relation_forward
      schedule right_env right_formula right_rows (SqlSuccess right_output)
      Hright left_env left_formula left_rows
      (fun right_row left_row => row_rel left_row right_row)
      Hrows_flip Hpoint_flip) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_output|left_error]; cbn in Hrelated.
    * exists left_output; split; [exact Hobserved|].
      now apply Forall2_relation_flip in Hrelated.
    * contradiction.
  + intro error; split; intro Herror.
    * destruct (@eval_filter_rows_relation_forward
        schedule left_env left_formula left_rows (SqlError error) Herror
        right_env right_formula right_rows row_rel Hrows Hpoint) as
        [observed [Hobserved Hrelated]].
      destruct observed as [right_output|right_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst right_error.
    * destruct (@eval_filter_rows_relation_forward
        schedule right_env right_formula right_rows (SqlError error) Herror
        left_env left_formula left_rows
        (fun right_row left_row => row_rel left_row right_row)
        Hrows_flip Hpoint_flip) as
        [observed [Hobserved Hrelated]].
      destruct observed as [left_output|left_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst left_error.
Qed.

(** Constructor-level forward transport for Project.  Child failures and
    per-row projection failures are kept distinct in the proof, but exported
    through one outcome relation. *)
Lemma query_expr_project_relation_forward :
  forall schedule env left_select left_input right_select right_input
      row_rel output_rel,
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_input)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_input) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      project_row_observation_related_at schedule
        env left_select left_row env right_select right_row output_rel) ->
    forall left_outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Project left_select left_input) left_outcome ->
      exists right_outcome,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env (QExpr_Project right_select right_input) right_outcome /\
        outcome_equiv (Forall2 output_rel) left_outcome right_outcome.
Proof.
intros schedule env left_select left_input right_select right_input
  row_rel output_rel [Hchild_forward [_ Hchild_errors]] Hpoint
  left_outcome Hleft.
destruct left_outcome as [left_output|error].
- inversion Hleft; subst.
  match goal with
  | H : @eval_query_expr_outcome _ _ _ _ _ _ _ _ _ _ left_input
      (SqlSuccess ?left_rows) |- _ =>
      rename H into Hleft_child
  end.
  match goal with
  | H : @eval_project_rows_outcome _ _ _ _ _ _ _ _ _ _ _ _
      (SqlSuccess left_output) |- _ => rename H into Hleft_project
  end.
  destruct (Hchild_forward _ Hleft_child) as
    [right_rows [Hright_child Hrows]].
  destruct (@eval_project_rows_relation_forward
    schedule env left_select _ (SqlSuccess left_output) Hleft_project
    env right_select right_rows row_rel output_rel Hrows Hpoint) as
    [observed [Hright_project Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists (SqlSuccess right_output); split; [|exact Hrelated].
    eapply EQuery_ProjectRows; eassumption.
  + contradiction.
- inversion Hleft; subst.
  + exists (SqlError error); split; [|reflexivity].
    apply EQuery_ProjectChildError.
    match goal with
    | H : @eval_query_expr_outcome _ _ _ _ _ _ _ _ _ _ left_input
        (SqlError error) |- _ =>
        now apply (proj1 (Hchild_errors error)) in H
    end.
  + match goal with
    | H : @eval_query_expr_outcome _ _ _ _ _ _ _ _ _ _ left_input
        (SqlSuccess ?left_rows) |- _ => rename H into Hleft_child
    end.
    match goal with
    | H : @eval_project_rows_outcome _ _ _ _ _ _ _ _ _ _ _ _
        (SqlError error) |- _ => rename H into Hleft_project
    end.
    destruct (Hchild_forward _ Hleft_child) as
      [right_rows [Hright_child Hrows]].
    destruct (@eval_project_rows_relation_forward
      schedule env left_select _ (SqlError error) Hleft_project
      env right_select right_rows row_rel output_rel Hrows Hpoint) as
      [observed [Hright_project Hrelated]].
    destruct observed as [right_output|right_error]; cbn in Hrelated.
    * contradiction.
    * subst right_error.
      exists (SqlError error); split; [|reflexivity].
      eapply EQuery_ProjectRows; eassumption.
Qed.

Theorem query_expr_project_relation_transport :
  forall schedule env left_select left_input right_select right_input
      row_rel output_rel,
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_input)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_input) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      project_row_observation_related_at schedule
        env left_select left_row env right_select right_row output_rel) ->
    outcome_relation_transport (Forall2 output_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Project left_select left_input))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Project right_select right_input)).
Proof.
intros schedule env left_select left_input right_select right_input
  row_rel output_rel Hchild Hpoint.
pose proof (outcome_relation_transport_Forall2_flip Hchild) as Hchild_flip.
assert (Hpoint_flip : forall right_row left_row,
  (fun right_row left_row => row_rel left_row right_row)
      right_row left_row ->
  project_row_observation_related_at schedule
    env right_select right_row env left_select left_row
    (fun right_output left_output => output_rel left_output right_output)).
{
  intros right_row left_row Hrow.
  unfold project_row_observation_related_at.
  apply outcome_relation_equiv_flip.
  now apply Hpoint.
}
split.
- intros left_output Hleft.
  destruct (query_expr_project_relation_forward
    Hchild Hpoint Hleft) as [observed [Hobserved Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists right_output; now split.
  + contradiction.
- split.
  + intros right_output Hright.
    destruct (@query_expr_project_relation_forward
      schedule env right_select right_input left_select left_input
      (fun right_row left_row => row_rel left_row right_row)
      (fun right_output left_output => output_rel left_output right_output)
      Hchild_flip Hpoint_flip (SqlSuccess right_output) Hright) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_output|left_error]; cbn in Hrelated.
    * exists left_output; split; [exact Hobserved|].
      now apply Forall2_relation_flip in Hrelated.
    * contradiction.
  + intro error; split; intro Herror.
    * destruct (query_expr_project_relation_forward
        Hchild Hpoint Herror) as [observed [Hobserved Hrelated]].
      destruct observed as [right_output|right_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst right_error.
    * destruct (@query_expr_project_relation_forward
        schedule env right_select right_input left_select left_input
        (fun right_row left_row => row_rel left_row right_row)
        (fun right_output left_output => output_rel left_output right_output)
        Hchild_flip Hpoint_flip (SqlError error) Herror) as
        [observed [Hobserved Hrelated]].
      destruct observed as [left_output|left_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst left_error.
Qed.

(** Filter constructor lift.  The output relation is the input row relation:
    corresponding rows are retained or rejected together by the pointwise SQL
    acceptance contract. *)
Lemma query_expr_filter_relation_forward :
  forall schedule env left_formula left_input right_formula right_input row_rel,
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_input)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_input) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      @filter_scalar_observation_equiv_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    forall left_outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter left_formula left_input) left_outcome ->
      exists right_outcome,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env (QExpr_Filter right_formula right_input) right_outcome /\
        outcome_equiv (Forall2 row_rel) left_outcome right_outcome.
Proof.
intros schedule env left_formula left_input right_formula right_input row_rel
  [Hchild_forward [_ Hchild_errors]] Hpoint left_outcome Hleft.
destruct left_outcome as [left_output|error].
- inversion Hleft; subst.
  match goal with
  | H : @eval_query_expr_outcome _ _ _ _ _ _ _ _ _ _ left_input
      (SqlSuccess ?left_rows) |- _ => rename H into Hleft_child
  end.
  match goal with
  | H : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _ _
      (SqlSuccess left_output) |- _ => rename H into Hleft_filter
  end.
  destruct (Hchild_forward _ Hleft_child) as
    [right_rows [Hright_child Hrows]].
  destruct (@eval_filter_rows_relation_forward
    schedule env left_formula _ (SqlSuccess left_output) Hleft_filter
    env right_formula right_rows row_rel Hrows Hpoint) as
    [observed [Hright_filter Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists (SqlSuccess right_output); split; [|exact Hrelated].
    eapply EQuery_FilterRows; eassumption.
  + contradiction.
- inversion Hleft; subst.
  + exists (SqlError error); split; [|reflexivity].
    apply EQuery_FilterChildError.
    match goal with
    | H : @eval_query_expr_outcome _ _ _ _ _ _ _ _ _ _ left_input
        (SqlError error) |- _ =>
        now apply (proj1 (Hchild_errors error)) in H
    end.
  + match goal with
    | H : @eval_query_expr_outcome _ _ _ _ _ _ _ _ _ _ left_input
        (SqlSuccess ?left_rows) |- _ => rename H into Hleft_child
    end.
    match goal with
    | H : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ _ _
        (SqlError error) |- _ => rename H into Hleft_filter
    end.
    destruct (Hchild_forward _ Hleft_child) as
      [right_rows [Hright_child Hrows]].
    destruct (@eval_filter_rows_relation_forward
      schedule env left_formula _ (SqlError error) Hleft_filter
      env right_formula right_rows row_rel Hrows Hpoint) as
      [observed [Hright_filter Hrelated]].
    destruct observed as [right_output|right_error]; cbn in Hrelated.
    * contradiction.
    * subst right_error.
      exists (SqlError error); split; [|reflexivity].
      eapply EQuery_FilterRows; eassumption.
Qed.

Theorem query_expr_filter_relation_transport :
  forall schedule env left_formula left_input right_formula right_input row_rel,
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_input)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_input) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      @filter_scalar_observation_equiv_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter left_formula left_input))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter right_formula right_input)).
Proof.
intros schedule env left_formula left_input right_formula right_input row_rel
  Hchild Hpoint.
pose proof (outcome_relation_transport_Forall2_flip Hchild) as Hchild_flip.
assert (Hpoint_flip : forall right_row left_row,
  (fun right_row left_row => row_rel left_row right_row)
      right_row left_row ->
  @filter_scalar_observation_equiv_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule
    (env_t T env right_row) right_formula
    (env_t T env left_row) left_formula).
{
  intros right_row left_row Hrow.
  apply filter_scalar_observation_equiv_at_sym.
  now apply Hpoint.
}
split.
- intros left_output Hleft.
  destruct (query_expr_filter_relation_forward
    Hchild Hpoint Hleft) as [observed [Hobserved Hrelated]].
  destruct observed as [right_output|right_error]; cbn in Hrelated.
  + exists right_output; now split.
  + contradiction.
- split.
  + intros right_output Hright.
    destruct (@query_expr_filter_relation_forward
      schedule env right_formula right_input left_formula left_input
      (fun right_row left_row => row_rel left_row right_row)
      Hchild_flip Hpoint_flip (SqlSuccess right_output) Hright) as
      [observed [Hobserved Hrelated]].
    destruct observed as [left_output|left_error]; cbn in Hrelated.
    * exists left_output; split; [exact Hobserved|].
      now apply Forall2_relation_flip in Hrelated.
    * contradiction.
  + intro error; split; intro Herror.
    * destruct (query_expr_filter_relation_forward
        Hchild Hpoint Herror) as [observed [Hobserved Hrelated]].
      destruct observed as [right_output|right_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst right_error.
    * destruct (@query_expr_filter_relation_forward
        schedule env right_formula right_input left_formula left_input
        (fun right_row left_row => row_rel left_row right_row)
        Hchild_flip Hpoint_flip (SqlError error) Herror) as
        [observed [Hobserved Hrelated]].
      destruct observed as [left_output|left_error]; cbn in Hrelated.
      -- contradiction.
      -- now subst left_error.
Qed.

(** Public possible-schedule Project lift.  The same-schedule premise is a
    sufficient compositional interface; rewrites that remap schedules can
    first use the general schedule-transport lemmas above. *)
Theorem query_expr_project_possible_outcome_related :
  forall env left_select left_input right_select right_input
      row_rel output_rel,
    (forall schedule,
      outcome_relation_transport (Forall2 row_rel)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env left_input)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env right_input)) ->
    (forall schedule left_row right_row,
      row_rel left_row right_row ->
      project_row_observation_related_at schedule
        env left_select left_row env right_select right_row output_rel) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env (QExpr_Project left_select left_input) outcome) ->
    query_expr_possible_outcome_related env (Forall2 output_rel)
      (QExpr_Project left_select left_input)
      (QExpr_Project right_select right_input).
Proof.
intros env left_select left_input right_select right_input
  row_rel output_rel Hchild Hpoint Hinhabited.
unfold query_expr_possible_outcome_related,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_of_left_inhabited_transport; [exact Hinhabited|].
apply outcome_relation_transport_exists_same_index.
intro schedule.
apply (query_expr_project_relation_transport (row_rel := row_rel)).
- exact (Hchild schedule).
- exact (Hpoint schedule).
Qed.

Theorem query_expr_row_map_possible_outcome_related :
  forall env
      left_outputs left_map left_input
      right_outputs right_map right_input row_rel output_rel,
    (forall schedule,
      outcome_relation_transport (Forall2 row_rel)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env left_input)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env right_input)) ->
    (forall left_row right_row,
      row_rel left_row right_row ->
      row_map_observation_related_at
        left_map left_row right_map right_row output_rel) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env
        (QExpr_RowMap left_outputs left_map left_input) outcome) ->
    query_expr_possible_outcome_related env (Forall2 output_rel)
      (QExpr_RowMap left_outputs left_map left_input)
      (QExpr_RowMap right_outputs right_map right_input).
Proof.
intros env left_outputs left_map left_input
  right_outputs right_map right_input row_rel output_rel
  Hchild Hpoint Hinhabited.
unfold query_expr_possible_outcome_related,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_of_left_inhabited_transport; [exact Hinhabited|].
apply outcome_relation_transport_exists_same_index.
intro schedule.
eapply query_expr_row_map_relation_transport.
- exact (Hchild schedule).
- exact Hpoint.
Qed.

Theorem query_expr_filter_possible_outcome_related :
  forall env left_formula left_input right_formula right_input row_rel,
    (forall schedule,
      outcome_relation_transport (Forall2 row_rel)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env left_input)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env right_input)) ->
    (forall schedule left_row right_row,
      row_rel left_row right_row ->
      @filter_scalar_observation_equiv_at T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        (env_t T env left_row) left_formula
        (env_t T env right_row) right_formula) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env (QExpr_Filter left_formula left_input) outcome) ->
    query_expr_possible_outcome_related env (Forall2 row_rel)
      (QExpr_Filter left_formula left_input)
      (QExpr_Filter right_formula right_input).
Proof.
intros env left_formula left_input right_formula right_input
  row_rel Hchild Hpoint Hinhabited.
unfold query_expr_possible_outcome_related,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_of_left_inhabited_transport; [exact Hinhabited|].
apply outcome_relation_transport_exists_same_index.
intro schedule.
apply (query_expr_filter_relation_transport (row_rel := row_rel)).
- exact (Hchild schedule).
- exact (Hpoint schedule).
Qed.

(** The local continuation after both children of a native JOIN have
    succeeded.  Keeping the arbitrary output-list representative inside this
    relation is essential: JOIN is a bag-reset operator, while its enclosing
    query observes rows rather than the implementation's output bag. *)
Definition query_join_rows_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (kind : query_join_kind)
    (predicate : scalar_expr T relname ScalarResultBoolean)
    (matched_select left_select right_select : @query_select_list T relname)
    (left_rows right_rows : list (tuple T)) :
    sql_outcome (list (tuple T)) -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_rows =>
        exists output_bag,
          @eval_join_bag_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            schedule env kind predicate matched_select left_select right_select
            (rows_bag T left_rows) (rows_bag T right_rows)
            (SqlSuccess output_bag) /\
          query_same_rows_as_bag output_rows output_bag
    | SqlError error =>
        @eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env kind predicate matched_select left_select right_select
          (rows_bag T left_rows) (rows_bag T right_rows)
          (SqlError error)
    end.

(** Complete scheduled evaluator transport for native JOIN.  The two child
    row relations and the output row relation are arbitrary.  Predicate
    acceptance, matched/unmatched projection, multiplicity, NULL-extension,
    and local errors remain together in the continuation contract instead of
    being approximated by tuple equality or a particular rewrite pattern. *)
Theorem query_expr_join_relation_transport :
  forall left_schedule right_schedule env
      left_kind left_predicate
      left_matched_select left_left_select left_right_select
      left_first left_second
      right_kind right_predicate
      right_matched_select right_left_select right_right_select
      right_first right_second
      left_row_rel right_row_rel output_row_rel,
    outcome_relation_transport (Forall2 left_row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_transport (Forall2 right_row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    (forall left_first_rows right_first_rows,
      Forall2 left_row_rel left_first_rows right_first_rows ->
      forall left_second_rows right_second_rows,
        Forall2 right_row_rel left_second_rows right_second_rows ->
        outcome_relation_transport (Forall2 output_row_rel)
          (query_join_rows_outcomes left_schedule env left_kind
            left_predicate left_matched_select left_left_select
            left_right_select left_first_rows left_second_rows)
          (query_join_rows_outcomes right_schedule env right_kind
            right_predicate right_matched_select right_left_select
            right_right_select right_first_rows right_second_rows)) ->
    outcome_relation_transport (Forall2 output_row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Join left_kind left_predicate left_matched_select
          left_left_select left_right_select left_first left_second))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Join right_kind right_predicate right_matched_select
          right_left_select right_right_select right_first right_second)).
Proof.
intros left_schedule right_schedule env
  left_kind left_predicate
  left_matched_select left_left_select left_right_select
  left_first left_second
  right_kind right_predicate
  right_matched_select right_left_select right_right_select
  right_first right_second
  left_row_rel right_row_rel output_row_rel
  Hfirst Hsecond Hlocal.
destruct Hfirst as [Hfirst_forward [Hfirst_backward Hfirst_errors]].
destruct Hsecond as [Hsecond_forward [Hsecond_backward Hsecond_errors]].
split.
- intros left_output Hleft_parent.
  apply eval_query_expr_join_success_iff in Hleft_parent.
  destruct Hleft_parent as
    [left_first_rows [left_second_rows [left_output_bag
      [Hleft_first [Hleft_second [Hleft_join Hleft_output]]]]]].
  destruct (Hfirst_forward left_first_rows Hleft_first) as
    [right_first_rows [Hright_first Hfirst_rows]].
  destruct (Hsecond_forward left_second_rows Hleft_second) as
    [right_second_rows [Hright_second Hsecond_rows]].
  destruct (Hlocal left_first_rows right_first_rows Hfirst_rows
    left_second_rows right_second_rows Hsecond_rows) as [Hforward _].
  destruct (Hforward left_output
    (ex_intro _ left_output_bag (conj Hleft_join Hleft_output))) as
    [right_output [Hright_local Houtput_rows]].
  exists right_output; split; [|exact Houtput_rows].
  destruct Hright_local as
    [right_output_bag [Hright_join Hright_output]].
  apply eval_query_expr_join_success_iff.
  now exists right_first_rows, right_second_rows, right_output_bag.
- split.
  + intros right_output Hright_parent.
    apply eval_query_expr_join_success_iff in Hright_parent.
    destruct Hright_parent as
      [right_first_rows [right_second_rows [right_output_bag
        [Hright_first [Hright_second [Hright_join Hright_output]]]]]].
    destruct (Hfirst_backward right_first_rows Hright_first) as
      [left_first_rows [Hleft_first Hfirst_rows]].
    destruct (Hsecond_backward right_second_rows Hright_second) as
      [left_second_rows [Hleft_second Hsecond_rows]].
    destruct (Hlocal left_first_rows right_first_rows Hfirst_rows
      left_second_rows right_second_rows Hsecond_rows) as
      [_ [Hbackward _]].
    destruct (Hbackward right_output
      (ex_intro _ right_output_bag (conj Hright_join Hright_output))) as
      [left_output [Hleft_local Houtput_rows]].
    exists left_output; split; [|exact Houtput_rows].
    destruct Hleft_local as
      [left_output_bag [Hleft_join Hleft_output]].
    apply eval_query_expr_join_success_iff.
    now exists left_first_rows, left_second_rows, left_output_bag.
  + intro error; split; intro Hparent_error.
    * apply eval_query_expr_join_error_iff in Hparent_error.
      destruct Hparent_error as
        [Hleft_first_error |
         [left_first_rows [Hleft_first Hleft_rest]]].
      -- apply eval_query_expr_join_error_iff; left.
         now apply (proj1 (Hfirst_errors error)).
      -- destruct Hleft_rest as
           [Hleft_second_error |
            [left_second_rows [Hleft_second Hleft_local_error]]].
         ++ destruct (Hfirst_forward left_first_rows Hleft_first) as
              [right_first_rows [Hright_first _]].
            apply eval_query_expr_join_error_iff; right.
            exists right_first_rows; split; [exact Hright_first|left].
            now apply (proj1 (Hsecond_errors error)).
         ++ destruct (Hfirst_forward left_first_rows Hleft_first) as
              [right_first_rows [Hright_first Hfirst_rows]].
            destruct (Hsecond_forward left_second_rows Hleft_second) as
              [right_second_rows [Hright_second Hsecond_rows]].
            destruct (Hlocal left_first_rows right_first_rows Hfirst_rows
              left_second_rows right_second_rows Hsecond_rows) as
              [_ [_ Hlocal_errors]].
            apply eval_query_expr_join_error_iff; right.
            exists right_first_rows; split; [exact Hright_first|right].
            exists right_second_rows; split; [exact Hright_second|].
            now apply (proj1 (Hlocal_errors error)).
    * apply eval_query_expr_join_error_iff in Hparent_error.
      destruct Hparent_error as
        [Hright_first_error |
         [right_first_rows [Hright_first Hright_rest]]].
      -- apply eval_query_expr_join_error_iff; left.
         now apply (proj2 (Hfirst_errors error)).
      -- destruct Hright_rest as
           [Hright_second_error |
            [right_second_rows [Hright_second Hright_local_error]]].
         ++ destruct (Hfirst_backward right_first_rows Hright_first) as
              [left_first_rows [Hleft_first _]].
            apply eval_query_expr_join_error_iff; right.
            exists left_first_rows; split; [exact Hleft_first|left].
            now apply (proj2 (Hsecond_errors error)).
         ++ destruct (Hfirst_backward right_first_rows Hright_first) as
              [left_first_rows' [Hleft_first' Hfirst_rows]].
            destruct (Hsecond_backward right_second_rows Hright_second) as
              [left_second_rows [Hleft_second Hsecond_rows]].
            destruct (Hlocal left_first_rows' right_first_rows Hfirst_rows
              left_second_rows right_second_rows Hsecond_rows) as
              [_ [_ Hlocal_errors]].
            apply eval_query_expr_join_error_iff; right.
            exists left_first_rows'; split; [exact Hleft_first'|right].
            exists left_second_rows; split; [exact Hleft_second|].
            now apply (proj2 (Hlocal_errors error)).
Qed.

(** Public all-schedule specialization.  It does not require the two sides to
    use identical JOIN syntax: kind, predicate, three projection branches,
    children, and row schemas may all differ.  The only semantic obligations
    are child relation transport and the local JOIN continuation contract. *)
Theorem query_expr_join_possible_outcome_related_same_schedule :
  forall env
      left_kind left_predicate
      left_matched_select left_left_select left_right_select
      left_first left_second
      right_kind right_predicate
      right_matched_select right_left_select right_right_select
      right_first right_second
      left_row_rel right_row_rel output_row_rel,
    (forall schedule,
      outcome_relation_transport (Forall2 left_row_rel)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left_first)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right_first)) ->
    (forall schedule,
      outcome_relation_transport (Forall2 right_row_rel)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left_second)
        (@eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right_second)) ->
    (forall schedule left_first_rows right_first_rows,
      Forall2 left_row_rel left_first_rows right_first_rows ->
      forall left_second_rows right_second_rows,
        Forall2 right_row_rel left_second_rows right_second_rows ->
        outcome_relation_transport (Forall2 output_row_rel)
          (query_join_rows_outcomes schedule env left_kind left_predicate
            left_matched_select left_left_select left_right_select
            left_first_rows left_second_rows)
          (query_join_rows_outcomes schedule env right_kind right_predicate
            right_matched_select right_left_select right_right_select
            right_first_rows right_second_rows)) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Join left_kind left_predicate left_matched_select
          left_left_select left_right_select left_first left_second) outcome) ->
    query_expr_possible_outcome_related env (Forall2 output_row_rel)
      (QExpr_Join left_kind left_predicate left_matched_select
        left_left_select left_right_select left_first left_second)
      (QExpr_Join right_kind right_predicate right_matched_select
        right_left_select right_right_select right_first right_second).
Proof.
intros env
  left_kind left_predicate
  left_matched_select left_left_select left_right_select
  left_first left_second
  right_kind right_predicate
  right_matched_select right_left_select right_right_select
  right_first right_second
  left_row_rel right_row_rel output_row_rel
  Hfirst Hsecond Hlocal Hinhabited.
unfold query_expr_possible_outcome_related,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_of_left_inhabited_transport; [exact Hinhabited|].
apply outcome_relation_transport_exists_same_index.
intro schedule.
eapply query_expr_join_relation_transport.
- exact (Hfirst schedule).
- exact (Hsecond schedule).
- intros; now apply Hlocal.
Qed.

(** Fully general all-schedule JOIN transport.  Each source schedule may be
    paired with a different target schedule, and conversely.  The paired
    schedule must transport both children coherently and use that same pair
    for the local JOIN continuation; this prevents predicate, projection, or
    error witnesses from being assembled from incompatible executions. *)
Theorem query_expr_join_possible_outcome_related :
  forall env
      left_kind left_predicate
      left_matched_select left_left_select left_right_select
      left_first left_second
      right_kind right_predicate
      right_matched_select right_left_select right_right_select
      right_first right_second
      left_row_rel right_row_rel output_row_rel,
    (forall left_schedule,
      exists right_schedule,
        outcome_relation_transport (Forall2 left_row_rel)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left_first)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right_first) /\
        outcome_relation_transport (Forall2 right_row_rel)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left_second)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right_second) /\
        (forall left_first_rows right_first_rows,
          Forall2 left_row_rel left_first_rows right_first_rows ->
          forall left_second_rows right_second_rows,
            Forall2 right_row_rel left_second_rows right_second_rows ->
            outcome_relation_transport (Forall2 output_row_rel)
              (query_join_rows_outcomes left_schedule env left_kind
                left_predicate left_matched_select left_left_select
                left_right_select left_first_rows left_second_rows)
              (query_join_rows_outcomes right_schedule env right_kind
                right_predicate right_matched_select right_left_select
                right_right_select right_first_rows right_second_rows))) ->
    (forall right_schedule,
      exists left_schedule,
        outcome_relation_transport (Forall2 left_row_rel)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left_first)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right_first) /\
        outcome_relation_transport (Forall2 right_row_rel)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left_second)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right_second) /\
        (forall left_first_rows right_first_rows,
          Forall2 left_row_rel left_first_rows right_first_rows ->
          forall left_second_rows right_second_rows,
            Forall2 right_row_rel left_second_rows right_second_rows ->
            outcome_relation_transport (Forall2 output_row_rel)
              (query_join_rows_outcomes left_schedule env left_kind
                left_predicate left_matched_select left_left_select
                left_right_select left_first_rows left_second_rows)
              (query_join_rows_outcomes right_schedule env right_kind
                right_predicate right_matched_select right_left_select
                right_right_select right_first_rows right_second_rows))) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Join left_kind left_predicate left_matched_select
          left_left_select left_right_select left_first left_second) outcome) ->
    query_expr_possible_outcome_related env (Forall2 output_row_rel)
      (QExpr_Join left_kind left_predicate left_matched_select
        left_left_select left_right_select left_first left_second)
      (QExpr_Join right_kind right_predicate right_matched_select
        right_left_select right_right_select right_first right_second).
Proof.
intros env
  left_kind left_predicate
  left_matched_select left_left_select left_right_select
  left_first left_second
  right_kind right_predicate
  right_matched_select right_left_select right_right_select
  right_first right_second
  left_row_rel right_row_rel output_row_rel
  Hschedule_forward Hschedule_backward Hinhabited.
unfold query_expr_possible_outcome_related,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_of_left_inhabited_transport; [exact Hinhabited|].
split.
- intros left_output [left_schedule Hleft].
  destruct (Hschedule_forward left_schedule) as
    [right_schedule [Hfirst [Hsecond Hlocal]]].
  pose proof (@query_expr_join_relation_transport
    left_schedule right_schedule env
    left_kind left_predicate left_matched_select left_left_select
    left_right_select left_first left_second
    right_kind right_predicate right_matched_select right_left_select
    right_right_select right_first right_second
    left_row_rel right_row_rel output_row_rel
    Hfirst Hsecond Hlocal) as Hparent.
  destruct (proj1 Hparent left_output Hleft) as
    [right_output [Hright Hrelated]].
  exists right_output; split; [now exists right_schedule|exact Hrelated].
- split.
  + intros right_output [right_schedule Hright].
    destruct (Hschedule_backward right_schedule) as
      [left_schedule [Hfirst [Hsecond Hlocal]]].
    pose proof (@query_expr_join_relation_transport
      left_schedule right_schedule env
      left_kind left_predicate left_matched_select left_left_select
      left_right_select left_first left_second
      right_kind right_predicate right_matched_select right_left_select
      right_right_select right_first right_second
      left_row_rel right_row_rel output_row_rel
      Hfirst Hsecond Hlocal) as Hparent.
    destruct (proj1 (proj2 Hparent) right_output Hright) as
      [left_output [Hleft Hrelated]].
    exists left_output; split; [now exists left_schedule|exact Hrelated].
  + intro error; split.
    * intros [left_schedule Hleft].
      destruct (Hschedule_forward left_schedule) as
        [right_schedule [Hfirst [Hsecond Hlocal]]].
      pose proof (@query_expr_join_relation_transport
        left_schedule right_schedule env
        left_kind left_predicate left_matched_select left_left_select
        left_right_select left_first left_second
        right_kind right_predicate right_matched_select right_left_select
        right_right_select right_first right_second
        left_row_rel right_row_rel output_row_rel
        Hfirst Hsecond Hlocal) as Hparent.
      exists right_schedule.
      now apply (proj1 ((proj2 (proj2 Hparent)) error)).
    * intros [right_schedule Hright].
      destruct (Hschedule_backward right_schedule) as
        [left_schedule [Hfirst [Hsecond Hlocal]]].
      pose proof (@query_expr_join_relation_transport
        left_schedule right_schedule env
        left_kind left_predicate left_matched_select left_left_select
        left_right_select left_first left_second
        right_kind right_predicate right_matched_select right_left_select
        right_right_select right_first right_second
        left_row_rel right_row_rel output_row_rel
        Hfirst Hsecond Hlocal) as Hparent.
      exists left_schedule.
      now apply (proj2 ((proj2 (proj2 Hparent)) error)).
Qed.

(** The local continuation after a successful GROUP child.  It includes the
    arbitrary list representative chosen for the result bag, so its relation
    parameter describes exactly the rows observable by the enclosing query,
    not an implementation-specific bag or group-list representation. *)
Definition query_group_rows_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (select_list : @query_select_list T relname)
    (group_keys : list (scalar_expr T relname ScalarResultValue))
    (having : scalar_expr T relname ScalarResultBoolean)
    (input_rows : list (tuple T)) : sql_outcome (list (tuple T)) -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_rows =>
        exists output_bag,
          @eval_group_bag_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            schedule env select_list group_keys having
            (rows_bag T input_rows) (SqlSuccess output_bag) /\
          query_same_rows_as_bag output_rows output_bag
    | SqlError error =>
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env select_list group_keys having
          (rows_bag T input_rows) (SqlError error)
    end.

(** Public introduction rules consume the complete possible relations
    directly, quantifying over Boolean evaluation schedules rather than
    selecting one schedule. *)
Theorem query_expr_possible_equiv_of_ordered_observations :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess rows)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left (SqlError error)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right (SqlError error)) ->
    (forall left_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right
          (SqlSuccess right_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left
          (SqlSuccess left_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Houtputs Hsuccess Hleft_safe Hright_safe
  Hforward Hbackward.
split; [exact Houtputs |].
unfold query_expr_possible_observation_equiv.
now apply successful_relation_equiv_intro.
Qed.

Theorem query_expr_possible_equiv_of_observations :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess rows)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left (SqlError error)) ->
    (forall error,
      ~ @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right (SqlError error)) ->
    (forall rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess rows) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlSuccess rows)) ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Houtputs Hsuccess Hleft_safe Hright_safe Hobservations.
apply query_expr_possible_equiv_of_ordered_observations; try assumption.
- intros rows Hrows; exists rows; split.
  + now apply (proj1 (Hobservations rows)).
  + apply ordered_rows_equiv_refl.
- intros rows Hrows; exists rows; split.
  + now apply (proj2 (Hobservations rows)).
  + apply ordered_rows_equiv_refl.
Qed.

Theorem query_expr_possible_outcome_equiv_of_observations :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right outcome) ->
    (forall left_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env right
          (SqlSuccess right_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null env left
          (SqlSuccess left_rows) /\
        ordered_rows_equiv T left_rows right_rows) ->
    (forall error,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlError error) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlError error)) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Houtputs Hleft Hright Hforward Hbackward Herrors.
split; [exact Houtputs |].
unfold query_expr_possible_outcome_observation_equiv.
now apply outcome_relation_equiv_intro.
Qed.

Definition query_expr_schedule_independent
    (env : Env.env T) (query : query_expr T relname) : Prop :=
  forall left_schedule right_schedule outcome,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left_schedule env query outcome <->
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      right_schedule env query outcome.

Definition query_expr_uniform_scheduled_outcome_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      schedule env left right.

Definition query_expr_uniform_global_typed_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    @query_expr_global_typed_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule left right.

Definition query_expr_uniform_global_exists_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    @query_expr_global_exists_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule left right.

Definition query_expr_uniform_global_demand_equiv
    (demand : query_context_demand)
    (left right : query_expr T relname) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    @query_expr_global_demand_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule demand left right.

(** Typed scalar congruence is indexed by the result kind.  In particular,
    value outcomes and three-valued Boolean outcomes cannot be accidentally
    interchanged.  The relation is global in correlated environments and
    uniform in the one query-wide Boolean schedule. *)
Definition scalar_expr_uniform_global_outcome_equiv
    {kind : scalar_result_kind}
    (left right : scalar_expr T relname kind) : Prop :=
  match kind as result_kind return
      scalar_expr T relname result_kind ->
      scalar_expr T relname result_kind -> Prop with
  | ScalarResultValue =>
      fun left_value right_value =>
        forall schedule env outcome,
          @eval_scalar_value_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            schedule env left_value outcome <->
          @eval_scalar_value_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            schedule env right_value outcome
  | ScalarResultBoolean =>
      fun left_boolean right_boolean =>
        forall schedule env outcome,
          @eval_scalar_boolean_expr_outcome T relname
            basesort instance unknown symbol_runtime_error
            aggregate_runtime_error value_is_null schedule env
            left_boolean outcome <->
          @eval_scalar_boolean_expr_outcome T relname
            basesort instance unknown symbol_runtime_error
            aggregate_runtime_error value_is_null schedule env
            right_boolean outcome
  end left right.

(** GROUP observes both the typed scalar relation and eager aggregate
    finalization owned by the current query level. *)
Definition scalar_expr_uniform_global_group_outcome_equiv
    {kind : scalar_result_kind}
    (left right : scalar_expr T relname kind) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    @scalar_expr_global_group_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule kind left right.

Lemma scalar_expr_uniform_global_group_outcome_equiv_outcomes :
  forall kind (left right : scalar_expr T relname kind),
    scalar_expr_uniform_global_group_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv left right.
Proof.
intros [|] left right Hequiv schedule.
all: exact (proj1 (Hequiv schedule)).
Qed.

Lemma scalar_expr_uniform_global_group_outcome_equiv_aggregates :
  forall kind (left right : scalar_expr T relname kind),
    scalar_expr_uniform_global_group_outcome_equiv left right ->
    forall env,
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error kind env left =
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error kind env right.
Proof.
intros kind left right Hequiv env.
exact (proj2 (Hequiv (fun _ => BooleanLeftFirst)) env).
Qed.

Definition scalar_value_expr_list_uniform_global_outcome_equiv
    (left right : list (scalar_expr T relname ScalarResultValue)) : Prop :=
  Forall2 scalar_expr_uniform_global_outcome_equiv left right.

Definition scalar_boolean_expr_list_uniform_global_outcome_equiv
    (left right : list (scalar_expr T relname ScalarResultBoolean)) : Prop :=
  Forall2 scalar_expr_uniform_global_outcome_equiv left right.

Definition scalar_select_list_uniform_global_outcome_equiv
    (left right : list
      (scalar_expr T relname ScalarResultValue * attribute T)) : Prop :=
  Forall2
    (fun left_item right_item =>
      snd left_item = snd right_item /\
      scalar_expr_uniform_global_outcome_equiv
        (fst left_item) (fst right_item))
    left right.

Lemma scalar_expr_uniform_global_outcome_equiv_refl :
  forall kind (expression : scalar_expr T relname kind),
    scalar_expr_uniform_global_outcome_equiv expression expression.
Proof.
intros [|] expression; intros schedule env outcome; tauto.
Qed.

Lemma scalar_select_list_uniform_global_outcome_equiv_refl :
  forall select_list,
    scalar_select_list_uniform_global_outcome_equiv select_list select_list.
Proof.
intro select_list; induction select_list as [|[expression attribute] rest IH].
- constructor.
- constructor; [split; [reflexivity|apply scalar_expr_uniform_global_outcome_equiv_refl]|].
  exact IH.
Qed.

Lemma scalar_value_expr_list_uniform_global_outcome_equiv_refl :
  forall expressions,
    scalar_value_expr_list_uniform_global_outcome_equiv
      expressions expressions.
Proof.
intro expressions; induction expressions; constructor; auto using
  scalar_expr_uniform_global_outcome_equiv_refl.
Qed.

Lemma scalar_value_expr_list_uniform_global_outcome_equiv_nil :
  scalar_value_expr_list_uniform_global_outcome_equiv nil nil.
Proof. constructor. Qed.

Lemma scalar_value_expr_list_uniform_global_outcome_equiv_cons :
  forall left lefts right rights,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_value_expr_list_uniform_global_outcome_equiv lefts rights ->
    scalar_value_expr_list_uniform_global_outcome_equiv
      (left :: lefts) (right :: rights).
Proof. intros; now constructor. Qed.

Lemma scalar_boolean_expr_list_uniform_global_outcome_equiv_nil :
  scalar_boolean_expr_list_uniform_global_outcome_equiv nil nil.
Proof. constructor. Qed.

Lemma scalar_boolean_expr_list_uniform_global_outcome_equiv_cons :
  forall left lefts right rights,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv lefts rights ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv
      (left :: lefts) (right :: rights).
Proof. intros; now constructor. Qed.

Lemma scalar_select_list_uniform_global_outcome_equiv_nil :
  scalar_select_list_uniform_global_outcome_equiv nil nil.
Proof. constructor. Qed.

Lemma scalar_select_list_uniform_global_outcome_equiv_cons :
  forall left_expression left_attribute left_select
      right_expression right_attribute right_select,
    left_attribute = right_attribute ->
    scalar_expr_uniform_global_outcome_equiv
      left_expression right_expression ->
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    scalar_select_list_uniform_global_outcome_equiv
      ((left_expression, left_attribute) :: left_select)
      ((right_expression, right_attribute) :: right_select).
Proof.
intros; constructor; [now split|assumption].
Qed.

Lemma scalar_select_list_uniform_global_outcome_equiv_outputs :
  forall left right,
    scalar_select_list_uniform_global_outcome_equiv left right ->
    scalar_select_outputs left = scalar_select_outputs right.
Proof.
intros left right Hequiv; induction Hequiv as [|[left_expression left_attribute]
  [right_expression right_attribute] left right [Hattribute _] _ IH];
  cbn in *; [reflexivity|now f_equal].
Qed.

Lemma scalar_select_list_uniform_global_outcome_equiv_values :
  forall left right,
    scalar_select_list_uniform_global_outcome_equiv left right ->
    scalar_value_expr_list_uniform_global_outcome_equiv
      (map fst left) (map fst right).
Proof.
intros left right Hequiv; induction Hequiv as [|[left_expression left_attribute]
  [right_expression right_attribute] left right [_ Hexpression] _ IH];
  cbn; constructor; assumption.
Qed.

Lemma eval_scalar_values_outcome_uniform_congr :
  forall left right,
    scalar_value_expr_list_uniform_global_outcome_equiv left right ->
    forall schedule env outcome,
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left outcome <->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right outcome.
Proof.
intros left right Hequiv; induction Hequiv as
  [|left_expression right_expression left right Hexpression _ IH];
  intros schedule env outcome; split; intro Heval; inversion Heval; subst.
- constructor.
- constructor.
- apply EScalarValues_HeadError.
  now apply (proj1 (Hexpression schedule env _)).
- eapply EScalarValues_Cons.
  + now apply (proj1 (Hexpression schedule env _)).
  + now apply (proj1 (IH schedule env _)).
- apply EScalarValues_HeadError.
  now apply (proj2 (Hexpression schedule env _)).
- eapply EScalarValues_Cons.
  + now apply (proj2 (Hexpression schedule env _)).
  + now apply (proj2 (IH schedule env _)).
Qed.

Lemma eval_scalar_boolean_operands_outcome_uniform_congr :
  forall left right,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    forall schedule env operation outcome,
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env operation left outcome <->
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env operation right outcome.
Proof.
intros left right Hequiv; induction Hequiv as
  [|left_expression right_expression left right Hexpression _ IH];
  intros schedule env operation outcome; split; intro Heval;
  inversion Heval; subst.
- constructor.
- constructor.
- apply EScalarBooleanOperands_HeadError.
  now apply (proj1 (Hexpression schedule env _)).
- eapply EScalarBooleanOperands_HeadDecides.
  + eapply (proj1 (Hexpression schedule env _)); eassumption.
  + eassumption.
- eapply EScalarBooleanOperands_Continue.
  + eapply (proj1 (Hexpression schedule env _)); eassumption.
  + eassumption.
  + now apply (proj1 (IH schedule env operation _)).
- apply EScalarBooleanOperands_HeadError.
  now apply (proj2 (Hexpression schedule env _)).
- eapply EScalarBooleanOperands_HeadDecides.
  + eapply (proj2 (Hexpression schedule env _)); eassumption.
  + eassumption.
- eapply EScalarBooleanOperands_Continue.
  + eapply (proj2 (Hexpression schedule env _)); eassumption.
  + eassumption.
  + now apply (proj2 (IH schedule env operation _)).
Qed.

(** Scheduling a flattened conjunction permutes both related operand lists in
    lockstep.  This is the reason [SExpr_ConjList] congruence can retain the
    ordinary pointwise list premise even though its evaluated list order is
    schedule-dependent. *)
Lemma insert_boolean_operand_uniform_Forall2 :
  forall schedule sites left_expression right_expression left right,
    scalar_expr_uniform_global_outcome_equiv
      left_expression right_expression ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    Forall2 scalar_expr_uniform_global_outcome_equiv
      (@insert_boolean_operand T relname schedule sites left_expression left)
      (@insert_boolean_operand T relname schedule sites right_expression right).
Proof.
intros schedule sites left_expression right_expression left right
  Hexpression Hordered.
revert sites; induction Hordered as
  [|left_head right_head left_tail right_tail Hhead Htail IH];
  intros [|site sites]; cbn.
- now constructor.
- now constructor.
- constructor; [exact Hexpression|now constructor].
- destruct (schedule site); cbn.
  + constructor; [exact Hexpression|now constructor].
  + constructor; [exact Hhead|now apply IH].
Qed.

Lemma schedule_boolean_operands_aux_uniform_Forall2 :
  forall schedule site_rows left right left_ordered right_ordered,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    scalar_boolean_expr_list_uniform_global_outcome_equiv
      left_ordered right_ordered ->
    Forall2 scalar_expr_uniform_global_outcome_equiv
      (@schedule_boolean_operands_aux T relname schedule
        site_rows left left_ordered)
      (@schedule_boolean_operands_aux T relname schedule
        site_rows right right_ordered).
Proof.
intros schedule site_rows left right left_ordered right_ordered Hequiv.
revert site_rows left_ordered right_ordered.
induction Hequiv as
  [|left_expression right_expression left right Hexpression _ IH];
  intros [|sites site_rows] left_ordered right_ordered Hordered; cbn.
- exact Hordered.
- exact Hordered.
- apply IH.
  now apply Forall2_app; [exact Hordered|constructor].
- apply IH.
  now apply insert_boolean_operand_uniform_Forall2.
Qed.

Lemma schedule_boolean_operands_uniform_Forall2 :
  forall schedule site_rows left right,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    Forall2 scalar_expr_uniform_global_outcome_equiv
      (@schedule_boolean_operands T relname schedule site_rows left)
      (@schedule_boolean_operands T relname schedule site_rows right).
Proof.
intros schedule site_rows left right Hequiv.
unfold schedule_boolean_operands.
eapply schedule_boolean_operands_aux_uniform_Forall2;
  [exact Hequiv|constructor].
Qed.

Lemma scalar_expr_call_uniform_global_congr :
  forall result_type operator left right,
    scalar_value_expr_list_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Call result_type operator left)
      (SExpr_Call result_type operator right).
Proof.
intros result_type operator left right Harguments schedule env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_CallArgumentsError.
  now apply (proj1
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
- apply EScalar_CallSuccess.
  now apply (proj1
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
- apply EScalar_CallArgumentsError.
  now apply (proj2
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
- apply EScalar_CallSuccess.
  now apply (proj2
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
Qed.

Lemma scalar_expr_case_uniform_global_congr :
  forall result_type left_condition right_condition
      left_then right_then left_else right_else,
    scalar_expr_uniform_global_outcome_equiv
      left_condition right_condition ->
    scalar_expr_uniform_global_outcome_equiv left_then right_then ->
    scalar_expr_uniform_global_outcome_equiv left_else right_else ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Case result_type left_condition left_then left_else)
      (SExpr_Case result_type right_condition right_then right_else).
Proof.
intros result_type left_condition right_condition left_then right_then
  left_else right_else Hcondition Hthen Helse schedule env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_CaseConditionError.
  now apply (proj1 (Hcondition schedule env _)).
- eapply EScalar_CaseThen.
  + eapply (proj1 (Hcondition schedule env _)); eassumption.
  + eassumption.
  + eapply (proj1 (Hthen schedule env _)); eassumption.
- eapply EScalar_CaseElse.
  + eapply (proj1 (Hcondition schedule env _)); eassumption.
  + eassumption.
  + eapply (proj1 (Helse schedule env _)); eassumption.
- apply EScalar_CaseConditionError.
  now apply (proj2 (Hcondition schedule env _)).
- eapply EScalar_CaseThen.
  + eapply (proj2 (Hcondition schedule env _)); eassumption.
  + eassumption.
  + eapply (proj2 (Hthen schedule env _)); eassumption.
- eapply EScalar_CaseElse.
  + eapply (proj2 (Hcondition schedule env _)); eassumption.
  + eassumption.
  + eapply (proj2 (Helse schedule env _)); eassumption.
Qed.

Lemma scalar_expr_bool_value_uniform_global_congr :
  forall result_type embed left right,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_BoolValue result_type embed left)
      (SExpr_BoolValue result_type embed right).
Proof.
intros result_type embed left right Hequiv schedule env outcome.
split; intro Heval; inversion Heval; subst; apply EScalar_BoolValue.
- now apply (proj1 (Hequiv schedule env _)).
- now apply (proj2 (Hequiv schedule env _)).
Qed.

Lemma scalar_expr_value_bool_uniform_global_congr :
  forall decode left right,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_ValueBool decode left) (SExpr_ValueBool decode right).
Proof.
intros decode left right Hequiv schedule env outcome.
split; intro Heval; inversion Heval; subst; apply EScalar_ValueBool.
- now apply (proj1 (Hequiv schedule env _)).
- now apply (proj2 (Hequiv schedule env _)).
Qed.

Lemma scalar_expr_pred_uniform_global_congr :
  forall predicate left right,
    scalar_value_expr_list_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Pred predicate left) (SExpr_Pred predicate right).
Proof.
intros predicate left right Harguments schedule env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_PredArgumentsError.
  now apply (proj1
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
- apply EScalar_PredSuccess.
  now apply (proj1
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
- apply EScalar_PredArgumentsError.
  now apply (proj2
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
- apply EScalar_PredSuccess.
  now apply (proj2
    (eval_scalar_values_outcome_uniform_congr Harguments schedule env _)).
Qed.

Lemma scalar_expr_conj_list_uniform_global_congr :
  forall site_rows operation left right,
    scalar_boolean_expr_list_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_ConjList site_rows operation left)
      (SExpr_ConjList site_rows operation right).
Proof.
intros site_rows operation left right Hequiv schedule env outcome.
split; intro Heval; inversion Heval; subst; apply EScalar_ConjList.
- eapply (proj1 (eval_scalar_boolean_operands_outcome_uniform_congr
    (schedule_boolean_operands_uniform_Forall2 schedule site_rows Hequiv)
    schedule env operation _)); eassumption.
- eapply (proj2 (eval_scalar_boolean_operands_outcome_uniform_congr
    (schedule_boolean_operands_uniform_Forall2 schedule site_rows Hequiv)
    schedule env operation _)); eassumption.
Qed.

Lemma scalar_expr_not_uniform_global_congr :
  forall left right,
    scalar_expr_uniform_global_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Not left) (SExpr_Not right).
Proof.
intros left right Hequiv schedule env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_NotError.
  now apply (proj1 (Hequiv schedule env _)).
- apply EScalar_NotSuccess.
  now apply (proj1 (Hequiv schedule env _)).
- apply EScalar_NotError.
  now apply (proj2 (Hequiv schedule env _)).
- apply EScalar_NotSuccess.
  now apply (proj2 (Hequiv schedule env _)).
Qed.

(** Scalar subqueries observe exact typed rows and cardinality errors.  The
    output-schema equality carried by typed query equivalence is needed even
    when the row relation happens to be empty or singleton. *)
Lemma scalar_expr_subquery_uniform_global_congr :
  forall result_type null_value left right,
    query_expr_uniform_global_typed_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Subquery result_type null_value left)
      (SExpr_Subquery result_type null_value right).
Proof.
intros result_type null_value left right Hequiv schedule env outcome.
destruct (Hequiv schedule) as [Houtputs Hquery].
split; intro Heval; inversion Heval; subst.
- rewrite Houtputs.
  eapply EScalar_Subquery; [eassumption|].
  eapply (proj1 (Hquery env _)); eassumption.
- rewrite <- Houtputs.
  eapply EScalar_Subquery; [eassumption|].
  eapply (proj2 (Hquery env _)); eassumption.
Qed.

Lemma scalar_expr_quant_uniform_global_congr :
  forall quantifier predicate left_arguments right_arguments left right,
    scalar_value_expr_list_uniform_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_uniform_global_typed_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Quant quantifier predicate left_arguments left)
      (SExpr_Quant quantifier predicate right_arguments right).
Proof.
intros quantifier predicate left_arguments right_arguments left right
  Harguments Hquery schedule env outcome.
destruct (Hquery schedule) as [Houtputs Hquery_outcomes].
split; intro Heval; inversion Heval; subst.
- apply EScalar_QuantArgumentsError.
  now apply (proj1 (eval_scalar_values_outcome_uniform_congr
    Harguments schedule env _)).
- eapply EScalar_QuantSubqueryError.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj1 (Hquery_outcomes env _)); eassumption.
- rewrite Houtputs.
  eapply EScalar_QuantSuccess.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj1 (Hquery_outcomes env _)); eassumption.
- apply EScalar_QuantArgumentsError.
  now apply (proj2 (eval_scalar_values_outcome_uniform_congr
    Harguments schedule env _)).
- eapply EScalar_QuantSubqueryError.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj2 (Hquery_outcomes env _)); eassumption.
- rewrite <- Houtputs.
  eapply EScalar_QuantSuccess.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj2 (Hquery_outcomes env _)); eassumption.
Qed.

Lemma scalar_expr_in_uniform_global_congr :
  forall left_arguments right_arguments left right,
    scalar_value_expr_list_uniform_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_uniform_global_typed_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_In left_arguments left) (SExpr_In right_arguments right).
Proof.
intros left_arguments right_arguments left right Harguments Hquery
  schedule env outcome.
destruct (Hquery schedule) as [Houtputs Hquery_outcomes].
split; intro Heval; inversion Heval; subst.
- apply EScalar_InArgumentsError.
  now apply (proj1 (eval_scalar_values_outcome_uniform_congr
    Harguments schedule env _)).
- eapply EScalar_InSubqueryError.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj1 (Hquery_outcomes env _)); eassumption.
- rewrite Houtputs.
  eapply EScalar_InSuccess.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj1 (Hquery_outcomes env _)); eassumption.
- apply EScalar_InArgumentsError.
  now apply (proj2 (eval_scalar_values_outcome_uniform_congr
    Harguments schedule env _)).
- eapply EScalar_InSubqueryError.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj2 (Hquery_outcomes env _)); eassumption.
- rewrite <- Houtputs.
  eapply EScalar_InSuccess.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr
      Harguments schedule env _)); eassumption.
  + eapply (proj2 (Hquery_outcomes env _)); eassumption.
Qed.

(** EXISTS keeps its deliberately weaker target-eliding demand observation;
    complete typed row equivalence is neither assumed nor manufactured. *)
Lemma scalar_expr_exists_uniform_global_congr :
  forall left right,
    query_expr_uniform_global_exists_outcome_equiv left right ->
    scalar_expr_uniform_global_outcome_equiv
      (SExpr_Exists left) (SExpr_Exists right).
Proof.
intros left right Hequiv schedule env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_ExistsError.
  eapply (proj1 (Hequiv schedule env _)); eassumption.
- apply EScalar_ExistsSuccess.
  eapply (proj1 (Hequiv schedule env _)); eassumption.
- apply EScalar_ExistsError.
  eapply (proj2 (Hequiv schedule env _)); eassumption.
- apply EScalar_ExistsSuccess.
  eapply (proj2 (Hequiv schedule env _)); eassumption.
Qed.

(** Exact bidirectional schedule transport is the most direct public bridge
    for site renaming.  The two maps may rename, extend, or merge schedules;
    both directions are required, and the transported outcome is unchanged,
    including its runtime-error category and exact row order. *)
Theorem query_expr_possible_outcome_equiv_of_exact_schedule_transport :
  forall env left right
      (forward_schedule backward_schedule :
        (boolean_site -> boolean_evaluation_order) ->
        boolean_site -> boolean_evaluation_order),
    query_expr_outputs left = query_expr_outputs right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left outcome) ->
    (forall schedule outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left outcome ->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        (forward_schedule schedule) env right outcome) ->
    (forall schedule outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right outcome ->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        (backward_schedule schedule) env left outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right forward_schedule backward_schedule Houtputs
  Hinhabited Hforward Hbackward.
split; [exact Houtputs|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome.
apply outcome_relation_equiv_intro.
- exact Hinhabited.
- destruct Hinhabited as [outcome [schedule Heval]].
  exists outcome, (forward_schedule schedule).
  now apply Hforward.
- intros left_rows [schedule Heval].
  exists left_rows; split.
  + exists (forward_schedule schedule); now apply Hforward.
  + apply ordered_rows_equiv_refl.
- intros right_rows [schedule Heval].
  exists right_rows; split.
  + exists (backward_schedule schedule); now apply Hbackward.
  + apply ordered_rows_equiv_refl.
- intro error; split.
  + intros [schedule Heval].
    exists (forward_schedule schedule); now apply Hforward.
  + intros [schedule Heval].
    exists (backward_schedule schedule); now apply Hbackward.
Qed.

(** A pairwise relation bridge permits observational row equivalence rather
    than exact tuple-record identity.  Unlike the theorem above it requires a
    relation-equivalence witness for every schedule in both directions. *)
Theorem query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall left_schedule,
      exists right_schedule,
        outcome_relation_equiv (@ordered_rows_equiv T)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right)) ->
    (forall right_schedule,
      exists left_schedule,
        outcome_relation_equiv (@ordered_rows_equiv T)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            left_schedule env left)
          (@eval_query_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            right_schedule env right)) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Houtputs Hforward Hbackward.
split; [exact Houtputs|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome.
eapply outcome_relation_equiv_exists_schedule_transport
  with (default_schedule := fun _ => BooleanLeftFirst);
  eassumption.
Qed.

Theorem query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv :
  forall env left right,
    query_expr_uniform_scheduled_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Hall.
pose proof (Hall (fun _ => BooleanLeftFirst)) as [Houtputs _].
apply query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport.
- exact Houtputs.
- intro schedule; exists schedule; exact (proj2 (Hall schedule)).
- intro schedule; exists schedule; exact (proj2 (Hall schedule)).
Qed.

(** One fixed-schedule theorem becomes public only after both queries are
    proved schedule-independent.  This is the explicit safe replacement for
    the invalid implication from a single scheduled equivalence alone. *)
Theorem query_expr_scheduled_outcome_equiv_implies_possible_of_independent :
  forall env left right fixed_schedule,
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      fixed_schedule env left right ->
    query_expr_schedule_independent env left ->
    query_expr_schedule_independent env right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right fixed_schedule [Houtputs Hequiv]
  Hleft_independent Hright_independent.
apply query_expr_possible_outcome_equiv_of_bidirectional_schedule_transport.
- exact Houtputs.
- intro schedule; exists schedule.
  eapply outcome_relation_equiv_transport_iff; [exact Hequiv| |].
  + apply Hleft_independent.
  + apply Hright_independent.
- intro schedule; exists schedule.
  eapply outcome_relation_equiv_transport_iff; [exact Hequiv| |].
  + apply Hleft_independent.
  + apply Hright_independent.
Qed.

(** Exact completeness of schedule precomposition is the transport premise
    needed for a site renaming.  Requiring function equality here keeps the
    public bridge constructive: a merely pointwise left inverse must not be
    promoted to function equality through an undeclared extensionality axiom. *)
Definition boolean_schedule_reindex_complete
    (rename_site : boolean_site -> boolean_site) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    exists reindexed_schedule : boolean_site -> boolean_evaluation_order,
      (fun site => reindexed_schedule (rename_site site)) = schedule.

Lemma boolean_schedule_reindex_complete_id :
  boolean_schedule_reindex_complete (fun site => site).
Proof.
intro schedule; now exists schedule.
Qed.

(** Reindexing the existential schedule by a complete site renaming cannot
    add or remove a possible success or error outcome. *)
Lemma eval_query_expr_possible_outcome_site_reindex_iff :
  forall (rename_site : boolean_site -> boolean_site),
    boolean_schedule_reindex_complete rename_site ->
    forall env query outcome,
      (exists schedule,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          (fun site => schedule (rename_site site)) env query outcome) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env query outcome.
Proof.
intros rename_site Hcomplete env query outcome.
unfold eval_query_expr_possible_outcome; split.
- intros [schedule Heval].
  now exists (fun site => schedule (rename_site site)).
- intros [schedule Heval].
  destruct (Hcomplete schedule) as [reindexed_schedule Hreindexed].
  exists reindexed_schedule.
  now rewrite Hreindexed.
Qed.

(** Uniform raw equality is a convenient internal proof layer for syntactic
    rewrites.  Only one possible source outcome is required at the public
    boundary; the same schedule transports every source/right outcome. *)
Theorem query_expr_possible_outcome_equiv_of_uniform_global_typed :
  forall env left right,
    query_expr_uniform_global_typed_outcome_equiv left right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env left outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right Hall Hinhabited.
destruct (Hall (fun _ => BooleanLeftFirst)) as [Houtputs _].
split; [exact Houtputs|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome.
apply outcome_relation_equiv_intro.
- exact Hinhabited.
- destruct Hinhabited as [outcome [schedule Heval]].
  exists outcome, schedule.
  now apply (proj1 (proj2 (Hall schedule) env outcome)).
- intros rows [schedule Heval].
  exists rows; split.
  + exists schedule.
    now apply (proj1 (proj2 (Hall schedule) env (SqlSuccess rows))).
  + apply ordered_rows_equiv_refl.
- intros rows [schedule Heval].
  exists rows; split.
  + exists schedule.
    now apply (proj2 (proj2 (Hall schedule) env (SqlSuccess rows))).
  + apply ordered_rows_equiv_refl.
- intro error; split; intros [schedule Heval]; exists schedule.
  + now apply (proj1 (proj2 (Hall schedule) env (SqlError error))).
  + now apply (proj2 (proj2 (Hall schedule) env (SqlError error))).
Qed.

(** Exact typed projection rows retain child list order.  Only the scalar
    expressions change; output attributes are related positionally, so the
    constructed tuples are definitionally equal after rewriting the output
    schema. *)
Lemma eval_project_rows_outcome_uniform_congr :
  forall left_select right_select,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    forall schedule env rows outcome,
      @eval_project_rows_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env left_select rows outcome <->
      @eval_project_rows_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env right_select rows outcome.
Proof.
intros left_select right_select Hselect schedule env rows.
assert (Hvalues :=
  scalar_select_list_uniform_global_outcome_equiv_values Hselect).
assert (Houtputs :=
  scalar_select_list_uniform_global_outcome_equiv_outputs Hselect).
assert (Hrow : forall values,
  @project_row T relname left_select values =
  @project_row T relname right_select values).
{
  intro values; unfold project_row.
  now rewrite Houtputs.
}
induction rows as [|row rows IH]; intro outcome; split; intro Heval;
  inversion Heval; subst.
- constructor.
- constructor.
- apply EProjectRows_HeadError.
  now apply (proj1 (eval_scalar_values_outcome_uniform_congr
    Hvalues schedule (env_t T env row) _)).
- rewrite Hrow.
  eapply EProjectRows_Cons.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr
      Hvalues schedule (env_t T env row) _)); eassumption.
  + now apply (proj1 (IH _)).
- apply EProjectRows_HeadError.
  now apply (proj2 (eval_scalar_values_outcome_uniform_congr
    Hvalues schedule (env_t T env row) _)).
- rewrite <- Hrow.
  eapply EProjectRows_Cons.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr
      Hvalues schedule (env_t T env row) _)); eassumption.
  + now apply (proj2 (IH _)).
Qed.

Lemma query_expr_filter_uniform_global_typed_congr :
  forall left_predicate right_predicate input,
    scalar_expr_uniform_global_outcome_equiv
      left_predicate right_predicate ->
    query_expr_uniform_global_typed_outcome_equiv
      (QExpr_Filter left_predicate input)
      (QExpr_Filter right_predicate input).
Proof.
intros left_predicate right_predicate input Hpredicate schedule.
apply query_expr_filter_expression_global_typed_congr.
exact (Hpredicate schedule).
Qed.

Lemma query_expr_project_uniform_global_typed_congr :
  forall left_select right_select input,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    query_expr_uniform_global_typed_outcome_equiv
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
Proof.
intros left_select right_select input Hselect schedule.
split.
- now apply scalar_select_list_uniform_global_outcome_equiv_outputs.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + now apply EQuery_ProjectChildError.
  + eapply EQuery_ProjectRows; [eassumption|].
    now apply (proj1
      (eval_project_rows_outcome_uniform_congr
        Hselect schedule env input_rows outcome)).
  + now apply EQuery_ProjectChildError.
  + eapply EQuery_ProjectRows; [eassumption|].
    now apply (proj2
      (eval_project_rows_outcome_uniform_congr
        Hselect schedule env input_rows outcome)).
Qed.

Theorem query_expr_filter_predicate_possible_outcome_equiv :
  forall env left_predicate right_predicate input,
    scalar_expr_uniform_global_outcome_equiv
      left_predicate right_predicate ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter left_predicate input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_predicate input)
      (QExpr_Filter right_predicate input).
Proof.
intros env left_predicate right_predicate input Hpredicate Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- now apply query_expr_filter_uniform_global_typed_congr.
- exact Houtcome.
Qed.

Theorem query_expr_project_select_possible_outcome_equiv :
  forall env left_select right_select input,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Project left_select input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
Proof.
intros env left_select right_select input Hselect Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- now apply query_expr_project_uniform_global_typed_congr.
- exact Houtcome.
Qed.

(** Typed GROUP evaluates syntax-directed aggregate finalization before the
    ordinary scalar outcome relation.  Those observations therefore remain
    explicit premises.  Given them, the following lemma preserves each exact
    local group-list outcome, including every runtime-error category and the
    exact order in which accepted group rows are produced. *)
Lemma eval_groups_outcome_uniform_congr :
  forall left_select right_select group_terms left_having right_having,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    scalar_expr_uniform_global_outcome_equiv left_having right_having ->
    (forall current_env,
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    (forall current_env,
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env left_having =
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env right_having) ->
    forall schedule env groups outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select group_terms left_having groups outcome <->
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select group_terms right_having groups outcome.
Proof.
intros left_select right_select group_terms left_having right_having
  Hselect Hhaving Hselect_aggregates Hhaving_aggregates schedule env groups.
assert (Hvalues :=
  scalar_select_list_uniform_global_outcome_equiv_values Hselect).
assert (Houtputs :=
  scalar_select_list_uniform_global_outcome_equiv_outputs Hselect).
assert (Hrow : forall values,
  @project_row T relname left_select values =
  @project_row T relname right_select values).
{
  intro values; unfold project_row.
  now rewrite Houtputs.
}
induction groups as [|group groups IH]; intro outcome; split; intro Heval;
  inversion Heval; subst.
- constructor.
- constructor.
- apply EGroups_SelectAggregateError.
  rewrite <- (Hselect_aggregates
    (env_g T env (@Group_By T group_terms) group)).
  assumption.
- eapply EGroups_HavingAggregateError.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
- eapply EGroups_HavingError.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + now apply (proj1 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)).
- eapply EGroups_HavingFalse.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + eapply (proj1 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + now apply (proj1 (IH _)).
- eapply EGroups_SelectError.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + eapply (proj1 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr Hvalues schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
- rewrite Hrow.
  eapply EGroups_SelectSuccess.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + eapply (proj1 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj1 (eval_scalar_values_outcome_uniform_congr Hvalues schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + now apply (proj1 (IH _)).
- apply EGroups_SelectAggregateError.
  rewrite (Hselect_aggregates
    (env_g T env (@Group_By T group_terms) group)).
  assumption.
- eapply EGroups_HavingAggregateError.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
- eapply EGroups_HavingError.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + now apply (proj2 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)).
- eapply EGroups_HavingFalse.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + eapply (proj2 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + now apply (proj2 (IH _)).
- eapply EGroups_SelectError.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + eapply (proj2 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr Hvalues schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
- rewrite <- Hrow.
  eapply EGroups_SelectSuccess.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)).
    assumption.
  + eapply (proj2 (Hhaving schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj2 (eval_scalar_values_outcome_uniform_congr Hvalues schedule
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + now apply (proj2 (IH _)).
Qed.

(** The fundamental GROUP composition law is heterogeneous and
    relation-parametric.  [scheduled_rows_rel] relates both the child rows and
    the schedules that produced them; this is essential because two possible
    outcomes need not come from the same Boolean evaluation order.  The local
    premise may simultaneously change GROUP keys, aggregates, HAVING, and
    projection syntax, provided their complete continuation relations preserve
    [output_rows_rel]. *)
Theorem query_expr_group_possible_outcome_transport :
  forall env left_select right_select left_group_keys right_group_keys
      left_having right_having left right
      (scheduled_rows_rel :
        (boolean_site -> boolean_evaluation_order) -> list (tuple T) ->
        (boolean_site -> boolean_evaluation_order) -> list (tuple T) -> Prop)
      (output_rows_rel : list (tuple T) -> list (tuple T) -> Prop),
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select left_group_keys left_having left) outcome) ->
    (forall left_schedule left_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left (SqlSuccess left_rows) ->
      exists right_schedule, exists right_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right (SqlSuccess right_rows) /\
        scheduled_rows_rel
          left_schedule left_rows right_schedule right_rows) ->
    (forall right_schedule right_rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right (SqlSuccess right_rows) ->
      exists left_schedule, exists left_rows,
        @eval_query_expr_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left (SqlSuccess left_rows) /\
        scheduled_rows_rel
          left_schedule left_rows right_schedule right_rows) ->
    (forall error,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlError error) <->
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlError error)) ->
    (forall left_schedule left_rows right_schedule right_rows,
      scheduled_rows_rel left_schedule left_rows right_schedule right_rows ->
      outcome_relation_transport output_rows_rel
        (query_group_rows_outcomes
          left_schedule env left_select left_group_keys left_having left_rows)
        (query_group_rows_outcomes
          right_schedule env right_select right_group_keys right_having
          right_rows)) ->
    query_expr_possible_outcome_related env output_rows_rel
      (QExpr_Group left_select left_group_keys left_having left)
      (QExpr_Group right_select right_group_keys right_having right).
Proof.
intros env left_select right_select left_group_keys right_group_keys
  left_having right_having left right scheduled_rows_rel output_rows_rel
  Hparent Hchild_forward Hchild_backward Hchild_errors Hlocal.
unfold query_expr_possible_outcome_related.
apply outcome_relation_equiv_of_left_inhabited_transport; [exact Hparent|].
split.
- intros left_output [left_schedule Hleft_parent].
  apply eval_query_expr_group_success_iff in Hleft_parent.
  destruct Hleft_parent as
    [left_rows [left_bag [Hleft [Hleft_group Hleft_output]]]].
  destruct (Hchild_forward left_schedule left_rows Hleft) as
    [right_schedule [right_rows [Hright Hrows]]].
  destruct (Hlocal left_schedule left_rows right_schedule right_rows Hrows)
    as [Hlocal_forward _].
  destruct (Hlocal_forward left_output
    (ex_intro _ left_bag (conj Hleft_group Hleft_output))) as
    [right_output [Hright_local Houtput]].
  exists right_output; split; [|exact Houtput].
  exists right_schedule.
  destruct Hright_local as [right_bag [Hright_group Hright_output]].
  apply eval_query_expr_group_success_iff.
  now exists right_rows, right_bag.
- split.
  + intros right_output [right_schedule Hright_parent].
    apply eval_query_expr_group_success_iff in Hright_parent.
    destruct Hright_parent as
      [right_rows [right_bag [Hright [Hright_group Hright_output]]]].
    destruct (Hchild_backward right_schedule right_rows Hright) as
      [left_schedule [left_rows [Hleft Hrows]]].
    destruct (Hlocal left_schedule left_rows right_schedule right_rows Hrows)
      as [_ [Hlocal_backward _]].
    destruct (Hlocal_backward right_output
      (ex_intro _ right_bag (conj Hright_group Hright_output))) as
      [left_output [Hleft_local Houtput]].
    exists left_output; split; [|exact Houtput].
    exists left_schedule.
    destruct Hleft_local as [left_bag [Hleft_group Hleft_output]].
    apply eval_query_expr_group_success_iff.
    now exists left_rows, left_bag.
  + intro error; split; intros [schedule Hparent_error].
    * apply eval_query_expr_group_error_iff in Hparent_error.
      destruct Hparent_error as
        [Hchild_error|[left_rows [Hleft Hlocal_error]]].
      -- destruct (proj1 (Hchild_errors error)
            (ex_intro _ schedule Hchild_error)) as
           [right_schedule Hright_error].
         exists right_schedule; now apply EQuery_GroupChildError.
      -- destruct (Hchild_forward schedule left_rows Hleft) as
           [right_schedule [right_rows [Hright Hrows]]].
         destruct (Hlocal schedule left_rows right_schedule right_rows Hrows)
           as [_ [_ Hlocal_errors]].
         exists right_schedule.
         eapply EQuery_GroupBagError; [exact Hright|].
         now apply (proj1 (Hlocal_errors error)).
    * apply eval_query_expr_group_error_iff in Hparent_error.
      destruct Hparent_error as
        [Hchild_error|[right_rows [Hright Hlocal_error]]].
      -- destruct (proj2 (Hchild_errors error)
            (ex_intro _ schedule Hchild_error)) as
           [left_schedule Hleft_error].
         exists left_schedule; now apply EQuery_GroupChildError.
      -- destruct (Hchild_backward schedule right_rows Hright) as
           [left_schedule [left_rows [Hleft Hrows]]].
         destruct (Hlocal left_schedule left_rows schedule right_rows Hrows)
           as [_ [_ Hlocal_errors]].
         exists left_schedule.
         eapply EQuery_GroupBagError; [exact Hleft|].
         now apply (proj2 (Hlocal_errors error)).
Qed.

(** Exact equality of local bag outcomes is the common specialization of the
    relation-parametric interface.  Reusing the same output representative
    yields ordinary ordered-row equivalence without inspecting GROUP syntax. *)
Lemma query_group_rows_outcomes_transport_of_exact_bag_outcomes :
  forall left_schedule left_env left_select left_group_keys left_having left_rows
      right_schedule right_env right_select right_group_keys right_having
      right_rows,
    (forall outcome,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule left_env left_select left_group_keys left_having
        (rows_bag T left_rows) outcome <->
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule right_env right_select right_group_keys right_having
        (rows_bag T right_rows) outcome) ->
    outcome_relation_transport (@ordered_rows_equiv T)
      (query_group_rows_outcomes
        left_schedule left_env left_select left_group_keys left_having left_rows)
      (query_group_rows_outcomes
        right_schedule right_env right_select right_group_keys right_having
        right_rows).
Proof.
intros left_schedule left_env left_select left_group_keys left_having left_rows
  right_schedule right_env right_select right_group_keys right_having right_rows
  Hbag.
split.
- intros output [output_bag [Heval Houtput]].
  exists output; split.
  + exists output_bag; split; [now apply (proj1 (Hbag _))|exact Houtput].
  + apply ordered_rows_equiv_refl.
- split.
  + intros output [output_bag [Heval Houtput]].
    exists output; split.
    * exists output_bag; split; [now apply (proj2 (Hbag _))|exact Houtput].
    * apply ordered_rows_equiv_refl.
  + intro error; apply Hbag.
Qed.

Lemma eval_group_bag_outcome_exact_local_congr :
  forall left_select right_select group_keys left_having right_having,
    (forall schedule env group_terms groups outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select group_terms left_having groups outcome <->
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select group_terms right_having groups outcome) ->
    forall schedule env input_bag outcome,
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left_select group_keys left_having input_bag outcome <->
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right_select group_keys right_having input_bag outcome.
Proof.
intros left_select right_select group_keys left_having right_having
  Hlocal schedule env input_bag outcome.
split; intro Heval; inversion Heval; subst.
- eapply EGroupBag_KeyError; eassumption.
- eapply EGroupBag_ProcessError; [eassumption|eassumption|eassumption|].
  now apply (proj1 (Hlocal schedule env group_terms
    (query_make_groups env representative group_terms) _)).
- eapply EGroupBag_Success; [eassumption|eassumption|eassumption| |eassumption].
  now apply (proj1 (Hlocal schedule env group_terms
    (query_make_groups env representative group_terms) _)).
- eapply EGroupBag_KeyError; eassumption.
- eapply EGroupBag_ProcessError; [eassumption|eassumption|eassumption|].
  now apply (proj2 (Hlocal schedule env group_terms
    (query_make_groups env representative group_terms) _)).
- eapply EGroupBag_Success; [eassumption|eassumption|eassumption| |eassumption].
  now apply (proj2 (Hlocal schedule env group_terms
    (query_make_groups env representative group_terms) _)).
Qed.

(** Exact local group-bag equality is the common [eq]-style specialization of
    the relation-parametric transport above.  Group keys may differ because
    the premise explicitly compares every resulting success and error under
    the same schedule, environment, and input bag. *)
Theorem query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes :
  forall env left_select right_select left_group_keys right_group_keys
      left_having right_having input,
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall schedule current_env input_bag outcome,
      @eval_group_bag_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule current_env
        left_select left_group_keys left_having input_bag outcome <->
      @eval_group_bag_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule current_env
        right_select right_group_keys right_having input_bag outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select left_group_keys left_having input)
        outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select left_group_keys left_having input)
      (QExpr_Group right_select right_group_keys right_having input).
Proof.
intros env left_select right_select left_group_keys right_group_keys
  left_having right_having input Houtputs Hbag Houtcome.
apply query_expr_possible_outcome_equiv_of_related; [exact Houtputs|].
eapply query_expr_group_possible_outcome_transport with
  (scheduled_rows_rel :=
    fun left_schedule left_rows right_schedule right_rows =>
      left_schedule = right_schedule /\ left_rows = right_rows).
- exact Houtcome.
- intros schedule rows Heval.
  exists schedule, rows; now repeat split.
- intros schedule rows Heval.
  exists schedule, rows; now repeat split.
- intro error; reflexivity.
- intros left_schedule left_rows right_schedule right_rows
    [Hschedules Hrows].
  subst right_schedule right_rows.
  apply query_group_rows_outcomes_transport_of_exact_bag_outcomes.
  intro outcome; apply Hbag.
Qed.

(** This public corollary exposes the exact group-list boundary directly.  The
    same representative and the same logical group list are transported in
    both directions; no permutation closure or bag equality is used for local
    aggregate evaluation. *)
Theorem query_expr_group_possible_outcome_equiv_of_exact_local_outcomes :
  forall env left_select right_select group_keys left_having right_having input,
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall schedule current_env group_terms groups outcome,
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        current_env left_select group_terms left_having groups outcome <->
      @eval_groups_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        current_env right_select group_terms right_having groups outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select group_keys left_having input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select group_keys left_having input)
      (QExpr_Group right_select group_keys right_having input).
Proof.
intros env left_select right_select group_keys left_having right_having input
  Houtputs Hlocal Houtcome.
eapply query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes.
- exact Houtputs.
- intros schedule current_env input_bag outcome.
  now apply eval_group_bag_outcome_exact_local_congr.
- exact Houtcome.
Qed.

Theorem query_expr_group_clauses_possible_outcome_equiv :
  forall env left_select right_select group_keys left_having right_having input,
    scalar_select_list_uniform_global_outcome_equiv
      left_select right_select ->
    scalar_expr_uniform_global_outcome_equiv left_having right_having ->
    (forall current_env,
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      @eval_scalar_select_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    (forall current_env,
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env left_having =
      @eval_scalar_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error ScalarResultBoolean
        current_env right_having) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group left_select group_keys left_having input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select group_keys left_having input)
      (QExpr_Group right_select group_keys right_having input).
Proof.
intros env left_select right_select group_keys left_having right_having input
  Hselect Hhaving Hselect_aggregates Hhaving_aggregates Houtcome.
eapply query_expr_group_possible_outcome_equiv_of_exact_local_outcomes.
- now apply scalar_select_list_uniform_global_outcome_equiv_outputs.
- intros schedule current_env group_terms groups outcome.
  now apply eval_groups_outcome_uniform_congr.
- exact Houtcome.
Qed.

Lemma query_expr_possible_outcome_equiv_refl :
  forall env query,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env query outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query query.
Proof.
intros env query Houtcome; split; [reflexivity|].
unfold query_expr_possible_outcome_observation_equiv.
apply outcome_relation_equiv_refl.
- apply ordered_rows_equiv_refl.
- exact Houtcome.
Qed.

Lemma query_expr_possible_outcome_equiv_sym :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env right left.
Proof.
intros env left right
  [Houtputs [Hleft [Hright [Hforward [Hbackward Herrors]]]]].
split; [now symmetry|].
apply outcome_relation_equiv_intro; try assumption.
- intros rows Hrows.
  destruct (Hbackward rows Hrows) as [other [Hother Hequiv]].
  exists other; split; [exact Hother|now apply ordered_rows_equiv_sym].
- intros rows Hrows.
  destruct (Hforward rows Hrows) as [other [Hother Hequiv]].
  exists other; split; [exact Hother|now apply ordered_rows_equiv_sym].
- intro error; symmetry; apply Herrors.
Qed.

Lemma query_expr_possible_outcome_equiv_trans :
  forall env first second third,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env second third ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first third.
Proof.
intros env first second third
  [Hfirst_outputs
    [Hfirst_outcome
      [Hsecond_outcome
        [Hfirst_forward [Hfirst_backward Hfirst_errors]]]]]
  [Hsecond_outputs
    [Hsecond_outcome'
      [Hthird_outcome
        [Hsecond_forward [Hsecond_backward Hsecond_errors]]]]].
split; [now transitivity (query_expr_outputs second)|].
apply outcome_relation_equiv_intro.
- exact Hfirst_outcome.
- exact Hthird_outcome.
- intros rows Hrows.
  destruct (Hfirst_forward rows Hrows) as [middle [Hmiddle Hfirst_rows]].
  destruct (Hsecond_forward middle Hmiddle)
    as [final [Hfinal Hsecond_rows]].
  exists final; split; [exact Hfinal|].
  eapply ordered_rows_equiv_trans; eassumption.
- intros rows Hrows.
  destruct (Hsecond_backward rows Hrows) as [middle [Hmiddle Hsecond_rows]].
  destruct (Hfirst_backward middle Hmiddle)
    as [initial [Hinitial Hfirst_rows]].
  exists initial; split; [exact Hinitial|].
  eapply ordered_rows_equiv_trans; eassumption.
- intro error; split; intro Herror.
  + apply (proj1 (Hsecond_errors error)).
    now apply (proj1 (Hfirst_errors error)).
  + apply (proj2 (Hfirst_errors error)).
    now apply (proj2 (Hsecond_errors error)).
Qed.

(** Typed scalar and query contexts are quantified over every stable Boolean
    schedule before they are lifted to the public union-of-schedules
    observation.  EXISTS retains its separate demand relation. *)
Theorem query_expr_context_possible_outcome_equiv :
  forall env (context : query_expr_context T relname) left right,
    query_expr_uniform_global_demand_equiv
      (query_expr_context_demand context) left right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (plug_query_expr_context context left) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (plug_query_expr_context context left)
      (plug_query_expr_context context right).
Proof.
intros env context left right Hequiv Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule; apply query_expr_context_global_congr.
  exact (Hequiv schedule).
- exact Houtcome.
Qed.

Theorem query_expr_filter_possible_outcome_equiv_of_uniform_expression :
  forall env left_expression right_expression input,
    scalar_expr_uniform_global_outcome_equiv
      left_expression right_expression ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter left_expression input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_expression input)
      (QExpr_Filter right_expression input).
Proof.
intros env left_expression right_expression input Hexpression Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule; apply query_expr_filter_expression_global_typed_congr.
  exact (Hexpression schedule).
- exact Houtcome.
Qed.

Theorem query_expr_group_possible_outcome_equiv_of_uniform_having :
  forall env select_list group_keys left_having right_having input,
    scalar_expr_uniform_global_group_outcome_equiv
      left_having right_having ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group select_list group_keys left_having input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group select_list group_keys left_having input)
      (QExpr_Group select_list group_keys right_having input).
Proof.
intros env select_list group_keys left_having right_having input
  Hhaving Houtcome.
eapply query_expr_group_clauses_possible_outcome_equiv.
- apply scalar_select_list_uniform_global_outcome_equiv_refl.
- now apply scalar_expr_uniform_global_group_outcome_equiv_outcomes.
- reflexivity.
- now apply scalar_expr_uniform_global_group_outcome_equiv_aggregates.
- exact Houtcome.
Qed.

Theorem query_expr_join_possible_outcome_equiv_of_uniform_predicate :
  forall env kind left_predicate right_predicate
      matched_select left_select right_select left right,
    scalar_expr_uniform_global_outcome_equiv
      left_predicate right_predicate ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Join kind left_predicate matched_select left_select right_select
          left right) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Join kind left_predicate matched_select left_select right_select
        left right)
      (QExpr_Join kind right_predicate matched_select left_select right_select
        left right).
Proof.
intros env kind left_predicate right_predicate matched_select left_select
  right_select left right Hpredicate Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule; apply query_expr_join_scalar_global_typed_congr.
  + exact (Hpredicate schedule).
  + apply scalar_select_list_global_outcome_equiv_refl.
  + apply scalar_select_list_global_outcome_equiv_refl.
  + apply scalar_select_list_global_outcome_equiv_refl.
- exact Houtcome.
Qed.

Corollary query_expr_filter_in_subquery_possible_outcome_equiv :
  forall env arguments left_subquery right_subquery input,
    query_expr_uniform_global_typed_outcome_equiv
      left_subquery right_subquery ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter (SExpr_In arguments left_subquery) input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter (SExpr_In arguments left_subquery) input)
      (QExpr_Filter (SExpr_In arguments right_subquery) input).
Proof.
intros env arguments left_subquery right_subquery input Hequiv Houtcome.
apply query_expr_filter_possible_outcome_equiv_of_uniform_expression.
- apply scalar_expr_in_uniform_global_congr.
  + apply scalar_value_expr_list_uniform_global_outcome_equiv_refl.
  + exact Hequiv.
- exact Houtcome.
Qed.

Corollary query_expr_filter_exists_subquery_possible_outcome_equiv :
  forall env left_subquery right_subquery input,
    query_expr_uniform_global_exists_outcome_equiv
      left_subquery right_subquery ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Filter (SExpr_Exists left_subquery) input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter (SExpr_Exists left_subquery) input)
      (QExpr_Filter (SExpr_Exists right_subquery) input).
Proof.
intros env left_subquery right_subquery input Hequiv Houtcome.
apply query_expr_filter_possible_outcome_equiv_of_uniform_expression.
- now apply scalar_expr_exists_uniform_global_congr.
- exact Houtcome.
Qed.

(** Binary reset congruence cannot be derived from two unrelated possible
    child equivalences: their witnesses may disagree on shared Boolean sites.
    These public conclusions therefore require same-schedule equivalence for
    every schedule and reuse the fixed-schedule reset proofs internally. *)
Theorem query_expr_set_possible_outcome_equiv_congr_uniform :
  forall env operation left left' right right',
    query_expr_uniform_scheduled_outcome_equiv env left left' ->
    query_expr_uniform_scheduled_outcome_equiv env right right' ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
Proof.
intros env operation left left' right right' Hleft Hright.
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
intro schedule; now apply query_expr_set_outcome_equiv_congr.
Qed.

Theorem query_expr_cross_join_possible_outcome_equiv_congr_uniform :
  forall env left left' right right',
    query_expr_uniform_scheduled_outcome_equiv env left left' ->
    query_expr_uniform_scheduled_outcome_equiv env right right' ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left right)
      (QExpr_CrossJoin left' right').
Proof.
intros env left left' right right' Hleft Hright.
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
intro schedule; now apply query_expr_cross_join_outcome_equiv_congr.
Qed.

Theorem query_expr_group_possible_outcome_equiv_congr_uniform :
  forall env select_list group_terms having left right,
    query_expr_uniform_scheduled_outcome_equiv env left right ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Group select_list group_terms having left) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
Proof.
intros env select_list group_terms having left right Hchild Houtcomes.
apply query_expr_possible_outcome_equiv_of_related.
- reflexivity.
- eapply query_expr_group_possible_outcome_transport with
    (scheduled_rows_rel :=
      fun left_schedule left_rows right_schedule right_rows =>
        left_schedule = right_schedule /\
        ordered_rows_equiv T left_rows right_rows).
  + destruct (Houtcomes (fun _ => BooleanLeftFirst)) as [outcome Houtcome].
    now exists outcome, (fun _ => BooleanLeftFirst).
  + intros schedule rows Heval.
    destruct (proj2 (Hchild schedule)) as
      [_ [_ [Hforward [_ _]]]].
    destruct (Hforward rows Heval) as [right_rows [Hright Hrows]].
    exists schedule, right_rows; now repeat split.
  + intros schedule rows Heval.
    destruct (proj2 (Hchild schedule)) as
      [_ [_ [_ [Hbackward _]]]].
    destruct (Hbackward rows Heval) as [left_rows [Hleft Hrows]].
    exists schedule, left_rows; now repeat split.
  + intro error; unfold eval_query_expr_possible_outcome; split.
    * intros [schedule Herror]; exists schedule.
      destruct (proj2 (Hchild schedule)) as [_ [_ [_ [_ Herrors]]]].
      now apply (proj1 (Herrors error)).
    * intros [schedule Herror]; exists schedule.
      destruct (proj2 (Hchild schedule)) as [_ [_ [_ [_ Herrors]]]].
      now apply (proj2 (Herrors error)).
  + intros left_schedule left_rows right_schedule right_rows
      [Hschedules Hrows].
    subst right_schedule.
    apply query_group_rows_outcomes_transport_of_exact_bag_outcomes.
    intro outcome; apply eval_group_bag_outcome_input_equiv.
    now apply ordered_rows_equiv_implies_bag_eq.
Qed.

Theorem query_expr_window_possible_outcome_equiv_congr_uniform :
  forall env partition_keys order_keys items left right,
    query_expr_uniform_scheduled_outcome_equiv env left right ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Window partition_keys order_keys items left) outcome) ->
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Window partition_keys order_keys items right) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Window partition_keys order_keys items left)
      (QExpr_Window partition_keys order_keys items right).
Proof.
intros env partition_keys order_keys items left right
  Hchild Hleft_outcomes Hright_outcomes.
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
intro schedule.
apply query_expr_window_outcome_equiv_congr.
- exact (Hchild schedule).
- exact (Hleft_outcomes schedule).
- exact (Hright_outcomes schedule).
Qed.

Definition query_expr_possible_runtime_safe
    (env : Env.env T) (query : query_expr T relname) : Prop :=
  forall error,
    ~ @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query (SqlError error).

Definition query_expr_possible_has_success
    (env : Env.env T) (query : query_expr T relname) : Prop :=
  exists rows,
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query (SqlSuccess rows).

(** Safe possible-equivalence remains useful for verification modes that rule
    out every runtime error.  Its algebra is stated over the complete union of
    schedules, and conversion from outcome equivalence requires safety
    explicitly rather than treating the selected verification mode as an
    oracle. *)
Lemma query_expr_possible_equiv_refl :
  forall env query,
    query_expr_possible_has_success env query ->
    query_expr_possible_runtime_safe env query ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env query query.
Proof.
intros env query Hsuccess Hsafe; split; [reflexivity |].
unfold query_expr_possible_observation_equiv.
apply successful_relation_equiv_refl.
- apply ordered_rows_equiv_refl.
- exact Hsuccess.
- exact Hsafe.
Qed.

Lemma query_expr_possible_equiv_sym :
  forall env left right,
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env right left.
Proof.
intros env left right
  [Houtputs [Hsuccess [Hleft_safe [Hright_safe [Hforward Hbackward]]]]].
split; [now symmetry |].
unfold query_expr_possible_observation_equiv.
apply successful_relation_equiv_intro.
- destruct Hsuccess as [left_rows Hleft].
  destruct (Hforward left_rows Hleft) as [right_rows [Hright _]].
  now exists right_rows.
- exact Hright_safe.
- exact Hleft_safe.
- intros right_rows Hright.
  destruct (Hbackward right_rows Hright) as [left_rows [Hleft Hrows]].
  exists left_rows; split; [exact Hleft |].
  now apply ordered_rows_equiv_sym.
- intros left_rows Hleft.
  destruct (Hforward left_rows Hleft) as [right_rows [Hright Hrows]].
  exists right_rows; split; [exact Hright |].
  now apply ordered_rows_equiv_sym.
Qed.

Lemma query_expr_possible_equiv_trans :
  forall env first second third,
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env second third ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first third.
Proof.
intros env first second third
  [Hfirst_outputs
    [Hfirst_success [Hfirst_safe [_ [Hfirst_forward Hfirst_backward]]]]]
  [Hsecond_outputs
    [_ [_ [Hthird_safe [Hsecond_forward Hsecond_backward]]]]].
split; [now transitivity (query_expr_outputs second) |].
unfold query_expr_possible_observation_equiv.
apply successful_relation_equiv_intro.
- exact Hfirst_success.
- exact Hfirst_safe.
- exact Hthird_safe.
- intros first_rows Hfirst.
  destruct (Hfirst_forward first_rows Hfirst)
    as [second_rows [Hsecond Hfirst_second]].
  destruct (Hsecond_forward second_rows Hsecond)
    as [third_rows [Hthird Hsecond_third]].
  exists third_rows; split; [exact Hthird |].
  eapply ordered_rows_equiv_trans; eassumption.
- intros third_rows Hthird.
  destruct (Hsecond_backward third_rows Hthird)
    as [second_rows [Hsecond Hsecond_third]].
  destruct (Hfirst_backward second_rows Hsecond)
    as [first_rows [Hfirst Hfirst_second]].
  exists first_rows; split; [exact Hfirst |].
  eapply ordered_rows_equiv_trans; eassumption.
Qed.

Theorem query_expr_possible_equiv_of_possible_outcome_equiv_safe :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    query_expr_possible_runtime_safe env left ->
    query_expr_possible_runtime_safe env right ->
    query_expr_possible_has_success env left ->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right.
Proof.
intros env left right
  [Houtputs Hobservations]
  Hleft_safe Hright_safe Hleft_success.
split; [exact Houtputs |].
unfold query_expr_possible_observation_equiv,
  query_expr_possible_outcome_observation_equiv in *.
now apply outcome_relation_equiv_implies_successful_relation_equiv_safe.
Qed.

(** Possible error-only relations are equivalent only when both expose the
    same category and neither exposes any success under any schedule. *)
Theorem query_expr_possible_outcome_equiv_of_shared_exact_error :
  forall env first second expected,
    query_expr_outputs first = query_expr_outputs second ->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first (SqlError expected) ->
    @eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env second (SqlError expected) ->
    (forall rows,
      ~ @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env first (SqlSuccess rows)) ->
    (forall rows,
      ~ @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env second (SqlSuccess rows)) ->
    (forall observed,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env first (SqlError observed) ->
      observed = expected) ->
    (forall observed,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env second (SqlError observed) ->
      observed = expected) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env first second.
Proof.
intros env first second expected Houtputs Hfirst_error Hsecond_error
  Hfirst_no_success Hsecond_no_success Hfirst_category Hsecond_category.
split; [exact Houtputs|].
apply outcome_relation_equiv_intro.
- now exists (SqlError expected).
- now exists (SqlError expected).
- intros rows Hrows; exfalso; exact (Hfirst_no_success rows Hrows).
- intros rows Hrows; exfalso; exact (Hsecond_no_success rows Hrows).
- intro observed; split; intro Herror.
  + rewrite (Hfirst_category observed Herror); exact Hsecond_error.
  + rewrite (Hsecond_category observed Herror); exact Hfirst_error.
Qed.

Definition possible_stable_total_filter_acceptance
    (env : Env.env T)
    (formula : scalar_expr T relname ScalarResultBoolean)
    (keep : tuple T -> bool) : Prop :=
  (forall first second,
    Oeset.compare (OTuple T) first second = Eq ->
    keep first = keep second) /\
  forall (schedule : boolean_site -> boolean_evaluation_order) row,
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule (env_t T env row) formula (keep row).

(** A stable total WHERE decision is independent of the Boolean schedule and
    introduces no local error.  Child success witnesses may still use
    different schedules; the common proper [keep] function transports their
    exact ordered lists without confusing FALSE with UNKNOWN. *)
Theorem query_expr_filter_possible_outcome_equiv_congr_stable_total :
  forall env left_formula right_formula keep left_input right_input,
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_input right_input ->
    possible_stable_total_filter_acceptance env left_formula keep ->
    possible_stable_total_filter_acceptance env right_formula keep ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_formula left_input)
      (QExpr_Filter right_formula right_input).
Proof.
intros env left_formula right_formula keep left_input right_input
  [Houtputs
    [Hleft_input
      [Hright_input [Hforward [Hbackward Herrors]]]]]
  [Hkeep Hleft_formula] [_ Hright_formula].
split; [exact Houtputs|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_intro.
- destruct Hleft_input as [[rows|error] [schedule Hinput]].
  + exists (SqlSuccess (List.filter keep rows)), schedule.
    eapply EQuery_FilterRows; [exact Hinput|].
    apply (proj2
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env left_formula rows keep
        (fun row _ => Hleft_formula schedule row)
        (SqlSuccess (List.filter keep rows)))).
    reflexivity.
  + exists (SqlError error), schedule.
    now apply EQuery_FilterChildError.
- destruct Hright_input as [[rows|error] [schedule Hinput]].
  + exists (SqlSuccess (List.filter keep rows)), schedule.
    eapply EQuery_FilterRows; [exact Hinput|].
    apply (proj2
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env right_formula rows keep
        (fun row _ => Hright_formula schedule row)
        (SqlSuccess (List.filter keep rows)))).
    reflexivity.
  + exists (SqlError error), schedule.
    now apply EQuery_FilterChildError.
- intros output [left_schedule Houtput].
  apply eval_query_expr_filter_success_iff in Houtput.
  destruct Houtput as [left_rows [Hleft Hfilter]].
  apply (proj1
    (@eval_filter_rows_acceptance_exact T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null left_schedule env left_formula left_rows keep
      (fun row _ => Hleft_formula left_schedule row)
      (SqlSuccess output))) in Hfilter.
  inversion Hfilter; subst output.
  destruct (Hforward left_rows (ex_intro _ left_schedule Hleft))
    as [right_rows [[right_schedule Hright] Hrows]].
  exists (List.filter keep right_rows); split.
  + exists right_schedule.
    eapply EQuery_FilterRows; [exact Hright|].
    apply (proj2
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null right_schedule env right_formula right_rows keep
        (fun row _ => Hright_formula right_schedule row)
        (SqlSuccess (List.filter keep right_rows)))).
    reflexivity.
  + now apply ordered_rows_equiv_filter.
- intros output [right_schedule Houtput].
  apply eval_query_expr_filter_success_iff in Houtput.
  destruct Houtput as [right_rows [Hright Hfilter]].
  apply (proj1
    (@eval_filter_rows_acceptance_exact T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null right_schedule env right_formula right_rows keep
      (fun row _ => Hright_formula right_schedule row)
      (SqlSuccess output))) in Hfilter.
  inversion Hfilter; subst output.
  destruct (Hbackward right_rows (ex_intro _ right_schedule Hright))
    as [left_rows [[left_schedule Hleft] Hrows]].
  exists (List.filter keep left_rows); split.
  + exists left_schedule.
    eapply EQuery_FilterRows; [exact Hleft|].
    apply (proj2
      (@eval_filter_rows_acceptance_exact T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null left_schedule env left_formula left_rows keep
        (fun row _ => Hleft_formula left_schedule row)
        (SqlSuccess (List.filter keep left_rows)))).
    reflexivity.
  + now apply ordered_rows_equiv_filter.
- intro error; split.
  + intros [left_schedule Herror].
    apply eval_query_expr_filter_error_iff in Herror.
    destruct Herror as [Hchild|[rows [Hchild Hlocal]]].
    * destruct (proj1 (Herrors error) (ex_intro _ left_schedule Hchild))
        as [right_schedule Hright].
      exists right_schedule; now apply EQuery_FilterChildError.
    * apply (proj1
        (@eval_filter_rows_acceptance_exact T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null left_schedule env
          left_formula rows keep
          (fun row _ => Hleft_formula left_schedule row)
          (SqlError error))) in Hlocal.
      discriminate.
  + intros [right_schedule Herror].
    apply eval_query_expr_filter_error_iff in Herror.
    destruct Herror as [Hchild|[rows [Hchild Hlocal]]].
    * destruct (proj2 (Herrors error) (ex_intro _ right_schedule Hchild))
        as [left_schedule Hleft].
      exists left_schedule; now apply EQuery_FilterChildError.
    * apply (proj1
        (@eval_filter_rows_acceptance_exact T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null right_schedule env
          right_formula rows keep
          (fun row _ => Hright_formula right_schedule row)
          (SqlError error))) in Hlocal.
      discriminate.
Qed.

(** Row-support corollary of the relation-parametric GROUP lift.  The support
    relation may remember keys, projections, or multiplicity refinements, but
    does not constrain the schedules paired by the child witnesses.  Therefore
    its local premise still compares every independently chosen schedule, so
    aggregate/HAVING errors and order-sensitive floating aggregates are not
    silently erased. *)
Theorem query_expr_group_possible_outcome_equiv_of_supported_child_outcomes :
  forall env select_list group_terms having left right
      (supported : list (tuple T) -> list (tuple T) -> Prop),
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Group select_list group_terms having left) outcome) ->
    (forall left_rows,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env left
        (SqlSuccess left_rows) ->
      exists right_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null env right (SqlSuccess right_rows) /\
        supported left_rows right_rows) ->
    (forall right_rows,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env right
        (SqlSuccess right_rows) ->
      exists left_rows,
        @eval_query_expr_possible_outcome T relname
          basesort instance unknown symbol_runtime_error aggregate_runtime_error
          value_is_null env left (SqlSuccess left_rows) /\
        supported left_rows right_rows) ->
    (forall error,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env left (SqlError error) <->
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env right (SqlError error)) ->
    (forall left_schedule right_schedule left_rows right_rows,
      supported left_rows right_rows ->
      forall outcome,
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env select_list group_terms having
          (rows_bag T left_rows) outcome <->
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env select_list group_terms having
          (rows_bag T right_rows) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group select_list group_terms having left)
      (QExpr_Group select_list group_terms having right).
Proof.
intros env select_list group_terms having left right supported
  Hparent Hforward Hbackward Herrors Hgroup.
apply query_expr_possible_outcome_equiv_of_related; [reflexivity|].
eapply query_expr_group_possible_outcome_transport with
  (scheduled_rows_rel :=
    fun _ left_rows _ right_rows => supported left_rows right_rows).
- exact Hparent.
- intros left_schedule left_rows Hleft.
  destruct (Hforward left_rows (ex_intro _ left_schedule Hleft)) as
    [right_rows [[right_schedule Hright] Hsupported]].
  now exists right_schedule, right_rows.
- intros right_schedule right_rows Hright.
  destruct (Hbackward right_rows (ex_intro _ right_schedule Hright)) as
    [left_rows [[left_schedule Hleft] Hsupported]].
  now exists left_schedule, left_rows.
- exact Herrors.
- intros left_schedule left_rows right_schedule right_rows Hsupported.
  apply query_group_rows_outcomes_transport_of_exact_bag_outcomes.
  intro outcome; now apply Hgroup.
Qed.

(** Read-only query programs compose the public relation statement by
    statement.  Each statement retains its own existential Boolean schedule,
    and these list laws expose that structure directly. *)
Lemma query_program_possible_equiv_nil :
  forall env,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env nil nil.
Proof.
intros; exact I.
Qed.

Lemma query_program_possible_equiv_cons :
  forall env left_query left_program right_query right_program,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (left_query :: left_program) (right_query :: right_program) <->
    @query_expr_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_query right_query /\
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_program right_program.
Proof.
reflexivity.
Qed.

Lemma query_program_possible_outcome_equiv_nil :
  forall env,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env nil nil.
Proof.
intros; exact I.
Qed.

Lemma query_program_possible_outcome_equiv_cons :
  forall env left_query left_program right_query right_program,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (left_query :: left_program) (right_query :: right_program) <->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_query right_query /\
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_program right_program.
Proof.
reflexivity.
Qed.

Lemma query_program_possible_equiv_length :
  forall env left right,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    length left = length right.
Proof.
intros env left; induction left as [|left_query left_program IH];
  intros [|right_query right_program] Hequiv; cbn in *; try contradiction.
- reflexivity.
- destruct Hequiv as [_ Hprogram].
  now rewrite (IH right_program Hprogram).
Qed.

Lemma query_program_possible_outcome_equiv_length :
  forall env left right,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    length left = length right.
Proof.
intros env left; induction left as [|left_query left_program IH];
  intros [|right_query right_program] Hequiv; cbn in *; try contradiction.
- reflexivity.
- destruct Hequiv as [_ Hprogram].
  now rewrite (IH right_program Hprogram).
Qed.

Theorem query_program_possible_equiv_iff_Forall2 :
  forall env left right,
    @query_program_possible_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right <->
    Forall2
      (@query_expr_possible_equiv T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env)
      left right.
Proof.
intros env left; induction left as [|left_query left_program IH];
  intros [|right_query right_program]; cbn.
- split; [intro; constructor | intro; exact I].
- split; [contradiction | intro H; inversion H].
- split; [contradiction | intro H; inversion H].
- rewrite IH.
  split.
  + intros [Hquery Hprogram]. now constructor.
  + intro H; inversion H; subst; now split.
Qed.

Theorem query_program_possible_outcome_equiv_iff_Forall2 :
  forall env left right,
    @query_program_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right <->
    Forall2
      (@query_expr_possible_outcome_equiv T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env)
      left right.
Proof.
intros env left; induction left as [|left_query left_program IH];
  intros [|right_query right_program]; cbn.
- split; [intro; constructor | intro; exact I].
- split; [contradiction | intro H; inversion H].
- split; [contradiction | intro H; inversion H].
- rewrite IH.
  split.
  + intros [Hquery Hprogram]. now constructor.
  + intro H; inversion H; subst; now split.
Qed.

(** Renaming certificates include the same canonical admissibility hooks as
    the one query/scalar well-formedness traversal.  Keeping them explicit
    prevents possible-outcome transport from dropping typed leaf, call,
    predicate, rank, Boolean, or NULL obligations. *)
Variable leaf_has_type : type T -> @aggterm T -> Prop.
Variable call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Variable predicate_has_types : predicate T -> list (type T) -> Prop.
Variable rank_type boolean_type : type T.

(** Attribute renaming has a distinct row observation and therefore is not
    ordinary same-schema query equivalence.  This possible-outcome relation
    aggregates the constructor-local scheduled transport over every schedule
    while retaining mapped ordered schemas and exact runtime errors. *)
Definition query_mapped_schema_possible_outcome_equiv
    (left_env right_env : Env.env T)
    (rho : attribute T -> attribute T)
    (left right : query_expr T relname) : Prop :=
  @query_rename_schema_compatible T relname basesort value_is_null
    leaf_has_type call_has_type predicate_has_types rank_type boolean_type
    rho left right /\
  outcome_relation_equiv (@query_rows_rename T rho)
    (@eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null left_env left)
    (@eval_query_expr_possible_outcome T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null right_env right).

Definition query_rename_uniform_transport_under
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left right : query_expr T relname) : Prop :=
  forall schedule : boolean_site -> boolean_evaluation_order,
    @query_rename_transport_under T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null schedule leaf_has_type call_has_type predicate_has_types
      rank_type boolean_type environment_relation rho left right.

Theorem query_rename_uniform_transport_implies_mapped_schema_possible_outcome_equiv :
  forall environment_relation left_env right_env rho left right,
    environment_relation left_env right_env ->
    query_rename_uniform_transport_under
      environment_relation rho left right ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_env left outcome) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_env right outcome) ->
    query_mapped_schema_possible_outcome_equiv
      left_env right_env rho left right.
Proof.
intros environment_relation left_env right_env rho left right
  Henvironment Htransport Hleft Hright.
split.
- exact (proj1 (Htransport (fun _ => BooleanLeftFirst))).
- apply outcome_relation_equiv_intro.
  + exact Hleft.
  + exact Hright.
  + intros left_rows [schedule Heval].
    destruct (proj2 (Htransport schedule) left_env right_env Henvironment)
      as [Hforward _].
    destruct (Hforward left_rows Heval)
      as [right_rows [Hright_rows Hrenamed]].
    exists right_rows; split; [now exists schedule|exact Hrenamed].
  + intros right_rows [schedule Heval].
    destruct (proj2 (Htransport schedule) left_env right_env Henvironment)
      as [_ [Hbackward _]].
    destruct (Hbackward right_rows Heval)
      as [left_rows [Hleft_rows Hrenamed]].
    exists left_rows; split; [now exists schedule|exact Hrenamed].
  + intro error; split; intros [schedule Heval].
    * destruct (proj2 (Htransport schedule) left_env right_env Henvironment)
        as [_ [_ Herrors]].
      exists schedule; now apply (proj1 (Herrors error)).
    * destruct (proj2 (Htransport schedule) left_env right_env Henvironment)
        as [_ [_ Herrors]].
      exists schedule; now apply (proj2 (Herrors error)).
Qed.

Lemma query_mapped_schema_possible_outcome_equiv_mapped_schema :
  forall left_env right_env rho left right,
    query_mapped_schema_possible_outcome_equiv
      left_env right_env rho left right ->
    map rho (query_expr_outputs left) = query_expr_outputs right.
Proof.
intros left_env right_env rho left right [[_ [_ [Houtputs _]]] _].
exact Houtputs.
Qed.

End PublicPossibleOutcomes.

(** Constructor adapters at the complete possible-bag/error boundary.  These
    laws deliberately consume the public bag contract rather than inventing a
    fixed Boolean schedule correspondence. *)
Section PossibleBagConstructorAdapters.

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

Local Abbreviation eval_possible :=
  (@eval_query_expr_possible_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation possible_bag_outcomes :=
  (@query_possible_bag_outcomes T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation possible_bag_outcome_equiv :=
  (@query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** Extracting an actual successful list is sound because [outcome_alpha]
    existentially records the list that generated each possible bag. *)
Lemma query_expr_possible_bag_outcome_equiv_success_forward :
  forall env left right left_rows,
    possible_bag_outcome_equiv env left right ->
    eval_possible env left (SqlSuccess left_rows) ->
    exists right_rows,
      eval_possible env right (SqlSuccess right_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
Proof.
intros env left right left_rows Hequiv Hleft.
destruct (query_expr_possible_bag_outcome_equiv_outcomes Hequiv)
  as [_ [_ [Hforward _]]].
assert (Hleft_bag :
  possible_bag_outcomes env left (SqlSuccess (rows_bag T left_rows))).
{
  unfold query_possible_bag_outcomes, outcome_alpha, alpha; simpl.
  exists left_rows; split; [exact Hleft | apply bag_eq_refl].
}
destruct (Hforward _ Hleft_bag)
  as [right_bag [Hright_bag Hbags]].
unfold query_possible_bag_outcomes, outcome_alpha, alpha in Hright_bag;
  simpl in Hright_bag.
destruct Hright_bag as [right_rows [Hright Hright_bag]].
exists right_rows; split; [exact Hright |].
eapply bag_eq_trans; [exact Hbags |].
now apply bag_eq_sym.
Qed.

Lemma query_expr_possible_bag_outcome_equiv_success_backward :
  forall env left right right_rows,
    possible_bag_outcome_equiv env left right ->
    eval_possible env right (SqlSuccess right_rows) ->
    exists left_rows,
      eval_possible env left (SqlSuccess left_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
Proof.
intros env left right right_rows Hequiv Hright.
destruct (query_expr_possible_bag_outcome_equiv_outcomes Hequiv)
  as [_ [_ [_ [Hbackward _]]]].
assert (Hright_bag :
  possible_bag_outcomes env right (SqlSuccess (rows_bag T right_rows))).
{
  unfold query_possible_bag_outcomes, outcome_alpha, alpha; simpl.
  exists right_rows; split; [exact Hright | apply bag_eq_refl].
}
destruct (Hbackward _ Hright_bag)
  as [left_bag [Hleft_bag Hbags]].
unfold query_possible_bag_outcomes, outcome_alpha, alpha in Hleft_bag;
  simpl in Hleft_bag.
destruct Hleft_bag as [left_rows [Hleft Hleft_bag]].
exists left_rows; split; [exact Hleft |].
eapply bag_eq_trans; eassumption.
Qed.

Lemma query_expr_possible_bag_outcome_equiv_error_iff :
  forall env left right error,
    possible_bag_outcome_equiv env left right ->
    (eval_possible env left (SqlError error) <->
     eval_possible env right (SqlError error)).
Proof.
intros env left right error Hequiv.
destruct (query_expr_possible_bag_outcome_equiv_outcomes Hequiv)
  as [_ [_ [_ [_ Herrors]]]].
unfold query_possible_bag_outcomes, outcome_alpha in Herrors; simpl in Herrors.
exact (Herrors error).
Qed.

Lemma query_expr_possible_bag_outcome_equiv_inhabited :
  forall env left right,
    possible_bag_outcome_equiv env left right ->
    (exists outcome, eval_possible env left outcome) /\
    (exists outcome, eval_possible env right outcome).
Proof.
intros env left right Hequiv.
destruct (query_expr_possible_bag_outcome_equiv_outcomes Hequiv)
  as [Hleft [Hright _]].
split.
- destruct Hleft as [[bag | error] Houtcome].
  + unfold query_possible_bag_outcomes, outcome_alpha, alpha in Houtcome;
      simpl in Houtcome.
    destruct Houtcome as [rows [Hrows _]].
    now exists (SqlSuccess rows).
  + unfold query_possible_bag_outcomes, outcome_alpha in Houtcome;
      simpl in Houtcome.
    now exists (SqlError error).
- destruct Hright as [[bag | error] Houtcome].
  + unfold query_possible_bag_outcomes, outcome_alpha, alpha in Houtcome;
      simpl in Houtcome.
    destruct Houtcome as [rows [Hrows _]].
    now exists (SqlSuccess rows).
  + unfold query_possible_bag_outcomes, outcome_alpha in Houtcome;
      simpl in Houtcome.
    now exists (SqlError error).
Qed.

(** [DISTINCT] is a bag reset: duplicate elimination preserves SQL bag
    multiplicity exactly (one occurrence of each present row), while the
    constructor exposes every representative of the resulting bag.  Its only
    runtime errors are the child's errors. *)
Theorem query_expr_distinct_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env left right,
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros env left right Hequiv.
apply query_expr_possible_outcome_equiv_of_observations.
- exact (query_expr_possible_bag_outcome_equiv_outputs Hequiv).
- destruct (proj1
    (query_expr_possible_bag_outcome_equiv_inhabited Hequiv))
    as [[rows | error] Houtcome].
  + destruct Houtcome as [schedule Hrows].
    exists (SqlSuccess
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_distinct_bag (rows_bag T rows)))).
    exists schedule; eapply EQuery_DistinctSuccess; [exact Hrows |].
    apply query_elements_same_rows_as_bag.
  + destruct Houtcome as [schedule Herror].
    exists (SqlError error), schedule.
    now apply EQuery_DistinctChildError.
- destruct (proj2
    (query_expr_possible_bag_outcome_equiv_inhabited Hequiv))
    as [[rows | error] Houtcome].
  + destruct Houtcome as [schedule Hrows].
    exists (SqlSuccess
      (Febag.elements (Fecol.CBag (CTuple T))
        (query_distinct_bag (rows_bag T rows)))).
    exists schedule; eapply EQuery_DistinctSuccess; [exact Hrows |].
    apply query_elements_same_rows_as_bag.
  + destruct Houtcome as [schedule Herror].
    exists (SqlError error), schedule.
    now apply EQuery_DistinctChildError.
- intros output [left_schedule Houtput].
  apply eval_query_expr_distinct_success_iff in Houtput.
  destruct Houtput as [left_rows [Hleft Houtput_bag]].
  destruct (query_expr_possible_bag_outcome_equiv_success_forward
    Hequiv (ex_intro _ left_schedule Hleft))
    as [right_rows [[right_schedule Hright] Hrows]].
  exists output; split.
  + exists right_schedule.
    apply eval_query_expr_distinct_success_iff.
    exists right_rows; split; [exact Hright |].
    eapply query_same_rows_as_bag_bag_transport; [exact Houtput_bag |].
    now apply query_distinct_bag_congr.
  + apply ordered_rows_equiv_refl.
- intros output [right_schedule Houtput].
  apply eval_query_expr_distinct_success_iff in Houtput.
  destruct Houtput as [right_rows [Hright Houtput_bag]].
  destruct (query_expr_possible_bag_outcome_equiv_success_backward
    Hequiv (ex_intro _ right_schedule Hright))
    as [left_rows [[left_schedule Hleft] Hrows]].
  exists output; split.
  + exists left_schedule.
    apply eval_query_expr_distinct_success_iff.
    exists left_rows; split; [exact Hleft |].
    eapply query_same_rows_as_bag_bag_transport; [exact Houtput_bag |].
    apply bag_eq_sym; now apply query_distinct_bag_congr.
  + apply ordered_rows_equiv_refl.
- intro error.
  rewrite 2 eval_query_expr_distinct_possible_error_iff.
  now apply query_expr_possible_bag_outcome_equiv_error_iff.
Qed.

(** [RANK] canonicalizes the child bag before assigning ranks, so neither the
    child's list order nor its concrete bag representation is observed.  The
    local [NumericValueOutOfRange] outcome from a partial [rank_value]
    callback is transported separately from exact child errors. *)
Theorem query_expr_rank_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value left)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value right).
Proof.
intros env partition_keys order_keys rank_attribute rank_value
  left right Hequiv.
apply query_expr_possible_outcome_equiv_of_observations.
- cbn [query_expr_outputs].
  now rewrite (query_expr_possible_bag_outcome_equiv_outputs Hequiv).
- destruct (proj1
    (query_expr_possible_bag_outcome_equiv_inhabited Hequiv))
    as [[rows | error] Houtcome].
  + destruct Houtcome as [schedule Hrows].
    destruct
      (@query_rank_rows_outcome T value_is_null
        partition_keys order_keys rank_attribute rank_value
        (query_rank_bag_rows (rows_bag T rows))
        (query_rank_bag_rows (rows_bag T rows)))
      as [ranked_rows |] eqn:Hrank.
    * exists (SqlSuccess
        (Febag.elements (Fecol.CBag (CTuple T))
          (rows_bag T ranked_rows))).
      exists schedule.
      eapply EQuery_RankSuccess with
        (input_rows := rows) (ranked_rows := ranked_rows).
      -- exact Hrows.
      -- exact Hrank.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError (DataException NumericValueOutOfRange)), schedule.
      eapply EQuery_RankValueError with (input_rows := rows);
        [exact Hrows | exact Hrank].
  + destruct Houtcome as [schedule Herror].
    exists (SqlError error), schedule.
    now apply EQuery_RankChildError.
- destruct (proj2
    (query_expr_possible_bag_outcome_equiv_inhabited Hequiv))
    as [[rows | error] Houtcome].
  + destruct Houtcome as [schedule Hrows].
    destruct
      (@query_rank_rows_outcome T value_is_null
        partition_keys order_keys rank_attribute rank_value
        (query_rank_bag_rows (rows_bag T rows))
        (query_rank_bag_rows (rows_bag T rows)))
      as [ranked_rows |] eqn:Hrank.
    * exists (SqlSuccess
        (Febag.elements (Fecol.CBag (CTuple T))
          (rows_bag T ranked_rows))).
      exists schedule.
      eapply EQuery_RankSuccess with
        (input_rows := rows) (ranked_rows := ranked_rows).
      -- exact Hrows.
      -- exact Hrank.
      -- apply query_elements_same_rows_as_bag.
    * exists (SqlError (DataException NumericValueOutOfRange)), schedule.
      eapply EQuery_RankValueError with (input_rows := rows);
        [exact Hrows | exact Hrank].
  + destruct Houtcome as [schedule Herror].
    exists (SqlError error), schedule.
    now apply EQuery_RankChildError.
- intros output [left_schedule Houtput].
  apply eval_query_expr_rank_success_iff in Houtput.
  destruct Houtput as
    [left_rows [output_bag [Hleft [Hrank Houtput_bag]]]].
  destruct (query_expr_possible_bag_outcome_equiv_success_forward
    Hequiv (ex_intro _ left_schedule Hleft))
    as [right_rows [[right_schedule Hright] Hrows]].
  pose proof
    (query_rank_bag_relation_extensional
      value_is_null partition_keys order_keys rank_attribute rank_value
      Hrows (bag_eq_refl T output_bag)) as Htransport.
  exists output; split.
  + exists right_schedule.
    apply eval_query_expr_rank_success_iff.
    exists right_rows, output_bag; repeat split; try assumption.
    now apply (proj1 Htransport).
  + apply ordered_rows_equiv_refl.
- intros output [right_schedule Houtput].
  apply eval_query_expr_rank_success_iff in Houtput.
  destruct Houtput as
    [right_rows [output_bag [Hright [Hrank Houtput_bag]]]].
  destruct (query_expr_possible_bag_outcome_equiv_success_backward
    Hequiv (ex_intro _ right_schedule Hright))
    as [left_rows [[left_schedule Hleft] Hrows]].
  pose proof
    (query_rank_bag_relation_extensional
      value_is_null partition_keys order_keys rank_attribute rank_value
      Hrows (bag_eq_refl T output_bag)) as Htransport.
  exists output; split.
  + exists left_schedule.
    apply eval_query_expr_rank_success_iff.
    exists left_rows, output_bag; repeat split; try assumption.
    now apply (proj2 Htransport).
  + apply ordered_rows_equiv_refl.
- intro error; split; intros [schedule Herror].
  + pose proof
      (proj1 (@eval_query_expr_rank_error_iff T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env partition_keys order_keys rank_attribute
        rank_value left error) Herror) as Hsource.
    destruct Hsource as [Hchild | [Hkind [left_rows [Hleft Hrank]]]].
    * destruct (proj1
        (query_expr_possible_bag_outcome_equiv_error_iff error Hequiv)
        (ex_intro _ schedule Hchild))
        as [right_schedule Hright].
      exists right_schedule; now apply EQuery_RankChildError.
    * destruct (query_expr_possible_bag_outcome_equiv_success_forward
        Hequiv (ex_intro _ schedule Hleft))
        as [right_rows [[right_schedule Hright] Hrows]].
      exists right_schedule.
      apply eval_query_expr_rank_error_iff; right.
      split; [exact Hkind |].
      exists right_rows; split; [exact Hright |].
      pose proof (query_rank_bag_rows_eq Hrows) as Hcanonical.
      change
        (query_rank_bag_rows (query_rows_bag left_rows) =
         query_rank_bag_rows (query_rows_bag right_rows)) in Hcanonical.
      now rewrite <- Hcanonical.
  + pose proof
      (proj1 (@eval_query_expr_rank_error_iff T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule env partition_keys order_keys rank_attribute
        rank_value right error) Herror) as Hsource.
    destruct Hsource as [Hchild | [Hkind [right_rows [Hright Hrank]]]].
    * destruct (proj2
        (query_expr_possible_bag_outcome_equiv_error_iff error Hequiv)
        (ex_intro _ schedule Hchild))
        as [left_schedule Hleft].
      exists left_schedule; now apply EQuery_RankChildError.
    * destruct (query_expr_possible_bag_outcome_equiv_success_backward
        Hequiv (ex_intro _ schedule Hright))
        as [left_rows [[left_schedule Hleft] Hrows]].
      exists left_schedule.
      apply eval_query_expr_rank_error_iff; right.
      split; [exact Hkind |].
      exists left_rows; split; [exact Hleft |].
      pose proof (query_rank_bag_rows_eq Hrows) as Hcanonical.
      change
        (query_rank_bag_rows (query_rows_bag left_rows) =
         query_rank_bag_rows (query_rows_bag right_rows)) in Hcanonical.
      now rewrite Hcanonical.
Qed.

(** [ORDER BY] consumes only the child bag and then exposes every legal sorted
    representative.  The proof transports each observed output list itself;
    in particular it neither fixes a sort implementation nor collapses peers
    to one representative. *)
Theorem query_expr_order_by_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env keys left right,
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_OrderBy keys left) (QExpr_OrderBy keys right).
Proof.
intros env keys left right Hequiv.
apply query_expr_possible_outcome_equiv_of_observations.
- exact (query_expr_possible_bag_outcome_equiv_outputs Hequiv).
- destruct (proj1
    (query_expr_possible_bag_outcome_equiv_inhabited Hequiv))
    as [[rows | error] Houtcome].
  + destruct Houtcome as [schedule Hrows].
    destruct (@order_by_rows_has_observation T value_is_null keys rows)
      as [output Horder].
    exists (SqlSuccess output), schedule.
    now apply EQuery_OrderBySuccess with rows.
  + destruct Houtcome as [schedule Herror].
    exists (SqlError error), schedule.
    now apply EQuery_OrderByChildError.
- destruct (proj2
    (query_expr_possible_bag_outcome_equiv_inhabited Hequiv))
    as [[rows | error] Houtcome].
  + destruct Houtcome as [schedule Hrows].
    destruct (@order_by_rows_has_observation T value_is_null keys rows)
      as [output Horder].
    exists (SqlSuccess output), schedule.
    now apply EQuery_OrderBySuccess with rows.
  + destruct Houtcome as [schedule Herror].
    exists (SqlError error), schedule.
    now apply EQuery_OrderByChildError.
- intros output [left_schedule Houtput].
  apply eval_query_expr_order_by_success_iff in Houtput.
  destruct Houtput as
    [left_rows [Hleft [Houtput_bag Houtput_ordered]]].
  destruct (query_expr_possible_bag_outcome_equiv_success_forward
    Hequiv (ex_intro _ left_schedule Hleft))
    as [right_rows [[right_schedule Hright] Hrows]].
  exists output; split.
  + exists right_schedule.
    apply eval_query_expr_order_by_success_iff.
    exists right_rows; split; [exact Hright |].
    split; [| exact Houtput_ordered].
    eapply query_same_rows_as_bag_bag_transport; eassumption.
  + apply ordered_rows_equiv_refl.
- intros output [right_schedule Houtput].
  apply eval_query_expr_order_by_success_iff in Houtput.
  destruct Houtput as
    [right_rows [Hright [Houtput_bag Houtput_ordered]]].
  destruct (query_expr_possible_bag_outcome_equiv_success_backward
    Hequiv (ex_intro _ right_schedule Hright))
    as [left_rows [[left_schedule Hleft] Hrows]].
  exists output; split.
  + exists left_schedule.
    apply eval_query_expr_order_by_success_iff.
    exists left_rows; split; [exact Hleft |].
    split; [| exact Houtput_ordered].
    eapply query_same_rows_as_bag_bag_transport; [exact Houtput_bag |].
    now apply bag_eq_sym.
  + apply ordered_rows_equiv_refl.
- intro error.
  rewrite 2 eval_query_expr_order_by_possible_error_iff.
  now apply query_expr_possible_bag_outcome_equiv_error_iff.
Qed.

(** Positional consumers require closure of both child success relations.
    The closure bridge recovers exact possible ordered outcomes first; the
    existing list congruence then transports [skipn] positionally. *)
Theorem query_expr_offset_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env offset left right,
    BagClosed T
      (fun rows => eval_possible env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible env right (SqlSuccess rows)) ->
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset offset left) (QExpr_Offset offset right).
Proof.
intros env offset left right Hleft_closed Hright_closed Hequiv.
apply query_expr_offset_possible_outcome_equiv_congr.
eapply query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv;
  eassumption.
Qed.

(** [FETCH] has the same all-representatives obligation as [OFFSET]; one bag
    witness cannot determine an ordered prefix. *)
Theorem query_expr_fetch_possible_outcome_equiv_of_possible_bag_outcome_equiv :
  forall env count left right,
    BagClosed T
      (fun rows => eval_possible env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible env right (SqlSuccess rows)) ->
    possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch count left) (QExpr_Fetch count right).
Proof.
intros env count left right Hleft_closed Hright_closed Hequiv.
apply query_expr_fetch_possible_outcome_equiv_congr.
eapply query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv;
  eassumption.
Qed.

End PossibleBagConstructorAdapters.

(******************************************************************************)
(** Functional native JOIN elimination at the evaluator boundary.            **)
(******************************************************************************)

Section FunctionalJoinElimination.

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

Definition fixed_success_outcomes {A : Type} (value : A) :
    sql_outcome A -> Prop :=
  fun outcome => outcome = SqlSuccess value.

(** Eliminate a native JOIN to its left child once the right child is
    inhabited and error-free and the complete local JOIN continuation is
    occurrence-equivalent to the fixed successful left rows.  Functional
    matching, FK witnesses, matched/padded projections, predicate acceptance,
    and local runtime errors are deliberately kept in [Hlocal]; this theorem
    performs only the reusable evaluator-level lifting. *)
Theorem query_expr_join_relation_transport_to_left :
  forall schedule env kind predicate matched_select left_select right_select
      left right (row_rel : Tuple.tuple T -> Tuple.tuple T -> Prop),
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
        env left (SqlSuccess left_rows) ->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows) ->
      outcome_relation_transport (Forall2 row_rel)
        (@query_join_rows_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env kind predicate matched_select left_select right_select
          left_rows right_rows)
        (fixed_success_outcomes left_rows)) ->
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left).
Proof.
intros schedule env kind predicate matched_select left_select right_select
  left right row_rel Hright_success Hright_safe Hlocal.
split.
- intros output Hjoin.
  apply eval_query_expr_join_success_iff in Hjoin.
  destruct Hjoin as
    [left_rows [right_rows [output_bag
      [Hleft [Hright [Hlocal_success Houtput]]]]]].
  destruct (Hlocal left_rows right_rows Hleft Hright) as [Hforward _].
  destruct (Hforward output
    (ex_intro _ output_bag (conj Hlocal_success Houtput))) as
    [target_rows [Hfixed Hrows]].
  unfold fixed_success_outcomes in Hfixed; injection Hfixed as Hfixed.
  subst target_rows.
  exists left_rows; now split.
- split.
  + intros left_rows Hleft.
    destruct Hright_success as [right_rows Hright].
    destruct (Hlocal left_rows right_rows Hleft Hright)
      as [_ [Hbackward _]].
    destruct (Hbackward left_rows eq_refl) as
      [output [Hjoin_local Hrows]].
    exists output; split; [|exact Hrows].
    destruct Hjoin_local as [output_bag [Hjoin_bag Houtput]].
    apply eval_query_expr_join_success_iff.
    now exists left_rows, right_rows, output_bag.
  + intro error; split; intro Herror.
    * apply eval_query_expr_join_error_iff in Herror.
      destruct Herror as
        [Hleft_error |
         [left_rows [Hleft [Hright_error |
          [right_rows [Hright Hlocal_error]]]]]].
      -- exact Hleft_error.
      -- exfalso; exact (Hright_safe error Hright_error).
      -- destruct (Hlocal left_rows right_rows Hleft Hright)
           as [_ [_ Herrors]].
         apply (proj1 (Herrors error)) in Hlocal_error.
         discriminate.
    * apply eval_query_expr_join_error_iff; now left.
Qed.

(** LEFT JOIN elimination is the principal consumer, but the evaluator proof
    is valid for every join kind whose local continuation satisfies the same
    contract.  This named corollary makes the intended outer-join use visible
    without baking any key or schema into the theorem. *)
Corollary query_expr_left_join_functional_elimination_transport :
  forall schedule env predicate matched_select left_select right_select
      left right (row_rel : Tuple.tuple T -> Tuple.tuple T -> Prop),
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
        env left (SqlSuccess left_rows) ->
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env right (SqlSuccess right_rows) ->
      outcome_relation_transport (Forall2 row_rel)
        (@query_join_rows_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env QueryJoinLeft predicate matched_select left_select right_select
          left_rows right_rows)
        (fixed_success_outcomes left_rows)) ->
    outcome_relation_transport (Forall2 row_rel)
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Join QueryJoinLeft predicate matched_select left_select
          right_select left right))
      (@eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env left).
Proof.
intros; now eapply query_expr_join_relation_transport_to_left.
Qed.

End FunctionalJoinElimination.
