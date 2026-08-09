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

(** These relation lemmas are independent of SQL syntax.  They make the
    quantifier change from one scheduled relation to the union of all
    scheduled relations explicit, so no proof can silently promote a theorem
    about one Boolean schedule to a public SQL certificate. *)

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

(** DISTINCT elimination at a bag reset is a public SQL rewrite only when
    duplicate elimination is inert for every successful child bag under
    every legal Boolean schedule.  The pointwise reset proof remains in
    [OrderedQueryFacts]; this theorem quantifies that premise uniformly and
    preserves the complete possible success/error outcome relation. *)
Theorem query_expr_distinct_possible_outcome_equiv_inert_reset :
  forall env input,
    query_expr_order_behavior input = BagReset ->
    (forall (schedule : boolean_site -> boolean_evaluation_order)
        current_env bag,
      @query_success_bags T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null schedule current_env input bag ->
      bag_eq T (query_distinct_bag bag) bag) ->
    (exists outcome,
      @eval_query_expr_possible_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null env input outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Distinct input) input.
Proof.
intros env input Hreset Hinert Hinput.
assert (Huniform :
  query_expr_uniform_global_typed_outcome_equiv
    (QExpr_Distinct input) input).
{
  intro schedule.
  apply query_expr_distinct_global_typed_inert_reset; [exact Hreset |].
  intros current_env bag Hbag.
  exact (Hinert schedule current_env bag Hbag).
}
eapply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- exact Huniform.
- destruct Hinput as [outcome [schedule Houtcome]].
  exists outcome, schedule.
  apply (proj2 (proj2 (Huniform schedule) env outcome)).
  exact Houtcome.
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

(** Complete local group-bag outcomes are the most general typed GROUP
    replacement boundary.  Group keys may differ here only because the
    premise explicitly compares every resulting group-bag success and error
    under the same schedule, environment, and input bag. *)
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
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule; split; [exact Houtputs|].
  intros current_env outcome; split; intro Heval; inversion Heval; subst.
  + now apply EQuery_GroupChildError.
  + eapply EQuery_GroupBagError; [eassumption|].
    now apply (proj1
      (Hbag schedule current_env (query_rows_bag input_rows)
        (SqlError error))).
  + eapply EQuery_GroupBagSuccess; [eassumption| |eassumption].
    now apply (proj1
      (Hbag schedule current_env (query_rows_bag input_rows)
        (SqlSuccess output_bag))).
  + now apply EQuery_GroupChildError.
  + eapply EQuery_GroupBagError; [eassumption|].
    now apply (proj2
      (Hbag schedule current_env (query_rows_bag input_rows)
        (SqlError error))).
  + eapply EQuery_GroupBagSuccess; [eassumption| |eassumption].
    now apply (proj2
      (Hbag schedule current_env (query_rows_bag input_rows)
        (SqlSuccess output_bag))).
- exact Houtcome.
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
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule; apply query_expr_group_scalar_global_typed_congr.
  + apply scalar_select_list_global_outcome_equiv_refl.
  + exact (Hhaving schedule).
  + reflexivity.
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
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
intro schedule.
apply query_expr_group_outcome_equiv_congr.
- exact (Hchild schedule).
- exact (Houtcomes schedule).
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

(** Exact ordered identities retain list order and runtime errors pointwise.
    Their scheduled iff proofs are uniform in the schedule, so a single
    possible source outcome suffices at the public boundary. *)

Theorem query_expr_offset_zero_possible_outcome_equiv :
  forall env input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Offset 0 input) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Offset 0 input) input.
Proof.
intros env input Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule.
  exact (@query_expr_offset_zero_global_typed_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule input).
- exact Houtcome.
Qed.

Theorem query_expr_offset_offset_possible_outcome_equiv :
  forall env outer inner input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Offset outer (QExpr_Offset inner input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset outer (QExpr_Offset inner input))
      (QExpr_Offset (outer + inner) input).
Proof.
intros env outer inner input Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule.
  exact (@query_expr_offset_offset_global_typed_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule outer inner input).
- exact Houtcome.
Qed.

Theorem query_expr_fetch_fetch_possible_outcome_equiv :
  forall env outer inner input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Fetch outer (QExpr_Fetch inner input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch outer (QExpr_Fetch inner input))
      (QExpr_Fetch (Nat.min outer inner) input).
Proof.
intros env outer inner input Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule.
  exact (@query_expr_fetch_fetch_global_typed_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule outer inner input).
- exact Houtcome.
Qed.

Theorem query_expr_offset_fetch_possible_outcome_equiv :
  forall env offset count input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Offset offset (QExpr_Fetch count input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Offset offset (QExpr_Fetch count input))
      (QExpr_Fetch (count - offset) (QExpr_Offset offset input)).
Proof.
intros env offset count input Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule.
  exact (@query_expr_offset_fetch_global_typed_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule offset count input).
- exact Houtcome.
Qed.

Theorem query_expr_fetch_offset_possible_outcome_equiv :
  forall env count offset input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_Fetch count (QExpr_Offset offset input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Fetch count (QExpr_Offset offset input))
      (QExpr_Offset offset (QExpr_Fetch (offset + count) input)).
Proof.
intros env count offset input Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule.
  exact (@query_expr_fetch_offset_global_typed_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule count offset input).
- exact Houtcome.
Qed.

Theorem query_expr_order_by_order_by_possible_outcome_equiv :
  forall env outer_keys inner_keys input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null env
        (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input)) outcome) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_OrderBy outer_keys (QExpr_OrderBy inner_keys input))
      (QExpr_OrderBy outer_keys input).
Proof.
intros env outer_keys inner_keys input Houtcome.
apply query_expr_possible_outcome_equiv_of_uniform_global_typed.
- intro schedule.
  exact (@query_expr_order_by_order_by_global_typed_equiv T relname
    basesort instance unknown symbol_runtime_error aggregate_runtime_error
    value_is_null schedule outer_keys inner_keys input).
- exact Houtcome.
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
  [Houtputs [_ [_ [Hforward [Hbackward _]]]]]
  Hleft_safe Hright_safe Hleft_success.
split; [exact Houtputs |].
unfold query_expr_possible_observation_equiv.
now apply successful_relation_equiv_intro.
Qed.

(** FETCH 0 still evaluates its child.  Complete possible-schedule safety is
    therefore essential even though every successful observation is empty. *)
Theorem query_expr_fetch_zero_possible_outcome_equiv_safe :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_expr_possible_runtime_safe env left ->
    query_expr_possible_runtime_safe env right ->
    query_expr_possible_has_success env left ->
    query_expr_possible_has_success env right ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Fetch 0 left) (QExpr_Fetch 0 right).
Proof.
intros env left right Houtputs Hleft_safe Hright_safe
  [left_rows [left_schedule Hleft]]
  [right_rows [right_schedule Hright]].
split; [exact Houtputs|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome.
apply outcome_relation_equiv_intro.
- exists (SqlSuccess nil), left_schedule.
  now apply EQuery_FetchSuccess with (input_rows := left_rows).
- exists (SqlSuccess nil), right_schedule.
  now apply EQuery_FetchSuccess with (input_rows := right_rows).
- intros output [schedule Houtput].
  apply eval_query_expr_fetch_zero_success_iff in Houtput.
  destruct Houtput as [-> _].
  exists nil; split.
  + exists right_schedule.
    now apply EQuery_FetchSuccess with (input_rows := right_rows).
  + apply ordered_rows_equiv_refl.
- intros output [schedule Houtput].
  apply eval_query_expr_fetch_zero_success_iff in Houtput.
  destruct Houtput as [-> _].
  exists nil; split.
  + exists left_schedule.
    now apply EQuery_FetchSuccess with (input_rows := left_rows).
  + apply ordered_rows_equiv_refl.
- intro error.
  split; intros [schedule Herror].
  + exfalso; apply (Hleft_safe error).
    exists schedule; now apply eval_query_expr_fetch_error_iff in Herror.
  + exfalso; apply (Hright_safe error).
    exists schedule; now apply eval_query_expr_fetch_error_iff in Herror.
Qed.

(** ORDER BY is redundant only under a bound on every possible successful
    child list.  The proof preserves exact row positions; no bag abstraction
    crosses this ordered boundary. *)
Theorem query_expr_order_by_possible_outcome_equiv_of_success_length_le_one :
  forall env keys input,
    (exists outcome,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env input outcome) ->
    (forall rows,
      @eval_query_expr_possible_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env input (SqlSuccess rows) ->
      (length rows <= 1)%nat) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_OrderBy keys input) input.
Proof.
intros env keys input Hinput_outcome Hbound.
split; [reflexivity|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome.
apply outcome_relation_equiv_intro.
- destruct Hinput_outcome as [[rows|error] [schedule Hinput]].
  + destruct (@order_by_rows_has_observation T value_is_null keys rows)
      as [output [Hsame Hordered]].
    exists (SqlSuccess output), schedule.
    now apply EQuery_OrderBySuccess with rows.
  + exists (SqlError error), schedule.
    now apply EQuery_OrderByChildError.
- exact Hinput_outcome.
- intros output [schedule Houtput].
  apply eval_query_expr_order_by_success_iff in Houtput.
  destruct Houtput as [input_rows [Hinput [Hsame _]]].
  exists input_rows; split.
  + now exists schedule.
  + apply query_same_rows_as_bag_length_le_one_ordered_equiv; [exact Hsame|].
    apply Hbound; now exists schedule.
- intros input_rows [schedule Hinput].
  destruct (@order_by_rows_has_observation T value_is_null keys input_rows)
    as [output [Hsame Hordered]].
  exists output; split.
  + exists schedule.
    apply eval_query_expr_order_by_success_iff.
    exists input_rows; repeat split; assumption.
  + apply query_same_rows_as_bag_length_le_one_ordered_equiv; [exact Hsame|].
    apply Hbound; now exists schedule.
- intro error; split; intros [schedule Herror].
  + exists schedule; now apply eval_query_expr_order_by_error_iff in Herror.
  + exists schedule; now apply eval_query_expr_order_by_error_iff.
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

(** Generic possible-outcome GROUP lift.  The support relation may remember
    keys, projections, multiplicity refinements, or another reusable child
    correspondence.  The decisive premise compares the complete group-bag
    outcome under the independently chosen child schedules, so aggregate and
    HAVING errors cannot be lost and order-sensitive floating aggregates are
    not silently treated as permutation-invariant. *)
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
assert (Hparent_forward :
  forall schedule outcome,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule env
      (QExpr_Group select_list group_terms having left) outcome ->
    exists right_schedule,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Group select_list group_terms having right) outcome).
{
  intros left_schedule [output|error] Heval.
  - apply eval_query_expr_group_success_iff in Heval.
    destruct Heval as
      [left_rows [output_bag [Hleft [Hleft_group Houtput]]]].
    destruct (Hforward left_rows (ex_intro _ left_schedule Hleft))
      as [right_rows [[right_schedule Hright] Hsupport]].
    exists right_schedule.
    apply eval_query_expr_group_success_iff.
    exists right_rows, output_bag; repeat split; try assumption.
    apply (proj1
      (Hgroup left_schedule right_schedule left_rows right_rows Hsupport
        (SqlSuccess output_bag))).
    exact Hleft_group.
  - apply eval_query_expr_group_error_iff in Heval.
    destruct Heval as [Hchild|[left_rows [Hleft Hleft_group]]].
    + destruct (proj1 (Herrors error) (ex_intro _ left_schedule Hchild))
        as [right_schedule Hright].
      exists right_schedule; now apply EQuery_GroupChildError.
    + destruct (Hforward left_rows (ex_intro _ left_schedule Hleft))
        as [right_rows [[right_schedule Hright] Hsupport]].
      exists right_schedule.
      eapply EQuery_GroupBagError with (input_rows := right_rows).
      * exact Hright.
      * apply (proj1
          (Hgroup left_schedule right_schedule left_rows right_rows Hsupport
            (SqlError error))).
        exact Hleft_group.
}
assert (Hparent_backward :
  forall schedule outcome,
    @eval_query_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule env
      (QExpr_Group select_list group_terms having right) outcome ->
    exists left_schedule,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Group select_list group_terms having left) outcome).
{
  intros right_schedule [output|error] Heval.
  - apply eval_query_expr_group_success_iff in Heval.
    destruct Heval as
      [right_rows [output_bag [Hright [Hright_group Houtput]]]].
    destruct (Hbackward right_rows (ex_intro _ right_schedule Hright))
      as [left_rows [[left_schedule Hleft] Hsupport]].
    exists left_schedule.
    apply eval_query_expr_group_success_iff.
    exists left_rows, output_bag; repeat split; try assumption.
    apply (proj2
      (Hgroup left_schedule right_schedule left_rows right_rows Hsupport
        (SqlSuccess output_bag))).
    exact Hright_group.
  - apply eval_query_expr_group_error_iff in Heval.
    destruct Heval as [Hchild|[right_rows [Hright Hright_group]]].
    + destruct (proj2 (Herrors error) (ex_intro _ right_schedule Hchild))
        as [left_schedule Hleft].
      exists left_schedule; now apply EQuery_GroupChildError.
    + destruct (Hbackward right_rows (ex_intro _ right_schedule Hright))
        as [left_rows [[left_schedule Hleft] Hsupport]].
      exists left_schedule.
      eapply EQuery_GroupBagError with (input_rows := left_rows).
      * exact Hleft.
      * apply (proj2
          (Hgroup left_schedule right_schedule left_rows right_rows Hsupport
            (SqlError error))).
        exact Hright_group.
}
split; [reflexivity|].
unfold query_expr_possible_outcome_observation_equiv,
  eval_query_expr_possible_outcome in *.
apply outcome_relation_equiv_intro.
- exact Hparent.
- destruct Hparent as [outcome [schedule Heval]].
  destruct (Hparent_forward schedule outcome Heval)
    as [right_schedule Hright].
  now exists outcome, right_schedule.
- intros output [schedule Heval].
  destruct (Hparent_forward schedule (SqlSuccess output) Heval)
    as [right_schedule Hright].
  exists output; split; [now exists right_schedule|].
  apply ordered_rows_equiv_refl.
- intros output [schedule Heval].
  destruct (Hparent_backward schedule (SqlSuccess output) Heval)
    as [left_schedule Hleft].
  exists output; split; [now exists left_schedule|].
  apply ordered_rows_equiv_refl.
- intro error; split; intros [schedule Heval].
  + destruct (Hparent_forward schedule (SqlError error) Heval)
      as [right_schedule Hright].
    now exists right_schedule.
  + destruct (Hparent_backward schedule (SqlError error) Heval)
      as [left_schedule Hleft].
    now exists left_schedule.
Qed.

Theorem query_expr_filter_possible_outcome_equiv_of_always_true_uniform :
  forall env formula input,
    (forall schedule, exists outcome,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env input outcome) ->
    (forall schedule rows,
      @eval_query_expr_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env input (SqlSuccess rows) ->
      forall row,
        In row rows ->
        forall outcome,
          @eval_scalar_boolean_expr_outcome T relname basesort instance unknown
            symbol_runtime_error aggregate_runtime_error value_is_null
            schedule (env_t T env row) formula outcome <->
          outcome = SqlSuccess (Bool.true (B T))) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env (QExpr_Filter formula input) input.
Proof.
intros env formula input Houtcomes Hformula.
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
intro schedule.
apply query_expr_filter_outcome_equiv_of_always_true.
- exact (Houtcomes schedule).
- exact (Hformula schedule).
Qed.

(** CROSS JOIN distribution duplicates the left child on the target.  The
    possible theorem therefore retains uniform, per-schedule bag
    functionality, safety, and success rather than pretending that unrelated
    possible child witnesses can be combined. *)
Theorem query_expr_cross_join_union_right_possible_outcome_equiv_safe_uniform :
  forall env left first second,
    query_expr_sort first =S= query_expr_sort second ->
    query_expr_sort (QExpr_CrossJoin left first) =S=
      query_expr_sort (QExpr_CrossJoin left second) ->
    (forall schedule left_bag left_bag',
      @query_success_bags T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left left_bag ->
      @query_success_bags T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env left left_bag' ->
      bag_eq T left_bag left_bag') ->
    (forall schedule,
      @query_expr_runtime_safe T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_CrossJoin left (QExpr_Set Union first second))) ->
    (forall schedule,
      @query_expr_runtime_safe T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Set Union
          (QExpr_CrossJoin left first)
          (QExpr_CrossJoin left second))) ->
    (forall schedule,
      @query_expr_has_success T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_CrossJoin left (QExpr_Set Union first second))) ->
    @query_expr_possible_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left (QExpr_Set Union first second))
      (QExpr_Set Union
        (QExpr_CrossJoin left first)
        (QExpr_CrossJoin left second)).
Proof.
intros env left first second Hsource_sort Htarget_sort Hfunctional
  Hsource_safe Htarget_safe Hsource_success.
apply query_expr_all_schedules_outcome_equiv_implies_possible_outcome_equiv.
intro schedule.
apply query_expr_cross_join_union_right_outcome_equiv_safe.
- exact Hsource_sort.
- exact Htarget_sort.
- exact (Hfunctional schedule).
- exact (Hsource_safe schedule).
- exact (Htarget_safe schedule).
- exact (Hsource_success schedule).
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
