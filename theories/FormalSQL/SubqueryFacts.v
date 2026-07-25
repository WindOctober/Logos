(** Reusable inversion and composition facts for predicate subqueries. *)

Set Implicit Arguments.

From Stdlib Require Import Bool List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula FTuples
  ListPermut OrderedSet Projection SqlErrorSemantics SqlOutcome
  SqlQueryContexts SqlQuerySemantics SqlQuerySyntax SqlQueryWellFormed.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts RelationalAlgebraFacts ScalarPredicateFacts.

Import ListNotations.
Import Tuple.

Arguments Select_List {T}.
Arguments _Select_List {T}.

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

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation project_rows :=
  (@project_rows_outcome T symbol_runtime_error aggregate_runtime_error).

(** Raw evaluation-relation equality for one expression at two correlated
    environments.  Unlike [query_expr_outcome_equiv], the query relation below
    deliberately asks for the same concrete successful row list; constructor
    lemmas that cannot justify that strength must expose an extra premise. *)
Definition formula_expr_env_outcome_equiv
    (left_env right_env : Env.env T) (formula : formula_expr T relname) : Prop :=
  forall outcome,
    eval_formula left_env formula outcome <->
    eval_formula right_env formula outcome.

Definition query_expr_env_outcome_equiv
    (left_env right_env : Env.env T) (query : query_expr T relname) : Prop :=
  forall outcome,
    eval_query left_env query outcome <->
    eval_query right_env query outcome.

Lemma formula_expr_conj_env_congr :
  forall left_env right_env operation left right,
    formula_expr_env_outcome_equiv left_env right_env left ->
    formula_expr_env_outcome_equiv left_env right_env right ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Conj operation left right).
Proof.
  intros left_env right_env operation left right Hleft Hright outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EFormula_ConjLeftError. now apply (proj1 (Hleft _)).
  - eapply EFormula_ConjRightError.
    + match goal with
      | H : eval_formula left_env left _ |- _ =>
          exact (proj1 (Hleft _) H)
      end.
    + match goal with
      | H : eval_formula left_env right _ |- _ =>
          exact (proj1 (Hright _) H)
      end.
  - eapply EFormula_ConjSuccess.
    + match goal with
      | H : eval_formula left_env left _ |- _ =>
          exact (proj1 (Hleft _) H)
      end.
    + match goal with
      | H : eval_formula left_env right _ |- _ =>
          exact (proj1 (Hright _) H)
      end.
  - apply EFormula_ConjLeftError. now apply (proj2 (Hleft _)).
  - eapply EFormula_ConjRightError.
    + match goal with
      | H : eval_formula right_env left _ |- _ =>
          exact (proj2 (Hleft _) H)
      end.
    + match goal with
      | H : eval_formula right_env right _ |- _ =>
          exact (proj2 (Hright _) H)
      end.
  - eapply EFormula_ConjSuccess.
    + match goal with
      | H : eval_formula right_env left _ |- _ =>
          exact (proj2 (Hleft _) H)
      end.
    + match goal with
      | H : eval_formula right_env right _ |- _ =>
          exact (proj2 (Hright _) H)
      end.
Qed.

Lemma formula_expr_not_env_congr :
  forall left_env right_env formula,
    formula_expr_env_outcome_equiv left_env right_env formula ->
    formula_expr_env_outcome_equiv left_env right_env (FExpr_Not formula).
Proof.
  intros left_env right_env formula Hformula outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EFormula_NotError. now apply (proj1 (Hformula _)).
  - apply EFormula_NotSuccess. now apply (proj1 (Hformula _)).
  - apply EFormula_NotError. now apply (proj2 (Hformula _)).
  - apply EFormula_NotSuccess. now apply (proj2 (Hformula _)).
Qed.

Lemma formula_expr_pred_env_congr_safe :
  forall left_env right_env predicate arguments,
    Env.equiv_env T left_env right_env ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      arguments = None ->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      arguments = None ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Pred predicate arguments).
Proof.
  intros left_env right_env predicate arguments Henv
    Hleft_safe Hright_safe outcome.
  assert (Harguments :
    map (Interp.interp_aggterm T left_env) arguments =
    map (Interp.interp_aggterm T right_env) arguments).
  {
    apply map_ext; intro argument.
    now apply Interp.interp_aggterm_eq.
  }
  destruct outcome as [truth|error].
  - split; intro Heval; inversion Heval; subst.
    + assert (Htarget :
        eval_formula right_env (FExpr_Pred predicate arguments)
          (SqlSuccess
            (interp_predicate T predicate
              (map (Interp.interp_aggterm T right_env) arguments)))).
      { apply EFormula_PredSuccess; exact Hright_safe. }
      rewrite <- Harguments in Htarget; exact Htarget.
    + assert (Hsource :
        eval_formula left_env (FExpr_Pred predicate arguments)
          (SqlSuccess
            (interp_predicate T predicate
              (map (Interp.interp_aggterm T left_env) arguments)))).
      { apply EFormula_PredSuccess; exact Hleft_safe. }
      rewrite Harguments in Hsource; exact Hsource.
  - split; intro Heval; inversion Heval; subst; congruence.
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
      formula_expr_env_outcome_equiv
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
      formula_expr_env_outcome_equiv
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

(** Exact projection congruence needs concrete projection equality in addition
    to runtime safety.  [Env.equiv_env] alone yields only semantic tuple
    equality for an arbitrary [Tuple.Rcd], which is insufficient for raw
    outcome [iff]. *)
Lemma project_rows_outcome_env_congr_safe_exact :
  forall left_env right_env select_list rows,
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T left_env row) select_list = None) ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T right_env row) select_list = None) ->
    (forall row,
      Projection.projection T (Env.env_t T left_env row)
        (@Select_List T select_list) =
      Projection.projection T (Env.env_t T right_env row)
        (@Select_List T select_list)) ->
    project_rows left_env select_list rows =
    project_rows right_env select_list rows.
Proof.
  intros left_env right_env select_list rows
    Hleft_safe Hright_safe Hprojection.
  induction rows as [|row rows IH]; [reflexivity|].
  cbn [project_rows_outcome].
  rewrite (Hleft_safe row), (Hright_safe row), (Hprojection row), IH.
  reflexivity.
Qed.

Lemma query_expr_project_env_congr_safe_exact :
  forall left_env right_env select_list input,
    query_expr_env_outcome_equiv left_env right_env input ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T left_env row) select_list = None) ->
    (forall row,
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (Env.env_t T right_env row) select_list = None) ->
    (forall row,
      Projection.projection T (Env.env_t T left_env row)
        (@Select_List T select_list) =
      Projection.projection T (Env.env_t T right_env row)
        (@Select_List T select_list)) ->
    query_expr_env_outcome_equiv left_env right_env
      (QExpr_Project select_list input).
Proof.
  intros left_env right_env select_list input Hinput
    Hleft_safe Hright_safe Hprojection outcome.
  split; intro Heval; inversion Heval; subst.
  - apply EQuery_ProjectChildError. now apply (proj1 (Hinput _)).
  - rewrite (@project_rows_outcome_env_congr_safe_exact
      left_env right_env select_list input_rows
      Hleft_safe Hright_safe Hprojection).
    apply EQuery_ProjectRows.
    match goal with
    | H : eval_query left_env input _ |- _ =>
        exact (proj1 (Hinput _) H)
    end.
  - apply EQuery_ProjectChildError. now apply (proj2 (Hinput _)).
  - rewrite <- (@project_rows_outcome_env_congr_safe_exact
      left_env right_env select_list input_rows
      Hleft_safe Hright_safe Hprojection).
    apply EQuery_ProjectRows.
    match goal with
    | H : eval_query right_env input _ |- _ =>
        exact (proj2 (Hinput _) H)
    end.
Qed.

Definition quantified_row_truth
    (env : Env.env T) (which_predicate : predicate T)
    (arguments : list (@aggterm T)) (subquery : query_expr T relname)
    (row : tuple T) : Bool.b (B T) :=
  let interpreted_arguments := map (@interp_aggterm T env) arguments in
  interp_predicate T which_predicate
    (interpreted_arguments ++
     map (dot T row) (query_expr_outputs subquery)).

Definition quantified_rows_truth
    (env : Env.env T) (which_quantifier : quantifier)
    (which_predicate : predicate T) (arguments : list (@aggterm T))
    (subquery : query_expr T relname) (rows : list (tuple T)) : Bool.b (B T) :=
  interp_quant (B T) which_quantifier
    (quantified_row_truth env which_predicate arguments subquery)
    (query_canonical_rows rows).

Definition in_row_truth
    (env : Env.env T) (select_items : list (@select T))
    (row : tuple T) : Bool.b (B T) :=
  let projected :=
    projection T env (Select_List (_Select_List select_items)) in
  @query_tuple_equal T unknown value_is_null projected row.

Definition in_rows_truth
    (env : Env.env T) (select_items : list (@select T))
    (rows : list (tuple T)) : Bool.b (B T) :=
  interp_quant (B T) Exists_F
    (in_row_truth env select_items)
    (query_canonical_rows rows).

(** SQL tuple comparison is proper for the semantic tuple equality exposed by
    [Tuple.OTuple].  This is the missing bridge between
    [Projection.projection_eq], which intentionally returns semantic equality,
    and the three-valued row comparison used by [IN]. *)
Lemma query_tuple_equal_congr :
  forall left left' right right',
    Oeset.compare (OTuple T) left left' = Eq ->
    Oeset.compare (OTuple T) right right' = Eq ->
    @query_tuple_equal T unknown value_is_null left right =
    @query_tuple_equal T unknown value_is_null left' right'.
Proof.
  intros left left' right right' Hleft Hright.
  rewrite tuple_eq in Hleft, Hright.
  destruct Hleft as [Hleft_labels Hleft_values].
  destruct Hright as [Hright_labels Hright_values].
  unfold query_tuple_equal.
  assert (Hlabels :
    (labels T left =S?= labels T right) =
    (labels T left' =S?= labels T right')).
  {
    transitivity (labels T left' =S?= labels T right).
    - now apply Fset.equal_eq_1.
    - now apply Fset.equal_eq_2.
  }
  rewrite Hlabels.
  destruct (labels T left' =S?= labels T right') eqn:Hmatches;
    [|reflexivity].
  rewrite <- (Fset.elements_spec1 _ _ _ Hleft_labels).
  assert (Hleft_right : labels T left =S= labels T right).
  {
    pose proof Hleft_labels as Hleft_labels_ext.
    pose proof Hright_labels as Hright_labels_ext.
    pose proof Hmatches as Hmatches_ext.
    rewrite Fset.equal_spec in
      Hleft_labels_ext, Hright_labels_ext, Hmatches_ext |- *.
    intro attribute.
    rewrite (Hleft_labels_ext attribute), (Hmatches_ext attribute).
    symmetry; apply Hright_labels_ext.
  }
  assert (Hvalues : forall attributes,
    (forall attribute,
      In attribute attributes -> attribute inS labels T left) ->
    (forall attribute,
      In attribute attributes -> attribute inS labels T right) ->
    @query_tuple_values_equal T unknown value_is_null
      attributes left right =
    @query_tuple_values_equal T unknown value_is_null
      attributes left' right').
  {
    intros attributes Hleft_mem Hright_mem.
    induction attributes as [|attribute attributes IH]; [reflexivity|].
    cbn [query_tuple_values_equal].
    rewrite (Hleft_values attribute
      (Hleft_mem attribute (or_introl eq_refl))).
    rewrite (Hright_values attribute
      (Hright_mem attribute (or_introl eq_refl))).
    rewrite IH.
    - reflexivity.
    - intros current Hcurrent.
      apply Hleft_mem; now right.
    - intros current Hcurrent.
      apply Hright_mem; now right.
  }
  apply Hvalues.
  - intros attribute Hattribute.
    now apply Fset.in_elements_mem.
  - intros attribute Hattribute.
    rewrite <- (Fset.mem_eq_2 _ _ _ Hleft_right).
    now apply Fset.in_elements_mem.
Qed.

Lemma in_row_truth_env_congr :
  forall left_env right_env select_items row,
    Env.equiv_env T left_env right_env ->
    in_row_truth left_env select_items row =
    in_row_truth right_env select_items row.
Proof.
  intros left_env right_env select_items row Henv.
  unfold in_row_truth.
  apply query_tuple_equal_congr.
  - now apply Projection.projection_eq.
  - apply Oeset.compare_eq_refl.
Qed.

Lemma in_rows_truth_env_congr :
  forall left_env right_env select_items rows,
    Env.equiv_env T left_env right_env ->
    in_rows_truth left_env select_items rows =
    in_rows_truth right_env select_items rows.
Proof.
  intros left_env right_env select_items rows Henv.
  unfold in_rows_truth, interp_quant.
  induction (query_canonical_rows rows) as [|row tail IH]; [reflexivity|].
  cbn [Bool.existsb].
  now rewrite (in_row_truth_env_congr
    (left_env := left_env) (right_env := right_env)
    select_items row Henv), IH.
Qed.

(** [IN] is three-valued, but a filtering consumer observes only whether its
    result is exactly TRUE.  If [accept] describes that decision for each
    candidate row, the decision over the canonical bag representative is the
    ordinary Boolean existence test over the original row list.  In
    particular, FALSE and UNKNOWN both remain non-accepting here; this lemma
    intentionally does not identify their underlying [Bool3] results. *)
Lemma in_rows_acceptance_existsb :
  forall env select_items rows (accept : tuple T -> bool),
    (forall row,
      Bool.is_true (B T) (in_row_truth env select_items row) = accept row) ->
    Bool.is_true (B T) (in_rows_truth env select_items rows) =
    existsb accept rows.
Proof.
  intros env select_items rows accept Haccept.
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
      (Bool.existsb (B T) (in_row_truth env select_items) candidates) =
    existsb
      (fun row =>
        Bool.is_true (B T) (in_row_truth env select_items row))
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
  unfold in_rows_truth, interp_quant.
  rewrite His_true_exists.
  eapply existsb_rel_permut.
  - intros left right Hequal.
    rewrite <- (Haccept right).
    apply f_equal.
    unfold in_row_truth.
    apply query_tuple_equal_congr.
    + apply Oeset.compare_eq_refl.
    + exact Hequal.
  - eapply query_same_rows_as_bag_permut_between
      with (bag := query_rows_bag rows).
    + apply query_canonical_rows_same_as_bag.
      unfold query_same_rows_as_bag; apply Febag.equal_refl.
    + unfold query_same_rows_as_bag; apply Febag.equal_refl.
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
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Exists_F which_predicate arguments subquery rows =
      Bool.true (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.true (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.existsb_exists_true.
Qed.

Lemma quantified_rows_exists_false_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Exists_F which_predicate arguments subquery rows =
      Bool.false (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.false (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.existsb_exists_false.
Qed.

Lemma quantified_rows_forall_true_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Forall_F which_predicate arguments subquery rows =
      Bool.true (B T) <->
    forall row,
      In row (query_canonical_rows rows) ->
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.true (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.forallb_forall_true.
Qed.

Lemma quantified_rows_forall_false_iff :
  forall env which_predicate arguments subquery rows,
    quantified_rows_truth env Forall_F which_predicate arguments subquery rows =
      Bool.false (B T) <->
    exists row,
      In row (query_canonical_rows rows) /\
        quantified_row_truth env which_predicate arguments subquery row =
          Bool.false (B T).
Proof.
  intros; unfold quantified_rows_truth, interp_quant.
  apply Bool.forallb_forall_false.
Qed.

Lemma in_rows_true_iff : forall env select_items rows,
  in_rows_truth env select_items rows = Bool.true (B T) <->
  exists row,
    In row (query_canonical_rows rows) /\
    in_row_truth env select_items row = Bool.true (B T).
Proof.
  intros; unfold in_rows_truth, interp_quant.
  apply Bool.existsb_exists_true.
Qed.

Lemma in_rows_false_iff : forall env select_items rows,
  in_rows_truth env select_items rows = Bool.false (B T) <->
  forall row,
    In row (query_canonical_rows rows) ->
    in_row_truth env select_items row = Bool.false (B T).
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

Lemma eval_formula_quant_error_iff :
  forall env which_quantifier which_predicate arguments subquery error,
    eval_formula env
      (FExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlError error) <->
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = Some error \/
    (first_runtime_error
       (@eval_aggterm_runtime_error T
         symbol_runtime_error aggregate_runtime_error env)
       arguments = None /\
     eval_query env subquery (SqlError error)).
Proof.
  intros env which_quantifier which_predicate arguments subquery error; split.
  - intro Heval; inversion Heval; subst.
    + now left.
    + right; now split.
  - intros [Harguments | [Harguments Hsubquery]].
    + now apply EFormula_QuantArgumentsError.
    + eapply EFormula_QuantSubqueryError; eassumption.
Qed.

Lemma eval_formula_quant_success_iff :
  forall env which_quantifier which_predicate arguments subquery truth,
    eval_formula env
      (FExpr_Quant which_quantifier which_predicate arguments subquery)
      (SqlSuccess truth) <->
    exists rows,
      first_runtime_error
        (@eval_aggterm_runtime_error T
          symbol_runtime_error aggregate_runtime_error env)
        arguments = None /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = quantified_rows_truth env which_quantifier which_predicate
        arguments subquery rows.
Proof.
  intros env which_quantifier which_predicate arguments subquery truth; split.
  - intro Heval; inversion Heval; subst.
    exists rows; repeat split; try assumption; reflexivity.
  - intros [rows [Harguments [Hsubquery ->]]].
    eapply EFormula_QuantSuccess; eassumption.
Qed.

Lemma eval_formula_quant_forall_empty :
  forall env which_predicate arguments subquery,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env
      (FExpr_Quant Forall_F which_predicate arguments subquery)
      (SqlSuccess (Bool.true (B T))).
Proof.
  intros env which_predicate arguments subquery Harguments Hsubquery.
  apply eval_formula_quant_success_iff.
  exists []; split; [exact Harguments|].
  split; [exact Hsubquery|].
  unfold quantified_rows_truth; rewrite query_canonical_rows_empty.
  reflexivity.
Qed.

Lemma eval_formula_quant_exists_empty :
  forall env which_predicate arguments subquery,
    first_runtime_error
      (@eval_aggterm_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      arguments = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env
      (FExpr_Quant Exists_F which_predicate arguments subquery)
      (SqlSuccess (Bool.false (B T))).
Proof.
  intros env which_predicate arguments subquery Harguments Hsubquery.
  apply eval_formula_quant_success_iff.
  exists []; split; [exact Harguments|].
  split; [exact Hsubquery|].
  unfold quantified_rows_truth; rewrite query_canonical_rows_empty.
  reflexivity.
Qed.

Lemma eval_formula_in_error_iff :
  forall env select_items subquery error,
    eval_formula env (FExpr_In select_items subquery) (SqlError error) <->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = Some error \/
    (first_runtime_error
       (@eval_select_runtime_error T
         symbol_runtime_error aggregate_runtime_error env)
       select_items = None /\
     eval_query env subquery (SqlError error)).
Proof.
  intros env select_items subquery error; split.
  - intro Heval; inversion Heval; subst.
    + now left.
    + right; now split.
  - intros [Harguments | [Harguments Hsubquery]].
    + now apply EFormula_InArgumentsError.
    + eapply EFormula_InSubqueryError; eassumption.
Qed.

Lemma eval_formula_in_success_iff :
  forall env select_items subquery truth,
    eval_formula env (FExpr_In select_items subquery) (SqlSuccess truth) <->
    exists rows,
      first_runtime_error
        (@eval_select_runtime_error T
          symbol_runtime_error aggregate_runtime_error env)
        select_items = None /\
      eval_query env subquery (SqlSuccess rows) /\
      truth = in_rows_truth env select_items rows.
Proof.
  intros env select_items subquery truth; split.
  - intro Heval; inversion Heval; subst.
    exists rows; repeat split; try assumption; reflexivity.
  - intros [rows [Harguments [Hsubquery ->]]].
    eapply EFormula_InSuccess; eassumption.
Qed.

Lemma eval_formula_in_empty :
  forall env select_items subquery,
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error env)
      select_items = None ->
    eval_query env subquery (SqlSuccess []) ->
    eval_formula env (FExpr_In select_items subquery)
      (SqlSuccess (Bool.false (B T))).
Proof.
  intros env select_items subquery Harguments Hsubquery.
  apply eval_formula_in_success_iff.
  exists []; split; [exact Harguments|].
  split; [exact Hsubquery|].
  unfold in_rows_truth; rewrite query_canonical_rows_empty.
  reflexivity.
Qed.

Lemma eval_formula_exists_error_iff : forall env subquery error,
  eval_formula env (FExpr_Exists subquery) (SqlError error) <->
  eval_query env subquery (SqlError error).
Proof.
  intros env subquery error; split.
  - intro Heval; inversion Heval; assumption.
  - intro Hsubquery; now apply EFormula_ExistsError.
Qed.

Lemma eval_formula_exists_success_iff : forall env subquery truth,
  eval_formula env (FExpr_Exists subquery) (SqlSuccess truth) <->
  (truth = Bool.false (B T) /\ eval_query env subquery (SqlSuccess [])) \/
  (truth = Bool.true (B T) /\
   exists row rows, eval_query env subquery (SqlSuccess (row :: rows))).
Proof.
  intros env subquery truth; split.
  - intro Heval; inversion Heval; subst.
    + left; now split.
    + right; split; [reflexivity|].
      exists row, rows; assumption.
  - intros [[-> Hempty] | [-> [row [rows Hnonempty]]]].
    + now apply EFormula_ExistsSuccessEmpty.
    + eapply EFormula_ExistsSuccessNonempty; exact Hnonempty.
Qed.

(** Cross-environment congruence for EXISTS.  The child relation is kept
    exact because this constructor observes only the child's error category
    and whether its successful row list is empty. *)
Lemma eval_formula_exists_env_congr :
  forall left_env right_env subquery,
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    forall outcome,
      eval_formula left_env (FExpr_Exists subquery) outcome <->
      eval_formula right_env (FExpr_Exists subquery) outcome.
Proof.
  intros left_env right_env subquery Hquery [truth|error].
  - rewrite 2 eval_formula_exists_success_iff.
    split.
    + intros [[Htruth Hempty] | [Htruth [row [rows Hnonempty]]]].
      * left; split; [exact Htruth|].
        now apply (proj1 (Hquery (SqlSuccess []))).
      * right; split; [exact Htruth|].
        exists row, rows.
        now apply (proj1 (Hquery (SqlSuccess (row :: rows)))).
    + intros [[Htruth Hempty] | [Htruth [row [rows Hnonempty]]]].
      * left; split; [exact Htruth|].
        now apply (proj2 (Hquery (SqlSuccess []))).
      * right; split; [exact Htruth|].
        exists row, rows.
        now apply (proj2 (Hquery (SqlSuccess (row :: rows)))).
  - rewrite 2 eval_formula_exists_error_iff.
    apply Hquery.
Qed.

(** Constructor-level form of [eval_formula_exists_env_congr], suitable for
    structural congruence proofs over formula syntax. *)
Lemma formula_expr_exists_env_congr :
  forall left_env right_env subquery,
    query_expr_env_outcome_equiv left_env right_env subquery ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_Exists subquery).
Proof.
  intros left_env right_env subquery Hquery outcome.
  now apply eval_formula_exists_env_congr.
Qed.

(** A safe IN expression is stable across equivalent correlated
    environments when its subquery exposes exactly the same outcome relation.
    Safety is explicit on both sides: generic runtime-error callbacks are not
    assumed to respect [Env.equiv_env]. *)
Lemma eval_formula_in_env_congr_safe :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    (forall outcome,
      eval_query left_env subquery outcome <->
      eval_query right_env subquery outcome) ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    forall outcome,
      eval_formula left_env (FExpr_In select_items subquery) outcome <->
      eval_formula right_env (FExpr_In select_items subquery) outcome.
Proof.
  intros left_env right_env select_items subquery Henv Hquery
    Hleft_safe Hright_safe [truth|error].
  - rewrite 2 eval_formula_in_success_iff.
    split.
    + intros [rows [_ [Hrows Htruth]]].
      exists rows; split; [exact Hright_safe|].
      split.
      * now apply (proj1 (Hquery (SqlSuccess rows))).
      * rewrite <- (in_rows_truth_env_congr
          (left_env := left_env) (right_env := right_env)
          select_items rows Henv).
        exact Htruth.
    + intros [rows [_ [Hrows Htruth]]].
      exists rows; split; [exact Hleft_safe|].
      split.
      * now apply (proj2 (Hquery (SqlSuccess rows))).
      * rewrite (in_rows_truth_env_congr
          (left_env := left_env) (right_env := right_env)
          select_items rows Henv).
        exact Htruth.
  - rewrite 2 eval_formula_in_error_iff.
    split.
    + intros [Harguments | [_ Hsubquery]].
      * rewrite Hleft_safe in Harguments; discriminate.
      * right; split; [exact Hright_safe|].
        now apply (proj1 (Hquery (SqlError error))).
    + intros [Harguments | [_ Hsubquery]].
      * rewrite Hright_safe in Harguments; discriminate.
      * right; split; [exact Hleft_safe|].
        now apply (proj2 (Hquery (SqlError error))).
Qed.

(** Constructor-level form of [eval_formula_in_env_congr_safe]. *)
Lemma formula_expr_in_env_congr_safe :
  forall left_env right_env select_items subquery,
    Env.equiv_env T left_env right_env ->
    query_expr_env_outcome_equiv left_env right_env subquery ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error left_env)
      select_items = None ->
    first_runtime_error
      (@eval_select_runtime_error T
        symbol_runtime_error aggregate_runtime_error right_env)
      select_items = None ->
    formula_expr_env_outcome_equiv left_env right_env
      (FExpr_In select_items subquery).
Proof.
  intros left_env right_env select_items subquery Henv Hquery
    Hleft_safe Hright_safe outcome.
  now apply eval_formula_in_env_congr_safe.
Qed.

Lemma eval_formula_exists_false_iff : forall env subquery,
  eval_formula env (FExpr_Exists subquery)
    (SqlSuccess (Bool.false (B T))) <->
  eval_query env subquery (SqlSuccess []).
Proof.
  intros env subquery; split.
  - intro Heval.
    apply eval_formula_exists_success_iff in Heval.
    destruct Heval as [[_ Hempty] | [Hequal _]]; [exact Hempty|].
    exfalso; apply (Bool.true_diff_false (B T)).
    symmetry; exact Hequal.
  - intro Hempty; now apply EFormula_ExistsSuccessEmpty.
Qed.

Lemma eval_formula_exists_true_iff : forall env subquery,
  eval_formula env (FExpr_Exists subquery)
    (SqlSuccess (Bool.true (B T))) <->
  exists row rows, eval_query env subquery (SqlSuccess (row :: rows)).
Proof.
  intros env subquery; split.
  - intro Heval.
    apply eval_formula_exists_success_iff in Heval.
    destruct Heval as [[Hequal _] | [_ Hnonempty]]; [|exact Hnonempty].
    exfalso; apply (Bool.true_diff_false (B T)).
    exact Hequal.
  - intros [row [rows Hnonempty]].
    eapply EFormula_ExistsSuccessNonempty; exact Hnonempty.
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

(** EXISTS depends only on whether a successful child observation is empty.
    Successful observations may otherwise differ, but they must all agree on
    emptiness at this fixed (possibly correlated) environment.  Inhabitation
    and no-error are explicit so the exact formula contract is not vacuous. *)
Theorem formula_exists_acceptance_exact :
  forall env subquery empty,
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      rows_empty_decision rows = empty) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_acceptance_exact_at
      basesort instance unknown symbol_runtime_error
      aggregate_runtime_error value_is_null env
      (FExpr_Exists subquery) (Datatypes.negb empty).
Proof.
  intros env subquery empty [rows Hrows] Hemptiness Herror.
  unfold formula_acceptance_exact_at.
  split.
  - pose proof (Hemptiness rows Hrows) as Hempty.
    destruct rows as [|row rows].
    + exists (Bool.false (B T)); split.
      * now apply EFormula_ExistsSuccessEmpty.
      * cbn [rows_empty_decision] in Hempty; subst empty.
        cbn [Datatypes.negb]; apply false_is_not_true.
    + exists (Bool.true (B T)); split.
      * eapply EFormula_ExistsSuccessNonempty; exact Hrows.
      * cbn [rows_empty_decision] in Hempty; subst empty.
        cbn [Datatypes.negb]; apply Bool.true_is_true_alt.
  - split.
    + intros truth Heval.
      apply eval_formula_exists_success_iff in Heval.
      destruct Heval as
        [[-> Hempty_rows] | [-> [row [tail Hnonempty_rows]]]].
      * pose proof (Hemptiness [] Hempty_rows) as Hempty.
        cbn [rows_empty_decision] in Hempty; subst empty.
        cbn [Datatypes.negb]; apply false_is_not_true.
      * pose proof (Hemptiness (row :: tail) Hnonempty_rows) as Hempty.
        cbn [rows_empty_decision] in Hempty; subst empty.
        cbn [Datatypes.negb]; apply Bool.true_is_true_alt.
    + intros error Heval.
      apply eval_formula_exists_error_iff in Heval.
      now apply (Herror error).
Qed.

(** Fixed-environment congruence is the useful correlated-query interface:
    [env] may already be extended with an outer row. *)

Lemma eval_formula_quant_subquery_congr :
  forall env which_quantifier which_predicate arguments left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env
        (FExpr_Quant which_quantifier which_predicate arguments left) outcome <->
      eval_formula env
        (FExpr_Quant which_quantifier which_predicate arguments right) outcome.
Proof.
  intros env which_quantifier which_predicate arguments left right
    Houtputs Hequiv outcome; split; intro Heval; inversion Heval; subst.
  - now apply EFormula_QuantArgumentsError.
  - eapply EFormula_QuantSubqueryError; [eassumption|].
    now apply (proj1 (Hequiv (SqlError error))).
  - rewrite Houtputs.
    eapply EFormula_QuantSuccess; [eassumption|].
    now apply (proj1 (Hequiv (SqlSuccess rows))).
  - now apply EFormula_QuantArgumentsError.
  - eapply EFormula_QuantSubqueryError; [eassumption|].
    now apply (proj2 (Hequiv (SqlError error))).
  - rewrite <- Houtputs.
    eapply EFormula_QuantSuccess; [eassumption|].
    now apply (proj2 (Hequiv (SqlSuccess rows))).
Qed.

Lemma eval_formula_in_subquery_congr :
  forall env select_items left right,
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env (FExpr_In select_items left) outcome <->
      eval_formula env (FExpr_In select_items right) outcome.
Proof.
  intros env select_items left right Hequiv outcome; split; intro Heval;
    inversion Heval; subst.
  - now apply EFormula_InArgumentsError.
  - eapply EFormula_InSubqueryError; [eassumption|].
    now apply (proj1 (Hequiv (SqlError error))).
  - eapply EFormula_InSuccess; [eassumption|].
    now apply (proj1 (Hequiv (SqlSuccess rows))).
  - now apply EFormula_InArgumentsError.
  - eapply EFormula_InSubqueryError; [eassumption|].
    now apply (proj2 (Hequiv (SqlError error))).
  - eapply EFormula_InSuccess; [eassumption|].
    now apply (proj2 (Hequiv (SqlSuccess rows))).
Qed.

Lemma eval_formula_exists_subquery_congr :
  forall env left right,
    (forall outcome,
      eval_query env left outcome <-> eval_query env right outcome) ->
    forall outcome,
      eval_formula env (FExpr_Exists left) outcome <->
      eval_formula env (FExpr_Exists right) outcome.
Proof.
  intros env left right Hequiv outcome; split; intro Heval;
    inversion Heval; subst.
  - apply EFormula_ExistsError.
    now apply (proj1 (Hequiv (SqlError error))).
  - apply EFormula_ExistsSuccessEmpty.
    now apply (proj1 (Hequiv (SqlSuccess []))).
  - eapply EFormula_ExistsSuccessNonempty.
    now apply (proj1 (Hequiv (SqlSuccess (row :: rows)))).
  - apply EFormula_ExistsError.
    now apply (proj2 (Hequiv (SqlError error))).
  - apply EFormula_ExistsSuccessEmpty.
    now apply (proj2 (Hequiv (SqlSuccess []))).
  - eapply EFormula_ExistsSuccessNonempty.
    now apply (proj2 (Hequiv (SqlSuccess (row :: rows)))).
Qed.

Lemma formula_expr_quant_admissible_iff :
  forall which_quantifier which_predicate arguments subquery,
    @formula_expr_admissible T relname basesort
      (FExpr_Quant which_quantifier which_predicate arguments subquery) <->
    @query_expr_admissible T relname basesort subquery /\
    length arguments = 1%nat /\
    length (query_expr_outputs subquery) = 1%nat /\
    (length arguments + length (query_expr_outputs subquery))%nat =
      predicate_arity T which_predicate.
Proof.
  intros; reflexivity.
Qed.

Lemma formula_expr_in_admissible_iff : forall select_items subquery,
  @formula_expr_admissible T relname basesort
    (FExpr_In select_items subquery) <->
  @query_expr_admissible T relname basesort subquery /\
  select_list_sort (_Select_List select_items) =S= query_expr_sort subquery /\
  query_in_positionally_aligned (_Select_List select_items)
    (query_expr_outputs subquery).
Proof.
  intros; reflexivity.
Qed.

Lemma formula_expr_exists_admissible_iff : forall subquery,
  @formula_expr_admissible T relname basesort (FExpr_Exists subquery) <->
  @query_expr_admissible T relname basesort subquery.
Proof.
  intros; reflexivity.
Qed.

Lemma eval_formula_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context left) outcome <->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  apply (@formula_expr_context_global_congr T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    context left right Hequiv (env_t T outer_env outer_row) outcome).
Qed.

Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  exact (proj2 (@query_expr_context_global_congr T relname basesort instance
    unknown symbol_runtime_error aggregate_runtime_error
    value_is_null context left right Hequiv)
    (env_t T outer_env outer_row) outcome).
Qed.

End PredicateSubquerySemantics.
