(** Reusable inversion and composition facts for predicate subqueries. *)

Set Implicit Arguments.

From Stdlib Require Import List.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula FTuples
  Projection SqlErrorSemantics SqlOutcome SqlQueryContexts SqlQuerySemantics SqlQuerySyntax
  SqlQueryWellFormed.
From Logos.FormalSQL Require Import ScalarPredicateFacts.

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

Section PredicateSubquerySemantics.

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

Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

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
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context left) outcome <->
    eval_formula (env_t T outer_env outer_row)
      (plug_formula_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  apply (@formula_expr_context_global_congr T relname basesort instance unknown
    contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
    context left right Hequiv (env_t T outer_env outer_row) outcome).
Qed.

Lemma eval_query_context_correlated_congr :
  forall context left right outer_env outer_row outcome,
    @query_expr_global_typed_outcome_equiv T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      left right ->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context left) outcome <->
    eval_query (env_t T outer_env outer_row)
      (plug_query_expr_context context right) outcome.
Proof.
  intros context left right outer_env outer_row outcome Hequiv.
  exact (proj2 (@query_expr_context_global_congr T relname basesort instance
    unknown contains_nulls symbol_runtime_error aggregate_runtime_error
    value_is_null context left right Hequiv)
    (env_t T outer_env outer_row) outcome).
Qed.

End PredicateSubquerySemantics.
