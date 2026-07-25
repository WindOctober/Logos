From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula OrderedSet
  SqlBagAbstraction SqlErrorSemantics SqlOutcome SqlQuerySemantics
  SqlQueryFacts SqlQuerySyntax.
From Logos.FormalSQL Require Import
  GroupingRewriteFacts GroupedFilterOutcomeFacts RelationalAlgebraFacts
  OrderedQueryFacts SubqueryFacts.
From Stdlib Require Import Bool List NArith.

Import ListNotations.
Import Tuple.

(** Lock the two-valued acceptance operation used only at filter/HAVING
    boundaries.  These equations do not equate SQL FALSE with UNKNOWN. *)
Example acceptance_interp_conj_truth_table :
  acceptance_interp_conj And_F true true = true /\
  acceptance_interp_conj And_F true false = false /\
  acceptance_interp_conj And_F false true = false /\
  acceptance_interp_conj And_F false false = false /\
  acceptance_interp_conj Or_F true true = true /\
  acceptance_interp_conj Or_F true false = true /\
  acceptance_interp_conj Or_F false true = true /\
  acceptance_interp_conj Or_F false false = false.
Proof. repeat split; reflexivity. Qed.

Example rows_empty_decision_regression :
  @rows_empty_decision nat [] = true /\
  rows_empty_decision [0%nat] = false.
Proof. split; reflexivity. Qed.

Section ExactFormulaAndGroupInterfaces.

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

Local Abbreviation formula_exact :=
  (@formula_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** One public theorem covers both eager connectives.  The same right exactness
    premise is retained for AND and OR, matching FormalSQL evaluation order. *)
Theorem eager_formula_conj_acceptance_regression :
  forall env left right left_accepted right_accepted,
    formula_exact env left left_accepted ->
    formula_exact env right right_accepted ->
    formula_exact env (FExpr_Conj And_F left right)
      (Datatypes.andb left_accepted right_accepted) /\
    formula_exact env (FExpr_Conj Or_F left right)
      (Datatypes.orb left_accepted right_accepted).
Proof.
  intros env left right left_accepted right_accepted Hleft Hright.
  split.
  - change (formula_exact env (FExpr_Conj And_F left right)
      (acceptance_interp_conj And_F left_accepted right_accepted)).
    now apply formula_conj_acceptance_exact.
  - change (formula_exact env (FExpr_Conj Or_F left right)
      (acceptance_interp_conj Or_F left_accepted right_accepted)).
    now apply formula_conj_acceptance_exact.
Qed.

(** Successful subquery observations need only agree on emptiness; row lists
    may otherwise differ.  Inhabitation and error exclusion remain separate. *)
Theorem exists_acceptance_exact_regression :
  forall env subquery empty,
    (exists rows, eval_query env subquery (SqlSuccess rows)) ->
    (forall rows,
      eval_query env subquery (SqlSuccess rows) ->
      rows_empty_decision rows = empty) ->
    (forall error, ~ eval_query env subquery (SqlError error)) ->
    formula_exact env (FExpr_Exists subquery) (Datatypes.negb empty).
Proof.
  intros env subquery empty Hsuccess Hempty Herror.
  eapply formula_exists_acceptance_exact; eassumption.
Qed.

Local Definition regression_group_env
    (env : Env.env T) (group_terms : list (@aggterm T))
    (group : list (tuple T)) : Env.env T :=
  env_g T env (@Group_By T group_terms) group.

(** Exercise the complete accepted-group interface with its four distinct
    runtime/exactness premises and literal ordered projection map. *)
Theorem accepted_groups_exact_regression :
  forall env select_list group_terms having groups,
    (forall group,
      In group groups ->
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) select_list = None /\
      @eval_formula_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) having = None /\
      formula_exact
        (regression_group_env env group_terms group) having true /\
      @eval_select_list_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) select_list = None) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess
        (map (group_projection env select_list group_terms) groups).
Proof.
  intros env select_list group_terms having groups Hsafe outcome.
  apply eval_groups_true_outcome_exact.
  intros group Hin.
  exact (Hsafe group Hin).
Qed.

(** Exercise the arbitrary-acceptance interface: rejected groups do not need
    scalar SELECT safety, while retained group order and duplicates are exact. *)
Theorem filtered_groups_exact_regression :
  forall env select_list group_terms having groups keep,
    (forall group,
      In group groups ->
      @eval_select_list_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) select_list = None /\
      @eval_formula_expr_aggregate_runtime_error T relname
        symbol_runtime_error aggregate_runtime_error
        (regression_group_env env group_terms group) having = None /\
      formula_exact
        (regression_group_env env group_terms group) having (keep group) /\
      (keep group = true ->
        @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (regression_group_env env group_terms group) select_list = None)) ->
    forall outcome,
      eval_groups env select_list group_terms having groups outcome <->
      outcome = SqlSuccess
        (map (group_projection env select_list group_terms)
          (filter keep groups)).
Proof.
  intros env select_list group_terms having groups keep Hsafe outcome.
  apply eval_groups_acceptance_outcome_exact.
  intros group Hin.
  exact (Hsafe group Hin).
Qed.

(** Exercise the reset boundary without selecting a privileged input-bag
    representative or requiring literal equality of the emitted row lists. *)
Theorem exact_group_bag_reset_regression :
  forall env select_list group_terms left_having right_having
      (left_bag right_bag :
        Febag.bag (Fecol.CBag (Tuple.CTuple T)))
      (left_rows right_rows :
        list (list (tuple T)) -> list (tuple T)),
    (forall representative,
      query_same_rows_as_bag representative left_bag ->
      let canonical := query_canonical_rows representative in
      let groups := query_make_groups env canonical group_terms in
      @group_keys_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        env group_terms canonical = None /\
      forall outcome,
        eval_groups env select_list group_terms left_having groups outcome <->
        outcome = SqlSuccess (left_rows groups)) ->
    (forall representative,
      query_same_rows_as_bag representative right_bag ->
      let canonical := query_canonical_rows representative in
      let groups := query_make_groups env canonical group_terms in
      @group_keys_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        env group_terms canonical = None /\
      forall outcome,
        eval_groups env select_list group_terms right_having groups outcome <->
        outcome = SqlSuccess (right_rows groups)) ->
    (forall left_representative right_representative,
      query_same_rows_as_bag left_representative left_bag ->
      query_same_rows_as_bag right_representative right_bag ->
      Oeset.permut (OTuple T)
        (left_rows
          (query_make_groups env
            (query_canonical_rows left_representative) group_terms))
        (right_rows
          (query_make_groups env
            (query_canonical_rows right_representative) group_terms))) ->
    forall outcome,
      eval_group_bag env select_list group_terms left_having left_bag outcome <->
      eval_group_bag env select_list group_terms right_having right_bag outcome.
Proof.
  intros env select_list group_terms left_having right_having
    left_bag right_bag left_rows right_rows
    Hleft Hright Hpermut outcome.
  eapply eval_group_bag_exact_rows_permut_equiv; eassumption.
Qed.

(** The exact output expression retains two equal group occurrences. *)
Example accepted_group_projection_keeps_occurrences :
  forall (env : Env.env T) (select_list : _select_list T)
      (group_terms : list (@aggterm T)) (group : list (tuple T)),
    map (group_projection env select_list group_terms) [group; group] =
    [group_projection env select_list group_terms group;
     group_projection env select_list group_terms group].
Proof. reflexivity. Qed.

End ExactFormulaAndGroupInterfaces.

Section ExactQueryFilterInterfaces.

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

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation success_bags :=
  (@query_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation formula_exact :=
  (@formula_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** Lock the multiplicity-preserving query-level bridge independently of any
    concrete schema or expression syntax. *)
Theorem exact_query_filter_success_bags_regression :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      formula_exact (env_t T env row) formula (keep row)) ->
    rel_equiv
      (success_bags env (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          success_bags env input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
Proof.
intros env formula input keep Hproper Hexact.
now apply query_filter_success_bags_exact.
Qed.

(** The local exactness premise is restricted to rows reached through a
    successful child observation; no global formula-safety assumption is
    hidden in the error theorem. *)
Theorem exact_query_filter_error_regression :
  forall env formula input (keep : tuple T -> bool),
    (forall input_rows row,
      eval_query env input (SqlSuccess input_rows) ->
      In row input_rows ->
      formula_exact (env_t T env row) formula (keep row)) ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros env formula input keep Hexact error.
exact
  (@query_filter_error_iff_exact T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    env formula input keep Hexact error).
Qed.

End ExactQueryFilterInterfaces.

Section CanonicalFilterRepresentativeInterfaces.

Context {T : Tuple.Rcd}.

(** Canonicalization preserves the cardinality of any two legal
    representatives of the same bag. *)
Theorem canonical_same_bag_length_regression :
  forall first second bag,
    @query_same_rows_as_bag T first bag ->
    @query_same_rows_as_bag T second bag ->
    List.length (@query_canonical_rows T first) =
    List.length (@query_canonical_rows T second).
Proof.
intros first second bag Hfirst Hsecond.
exact
  (@query_canonical_rows_length_between T first second bag Hfirst Hsecond).
Qed.

(** Filtering before or after choosing canonical representatives preserves
    every semantic row occurrence and can vary only by permutation. *)
Theorem canonical_filter_permutation_regression :
  forall (keep : tuple T -> bool) left right original,
    (forall first second,
      Oeset.compare (OTuple T) first second = Eq ->
      keep first = keep second) ->
    @query_same_rows_as_bag T left (rows_bag T original) ->
    @query_same_rows_as_bag T right
      (rows_bag T (List.filter keep original)) ->
    Oeset.permut (OTuple T)
      (List.filter keep (@query_canonical_rows T left))
      (@query_canonical_rows T right).
Proof.
intros keep left right original Hproper Hleft Hright.
exact
  (@query_canonical_rows_filter_permut T keep left right original
    Hproper Hleft Hright).
Qed.

End CanonicalFilterRepresentativeInterfaces.

Section SupportAwareBagFilterInterface.

Context {T : Tuple.Rcd}.

(** Predicates need agree only on represented tuple support, and the inputs
    themselves may be merely finite-bag equal. *)
Theorem support_filter_congruence_regression :
  forall (left_keep right_keep : tuple T -> bool)
      (left right : SqlBagAbstraction.bagT T),
    bag_eq T left right ->
    (forall left_row right_row,
      (Febag.nb_occ (Fecol.CBag (CTuple T)) left_row left >= 1)%N ->
      Oeset.compare (OTuple T) left_row right_row = Eq ->
      left_keep left_row = right_keep right_row) ->
    bag_eq T
      (Febag.filter (Fecol.CBag (CTuple T)) left_keep left)
      (Febag.filter (Fecol.CBag (CTuple T)) right_keep right).
Proof.
  intros left_keep right_keep left right Hequal Hkeep.
  now apply bag_filter_congr_on_support.
Qed.

End SupportAwareBagFilterInterface.

Section ConstantKeyConstructionInterface.

Context {T : Tuple.Rcd}.

(** Nonempty grouping terms are explicit, and member order is exactly reversed
    by the underlying partition accumulator. *)
Theorem constant_nonempty_key_groups_regression :
  forall (env : Env.env T) rows group_terms (key : list (value T)),
    group_terms <> nil ->
    (forall row,
      In row rows ->
      query_grouping_key env group_terms row = key) ->
    @query_make_groups T env rows group_terms =
      match rows with
      | nil => nil
      | _ :: _ => rev rows :: nil
      end.
Proof.
  intros env rows group_terms key Hterms Hconstant.
  eapply query_make_groups_constant_nonempty_key with (key := key);
    eassumption.
Qed.

End ConstantKeyConstructionInterface.

Section GroupSupportRelationsRegression.

Context {T : Tuple.Rcd}.

(** Every input occurrence belongs to some ordinary nonempty-key group, and
    every selected group member comes from the input. *)
Theorem nonempty_query_group_support_exact_regression :
  forall (env : Env.env T) rows group_terms row,
    group_terms <> nil ->
    In row rows <->
    exists group,
      In group (@query_make_groups T env rows group_terms) /\
      In row group.
Proof.
  intros env rows group_terms row Hterms.
  now apply query_make_groups_support_exact.
Qed.

(** Group representatives may expose a different schema; only the supplied
    row-to-emission relation is required. *)
Theorem nonempty_query_group_support_relation_regression :
  forall (R : tuple T -> tuple T -> Prop) env rows group_terms
      (emit : list (tuple T) -> tuple T),
    group_terms <> nil ->
    (forall group row,
      In group (@query_make_groups T env rows group_terms) ->
      In row group ->
      R row (emit group)) ->
    list_support_rel R rows
      (map emit (@query_make_groups T env rows group_terms)).
Proof.
  intros R env rows group_terms emit Hterms Hemit.
  now apply query_make_groups_support_rel.
Qed.

Print Assumptions query_make_groups_support_exact.
Print Assumptions query_make_groups_support_rel.
Print Assumptions nonempty_query_group_support_relation_regression.

End GroupSupportRelationsRegression.

Section GroupPermutationInterfaces.

Context {T : Tuple.Rcd}.

(** Input bag equivalence is sufficient for ordinary nonempty grouping, even
    though both group discovery and group-member list order may differ. *)
Theorem nonempty_query_group_permutation_regression :
  forall (env : Env.env T) group_terms left right,
    group_terms <> nil ->
    Oeset.permut (OTuple T) left right ->
    Oeset.permut (OLTuple T)
      (@query_make_groups T env left group_terms)
      (@query_make_groups T env right group_terms).
Proof.
  intros env group_terms left right Hterms Hrows.
  now apply query_make_groups_permut_nonempty.
Qed.

(** A HAVING predicate and its group projection transport together across the
    semantic group permutation exposed by the preceding interface. *)
Theorem filtered_group_projection_permutation_regression :
  forall left right
      (keep : list (tuple T) -> bool)
      (emit : list (tuple T) -> tuple T),
    (forall first second,
      Oeset.compare (OLTuple T) first second = Eq ->
      keep first = keep second) ->
    (forall first second,
      Oeset.compare (OLTuple T) first second = Eq ->
      Oeset.compare (OTuple T) (emit first) (emit second) = Eq) ->
    Oeset.permut (OLTuple T) left right ->
    Oeset.permut (OTuple T)
      (map emit (filter keep left))
      (map emit (filter keep right)).
Proof.
  intros left right keep emit Hkeep Hemit Hgroups.
  now apply group_filter_map_permutation.
Qed.

End GroupPermutationInterfaces.
