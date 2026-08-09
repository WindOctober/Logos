From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FlatData Formula OrderedSet
  SqlBagAbstraction SqlErrorSemantics SqlOutcome SqlQuerySemantics
  SqlQueryFacts SqlQuerySyntax.
From Logos.FormalSQL Require Import
  GroupingRewriteFacts GroupedFilterOutcomeFacts RelationalAlgebraFacts
  OrderedQueryFacts SubqueryFacts.
From Stdlib Require Import Bool List NArith String.

Import ListNotations.
Import Tuple.
Open Scope string_scope.

(** Lock the two-valued acceptance operation used only at filter/HAVING
    boundaries.  These equations do not equate SQL FALSE with UNKNOWN. *)
Example scalar_acceptance_combine_truth_table :
  scalar_acceptance_combine And_F true true = true /\
  scalar_acceptance_combine And_F true false = false /\
  scalar_acceptance_combine And_F false true = false /\
  scalar_acceptance_combine And_F false false = false /\
  scalar_acceptance_combine Or_F true true = true /\
  scalar_acceptance_combine Or_F true false = true /\
  scalar_acceptance_combine Or_F false true = true /\
  scalar_acceptance_combine Or_F false false = false.
Proof. repeat split; reflexivity. Qed.

Example rows_empty_decision_regression :
  @rows_empty_decision nat [] = true /\
  rows_empty_decision [0%nat] = false.
Proof. split; reflexivity. Qed.

Section ExactScalarAndGroupInterfaces.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation scalar_exact :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** Flattened Boolean operands retain exact TRUE/non-TRUE acceptance under
    every statement schedule.  The contract also excludes every scalar-local
    runtime error, including errors reached through subqueries or lazy CASE
    arms selected by an operand. *)
Theorem eager_scalar_conj_list_acceptance_regression :
  forall site_rows env expressions decide,
    (forall expression,
      In expression expressions ->
      scalar_exact env expression (decide expression)) ->
    scalar_exact env (SExpr_ConjList site_rows And_F expressions)
      (scalar_acceptance_fold And_F (map decide expressions)) /\
    scalar_exact env (SExpr_ConjList site_rows Or_F expressions)
      (scalar_acceptance_fold Or_F (map decide expressions)).
Proof.
  intros site_rows env expressions decide Hexact.
  split.
  - now apply scalar_expr_conj_list_acceptance_exact.
  - now apply scalar_expr_conj_list_acceptance_exact.
Qed.

(** Native existential observations need only agree on the two-valued result.
    Inhabitation and error exclusion remain separate. *)
Theorem exists_acceptance_exact_regression :
  forall env subquery empty,
    (exists truth, eval_exists env subquery (SqlSuccess truth)) ->
    (forall truth,
      eval_exists env subquery (SqlSuccess truth) ->
      truth = exists_truth_from_empty empty) ->
    (forall error, ~ eval_exists env subquery (SqlError error)) ->
    scalar_exact env (SExpr_Exists subquery) (Datatypes.negb empty).
Proof.
  intros env subquery empty Hsuccess Hempty Herror.
  eapply scalar_expr_exists_acceptance_exact; eassumption.
Qed.

(** Typed projection may be relational and schedule-dependent.  The global
    grouping shape nevertheless emits at most one ordered row, independently
    of the successful scalar values chosen for that row. *)
Theorem global_group_success_shape_regression :
  forall env select_list having rows output,
    eval_groups env select_list [] having
      (query_make_groups env rows []) (SqlSuccess output) ->
    (List.length output <= 1)%nat /\
    SetoidList.NoDupA (@eq (tuple T)) output.
Proof.
  intros env select_list having rows output Heval.
  split.
  - exact (eval_groups_global_success_length_le_one
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env select_list having rows output Heval).
  - exact (eval_groups_global_success_NoDupA
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule (@eq (tuple T)) env select_list having
      rows output Heval).
Qed.

(** Exercise the reset boundary without selecting a privileged input-bag
    representative or requiring literal equality of the emitted row lists. *)
Theorem exact_group_bag_reset_regression :
  forall env select_list group_keys group_terms left_having right_having
      (left_bag right_bag :
        Febag.bag (Fecol.CBag (Tuple.CTuple T)))
      (left_rows right_rows :
        list (list (tuple T)) -> list (tuple T)),
    scalar_group_key_terms group_keys = Some group_terms ->
    (forall representative,
      query_same_rows_as_bag representative left_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        eval_groups env select_list group_terms left_having groups outcome <->
        outcome = SqlSuccess (left_rows groups)) ->
    (forall representative,
      query_same_rows_as_bag representative right_bag ->
      let groups := query_make_groups env representative group_terms in
      @group_keys_runtime_error T
        symbol_runtime_error aggregate_runtime_error
        env group_terms representative = None /\
      forall outcome,
        eval_groups env select_list group_terms right_having groups outcome <->
        outcome = SqlSuccess (right_rows groups)) ->
    (forall left_representative right_representative,
      query_same_rows_as_bag left_representative left_bag ->
      query_same_rows_as_bag right_representative right_bag ->
      Oeset.permut (OTuple T)
        (left_rows
          (query_make_groups env left_representative group_terms))
        (right_rows
          (query_make_groups env right_representative group_terms))) ->
    forall outcome,
      eval_group_bag env select_list group_keys left_having left_bag outcome <->
      eval_group_bag env select_list group_keys right_having right_bag outcome.
Proof.
  intros env select_list group_keys group_terms left_having right_having
    left_bag right_bag left_rows right_rows
    Hgroup_keys Hleft Hright Hpermut outcome.
  eapply eval_group_bag_exact_rows_permut_equiv; eassumption.
Qed.

(** Exact ordered observations retain two equal group occurrences before the
    separately proved bag abstraction forgets their list positions. *)
Example accepted_group_projection_keeps_occurrences :
  forall (emit : list (tuple T) -> tuple T) group,
    map emit [group; group] = [emit group; emit group].
Proof. reflexivity. Qed.

End ExactScalarAndGroupInterfaces.

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
Variable boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation success_bags :=
  (@query_success_bags T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation scalar_exact :=
  (@scalar_expr_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** Lock the multiplicity-preserving query-level bridge independently of any
    concrete schema or expression syntax. *)
Theorem exact_query_filter_success_bags_regression :
  forall env formula input (keep : tuple T -> bool),
    (forall left right,
      Oeset.compare (OTuple T) left right = Eq ->
      keep left = keep right) ->
    (forall row,
      scalar_exact (env_t T env row) formula (keep row)) ->
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
      scalar_exact (env_t T env row) formula (keep row)) ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros env formula input keep Hexact error.
exact
  (@query_filter_error_iff_exact T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
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
