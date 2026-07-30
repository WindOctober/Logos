From Stdlib Require Import List SetoidList.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance Interp Projection SchemaConstraints SqlErrorSemantics SqlOutcome
  SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  CorrelatedMembershipFacts GroupedFilterOutcomeFacts SubqueryFacts
  TNullSyntax.

Import ListNotations.
Import Tuple.

(** The generic key theorem is usable without a SQL scalar-type
    specialization or a globally reflexive key relation. *)
Lemma key_unique_self_filter_route_regression :
  forall (Row Key : Type) (key_relation : Key -> Key -> Prop)
      (key_of : Row -> Key) rows (keep matches : Row -> bool) outer,
    NoDupA key_relation (map key_of rows) ->
    In outer rows ->
    matches outer = true ->
    (forall candidate,
      In candidate rows ->
      matches candidate = true ->
      key_relation (key_of outer) (key_of candidate)) ->
    (forall candidate,
      In candidate rows ->
      key_relation (key_of outer) (key_of candidate) ->
      key_relation (key_of candidate) (key_of outer)) ->
    existsb matches (filter keep rows) = keep outer.
Proof.
intros Row Key key_relation key_of rows keep matches outer Hkeys Houter
  Hself Hreflect Hreverse.
eapply key_unique_self_filter_existsb_exact; eassumption.
Qed.

(** Primary-key self-membership exposes both reached TRUE acceptance and the
    NOT NULL key boundary.  Candidate projection remains arbitrary. *)
Lemma primary_key_self_in_true_route_regression :
  forall key rows (keep : tuple TNull -> bool) outer env select_items
      (project_candidate : tuple TNull -> tuple TNull),
    primary_key_conforms key rows ->
    In outer rows ->
    keep outer = true ->
    Bool.is_true Bool3
      (@in_row_truth TNull unknown3 NullValues.is_null_value
        env select_items (project_candidate outer)) = true ->
    (forall candidate,
      In candidate rows ->
      Bool.is_true Bool3
        (@in_row_truth TNull unknown3 NullValues.is_null_value
          env select_items (project_candidate candidate)) = true ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (project_row key outer) (project_row key candidate) ->
      sql_key_equal_true
        (project_row key candidate) (project_row key outer)) ->
    Bool.is_true Bool3
      (@in_rows_truth TNull unknown3 NullValues.is_null_value
        env select_items
        (map project_candidate (filter keep rows))) = true /\
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (project_row key outer).
Proof.
intros key rows keep outer env select_items project_candidate Hprimary
  Houter Hkeep Hself Hreflect Hreverse.
eapply tnull_primary_key_self_in_rows_true; eassumption.
Qed.

Section CorrelatedGuardEagerRoute.

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

Local Abbreviation formula_exact :=
  (@formula_acceptance_exact_at T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** A reached semantic outer match supplies the inner correlated guard after
    shadow/fallback lookup.  Existing exact conjunction composition then
    retains eager right evaluation and excludes both left and right errors. *)
Lemma correlated_guard_eager_acceptance_route_regression :
  forall base_env outer_row inner_row outer_attribute inner_attribute
      (relation : value T -> value T -> Prop)
      reached_formula guard_formula reached_accepted guard_accepted,
    (forall left right, relation left right -> relation right left) ->
    inner_attribute inS labels T inner_row ->
    (outer_attribute inS? labels T inner_row) = false ->
    outer_attribute inS labels T outer_row ->
    (reached_accepted = true ->
      relation
        (dot T outer_row outer_attribute)
        (dot T inner_row inner_attribute)) ->
    (relation
      (interp_aggterm T
        (env_t T (env_t T base_env outer_row) inner_row)
        (@A_Expr T (@F_Dot T inner_attribute)))
      (interp_aggterm T
        (env_t T (env_t T base_env outer_row) inner_row)
        (@A_Expr T (@F_Dot T outer_attribute))) ->
      guard_accepted = true) ->
    formula_exact
      (env_t T (env_t T base_env outer_row) inner_row)
      reached_formula reached_accepted ->
    formula_exact
      (env_t T (env_t T base_env outer_row) inner_row)
      guard_formula guard_accepted ->
    formula_exact
      (env_t T (env_t T base_env outer_row) inner_row)
      (FExpr_Conj And_F reached_formula guard_formula) reached_accepted.
Proof.
intros base_env outer_row inner_row outer_attribute inner_attribute
  relation reached_formula guard_formula reached_accepted guard_accepted
  Hsym Hinner Houter_absent Houter Hmatch Hguard Hreached Hguard_exact.
eapply formula_and_redundant_right_acceptance_exact.
- exact Hreached.
- exact Hguard_exact.
- intro Hreached_true.
  apply Hguard.
  eapply correlated_inner_guard_relation_of_outer_match; try eassumption.
  now apply Hmatch.
Qed.

End CorrelatedGuardEagerRoute.

Print Assumptions interp_direct_attribute_in_env_t_absent.
Print Assumptions correlated_inner_guard_relation_of_outer_match.
Print Assumptions NoDupA_bidirectionally_related_members_eq.
Print Assumptions key_unique_self_filter_existsb_exact.
Print Assumptions primary_key_self_filter_existsb_exact.
Print Assumptions tnull_primary_key_self_in_rows_acceptance_exact.
Print Assumptions tnull_primary_key_self_in_rows_true.
