(******************************************************************************)
(** Generic lookup, correlation, and self-membership composition interfaces. **)
(******************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List SetoidList.
From SQLFS Require Import
  ATerms Bool3 Env FiniteBag FiniteCollection FiniteSet Formula FTuples
  GenericInstance Interp OrderedSet Projection SchemaConstraints
  SqlErrorSemantics SqlOutcome SqlQuerySemantics SqlQuerySyntax Values.
From Logos.FormalSQL Require Import
  CardinalityCombinators GroupedFilterOutcomeFacts IntegrityFacts
  RelationalAlgebraFacts SubqueryFacts TNullSyntax.

Import ListNotations.
Import Tuple.

(** An attribute absent from the current row is looked up in the retained
    outer environment.  This is the capture-sensitive counterpart of
    [interp_direct_attribute_in_env_t]; the absence premise must not be
    dropped because a present current-row attribute shadows the outer one. *)
Lemma interp_direct_attribute_in_env_t_absent :
  forall (T : Tuple.Rcd) env row attribute,
    (attribute inS? labels T row) = false ->
    interp_aggterm T (env_t T env row)
      (@A_Expr T (@F_Dot T attribute)) =
    interp_aggterm T env (@A_Expr T (@F_Dot T attribute)).
Proof.
intros T env row attribute Habsent.
rewrite interp_aggterm_unfold, interp_funterm_unfold, interp_dot_unfold.
unfold env_t; rewrite ListSort.quicksort_1, Habsent; reflexivity.
Qed.

(** A reached outer semantic match entails the corresponding inner guard
    after two explicit environment-extension lookups.  The current inner row
    supplies [inner_attribute], while [outer_attribute] must fall through to
    the retained outer row.  Symmetry is explicit because this theorem does
    not assume that an arbitrary SQL-facing relation is symmetric. *)
Theorem correlated_inner_guard_relation_of_outer_match :
  forall (T : Tuple.Rcd) (relation : value T -> value T -> Prop)
      base_env outer_row inner_row outer_attribute inner_attribute,
    (forall left right, relation left right -> relation right left) ->
    relation
      (dot T outer_row outer_attribute)
      (dot T inner_row inner_attribute) ->
    inner_attribute inS labels T inner_row ->
    (outer_attribute inS? labels T inner_row) = false ->
    outer_attribute inS labels T outer_row ->
    relation
      (interp_aggterm T
        (env_t T (env_t T base_env outer_row) inner_row)
        (@A_Expr T (@F_Dot T inner_attribute)))
      (interp_aggterm T
        (env_t T (env_t T base_env outer_row) inner_row)
        (@A_Expr T (@F_Dot T outer_attribute))).
Proof.
intros T relation base_env outer_row inner_row outer_attribute
  inner_attribute Hsym Hmatch Hinner Houter_absent Houter.
rewrite (@interp_direct_attribute_in_env_t
  T (env_t T base_env outer_row) inner_row inner_attribute Hinner).
rewrite (@interp_direct_attribute_in_env_t_absent
  T (env_t T base_env outer_row) inner_row outer_attribute Houter_absent).
rewrite (@interp_direct_attribute_in_env_t
  T base_env outer_row outer_attribute Houter).
now apply Hsym.
Qed.

(** Two represented occurrences related in both directions by a [NoDupA]
    relation are the same occurrence value.  Both directions are premises:
    SQL equality-like relations are not silently assumed symmetric or
    reflexive, especially in the presence of NULL. *)
Lemma NoDupA_bidirectionally_related_members_eq :
  forall (A : Type) (relation : A -> A -> Prop) values left right,
    NoDupA relation values ->
    In left values ->
    In right values ->
    relation left right ->
    relation right left ->
    left = right.
Proof.
intros A relation values.
induction values as [|first rest IH]; intros left right Hnodup Hleft Hright
  Hforward Hbackward; [contradiction|].
inversion Hnodup as [|? ? Hfirst Hrest]; subst.
destruct Hleft as [Hleft | Hleft]; destruct Hright as [Hright | Hright].
- now subst.
- subst left; exfalso; apply Hfirst.
  apply InA_alt; exists right; now split.
- subst right; exfalso; apply Hfirst.
  apply InA_alt; exists left; now split.
- eapply IH; eassumption.
Qed.

(** Semantic key uniqueness reduces a filtered self-membership decision to
    the filter decision of the represented outer row.  [matches outer] is an
    actual semantic self-witness; no reflexivity of [key_relation] is assumed.
    A TRUE match must reflect the declared key relation, and the reverse
    relation is required explicitly before [NoDupA] can identify occurrences. *)
Theorem key_unique_self_filter_existsb_exact :
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
assert (Hrows : NoDupA
  (fun left right => key_relation (key_of left) (key_of right)) rows).
{ now apply NoDupA_map_preimage. }
destruct (keep outer) eqn:Hkeep.
- apply (proj2 (existsb_exists _ _)).
  exists outer; split; [apply filter_In; now split|exact Hself].
- destruct (existsb matches (filter keep rows)) eqn:Hexists;
    [|reflexivity].
  exfalso.
  apply (proj1 (existsb_exists _ _)) in Hexists.
  destruct Hexists as [candidate [Hcandidate Hmatches]].
  apply filter_In in Hcandidate as [Hcandidate Hcandidate_keep].
  assert (Hforward : key_relation (key_of outer) (key_of candidate)).
  { now apply Hreflect. }
  assert (Hbackward : key_relation (key_of candidate) (key_of outer)).
  { now apply Hreverse. }
  pose proof
    (@NoDupA_bidirectionally_related_members_eq
      Row (fun left right => key_relation (key_of left) (key_of right))
      rows outer candidate Hrows Houter Hcandidate Hforward Hbackward)
    as Hequal.
  subst candidate; congruence.
Qed.

(** Primary-key conformance instantiates the generic key interface and also
    exposes the complete NOT NULL fact needed to justify SQL self-equality.
    The actual self-witness remains explicit because NOT NULL alone does not
    establish type- or collation-specific equality semantics. *)
Theorem primary_key_self_filter_existsb_exact :
  forall key rows (keep matches : tuple TNull -> bool) outer,
    primary_key_conforms key rows ->
    In outer rows ->
    matches outer = true ->
    (forall candidate,
      In candidate rows ->
      matches candidate = true ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate) ->
      sql_key_equal_true
        (SchemaConstraints.project_row key candidate)
        (SchemaConstraints.project_row key outer)) ->
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (SchemaConstraints.project_row key outer) /\
    existsb matches (filter keep rows) = keep outer.
Proof.
intros key rows keep matches outer Hprimary Houter Hself Hreflect Hreverse.
split.
- now apply primary_key_projection_not_null with (rows := rows).
- eapply key_unique_self_filter_existsb_exact
    with (key_relation := sql_key_equal_true)
      (key_of := SchemaConstraints.project_row key); try eassumption.
  exact (proj2 (proj2 Hprimary)).
Qed.

Local Lemma existsb_map_exact :
  forall (A B : Type) (predicate : B -> bool) (mapping : A -> B) rows,
    existsb predicate (map mapping rows) =
    existsb (fun row => predicate (mapping row)) rows.
Proof.
intros A B predicate mapping rows.
induction rows as [|row rest IH]; [reflexivity|].
cbn; now rewrite IH.
Qed.

(** Exact filter acceptance for primary-key self-[IN].  Candidate projection
    and the evaluator environment are arbitrary, so aliases, nested direct
    projections, and distinct outer/candidate environments are handled by the
    semantic self-witness and match-reflection premises instead of a fixed
    scalar type or projection topology.  Duplicate occurrences are ruled out
    only through declared primary-key semantics. *)
Theorem tnull_primary_key_self_in_rows_acceptance_exact :
  forall {relname : Type} key rows (keep : tuple TNull -> bool) outer
      (values : list (value TNull)) (subquery : query_expr TNull relname)
      (project_candidate : tuple TNull -> tuple TNull),
    primary_key_conforms key rows ->
    In outer rows ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery))
      (map project_candidate (filter keep rows)) ->
    Bool.is_true Bool3
      (@in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery (project_candidate outer)) = true ->
    (forall candidate,
      In candidate rows ->
      Bool.is_true Bool3
        (@in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery (project_candidate candidate)) = true ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate) ->
      sql_key_equal_true
        (SchemaConstraints.project_row key candidate)
        (SchemaConstraints.project_row key outer)) ->
    Bool.is_true Bool3
      (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery
        (map project_candidate (filter keep rows))) = keep outer /\
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (SchemaConstraints.project_row key outer).
Proof.
intros relname key rows keep outer values subquery project_candidate Hprimary
  Houter Houtputs Hself Hreflect Hreverse.
pose proof
  (@in_rows_acceptance_existsb TNull relname
    unknown3 NullValues.is_null_value values subquery
    (map project_candidate (filter keep rows))
    (fun candidate =>
      Bool.is_true Bool3
        (@in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery candidate))
    Houtputs
    (fun candidate => eq_refl)) as Hacceptance.
change
  (Bool.is_true Bool3
    (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
      values subquery (map project_candidate (filter keep rows))) =
   existsb
    (fun candidate =>
      Bool.is_true Bool3
        (@in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery candidate))
    (map project_candidate (filter keep rows))) in Hacceptance.
pose proof
  (@primary_key_self_filter_existsb_exact
    key rows keep
    (fun candidate =>
      Bool.is_true Bool3
        (@in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery (project_candidate candidate)))
    outer
    Hprimary Houter Hself Hreflect Hreverse) as [Hnonnull Hexact].
split.
- rewrite Hacceptance, existsb_map_exact.
  exact Hexact.
- exact Hnonnull.
Qed.

(** Reached-row form of the preceding theorem. *)
Corollary tnull_primary_key_self_in_rows_true :
  forall {relname : Type} key rows (keep : tuple TNull -> bool) outer
      (values : list (value TNull)) (subquery : query_expr TNull relname)
      (project_candidate : tuple TNull -> tuple TNull),
    primary_key_conforms key rows ->
    In outer rows ->
    keep outer = true ->
    Forall
      (query_row_has_outputs (query_expr_outputs subquery))
      (map project_candidate (filter keep rows)) ->
    Bool.is_true Bool3
      (@in_row_truth TNull relname unknown3 NullValues.is_null_value
        values subquery (project_candidate outer)) = true ->
    (forall candidate,
      In candidate rows ->
      Bool.is_true Bool3
        (@in_row_truth TNull relname unknown3 NullValues.is_null_value
          values subquery (project_candidate candidate)) = true ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate)) ->
    (forall candidate,
      In candidate rows ->
      sql_key_equal_true
        (SchemaConstraints.project_row key outer)
        (SchemaConstraints.project_row key candidate) ->
      sql_key_equal_true
        (SchemaConstraints.project_row key candidate)
        (SchemaConstraints.project_row key outer)) ->
    Bool.is_true Bool3
      (@in_rows_truth TNull relname unknown3 NullValues.is_null_value
        values subquery
        (map project_candidate (filter keep rows))) = true /\
    Forall
      (fun cell => NullValues.is_null_value cell = false)
      (SchemaConstraints.project_row key outer).
Proof.
intros relname key rows keep outer values subquery project_candidate Hprimary
  Houter Hkeep Houtputs Hself Hreflect Hreverse.
pose proof
  (@tnull_primary_key_self_in_rows_acceptance_exact
    relname key rows keep outer values subquery project_candidate
    Hprimary Houter Houtputs Hself Hreflect Hreverse) as [Hexact Hnonnull].
now rewrite Hkeep in Hexact.
Qed.
