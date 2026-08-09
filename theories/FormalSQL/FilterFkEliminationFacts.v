(*****************************************************************************)
(** Safe filter movement and functional middle-row elimination.             **)
(*****************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Bool List Lia.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  ListFacts ListPermut OrderedSet SchemaConstraints SqlErrorSemantics
  SqlBagAbstraction SqlOutcome SqlQueryFacts SqlQuerySemantics SqlQuerySyntax
  SqlSyntax Values.
From Logos.FormalSQL Require Import
  GroupedFilterOutcomeFacts IntegrityFacts OrderedQueryFacts
  OuterJoinFilterFacts RelationalAlgebraFacts TNullSyntax.

Import ListNotations.
Import Tuple.

(*****************************************************************************)
(** Occurrence-exact filter movement.                                       **)
(*****************************************************************************)

Local Lemma list_filter_factor_exact :
  forall (A : Type) (source guard accept : A -> bool) rows,
    (forall row,
      source row = andb (guard row) (accept row)) ->
    filter source rows = filter accept (filter guard rows).
Proof.
intros A source guard accept rows Hfactor.
induction rows as [|row rows IH]; [reflexivity|].
cbn [filter].
rewrite Hfactor.
destruct (guard row) eqn:Hguard;
  destruct (accept row) eqn:Haccept;
  cbn [filter]; rewrite ?Hguard, ?Haccept; now rewrite IH.
Qed.

(** Factoring a pair predicate into a left guard, a right guard, and a
    residual join predicate preserves the exact output list.  In particular,
    duplicate occurrences are neither merged nor created.  The Boolean
    callbacks are mathematical total, stable decisions; a SQL use must
    separately prove that the corresponding formula observations implement
    these callbacks exactly and as a stable, non-volatile observation. *)
Theorem join_matched_rows_filter_inputs_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (source accept : A -> B -> bool)
      (left_guard : A -> bool) (right_guard : B -> bool) left right,
    (forall left_row right_row,
      source left_row right_row =
      andb (left_guard left_row)
        (andb (right_guard right_row) (accept left_row right_row))) ->
    join_matched_rows join source left right =
    join_matched_rows join accept
      (filter left_guard left) (filter right_guard right).
Proof.
intros A B C join source accept left_guard right_guard left right Hsource.
unfold join_matched_rows.
induction left as [|left_row left IH]; [reflexivity|].
cbn [flat_map filter].
destruct (left_guard left_row) eqn:Hguard.
- cbn.
  f_equal.
  + apply (f_equal (map (join left_row))).
    apply list_filter_factor_exact.
    intro right_row.
    rewrite Hsource, Hguard; reflexivity.
  + exact IH.
- cbn.
  assert (Hnone : filter (source left_row) right = nil).
  {
    clear IH.
    induction right as [|right_row right IHright]; [reflexivity|].
    cbn [filter].
    rewrite Hsource, Hguard; cbn.
    exact IHright.
  }
  rewrite Hnone; cbn.
  exact IH.
Qed.

Local Lemma filter_join_matched_rows_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) (keep : C -> bool) left right,
    filter keep (join_matched_rows join accept left right) =
    join_matched_rows join
      (fun left_row right_row =>
        andb (accept left_row right_row)
          (keep (join left_row right_row))) left right.
Proof.
intros A B C join accept keep left right.
unfold join_matched_rows.
induction left as [|left_row left IH]; [reflexivity|].
cbn [flat_map].
rewrite ListFacts.filter_app, ListFacts.filter_map, IH.
f_equal.
apply (f_equal (map (join left_row))).
rewrite ListFacts.filter_filter.
apply ListFacts.filter_eq.
intros right_row Hright.
apply andb_comm.
Qed.

(** A post-join filter may be distributed to both inputs only when its
    accepted-pair decision factors exactly as stated.  This theorem is an
    exact list law, not an outcome theorem: condition, projection, and filter
    errors remain separate obligations below. *)
Theorem inner_filter_to_input_filters_exact :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) (post : C -> bool)
      (left_guard : A -> bool) (right_guard : B -> bool) left right,
    (forall left_row right_row,
      andb (accept left_row right_row) (post (join left_row right_row)) =
      andb (left_guard left_row)
        (andb (right_guard right_row) (accept left_row right_row))) ->
    filter post (join_matched_rows join accept left right) =
    join_matched_rows join accept
      (filter left_guard left) (filter right_guard right).
Proof.
intros A B C join accept post left_guard right_guard left right Hfactor.
rewrite filter_join_matched_rows_exact.
apply join_matched_rows_filter_inputs_exact.
exact Hfactor.
Qed.

(** Moving a guard before a join changes the rows on which it is evaluated.
    These predicates expose the exact reachability obligations rather than
    silently treating an unreachable expression as total. *)
Definition join_left_guard_reached {A B : Type}
    (accept : A -> B -> bool) (left : list A) (right : list B)
    (left_row : A) : Prop :=
  In left_row left /\
  exists right_row, In right_row right /\ accept left_row right_row = true.

Definition join_right_guard_reached {A B : Type}
    (accept : A -> B -> bool) (left : list A) (right : list B)
    (right_row : B) : Prop :=
  In right_row right /\
  exists left_row, In left_row left /\ accept left_row right_row = true.

Theorem join_left_guard_reached_iff_of_witness :
  forall (A B : Type) (accept : A -> B -> bool) left right,
    (forall left_row,
      In left_row left ->
      exists right_row,
        In right_row right /\ accept left_row right_row = true) ->
    forall left_row,
      join_left_guard_reached accept left right left_row <->
      In left_row left.
Proof.
intros A B accept left right Hwitness left_row; split.
- intros [Hleft Hright]; exact Hleft.
- intro Hleft; split; [exact Hleft|now apply Hwitness].
Qed.

Theorem join_right_guard_reached_iff_of_witness :
  forall (A B : Type) (accept : A -> B -> bool) left right,
    (forall right_row,
      In right_row right ->
      exists left_row,
        In left_row left /\ accept left_row right_row = true) ->
    forall right_row,
      join_right_guard_reached accept left right right_row <->
      In right_row right.
Proof.
intros A B accept left right Hwitness right_row; split.
- intros [Hright Hleft]; exact Hright.
- intro Hright; split; [exact Hright|now apply Hwitness].
Qed.

(** A reflexive self-match supplies both reachability directions.  This
    theorem does not claim that the reached predicates are error-free. *)
Theorem join_self_guard_reachability_exact :
  forall (A : Type) (accept : A -> A -> bool) rows,
    (forall row, In row rows -> accept row row = true) ->
    (forall row,
      join_left_guard_reached accept rows rows row <-> In row rows) /\
    (forall row,
      join_right_guard_reached accept rows rows row <-> In row rows).
Proof.
intros A accept rows Hself; split.
- apply join_left_guard_reached_iff_of_witness.
  intros row Hrow; exists row; split; [exact Hrow|now apply Hself].
- apply join_right_guard_reached_iff_of_witness.
  intros row Hrow; exists row; split; [exact Hrow|now apply Hself].
Qed.

(** An accepted scheduler cell contributes its emitted occurrence to the
    matched list.  This is the concrete bridge from a witness/reachability
    proof to a later row-level FILTER proof. *)
Lemma join_matched_rows_member_of_accepted_cell :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) left right left_row right_row,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    In (join left_row right_row)
      (join_matched_rows join accept left right).
Proof.
intros A B C join accept left right left_row right_row
  Hleft Hright Haccepted.
unfold join_matched_rows.
apply in_flat_map.
exists left_row; split; [exact Hleft|].
apply in_map.
apply filter_In; now split.
Qed.

(** FormalSQL has no separate volatile-expression constructor.  A single
    semantic-equality-respecting Boolean function, implemented exactly by
    every formula observation, is therefore the explicit interface for a
    proper, total, stable (non-volatile) filter decision. *)
Section StableTotalFilterAcceptance.

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

Definition stable_total_filter_acceptance
    (env : Env.env T) (formula : scalar_expr T relname ScalarResultBoolean)
    (keep : tuple T -> bool) : Prop :=
  (forall first second,
    Oeset.compare (OTuple T) first second = Eq ->
    keep first = keep second) /\
  (forall row,
    scalar_expr_acceptance_exact_at
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule (env_t T env row) formula (keep row)).

(** The stable-total contract exposes successful filtering as the exact
    finite-bag filter, retaining semantic row multiplicities. *)
Theorem query_filter_success_bags_of_stable_total_acceptance :
  forall env formula input keep,
    stable_total_filter_acceptance env formula keep ->
    rel_equiv
      (query_success_bags basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null boolean_schedule env
        (QExpr_Filter formula input))
      (fun output =>
        exists input_bag,
          query_success_bags basesort instance unknown symbol_runtime_error
            aggregate_runtime_error value_is_null boolean_schedule env
            input input_bag /\
          bag_eq T
            (Febag.filter (Fecol.CBag (CTuple T)) keep input_bag)
            output).
Proof.
intros env formula input keep [Hproper Hexact].
now apply query_filter_success_bags_exact.
Qed.

(** Under the same contract a FILTER introduces no local error category;
    child categories are propagated exactly. *)
Theorem query_filter_error_iff_of_stable_total_acceptance :
  forall env formula input keep,
    stable_total_filter_acceptance env formula keep ->
    forall error,
      eval_query env (QExpr_Filter formula input) (SqlError error) <->
      eval_query env input (SqlError error).
Proof.
intros env formula input keep [Hproper Hexact] error.
apply (query_filter_error_iff_exact
  (env := env) (formula := formula) (input := input) keep).
intros input_rows row Hinput Hrow.
exact (Hexact row).
Qed.

End StableTotalFilterAcceptance.

(*****************************************************************************)
(** Reached-row exact error scheduling for unsafe filters.                  **)
(*****************************************************************************)

Section ReachedFilterErrors.

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

Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).

(** A reached bad occurrence forces the sequential FILTER traversal to expose
    its error category when every preceding occurrence can either succeed or
    expose that same category.  This theorem constructs a real FormalSQL
    derivation; it does not summarize errors with an unconstrained predicate. *)
Theorem eval_filter_rows_uniform_error_of_reached_member :
  forall env formula rows bad error,
    In bad rows ->
    eval_scalar_boolean (env_t T env bad) formula (SqlError error) ->
    (forall row,
      In row rows ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula rows (SqlError error).
Proof.
intros env formula rows.
induction rows as [|head tail IH]; intros bad error Hbad Hbad_error Hall.
- contradiction.
- destruct Hbad as [Hbad|Hbad].
  + subst bad; now apply EFilterRows_HeadError.
  + destruct (Hall head (or_introl eq_refl)) as
      [[truth Htruth]|Hhead_error].
    * replace (SqlError error) with
        (@filter_cons_outcome T truth head (SqlError error))
        by reflexivity.
      eapply EFilterRows_Cons.
      -- exact Htruth.
      -- eapply IH; [exact Hbad|exact Hbad_error|].
         intros row Hrow; apply Hall; now right.
    * now apply EFilterRows_HeadError.
Qed.

Local Lemma eval_filter_rows_error_has_reached_member :
  forall env formula rows error,
    eval_filter_rows env formula rows (SqlError error) ->
    exists row,
      In row rows /\
      eval_scalar_boolean (env_t T env row) formula (SqlError error).
Proof.
intros env formula rows.
induction rows as [|head tail IH]; intros error Hfilter.
- inversion Hfilter.
- inversion Hfilter; subst.
  + exists head; split; [now left|eassumption].
  + match goal with
    | Htail : eval_filter_rows _ _ tail ?tail_outcome |- _ =>
        destruct tail_outcome as [tail_rows|tail_error] eqn:Htail_outcome
    end.
    * unfold filter_cons_outcome in *.
      destruct (Bool.is_true (B T) truth); discriminate.
    * cbn [filter_cons_outcome] in *.
      match goal with
      | H : SqlError tail_error = SqlError error |- _ =>
          injection H as Hcategory; subst tail_error
      | H : SqlError error = SqlError tail_error |- _ =>
          injection H as Hcategory; subst tail_error
      | _ => idtac
      end.
      destruct (IH error) as [row [Hrow Hrow_error]]; [eassumption|].
      exists row; split; [now right|exact Hrow_error].
Qed.

(** If every reached formula failure has one category, every failure of the
    sequential row scheduler has exactly that category. *)
Theorem eval_filter_rows_error_category_of_reached_categories :
  forall env formula rows expected error,
    (forall row,
      In row rows ->
      forall observed,
        eval_scalar_boolean (env_t T env row) formula (SqlError observed) ->
        observed = expected) ->
    eval_filter_rows env formula rows (SqlError error) ->
    error = expected.
Proof.
intros env formula rows expected error Hcategories Hfilter.
destruct (eval_filter_rows_error_has_reached_member Hfilter)
  as [row [Hrow Hrow_error]].
now apply (Hcategories row Hrow error).
Qed.

(** A successful FILTER traversal evaluates every reached row successfully.
    Therefore one reached occurrence with no successful formula observation
    excludes every successful output list, independently of acceptance truth. *)
Theorem eval_filter_rows_success_excludes_reached_exact_error :
  forall env formula rows bad,
    In bad rows ->
    (forall truth,
      ~ eval_scalar_boolean (env_t T env bad) formula (SqlSuccess truth)) ->
    forall output,
      ~ eval_filter_rows env formula rows (SqlSuccess output).
Proof.
intros env formula rows.
induction rows as [|head tail IH]; intros bad Hbad Hexclude output Hfilter.
- contradiction.
- inversion Hfilter; subst.
  match goal with
  | Htail : eval_filter_rows _ _ tail ?outcome |- _ =>
      destruct outcome as [tail_rows|tail_error]
  end.
  + destruct Hbad as [Hbad|Hbad].
    * subst bad.
      match goal with
      | Hhead : eval_scalar_boolean _ formula (SqlSuccess ?truth) |- _ =>
          exact (Hexclude truth Hhead)
      end.
    * eapply IH; [exact Hbad|exact Hexclude|eassumption].
  + cbn [filter_cons_outcome] in *; discriminate.
Qed.

(** Package the three independent facts needed by an unsafe branch: actual
    error existence, exclusion of all successful traversals, and uniqueness
    of the possible error category. *)
Theorem eval_filter_rows_reached_uniform_error_exact :
  forall env formula rows bad expected,
    In bad rows ->
    eval_scalar_boolean (env_t T env bad) formula (SqlError expected) ->
    (forall row,
      In row rows ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError expected)) ->
    (forall truth,
      ~ eval_scalar_boolean (env_t T env bad) formula (SqlSuccess truth)) ->
    (forall row,
      In row rows ->
      forall observed,
        eval_scalar_boolean (env_t T env row) formula (SqlError observed) ->
        observed = expected) ->
    eval_filter_rows env formula rows (SqlError expected) /\
    (forall output,
      ~ eval_filter_rows env formula rows (SqlSuccess output)) /\
    (forall observed,
      eval_filter_rows env formula rows (SqlError observed) ->
      observed = expected).
Proof.
intros env formula rows bad expected Hbad Hbad_error Hall Hexclude
  Hcategories.
split.
- eapply eval_filter_rows_uniform_error_of_reached_member; eassumption.
- split.
  + intros output Hsuccess.
    eapply eval_filter_rows_success_excludes_reached_exact_error;
      eassumption.
  + intros observed Herror.
    eapply eval_filter_rows_error_category_of_reached_categories;
      eassumption.
Qed.

(** A concrete accepted join cell supplies the reached bad row needed by the
    unsafe FILTER theorem.  The remaining premise is the exact per-occurrence
    success-or-same-error contract for the actual matched-row list. *)
Theorem eval_filter_rows_uniform_error_of_join_witness :
  forall (A B : Type) env formula
      (join : A -> B -> tuple T) (accept : A -> B -> bool)
      left right left_row right_row error,
    In left_row left ->
    In right_row right ->
    accept left_row right_row = true ->
    eval_scalar_boolean (env_t T env (join left_row right_row)) formula
      (SqlError error) ->
    (forall row,
      In row (join_matched_rows join accept left right) ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula
      (join_matched_rows join accept left right) (SqlError error).
Proof.
intros A B env formula join accept left right left_row right_row error
  Hleft Hright Haccepted Herror Hall.
eapply eval_filter_rows_uniform_error_of_reached_member
  with (bad := join left_row right_row); [|exact Herror|exact Hall].
now apply join_matched_rows_member_of_accepted_cell.
Qed.

(** The self-join specialization keeps the accepted diagonal premise
    explicit.  It says nothing about rows outside the actual matched list. *)
Corollary eval_filter_rows_uniform_error_of_self_match :
  forall (A : Type) env formula
      (join : A -> A -> tuple T) (accept : A -> A -> bool)
      rows bad error,
    In bad rows ->
    accept bad bad = true ->
    eval_scalar_boolean (env_t T env (join bad bad)) formula (SqlError error) ->
    (forall row,
      In row (join_matched_rows join accept rows rows) ->
      (exists truth,
        eval_scalar_boolean (env_t T env row) formula (SqlSuccess truth)) \/
      eval_scalar_boolean (env_t T env row) formula (SqlError error)) ->
    eval_filter_rows env formula
      (join_matched_rows join accept rows rows) (SqlError error).
Proof.
intros A env formula join accept rows bad error Hbad Haccepted Herror Hall.
eapply eval_filter_rows_uniform_error_of_join_witness
  with (left_row := bad) (right_row := bad); eassumption.
Qed.

End ReachedFilterErrors.

(*****************************************************************************)
(** Foreign-key witnesses and functional middle-row elimination.            **)
(*****************************************************************************)

(** A non-NULL referencing occurrence has a real referenced witness.  The
    bridge premise is intentionally row-local: it connects an accepted direct
    edge to the middle predicate without encoding a surrounding query. *)
Theorem nonnull_foreign_key_direct_accept_has_middle :
  forall db raw_foreigns referenced_relation
      source_attributes referenced_attributes
      (project_source project_foreign project_referenced :
        tuple TNull -> tuple TNull)
      (middle_accept direct_accept :
        tuple TNull -> tuple TNull -> bool)
      source foreign,
    rows_attributes_not_null source_attributes raw_foreigns ->
    foreign_key_conforms db raw_foreigns
      (ForeignKeyConstraint source_attributes referenced_relation
        referenced_attributes) ->
    In foreign raw_foreigns ->
    direct_accept (project_source source) (project_foreign foreign) = true ->
    (forall referenced,
      In referenced (instance_rows db referenced_relation) ->
      foreign_key_key_equal_true source_attributes referenced_attributes
        foreign referenced ->
      direct_accept (project_source source) (project_foreign foreign) = true ->
      middle_accept (project_source source)
        (project_referenced referenced) = true) ->
    exists referenced,
      In referenced (instance_rows db referenced_relation) /\
      foreign_key_key_equal_true source_attributes referenced_attributes
        foreign referenced /\
      middle_accept (project_source source)
        (project_referenced referenced) = true.
Proof.
intros db raw_foreigns referenced_relation source_attributes
  referenced_attributes project_source project_foreign project_referenced
  middle_accept direct_accept source foreign Hnotnull Hforeign_key
  Hforeign Hdirect Hbridge.
assert (Hrow_notnull : row_attributes_not_null source_attributes foreign).
{
  intros attribute Hattribute.
  eapply Hnotnull; eassumption.
}
destruct
  (foreign_key_conforms_nonnull_row_referenced
    db raw_foreigns
    (ForeignKeyConstraint source_attributes referenced_relation
      referenced_attributes)
    foreign Hforeign_key Hforeign Hrow_notnull)
  as [referenced [Hreferenced Hkey]].
exists referenced; repeat split; try assumption.
now apply Hbridge.
Qed.

Corollary nonnull_foreign_key_no_middle_rejects_direct :
  forall db raw_foreigns referenced_relation
      source_attributes referenced_attributes
      (project_source project_foreign project_referenced :
        tuple TNull -> tuple TNull)
      (middle_accept direct_accept :
        tuple TNull -> tuple TNull -> bool)
      source foreign,
    rows_attributes_not_null source_attributes raw_foreigns ->
    foreign_key_conforms db raw_foreigns
      (ForeignKeyConstraint source_attributes referenced_relation
        referenced_attributes) ->
    In foreign raw_foreigns ->
    (forall referenced,
      In referenced (instance_rows db referenced_relation) ->
      middle_accept (project_source source)
        (project_referenced referenced) = false) ->
    (forall referenced,
      In referenced (instance_rows db referenced_relation) ->
      foreign_key_key_equal_true source_attributes referenced_attributes
        foreign referenced ->
      direct_accept (project_source source) (project_foreign foreign) = true ->
      middle_accept (project_source source)
        (project_referenced referenced) = true) ->
    direct_accept (project_source source) (project_foreign foreign) = false.
Proof.
intros db raw_foreigns referenced_relation source_attributes
  referenced_attributes project_source project_foreign project_referenced
  middle_accept direct_accept source foreign Hnotnull Hforeign_key
  Hforeign Hnone Hbridge.
destruct (direct_accept (project_source source) (project_foreign foreign))
  eqn:Hdirect; [|reflexivity].
destruct (nonnull_foreign_key_direct_accept_has_middle
  (db := db) (raw_foreigns := raw_foreigns)
  (referenced_relation := referenced_relation)
  (source_attributes := source_attributes)
  (referenced_attributes := referenced_attributes)
  project_source project_foreign project_referenced
  middle_accept direct_accept source foreign
  Hnotnull Hforeign_key Hforeign Hdirect
  (fun referenced Hreferenced Hkey _ =>
    Hbridge referenced Hreferenced Hkey eq_refl))
  as [referenced [Hreferenced [Hkey Hmiddle]]].
rewrite (Hnone referenced Hreferenced) in Hmiddle; discriminate.
Qed.

(** If every reached pair is rejected, the inner scheduler is empty. *)
Lemma join_matched_rows_empty_of_rejection :
  forall (A B C : Type) (join : A -> B -> C)
      (accept : A -> B -> bool) left right,
    (forall left_row right_row,
      In left_row left -> In right_row right ->
      accept left_row right_row = false) ->
    join_matched_rows join accept left right = nil.
Proof.
intros A B C join accept left right Hreject.
unfold join_matched_rows.
induction left as [|left_row left IH]; [reflexivity|].
cbn [flat_map].
assert (Hhead : filter (accept left_row) right = nil).
{
  apply ListFacts.filter_false.
  intros right_row Hright.
  apply Hreject; [now left|exact Hright].
}
rewrite Hhead; cbn.
apply IH.
intros row right_row Hrow Hright.
apply Hreject; [now right|exact Hright].
Qed.

(** A downstream null-rejecting predicate makes every padded middle
    occurrence unreachable.  The result is exact list emptiness, so no
    duplicate or order quotient is involved. *)
Theorem middle_padding_downstream_empty :
  forall (A B D M O : Type)
      (pad : A -> M) (middle_accept : A -> B -> bool)
      (emit : M -> D -> O) (downstream_accept : M -> D -> bool)
      source_rows middle_rows downstream_rows,
    (forall source downstream,
      In source source_rows -> In downstream downstream_rows ->
      downstream_accept (pad source) downstream = false) ->
    join_matched_rows emit downstream_accept
      (join_unmatched_left_rows pad middle_accept
        source_rows middle_rows)
      downstream_rows = nil.
Proof.
intros A B D M O pad middle_accept emit downstream_accept
  source_rows middle_rows downstream_rows Hreject.
apply join_matched_rows_empty_of_rejection.
intros padded downstream Hpadded Hdownstream.
unfold join_unmatched_left_rows in Hpadded.
apply in_map_iff in Hpadded.
destruct Hpadded as [source [Hpadded Hsource]].
subst padded.
apply filter_In in Hsource as [Hsource Hnone].
now apply Hreject.
Qed.

(** Pairwise predicate agreement plus payload erasure transports one exact
    filtered occurrence block through semantic relation [R]. *)
Theorem filtered_payload_erasure_permut :
  forall (M A D O1 O2 : Type) (R : O1 -> O2 -> Prop)
      (emit_left : M -> D -> O1) (emit_right : A -> D -> O2)
      (accept_left : M -> D -> bool) (accept_right : A -> D -> bool)
      middle source downstream_rows,
    (forall downstream,
      In downstream downstream_rows ->
      accept_left middle downstream = accept_right source downstream) ->
    (forall downstream,
      In downstream downstream_rows ->
      accept_left middle downstream = true ->
      R (emit_left middle downstream) (emit_right source downstream)) ->
    _permut R
      (map (emit_left middle)
        (filter (accept_left middle) downstream_rows))
      (map (emit_right source)
        (filter (accept_right source) downstream_rows)).
Proof.
intros M A D O1 O2 R emit_left emit_right accept_left accept_right
  middle source downstream_rows Hagree Herase.
induction downstream_rows as [|downstream downstream_rows IH];
  [constructor|].
pose proof (Hagree downstream (or_introl eq_refl)) as Hflag.
destruct (accept_left middle downstream) eqn:Haccepted.
- cbn [filter map].
  rewrite Haccepted, <- Hflag; cbn [filter map].
  apply (@Pcons _ _ R
    (emit_left middle downstream) (emit_right source downstream)
    (map (emit_left middle)
      (filter (accept_left middle) downstream_rows)) nil
    (map (emit_right source)
      (filter (accept_right source) downstream_rows))).
  + apply Herase; [now left|exact Haccepted].
  + apply IH.
    * intros row Hrow; apply Hagree; now right.
    * intros row Hrow; apply Herase; now right.
- cbn [filter map].
  rewrite Haccepted, <- Hflag; cbn [filter map].
  apply IH.
  + intros row Hrow; apply Hagree; now right.
  + intros row Hrow; apply Herase; now right.
Qed.

(*****************************************************************************)
(** Exact-error-only query outcome lift.                                    **)
(*****************************************************************************)

Section ExactErrorOnlyOutcomeLift.

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

(** Two error-only queries are outcome-equivalent when each actually exposes
    the same fixed category, neither can expose a successful row list, and
    every possible error on each side is that category.  Unlike a raw error
    iff premise, these obligations decompose into concrete existence,
    success-exclusion, and category proofs supplied by operator schedulers. *)
Theorem query_expr_outcome_equiv_of_shared_exact_error :
  forall env first second expected,
    query_expr_outputs first = query_expr_outputs second ->
    eval_query env first (SqlError expected) ->
    eval_query env second (SqlError expected) ->
    (forall rows, ~ eval_query env first (SqlSuccess rows)) ->
    (forall rows, ~ eval_query env second (SqlSuccess rows)) ->
    (forall observed,
      eval_query env first (SqlError observed) -> observed = expected) ->
    (forall observed,
      eval_query env second (SqlError observed) -> observed = expected) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule env first second.
Proof.
intros env first second expected Houtputs Hfirst_error Hsecond_error
  Hfirst_no_success Hsecond_no_success Hfirst_category Hsecond_category.
apply query_expr_outcome_equiv_of_observations.
- exact Houtputs.
- now exists (SqlError expected).
- now exists (SqlError expected).
- intros rows Hrows.
  exfalso; exact (Hfirst_no_success rows Hrows).
- intros rows Hrows.
  exfalso; exact (Hsecond_no_success rows Hrows).
- intro observed; split; intro Herror.
  + rewrite (Hfirst_category observed Herror).
    exact Hsecond_error.
  + rewrite (Hsecond_category observed Herror).
    exact Hfirst_error.
Qed.

End ExactErrorOnlyOutcomeLift.
