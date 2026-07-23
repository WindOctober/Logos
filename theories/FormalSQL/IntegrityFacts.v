(************************************************************************************)
(** Compositional facts for generated FormalSQL integrity constraints.             **)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet Bool3 Formula Interp Env ListFacts SchemaConstraints.
From Logos.FormalSQL Require Import CardinalityCombinators.
From Stdlib Require Import List SetoidList String Lia.

Import ListNotations.
Import Tuple.

(** Row projection preserves the declared key arity. *)
Lemma project_row_length :
  forall attributes row,
    List.length (project_row attributes row) = List.length attributes.
Proof.
intros attributes row.
unfold project_row.
apply length_map.
Qed.

(** A successful componentwise SQL key comparison has equal arity. *)
Lemma sql_key_equal_true_length :
  forall left right,
    sql_key_equal_true left right ->
    List.length left = List.length right.
Proof.
intros left.
induction left as [|left_value left_rest IH]; intro right;
  destruct right as [|right_value right_rest]; intro Hequal;
  cbn in Hequal |- *.
- reflexivity.
- contradiction.
- contradiction.
- destruct Hequal as [Hvalue Hrest].
  f_equal; now apply IH.
Qed.

(** The recursive SQL key relation is exactly the standard pointwise relation. *)
Lemma sql_key_equal_true_iff_Forall2 :
  forall left right,
    sql_key_equal_true left right <->
    Forall2 sql_value_equal_true left right.
Proof.
intros left.
induction left as [|left_value left_rest IH]; intro right;
  destruct right as [|right_value right_rest]; cbn.
- split; intro H.
  + constructor.
  + exact I.
- split; intro H.
  + contradiction.
  + inversion H.
- split; intro H.
  + contradiction.
  + inversion H.
- split.
  + intros [Hvalue Hrest].
    constructor.
    * exact Hvalue.
    * now apply (proj1 (IH right_rest)).
  + intro Hpointwise.
    inversion Hpointwise as [|? ? ? ? Hvalue Hrest]; subst.
    split.
    * exact Hvalue.
    * now apply (proj2 (IH right_rest)).
Qed.

(** Row-level NOT NULL conformance transfers directly to the projected cells. *)
Lemma row_attributes_not_null_project :
  forall attributes row,
    row_attributes_not_null attributes row ->
    Forall
      (fun value => NullValues.is_null_value value = false)
      (project_row attributes row).
Proof.
intros attributes.
induction attributes as [|attribute attributes IH]; intros row Hnot_null;
  cbn [project_row].
- constructor.
- constructor.
  + apply Hnot_null; now left.
  + apply IH.
    intros other Hother.
    apply Hnot_null; now right.
Qed.

(** A declared NOT NULL set may be weakened to any included attribute set. *)
Lemma rows_attributes_not_null_weaken :
  forall required declared rows,
    incl required declared ->
    rows_attributes_not_null declared rows ->
    rows_attributes_not_null required rows.
Proof.
intros required declared rows Hincluded Hnot_null row Hrow attribute Hattribute.
eapply Hnot_null.
- exact Hrow.
- now apply Hincluded.
Qed.

(** Filtering cannot introduce a NULL into a declared NOT NULL column. *)
Lemma rows_attributes_not_null_filter :
  forall attributes rows keep,
    rows_attributes_not_null attributes rows ->
    rows_attributes_not_null attributes (filter keep rows).
Proof.
intros attributes rows keep Hnot_null row Hrow.
apply filter_In in Hrow as [Hrow Hkeep].
now apply Hnot_null.
Qed.

(** Every component of every stored primary-key row is non-NULL. *)
Lemma primary_key_component_not_null :
  forall primary_key rows row attribute,
    primary_key_conforms primary_key rows ->
    In row rows ->
    In attribute primary_key ->
    NullValues.is_null_value (dot TNull row attribute) = false.
Proof.
intros primary_key rows row attribute Hprimary Hrow Hattribute.
pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnot_null.
exact (Hnot_null row Hrow attribute Hattribute).
Qed.

(** Complete primary-key projections contain no NULL component. *)
Corollary primary_key_projection_not_null :
  forall primary_key rows row,
    primary_key_conforms primary_key rows ->
    In row rows ->
    Forall
      (fun value => NullValues.is_null_value value = false)
      (project_row primary_key row).
Proof.
intros primary_key rows row Hprimary Hrow.
apply row_attributes_not_null_project.
intros attribute Hattribute.
eapply primary_key_component_not_null; eassumption.
Qed.

(** Ordinary SQL unique-key conformance is preserved by filtering. *)
Lemma unique_key_conforms_filter :
  forall key rows keep,
    unique_key_conforms key rows ->
    unique_key_conforms key (filter keep rows).
Proof.
intros key rows keep [Hnonempty Hnodup].
split.
- exact Hnonempty.
- now apply NoDupA_map_filter.
Qed.

(** A unique key turns any pairwise-conflicting Boolean lookup into an
    at-most-one occurrence lookup, without replacing SQL equality by Rocq
    equality. *)
Theorem unique_key_pairwise_lookup_length_le_one :
  forall key rows keep,
    unique_key_conforms key rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      keep left = true ->
      keep right = true ->
      sql_key_equal_true
        (project_row key left) (project_row key right)) ->
    (List.length (filter keep rows) <= 1)%nat.
Proof.
intros key rows keep Hunique Hpairwise.
pose proof (unique_key_conforms_nodupA _ _ Hunique) as Hkeys.
pose proof
  (NoDupA_map_preimage
    (tuple TNull) (list (value TNull)) sql_key_equal_true
    (project_row key) rows Hkeys) as Hrows.
eapply NoDupA_pairwise_filter_length_le_one.
- exact Hrows.
- exact Hpairwise.
Qed.

(** Foreign-key conformance exposes its nonempty and equal-arity declaration
    requirements together. *)
Lemma foreign_key_conforms_shape :
  forall db rows foreign_key,
    foreign_key_conforms db rows foreign_key ->
    foreign_key_columns foreign_key <> nil /\
    List.length (foreign_key_columns foreign_key) =
      List.length (foreign_key_referenced_columns foreign_key).
Proof.
intros db rows foreign_key [Hnonempty [Hlength Hrows]].
now split.
Qed.

(** Under MATCH SIMPLE, a conforming row with no NULL source component must
    have an actual referenced witness. *)
Lemma foreign_key_conforms_nonnull_row_referenced :
  forall db rows foreign_key row,
    foreign_key_conforms db rows foreign_key ->
    In row rows ->
    row_attributes_not_null (foreign_key_columns foreign_key) row ->
    exists referenced_row,
      In referenced_row
        (instance_rows db
          (foreign_key_referenced_relation foreign_key)) /\
      foreign_key_key_equal_true
        (foreign_key_columns foreign_key)
        (foreign_key_referenced_columns foreign_key)
        row referenced_row.
Proof.
intros db rows foreign_key row Hforeign Hrow Hnot_null.
destruct Hforeign as [Hnonempty [Hlength Hconforms]].
specialize (Hconforms row Hrow).
destruct Hconforms as
  [[attribute [Hattribute Hnull]] | [referenced_row Hreferenced]].
- pose proof (Hnot_null attribute Hattribute) as Hnonnull.
  rewrite Hnull in Hnonnull; discriminate.
- now exists referenced_row.
Qed.

(** Filtering referencing rows preserves the same MATCH SIMPLE snapshot
    foreign-key contract. *)
Lemma foreign_key_conforms_filter :
  forall db rows foreign_key keep,
    foreign_key_conforms db rows foreign_key ->
    foreign_key_conforms db (filter keep rows) foreign_key.
Proof.
intros db rows foreign_key keep [Hnonempty [Hlength Hrows]].
split.
- exact Hnonempty.
- split.
  + exact Hlength.
  + intros row Hrow.
    apply filter_In in Hrow as [Hrow Hkeep].
    now apply Hrows.
Qed.

(** A conforming check applies to every member occurrence. *)
Lemma check_constraint_conforms_row :
  forall db rows check row,
    check_constraint_conforms db rows check ->
    In row rows ->
    check_row_conforms db check row.
Proof.
intros db rows check row Hcheck Hrow.
unfold check_constraint_conforms in Hcheck.
rewrite Forall_forall in Hcheck.
now apply Hcheck.
Qed.

(** Filtering preserves check conformance, including its runtime-error
    exclusion. *)
Lemma check_constraint_conforms_filter :
  forall db rows check keep,
    check_constraint_conforms db rows check ->
    check_constraint_conforms db (filter keep rows) check.
Proof.
intros db rows check keep Hcheck.
unfold check_constraint_conforms in Hcheck |- *.
rewrite Forall_forall in Hcheck |- *.
intros row Hrow.
apply filter_In in Hrow as [Hrow Hkeep].
now apply Hcheck.
Qed.

(** Check conformance composes exactly across list concatenation. *)
Lemma check_constraint_conforms_app_iff :
  forall db left right check,
    check_constraint_conforms db (left ++ right) check <->
    check_constraint_conforms db left check /\
    check_constraint_conforms db right check.
Proof.
intros db left right check.
unfold check_constraint_conforms.
apply Forall_app.
Qed.

(** Participation in a partial unique index is characterized by an error-free
    predicate whose three-valued result is TRUE. *)
Lemma unique_index_row_participates_iff :
  forall db index row,
    unique_index_row_participates db index row = true <->
    unique_index_predicate_error db row index = None /\
    unique_index_predicate_truth db row index = true3.
Proof.
intros db index row.
unfold unique_index_row_participates.
destruct (unique_index_predicate_error db row index) as [error|] eqn:Herror;
  destruct (unique_index_predicate_truth db row index) eqn:Htruth; cbn.
- split.
  + intro H; discriminate.
  + intros [Hnone Htrue]; discriminate.
- split.
  + intro H; discriminate.
  + intros [Hnone Hfalse]; discriminate.
- split.
  + intro H; discriminate.
  + intros [Hnone Hunknown]; discriminate.
- split.
  + intro H; split; reflexivity.
  + intros [Hnone Htrue]; reflexivity.
- split.
  + intro H; discriminate.
  + intros [Hnone Hfalse]; discriminate.
- split.
  + intro H; discriminate.
  + intros [Hnone Hunknown]; discriminate.
Qed.

(** A non-partial expression index includes every row at the predicate stage. *)
Lemma unique_index_without_predicate_participates :
  forall db index row,
    unique_index_predicate index = None ->
    unique_index_row_participates db index row = true.
Proof.
intros db index row Hpredicate.
apply unique_index_row_participates_true.
- unfold unique_index_predicate_error.
  now rewrite Hpredicate.
- unfold unique_index_predicate_truth.
  now rewrite Hpredicate.
Qed.

(** Evaluating an expression-index key preserves its declared term arity. *)
Lemma unique_index_key_length :
  forall terms row,
    List.length (unique_index_key terms row) = List.length terms.
Proof.
intros terms row.
unfold unique_index_key.
apply length_map.
Qed.

(** Filtering preserves partial/expression unique-index conformance: predicate
    success, participating expression success, and semantic uniqueness. *)
Lemma unique_index_conforms_filter :
  forall db rows index keep,
    unique_index_conforms db rows index ->
    unique_index_conforms db (filter keep rows) index.
Proof.
intros db rows index keep [Hnonempty [Hpredicate [Hterms Hnodup]]].
split.
- exact Hnonempty.
- split.
  + intros row Hrow.
    apply filter_In in Hrow as [Hrow Hkeep].
    now apply Hpredicate.
  + split.
    * intros row Hrow Hparticipates.
      apply filter_In in Hrow as [Hrow Hkeep].
      now apply Hterms.
    * pose proof
        (NoDupA_map_filter
          (tuple TNull) (list (value TNull)) sql_key_equal_true
          (unique_index_key (unique_index_terms index)) keep
          (filter (unique_index_row_participates db index) rows)
          Hnodup) as Hfiltered.
      rewrite filter_filter_commute in Hfiltered.
      exact Hfiltered.
Qed.

(** A conforming partial/expression unique index makes every pairwise-conflict
    lookup within its participating rows functional. *)
Theorem unique_index_pairwise_lookup_length_le_one :
  forall db rows index keep,
    unique_index_conforms db rows index ->
    (forall left right,
      In left rows ->
      In right rows ->
      unique_index_row_participates db index left = true ->
      unique_index_row_participates db index right = true ->
      keep left = true ->
      keep right = true ->
      sql_key_equal_true
        (unique_index_key (unique_index_terms index) left)
        (unique_index_key (unique_index_terms index) right)) ->
    (List.length
      (filter keep
        (filter (unique_index_row_participates db index) rows)) <= 1)%nat.
Proof.
intros db rows index keep Hindex Hpairwise.
pose proof (unique_index_conforms_nodupA db rows index Hindex) as Hkeys.
pose proof
  (NoDupA_map_preimage
    (tuple TNull) (list (value TNull)) sql_key_equal_true
    (unique_index_key (unique_index_terms index))
    (filter (unique_index_row_participates db index) rows) Hkeys)
  as Hrows.
eapply NoDupA_pairwise_filter_length_le_one.
- exact Hrows.
- intros left right Hleft Hright Hleft_keep Hright_keep.
  apply filter_In in Hleft as [Hleft Hleft_participates].
  apply filter_In in Hright as [Hright Hright_participates].
  eapply Hpairwise; eassumption.
Qed.

(** The complete row-constraint bundle is hereditary under filtering. *)
Theorem rows_constraint_conform_filter :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows keep,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes (filter keep rows).
Proof.
intros db not_null primary_key unique_keys foreign_keys checks
  unique_indexes rows keep
  [Hnot_null [Hprimary [Hunique [Hforeign [Hchecks Hindexes]]]]].
split.
- now apply rows_attributes_not_null_filter.
- split.
  + destruct primary_key as [key|].
    * destruct Hprimary as [Hnonempty [Hkey_not_null Hkey_nodup]].
      split.
      -- exact Hnonempty.
      -- split.
         ++ now apply rows_attributes_not_null_filter.
         ++ now apply NoDupA_map_filter.
    * exact I.
  + split.
    * rewrite Forall_forall in Hunique |- *.
      intros key Hkey.
      apply unique_key_conforms_filter.
      now apply Hunique.
    * split.
      -- rewrite Forall_forall in Hforeign |- *.
         intros foreign_key Hforeign_key.
         apply foreign_key_conforms_filter.
         now apply Hforeign.
      -- split.
         ++ rewrite Forall_forall in Hchecks |- *.
            intros check Hcheck.
            apply check_constraint_conforms_filter.
            now apply Hchecks.
         ++ rewrite Forall_forall in Hindexes |- *.
            intros index Hindex.
            apply unique_index_conforms_filter.
            now apply Hindexes.
Qed.

(** Table conformance projects the declared NOT NULL contract. *)
Lemma table_constraint_conforms_not_null :
  forall db constraint,
    table_constraint_conforms db constraint ->
    rows_attributes_not_null
      (constraint_not_null constraint)
      (instance_rows db (constraint_relation constraint)).
Proof.
intros db constraint Hconstraint.
unfold table_constraint_conforms in Hconstraint.
eapply rows_constraint_conform_not_null; exact Hconstraint.
Qed.

(** Table conformance projects a declared primary key. *)
Lemma table_constraint_conforms_primary_key :
  forall db constraint key,
    table_constraint_conforms db constraint ->
    constraint_primary_key constraint = Some key ->
    primary_key_conforms key
      (instance_rows db (constraint_relation constraint)).
Proof.
intros db constraint key Hconstraint Hkey.
unfold table_constraint_conforms in Hconstraint.
rewrite Hkey in Hconstraint.
eapply rows_constraint_conform_primary_key; exact Hconstraint.
Qed.

(** Table conformance projects any member of the ordinary unique-key list. *)
Lemma table_constraint_conforms_unique_key :
  forall db constraint key,
    table_constraint_conforms db constraint ->
    In key (constraint_unique_keys constraint) ->
    unique_key_conforms key
      (instance_rows db (constraint_relation constraint)).
Proof.
intros db constraint key Hconstraint Hkey.
unfold table_constraint_conforms in Hconstraint.
eapply rows_constraint_conform_unique_key; eassumption.
Qed.

(** Table conformance projects any member of the foreign-key list. *)
Lemma table_constraint_conforms_foreign_key :
  forall db constraint foreign_key,
    table_constraint_conforms db constraint ->
    In foreign_key (constraint_foreign_keys constraint) ->
    foreign_key_conforms db
      (instance_rows db (constraint_relation constraint)) foreign_key.
Proof.
intros db constraint foreign_key Hconstraint Hforeign_key.
unfold table_constraint_conforms in Hconstraint.
eapply rows_constraint_conform_foreign_key; eassumption.
Qed.

(** Table conformance projects any member of the check list. *)
Lemma table_constraint_conforms_check :
  forall db constraint check,
    table_constraint_conforms db constraint ->
    In check (constraint_checks constraint) ->
    check_constraint_conforms db
      (instance_rows db (constraint_relation constraint)) check.
Proof.
intros db constraint check Hconstraint Hcheck.
unfold table_constraint_conforms in Hconstraint.
eapply rows_constraint_conform_check; eassumption.
Qed.

(** Table conformance projects any member of the logical unique-index list. *)
Lemma table_constraint_conforms_unique_index :
  forall db constraint index,
    table_constraint_conforms db constraint ->
    In index (constraint_unique_indexes constraint) ->
    unique_index_conforms db
      (instance_rows db (constraint_relation constraint)) index.
Proof.
intros db constraint index Hconstraint Hindex.
unfold table_constraint_conforms in Hconstraint.
eapply rows_constraint_conform_unique_index; eassumption.
Qed.

(** Database conformance selects any member table constraint in one step. *)
Lemma database_conforms_schema_table_constraint :
  forall expected constraints actual constraint,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    table_constraint_conforms actual constraint.
Proof.
intros expected constraints actual constraint Hdatabase Hconstraint.
pose proof
  (database_conforms_schema_constraints
    expected constraints actual Hdatabase) as Hconstraints.
eapply schema_constraints_conform_member; eassumption.
Qed.

(** End-to-end database conformance makes every declared NOT NULL member
    non-NULL in every stored row occurrence of the constrained table. *)
Corollary database_conforms_schema_not_null_member :
  forall expected constraints actual constraint row attribute,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    In row (instance_rows actual (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    NullValues.is_null_value (dot TNull row attribute) = false.
Proof.
intros expected constraints actual constraint row attribute
  Hdatabase Hconstraint Hrow Hattribute.
pose proof
  (database_conforms_schema_table_constraint
    expected constraints actual constraint Hdatabase Hconstraint)
  as Htable.
pose proof
  (table_constraint_conforms_not_null actual constraint Htable)
  as Hnot_null.
exact (Hnot_null row Hrow attribute Hattribute).
Qed.
