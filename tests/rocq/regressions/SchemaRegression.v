From Stdlib Require Import Lia List SetoidList String ZArith.
From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet ValueInteger Bool3 Formula SqlErrorSemantics
  SchemaConstraints.
From Logos.FormalSQL Require Import
  TNullSyntax SchemaCardinality QueryCardinality IntegrityFacts WitnessFacts.

Import ListNotations.
Import Tuple.
Open Scope string_scope.
Open Scope Z_scope.

Definition ConstraintPred
    (predicate : ValueCore.predicate) (args : list AggTerm) :
    constraint_formula :=
  @Sql_Pred TNull constraint_query predicate args.

Definition regression_key : attribute TNull := Attr_Z "key".
Definition regression_payload : attribute TNull := Attr_Z "payload".

Definition regression_row (key payload : Z) : tuple TNull :=
  mk_tuple_lists
    [regression_key; regression_payload]
    [Value_Z (Some key); Value_Z (Some payload)].

Definition regression_null_key_row (payload : Z) : tuple TNull :=
  mk_tuple_lists
    [regression_key; regression_payload]
    [Value_Z None; Value_Z (Some payload)].

Definition regression_optional_row
    (key payload : option Z) : tuple TNull :=
  mk_tuple_lists
    [regression_key; regression_payload]
    [Value_Z key; Value_Z payload].

Lemma regression_NoDupA_two :
  forall (A : Type) (relation : A -> A -> Prop) left right,
    ~ relation left right ->
    NoDupA relation [left; right].
Proof.
intros A relation left right Hdistinct.
constructor.
- intro Hin.
  apply InA_alt in Hin as [value [Hrelated Hvalue]].
  cbn in Hvalue.
  destruct Hvalue as [-> | []].
  now apply Hdistinct.
- constructor.
  + intro Hin.
    apply InA_alt in Hin as [value [_ Hvalue]].
    now inversion Hvalue.
  + constructor.
Qed.

Example duplicate_primary_key_is_rejected :
  ~ primary_key_conforms
      [regression_key]
      [regression_row 1 10; regression_row 1 20].
Proof.
intros [_ [_ Hnodup]].
inversion Hnodup as [| projected remaining Hnotin _].
apply Hnotin.
apply InA_cons_hd.
vm_compute.
split; [reflexivity|exact I].
Qed.

Example null_primary_key_is_rejected :
  ~ primary_key_conforms
      [regression_key]
      [regression_null_key_row 10].
Proof.
intros [_ [Hnot_null _]].
specialize
  (Hnot_null
    (regression_null_key_row 10)
    (or_introl eq_refl)
    regression_key
    (or_introl eq_refl)).
vm_compute in Hnot_null; discriminate.
Qed.

Example duplicate_ordinary_unique_key_is_rejected :
  ~ unique_key_conforms
      [regression_key]
      [regression_row 1 10; regression_row 1 20].
Proof.
intros [_ Hnodup].
inversion Hnodup as [| projected remaining Hnotin _].
apply Hnotin.
apply InA_cons_hd.
vm_compute.
split; [reflexivity|exact I].
Qed.

Example ordinary_unique_nulls_are_distinct :
  unique_key_conforms
    [regression_key]
    [regression_null_key_row 10; regression_null_key_row 20].
Proof.
split; [discriminate|].
apply regression_NoDupA_two.
vm_compute.
intros [Hequal _]; discriminate.
Qed.

Example composite_unique_null_component_is_distinct :
  unique_key_conforms
    [regression_key; regression_payload]
    [regression_optional_row (Some 1) None;
     regression_optional_row (Some 1) None].
Proof.
split; [discriminate|].
apply regression_NoDupA_two.
vm_compute.
intros [_ [Hequal _]]; discriminate.
Qed.

Definition regression_foreign_key : foreign_key_constraint :=
  ForeignKeyConstraint
    [regression_key]
    (Rel "parent")
    [regression_key].

Definition regression_composite_foreign_key : foreign_key_constraint :=
  ForeignKeyConstraint
    [regression_key; regression_payload]
    (Rel "composite_parent")
    [regression_key; regression_payload].

Example match_simple_matching_row_satisfies_foreign_key :
  foreign_key_row_conforms_against
    regression_foreign_key
    (regression_row 1 20)
    [regression_row 1 10].
Proof.
eapply foreign_key_match_simple_referenced_row with
  (referenced_row := regression_row 1 10).
- now left.
- vm_compute.
  repeat split; try reflexivity; exact I.
Qed.

Example match_simple_null_component_satisfies_foreign_key :
  foreign_key_row_conforms_against
    regression_foreign_key
    (regression_null_key_row 20)
    nil.
Proof.
eapply foreign_key_match_simple_null_component with
  (attribute := regression_key).
- now left.
- reflexivity.
Qed.

Example match_simple_composite_any_null_component_satisfies_foreign_key :
  foreign_key_row_conforms_against
    regression_composite_foreign_key
    (regression_optional_row (Some 1) None)
    nil.
Proof.
eapply foreign_key_match_simple_null_component with
  (attribute := regression_payload).
- now right; left.
- reflexivity.
Qed.

Example unmatched_nonnull_row_violates_foreign_key :
  ~ foreign_key_row_conforms_against
      regression_foreign_key
      (regression_row 2 20)
      [regression_row 1 10].
Proof.
intros [[attribute [Hattribute Hnull]] |
  [referenced_row [Hrow Hequal]]].
- cbn in Hattribute.
  destruct Hattribute as [<- | []].
  vm_compute in Hnull; discriminate.
- cbn in Hrow.
  destruct Hrow as [<- | []].
  vm_compute in Hequal.
  intuition discriminate.
Qed.

Definition regression_parent_constraint : table_constraint :=
  TableConstraint
    (Rel "parent") [regression_key] (Some [regression_key])
    nil nil nil nil.

Definition regression_child_constraint : table_constraint :=
  TableConstraint
    (Rel "child") nil None nil [regression_foreign_key] nil nil.

Example referenced_primary_key_is_well_formed :
  foreign_key_reference_well_formed
    [regression_parent_constraint; regression_child_constraint]
    regression_foreign_key.
Proof.
unfold foreign_key_reference_well_formed.
cbn [regression_foreign_key].
split; [discriminate|].
split; [reflexivity|].
split.
- constructor; [reflexivity|constructor].
- exists regression_parent_constraint.
  split; [now left|].
  split; [reflexivity|now left].
Qed.

Definition regression_unique_parent_constraint : table_constraint :=
  TableConstraint
    (Rel "parent") nil None [[regression_key]] nil nil nil.

Example referenced_ordinary_unique_key_is_well_formed :
  foreign_key_reference_well_formed
    [regression_unique_parent_constraint; regression_child_constraint]
    regression_foreign_key.
Proof.
unfold foreign_key_reference_well_formed.
cbn [regression_foreign_key].
split; [discriminate|].
split; [reflexivity|].
split.
- constructor; [reflexivity|constructor].
- exists regression_unique_parent_constraint.
  split; [now left|].
  split; [reflexivity|now right; left].
Qed.

Definition regression_nonunique_parent_constraint : table_constraint :=
  TableConstraint (Rel "parent") nil None nil nil nil nil.

Example foreign_key_to_nonunique_columns_is_malformed :
  ~ foreign_key_reference_well_formed
      [regression_nonunique_parent_constraint]
      regression_foreign_key.
Proof.
intros [_ [_ [_
  [referenced_constraint [Hconstraint [_ Hunique]]]]]].
cbn in Hconstraint.
destruct Hconstraint as [<- | []].
cbn [table_declares_unique_key
  regression_nonunique_parent_constraint] in Hunique.
destruct Hunique as [Hprimary | Hordinary].
- discriminate.
- contradiction.
Qed.

Definition regression_int32_one : int32.
Proof.
refine (Int32 1 _); unfold int32_min, int32_max; lia.
Defined.

Definition regression_int64_one : int64.
Proof.
refine (Int64 1 _); unfold int64_min, int64_max; lia.
Defined.

Definition regression_child_int32 : attribute TNull :=
  Attr_int32 "child_id".

Definition regression_parent_int64 : attribute TNull :=
  Attr_int64 "parent_id".

Definition regression_int32_row : tuple TNull :=
  mk_tuple_lists
    [regression_child_int32]
    [NullValues.Value_int32 (Some regression_int32_one)].

Definition regression_int64_row : tuple TNull :=
  mk_tuple_lists
    [regression_parent_int64]
    [NullValues.Value_int64 (Some regression_int64_one)].

Definition regression_cross_integral_foreign_key : foreign_key_constraint :=
  ForeignKeyConstraint
    [regression_child_int32]
    (Rel "big_parent")
    [regression_parent_int64].

Example cross_integral_foreign_key_components_are_compatible :
  Forall2 foreign_key_attribute_compatible
    [regression_child_int32] [regression_parent_int64].
Proof.
constructor.
- apply foreign_key_attribute_compatible_int32_int64.
- constructor.
Qed.

Example heterogeneous_string_foreign_key_components_fail_closed :
  ~ foreign_key_attribute_compatible
      (Attr_string "child" StringText)
      (Attr_string "parent" (StringChar 4)).
Proof.
cbn; discriminate.
Qed.

Example cross_integral_equal_payload_satisfies_foreign_key :
  foreign_key_row_conforms_against
    regression_cross_integral_foreign_key
    regression_int32_row
    [regression_int64_row].
Proof.
eapply foreign_key_match_simple_referenced_row with
  (referenced_row := regression_int64_row).
- now left.
- cbn [regression_cross_integral_foreign_key
    foreign_key_key_equal_true regression_int32_row
    regression_int64_row].
  split.
  + apply foreign_key_value_equal_true_int32_int64.
    reflexivity.
  + exact I.
Qed.

Definition regression_positive_payload_formula : constraint_formula :=
  ConstraintPred PredicateGt
    [AExpr (Dot regression_payload);
     AExpr (Constant (Value_Z (Some 0)))].

Definition regression_positive_payload_check : check_constraint :=
  CheckConstraint regression_positive_payload_formula.

Example check_true_satisfies_constraint :
  check_row_conforms
    init_db regression_positive_payload_check (regression_row 1 10).
Proof.
vm_compute.
split; [reflexivity|discriminate].
Qed.

Example witness_check_true_reflects :
  check_row_conformsb
    init_db regression_positive_payload_check (regression_row 1 10) = true.
Proof. reflexivity. Qed.

Example check_unknown_satisfies_constraint :
  check_row_conforms
    init_db regression_positive_payload_check
    (regression_optional_row (Some 1) None).
Proof.
vm_compute.
split; [reflexivity|discriminate].
Qed.

Example witness_check_unknown_reflects_as_accepted :
  check_row_conformsb
    init_db regression_positive_payload_check
      (regression_optional_row (Some 1) None) = true.
Proof. reflexivity. Qed.

Example check_false_violates_constraint :
  ~ check_row_conforms
      init_db regression_positive_payload_check (regression_row 1 (-10)).
Proof.
vm_compute.
intros [_ Hnot_false]; now apply Hnot_false.
Qed.

Example witness_check_false_reflects_as_rejected :
  check_row_conformsb
    init_db regression_positive_payload_check (regression_row 1 (-10)) = false.
Proof. reflexivity. Qed.

Definition regression_int32_zero : int32.
Proof.
refine (Int32 0 _); unfold int32_min, int32_max; lia.
Defined.

Definition regression_division_by_zero_formula : constraint_formula :=
  ConstraintPred PredicateEq
    [AScalarCall (ScalarDivide ScalarInt32)
       [AExpr
          (Constant
            (NullValues.Value_int32 (Some regression_int32_one)));
        AExpr
          (Constant
            (NullValues.Value_int32 (Some regression_int32_zero)))];
     AExpr
       (Constant (NullValues.Value_int32 (Some regression_int32_one)))].

Definition regression_error_check : check_constraint :=
  CheckConstraint regression_division_by_zero_formula.

Example check_evaluation_error_violates_constraint :
  ~ check_row_conforms init_db regression_error_check (regression_row 1 10).
Proof.
intros [Herror _].
vm_compute in Herror; discriminate.
Qed.

Example witness_check_error_reflects_as_rejected :
  check_row_conformsb
    init_db regression_error_check (regression_row 1 10) = false.
Proof. reflexivity. Qed.

Definition regression_key_index_term : constraint_term :=
  Dot regression_key.

Definition regression_partial_positive_index : unique_index_constraint :=
  UniqueIndexConstraint
    [regression_key_index_term]
    (Some regression_positive_payload_formula).

Example duplicate_participating_partial_index_key_is_rejected :
  ~ unique_index_conforms
      init_db
      [regression_row 1 10; regression_row 1 20]
      regression_partial_positive_index.
Proof.
intros [_ [_ [_ Hnodup]]].
assert (Hfirst_participates :
  unique_index_row_participates init_db regression_partial_positive_index
    (regression_row 1 10) = true) by reflexivity.
assert (Hsecond_participates :
  unique_index_row_participates init_db regression_partial_positive_index
    (regression_row 1 20) = true) by reflexivity.
cbn [filter] in Hnodup.
rewrite Hfirst_participates, Hsecond_participates in Hnodup.
cbn [map] in Hnodup.
inversion Hnodup as [| projected remaining Hnotin _].
apply Hnotin.
apply InA_cons_hd.
change
  (sql_value_equal_true (Value_Z (Some 1)) (Value_Z (Some 1)) /\ True).
split; [reflexivity|exact I].
Qed.

Example witness_duplicate_partial_index_key_reflects_as_rejected :
  unique_index_conformsb
    init_db
    [regression_row 1 10; regression_row 1 20]
    regression_partial_positive_index = false.
Proof. reflexivity. Qed.

Example false_predicate_rows_do_not_participate_in_partial_index :
  unique_index_conforms
    init_db
    [regression_row 1 (-10); regression_row 1 (-20)]
    regression_partial_positive_index.
Proof.
unfold unique_index_conforms.
split; [discriminate|].
split.
- intros row Hrow.
  cbn in Hrow.
  destruct Hrow as [<- | [<- | []]]; reflexivity.
- split.
  + intros row Hrow Hparticipates.
    cbn in Hrow.
    destruct Hrow as [<- | [<- | []]];
      change (false = true) in Hparticipates; discriminate.
  + assert (Hfirst :
      unique_index_row_participates init_db regression_partial_positive_index
        (regression_row 1 (-10)) = false) by reflexivity.
    assert (Hsecond :
      unique_index_row_participates init_db regression_partial_positive_index
        (regression_row 1 (-20)) = false) by reflexivity.
    cbn [filter].
    now rewrite Hfirst, Hsecond; constructor.
Qed.

Example witness_false_partial_index_predicates_reflect_as_conforming :
  unique_index_conformsb
    init_db
    [regression_row 1 (-10); regression_row 1 (-20)]
    regression_partial_positive_index = true.
Proof. reflexivity. Qed.

Example unknown_predicate_rows_do_not_participate_in_partial_index :
  unique_index_conforms
    init_db
    [regression_optional_row (Some 1) None;
     regression_optional_row (Some 1) None]
    regression_partial_positive_index.
Proof.
unfold unique_index_conforms.
split; [discriminate|].
split.
- intros row Hrow.
  cbn in Hrow.
  destruct Hrow as [<- | [<- | []]]; reflexivity.
- split.
  + intros row Hrow Hparticipates.
    cbn in Hrow.
    destruct Hrow as [<- | [<- | []]];
      change (false = true) in Hparticipates; discriminate.
  + assert (Hfirst :
      unique_index_row_participates init_db regression_partial_positive_index
        (regression_optional_row (Some 1) None) = false) by reflexivity.
    cbn [filter].
    now rewrite Hfirst; constructor.
Qed.

Example witness_unknown_partial_index_predicates_reflect_as_conforming :
  unique_index_conformsb
    init_db
    [regression_optional_row (Some 1) None;
     regression_optional_row (Some 1) None]
    regression_partial_positive_index = true.
Proof. reflexivity. Qed.

Definition regression_error_index_term : constraint_term :=
  ScalarCall (ScalarDivide ScalarInt32)
    [Constant (NullValues.Value_int32 (Some regression_int32_one));
     Constant (NullValues.Value_int32 (Some regression_int32_zero))].

Definition regression_error_expression_index : unique_index_constraint :=
  UniqueIndexConstraint [regression_error_index_term] None.

Example participating_index_expression_error_is_rejected :
  ~ unique_index_conforms
      init_db [regression_row 1 10] regression_error_expression_index.
Proof.
intros [_ [_ [Hterms _]]].
specialize Hterms with
  (row := regression_row 1 10) (1 := or_introl eq_refl) (2 := eq_refl).
unfold unique_index_row_terms_succeed in Hterms.
inversion Hterms as [|term terms Herror _].
vm_compute in Herror; discriminate.
Qed.

Example witness_participating_index_expression_error_reflects_as_rejected :
  unique_index_conformsb
    init_db [regression_row 1 10] regression_error_expression_index = false.
Proof. reflexivity. Qed.

Definition regression_nonparticipating_error_expression_index
    : unique_index_constraint :=
  UniqueIndexConstraint
    [regression_error_index_term]
    (Some regression_positive_payload_formula).

Example nonparticipating_index_expression_error_is_irrelevant :
  unique_index_conforms
    init_db
    [regression_row 1 (-10)]
    regression_nonparticipating_error_expression_index.
Proof.
unfold unique_index_conforms.
split; [discriminate|].
split.
- intros row Hrow.
  cbn in Hrow.
  destruct Hrow as [<- | []]; reflexivity.
- split.
  + intros row Hrow Hparticipates.
    cbn in Hrow.
    destruct Hrow as [<- | []].
    change (false = true) in Hparticipates; discriminate.
  + assert (Hrow :
      unique_index_row_participates init_db
        regression_nonparticipating_error_expression_index
        (regression_row 1 (-10)) = false) by reflexivity.
    cbn [filter].
    now rewrite Hrow; constructor.
Qed.

Example witness_nonparticipating_index_expression_error_is_not_evaluated :
  unique_index_conformsb
    init_db
    [regression_row 1 (-10)]
    regression_nonparticipating_error_expression_index = true.
Proof. reflexivity. Qed.

Definition regression_error_predicate_index : unique_index_constraint :=
  UniqueIndexConstraint
    [regression_key_index_term]
    (Some regression_division_by_zero_formula).

Example partial_index_predicate_error_is_rejected :
  ~ unique_index_conforms
      init_db [regression_row 1 10] regression_error_predicate_index.
Proof.
intros [_ [Hpredicate_error _]].
specialize Hpredicate_error with
  (row := regression_row 1 10) (1 := or_introl eq_refl).
vm_compute in Hpredicate_error; discriminate.
Qed.

Example witness_partial_index_predicate_error_reflects_as_rejected :
  unique_index_conformsb
    init_db [regression_row 1 10] regression_error_predicate_index = false.
Proof. reflexivity. Qed.

Definition regression_is_null_index : unique_index_constraint :=
  UniqueIndexConstraint
    [regression_key_index_term]
    (Some (ConstraintPred PredicateIsNull [AExpr (Dot regression_key)])).

Example is_null_partial_index_participates_only_on_true :
  unique_index_row_participates
    init_db regression_is_null_index (regression_null_key_row 10) = true /\
  unique_index_row_participates
    init_db regression_is_null_index (regression_row 1 10) = false.
Proof.
split; reflexivity.
Qed.

Definition regression_name : attribute TNull :=
  Attr_string "name" StringText.

Definition regression_name_row (name : string) : tuple TNull :=
  mk_tuple_lists
    [regression_name]
    [NullValues.Value_string (StringValue StringText (Some name))].

Definition regression_lower_name_term : constraint_term :=
  ScalarCall (ScalarStringCase ScalarLower) [Dot regression_name].

Definition regression_lower_name_index : unique_index_constraint :=
  UniqueIndexConstraint [regression_lower_name_term] None.

Example lower_expression_index_evaluates_the_indexed_expression :
  unique_index_key
    [regression_lower_name_term] (regression_name_row "A") =
  [NullValues.Value_string (StringValue StringText (Some "a"))].
Proof.
reflexivity.
Qed.

Definition regression_empty_index : unique_index_constraint :=
  UniqueIndexConstraint nil None.

Definition regression_malformed_table_constraint : table_constraint :=
  TableConstraint
    (Rel "malformed") nil None [nil] nil nil [regression_empty_index].

Example empty_unique_and_index_keys_are_malformed :
  ~ table_constraint_declarations_well_formed
      [regression_malformed_table_constraint]
      regression_malformed_table_constraint.
Proof.
intros [_ [Hunique _]].
inversion Hunique as [|key keys Hnonempty _].
now apply Hnonempty.
Qed.

(** This interface check avoids rebuilding a large concrete finite-domain
    witness while still detecting changes to the Logos cardinality theorem. *)
Example complete_int32_primary_key_has_finite_bound :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    (List.length rows <= int32_domain_size)%nat.
Proof.
exact int32_singleton_primary_key_length.
Qed.

Check query_success_composite_key_fixed_first_length.
Check query_success_composite_key_fixed_second_length.

Example conforming_database_exposes_declared_primary_key :
  forall expected constraints actual constraint key,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    constraint_primary_key constraint = Some key ->
    primary_key_conforms key
      (instance_rows actual (constraint_relation constraint)).
Proof.
exact database_conforms_schema_primary_key.
Qed.

(** A complete declared NOT NULL covering set rules out the nullable MATCH
    SIMPLE branch and exposes an actual referenced row. *)
Example conforming_nonnull_foreign_key_has_referenced_row :
  forall expected constraints actual constraint foreign_key row,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    In foreign_key (constraint_foreign_keys constraint) ->
    In row (instance_rows actual (constraint_relation constraint)) ->
    incl
      (foreign_key_columns foreign_key)
      (constraint_not_null constraint) ->
    exists referenced_row,
      In referenced_row
        (instance_rows actual
          (foreign_key_referenced_relation foreign_key)) /\
      foreign_key_key_equal_true
        (foreign_key_columns foreign_key)
        (foreign_key_referenced_columns foreign_key)
        row referenced_row.
Proof.
exact database_conforms_schema_foreign_key_nonnull_referenced.
Qed.
