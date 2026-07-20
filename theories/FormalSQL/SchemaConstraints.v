(************************************************************************************)
(** Integrity constraints for generated FormalSQL base-table schemas.              *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet.
From Stdlib Require Import List String.

Import ListNotations.
Import Tuple.

Record table_constraint : Type := TableConstraint {
  constraint_relation : relname;
  constraint_not_null : list (attribute TNull);
  constraint_primary_key : option (list (attribute TNull))
}.

(** [Febag.elements] is intentionally used rather than a set conversion: its
    list contains one element for every bag occurrence, so duplicate stored
    rows remain observable to primary-key uniqueness. *)
Definition instance_rows
    (db : db_state) (relation : relname) : list (tuple TNull) :=
  Febag.elements
    (Fecol.CBag (CTuple TNull))
    (@_instance TNull db relation).

Definition project_row
    (attributes : list (attribute TNull))
    (row : tuple TNull) : list (value TNull) :=
  map (dot TNull row) attributes.

Definition row_attributes_not_null
    (attributes : list (attribute TNull))
    (row : tuple TNull) : Prop :=
  forall attribute,
    In attribute attributes ->
    NullValues.is_null_value (dot TNull row attribute) = false.

Definition rows_attributes_not_null
    (attributes : list (attribute TNull))
    (rows : list (tuple TNull)) : Prop :=
  forall row,
    In row rows ->
    row_attributes_not_null attributes row.

Definition primary_key_conforms
    (primary_key : list (attribute TNull))
    (rows : list (tuple TNull)) : Prop :=
  primary_key <> nil /\
  rows_attributes_not_null primary_key rows /\
  (** Structural carrier equality is no coarser than PostgreSQL equality for
      two identical, conforming non-NULL values of one declared attribute.
      Where a PostgreSQL operator class identifies additional representations,
      this [NoDup] condition admits extra states rather than excluding valid
      PostgreSQL states. Later exact cardinality arguments therefore consume
      only key types with a proved equality bridge. *)
  NoDup (map (project_row primary_key) rows).

Definition rows_constraint_conform
    (not_null : list (attribute TNull))
    (primary_key : option (list (attribute TNull)))
    (rows : list (tuple TNull)) : Prop :=
  rows_attributes_not_null not_null rows /\
  match primary_key with
  | None => True
  | Some key => primary_key_conforms key rows
  end.

Definition table_constraint_conforms
    (db : db_state) (constraint : table_constraint) : Prop :=
  rows_constraint_conform
    (constraint_not_null constraint)
    (constraint_primary_key constraint)
    (instance_rows db (constraint_relation constraint)).

Definition schema_constraints_conform
    (db : db_state) (constraints : list table_constraint) : Prop :=
  Forall (table_constraint_conforms db) constraints.

Definition database_conforms_schema
    (expected : db_state)
    (constraints : list table_constraint)
    (actual : db_state) : Prop :=
  @_relnames TNull actual = @_relnames TNull expected /\
  (forall relation,
    @_basesort TNull actual relation =S=
    @_basesort TNull expected relation) /\
  database_values_conform actual /\
  schema_constraints_conform actual constraints.

(** Value conformance alone is insufficient when rows may later be replaced by
    arbitrary [OTuple]-equal representatives: tuple equality constrains [dot]
    only for labels which are actually present.  Keep presence and value
    conformance together at the row boundary. *)
Definition row_attribute_present_conforms
    (attribute : attribute TNull) (row : tuple TNull) : Prop :=
  attribute inS labels TNull row /\
  value_conforms_attribute attribute (dot TNull row attribute).

Definition rows_attribute_present_conform
    (attribute : attribute TNull) (rows : list (tuple TNull)) : Prop :=
  Forall (row_attribute_present_conforms attribute) rows.

Lemma row_attribute_present_conforms_eq :
  forall attribute left right,
    Oeset.compare (OTuple TNull) left right = Eq ->
    (row_attribute_present_conforms attribute left <->
     row_attribute_present_conforms attribute right).
Proof.
intros attribute left right Hequal.
assert (Hlabels : labels TNull left =S= labels TNull right).
{ now apply tuple_eq_labels. }
split.
- intros [Hpresent Hconforms].
  assert (Hright : attribute inS labels TNull right).
  {
    rewrite <- (Fset.mem_eq_2 _ _ _ Hlabels).
    exact Hpresent.
  }
  split; [exact Hright|].
  rewrite <- (tuple_eq_dot_alt TNull left right Hequal attribute Hpresent).
  exact Hconforms.
- intros [Hpresent Hconforms].
  assert (Hreverse : Oeset.compare (OTuple TNull) right left = Eq).
  { now apply Oeset.compare_eq_sym. }
  assert (Hleft : attribute inS labels TNull left).
  {
    rewrite (Fset.mem_eq_2 _ _ _ Hlabels).
    exact Hpresent.
  }
  split; [exact Hleft|].
  rewrite <- (tuple_eq_dot_alt TNull right left Hreverse attribute Hpresent).
  exact Hconforms.
Qed.

Lemma instance_rows_nb_occ :
  forall db relation row,
    Febag.nb_occ
      (Fecol.CBag (CTuple TNull)) row
      (@_instance TNull db relation) =
    Oeset.nb_occ
      (OTuple TNull) row
      (instance_rows db relation).
Proof.
intros; apply Febag.nb_occ_elements.
Qed.

Lemma project_row_nil :
  forall row, project_row nil row = nil.
Proof.
reflexivity.
Qed.

Lemma project_row_cons :
  forall attribute attributes row,
    project_row (attribute :: attributes) row =
      dot TNull row attribute :: project_row attributes row.
Proof.
reflexivity.
Qed.

Lemma rows_attributes_not_null_member :
  forall attributes rows row,
    rows_attributes_not_null attributes rows ->
    In row rows ->
    row_attributes_not_null attributes row.
Proof.
intros attributes rows row Hrows Hrow.
now apply Hrows.
Qed.

Lemma primary_key_conforms_nonempty :
  forall primary_key rows,
    primary_key_conforms primary_key rows ->
    primary_key <> nil.
Proof.
intros primary_key rows [Hnonempty _].
exact Hnonempty.
Qed.

Lemma primary_key_conforms_not_null :
  forall primary_key rows,
    primary_key_conforms primary_key rows ->
    rows_attributes_not_null primary_key rows.
Proof.
intros primary_key rows [_ [Hnot_null _]].
exact Hnot_null.
Qed.

Lemma primary_key_conforms_nodup :
  forall primary_key rows,
    primary_key_conforms primary_key rows ->
    NoDup (map (project_row primary_key) rows).
Proof.
intros primary_key rows [_ [_ Hnodup]].
exact Hnodup.
Qed.

Lemma rows_constraint_conform_not_null :
  forall not_null primary_key rows,
    rows_constraint_conform not_null primary_key rows ->
    rows_attributes_not_null not_null rows.
Proof.
intros not_null primary_key rows [Hnot_null _].
exact Hnot_null.
Qed.

Lemma rows_constraint_conform_primary_key :
  forall not_null primary_key rows,
    rows_constraint_conform not_null (Some primary_key) rows ->
    primary_key_conforms primary_key rows.
Proof.
intros not_null primary_key rows [_ Hprimary_key].
exact Hprimary_key.
Qed.

Lemma schema_constraints_conform_member :
  forall db constraints constraint,
    schema_constraints_conform db constraints ->
    In constraint constraints ->
    table_constraint_conforms db constraint.
Proof.
intros db constraints constraint Hconstraints Hconstraint.
unfold schema_constraints_conform in Hconstraints.
rewrite Forall_forall in Hconstraints.
now apply Hconstraints.
Qed.

Lemma database_conforms_schema_relnames :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    @_relnames TNull actual = @_relnames TNull expected.
Proof.
intros expected constraints actual [Hrelnames _].
exact Hrelnames.
Qed.

Lemma database_conforms_schema_basesort :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    forall relation,
      @_basesort TNull actual relation =S=
      @_basesort TNull expected relation.
Proof.
intros expected constraints actual [_ [Hbasesort _]].
exact Hbasesort.
Qed.

Lemma database_conforms_schema_values :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    database_values_conform actual.
Proof.
intros expected constraints actual [_ [_ [Hvalues _]]].
exact Hvalues.
Qed.

Lemma database_conforms_schema_constraints :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    schema_constraints_conform actual constraints.
Proof.
intros expected constraints actual [_ [_ [_ Hconstraints]]].
exact Hconstraints.
Qed.

Lemma database_conforms_schema_rows_attribute_present :
  forall expected constraints actual relation attribute,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    rows_attribute_present_conform attribute (instance_rows actual relation).
Proof.
intros expected constraints actual relation attribute Hschema Hattribute.
unfold rows_attribute_present_conform.
rewrite Forall_forall.
intros row Hrow.
pose proof
  (database_conforms_schema_values expected constraints actual Hschema)
  as Hvalues.
specialize (Hvalues relation row Hrow) as [Hlabels Htyped].
pose proof
  (database_conforms_schema_basesort expected constraints actual Hschema
    relation) as Hbasesort.
assert (Hactual : attribute inS @_basesort TNull actual relation).
{
  rewrite (Fset.mem_eq_2 _ _ _ Hbasesort).
  exact Hattribute.
}
split.
- rewrite (Fset.mem_eq_2 _ _ _ Hlabels).
  exact Hactual.
- now apply Htyped.
Qed.

Lemma rows_attribute_present_conform_implies_value_conform :
  forall attribute rows,
    rows_attribute_present_conform attribute rows ->
    forall row,
      In row rows ->
      value_conforms_attribute attribute (dot TNull row attribute).
Proof.
intros attribute rows Hrows row Hrow.
unfold rows_attribute_present_conform in Hrows.
rewrite Forall_forall in Hrows.
exact (proj2 (Hrows row Hrow)).
Qed.
