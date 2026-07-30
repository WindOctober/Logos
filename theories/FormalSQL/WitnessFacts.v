(************************************************************************************)
(** Reflection support for host-generated, finite FormalSQL database witnesses.    *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet SchemaConstraints Bool3 SqlQuerySemantics.
From Stdlib Require Import List String Bool ZArith NArith SetoidList.

Import ListNotations.
Import Tuple.

Record witness_table : Type := WitnessTable {
  witness_table_relation : relname;
  witness_table_rows : list (tuple TNull)
}.

Fixpoint witness_rows_for
    (tables : list witness_table) (relation : relname)
    : list (tuple TNull) :=
  match tables with
  | nil => nil
  | table :: rest =>
      if Oset.eq_bool ORN relation (witness_table_relation table)
      then witness_table_rows table
      else witness_rows_for rest relation
  end.

Definition witness_database
    (expected : db_state) (tables : list witness_table) : db_state :=
  @mk_state TNull
    (@_relnames TNull expected)
    (@_basesort TNull expected)
    (fun relation =>
      Febag.mk_bag (Fecol.CBag (CTuple TNull))
        (witness_rows_for tables relation)).

Definition witness_instance_rows
    (tables : list witness_table) (relation : relname)
    : list (tuple TNull) :=
  Febag.elements (Fecol.CBag (CTuple TNull))
    (Febag.mk_bag (Fecol.CBag (CTuple TNull))
      (witness_rows_for tables relation)).

Lemma witness_database_instance_rows :
  forall expected tables relation,
    instance_rows (witness_database expected tables) relation =
    witness_instance_rows tables relation.
Proof.
reflexivity.
Qed.

(** The witness database preserves every occurrence in the host-provided raw
    row list.  This statement deliberately uses bag cardinality rather than
    [length (witness_instance_rows ...)], so clients need not unfold the
    canonical sorting performed by [Febag.elements]. *)
Lemma witness_database_instance_cardinal :
  forall expected tables relation,
    Febag.cardinal (Fecol.CBag (CTuple TNull))
      (@_instance TNull (witness_database expected tables) relation) =
    N.of_nat (length (witness_rows_for tables relation)).
Proof.
intros expected tables relation.
unfold witness_database; cbn.
apply Febag.cardinal_mk_bag.
Qed.

(** A well-sorted table scan exposes exactly the raw witness multiplicity.
    The only semantic premise is the ordinary table-output sort check used by
    [query_table_bag]; neither the concrete rows nor their canonical ordering
    is inspected by this proof. *)
Lemma witness_query_table_bag_cardinal :
  forall expected tables outputs relation,
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull expected relation ->
    Febag.cardinal (Fecol.CBag (CTuple TNull))
      (@query_table_bag TNull relname
        (@_basesort TNull (witness_database expected tables))
        (@_instance TNull (witness_database expected tables))
        outputs relation) =
    N.of_nat (length (witness_rows_for tables relation)).
Proof.
intros expected tables outputs relation Hsort.
assert (Hscan_sort :
  @query_outputs_sort TNull outputs =S=
    @_basesort TNull (witness_database expected tables) relation).
{
  change (@query_outputs_sort TNull outputs =S=
    @_basesort TNull expected relation).
  exact Hsort.
}
unfold query_table_bag.
rewrite Hscan_sort.
unfold witness_database; cbn.
apply Febag.cardinal_mk_bag.
Qed.

(** Generated query modules expose their table-sort certificate in the
    opposite orientation.  Keep this corollary so an agent can use that
    certificate directly, without reopening finite-set extensionality. *)
Corollary witness_query_table_bag_cardinal_generated_sort :
  forall expected tables outputs relation,
    @_basesort TNull expected relation =S=
      @query_outputs_sort TNull outputs ->
    Febag.cardinal (Fecol.CBag (CTuple TNull))
      (@query_table_bag TNull relname
        (@_basesort TNull (witness_database expected tables))
        (@_instance TNull (witness_database expected tables))
        outputs relation) =
    N.of_nat (length (witness_rows_for tables relation)).
Proof.
intros expected tables outputs relation Hsort.
apply witness_query_table_bag_cardinal.
rewrite Fset.equal_spec in Hsort |- *.
intro attribute; symmetry; exact (Hsort attribute).
Qed.

Definition option_numeric_eqb
    (first second : option numeric) : bool :=
  match first, second with
  | None, None => true
  | Some first, Some second => Oset.eq_bool Onumeric first second
  | _, _ => false
  end.

Definition value_conforms_attributeb
    (attribute : attribute TNull) (value : value TNull) : bool :=
  match attribute, value with
  | Attr_string _ expected, NullValues.Value_string (actual, payload) =>
      Oset.eq_bool OStringTypmod expected actual &&
      match payload with
      | None => true
      | Some text =>
          string_fits_typmod expected text &&
          String.eqb (string_canonical_value expected text) text
      end
  | Attr_decimal _ precision scale, NullValues.Value_numeric payload =>
      match payload with
      | None => true
      | Some number =>
          option_numeric_eqb
            (numeric_cast_typmod number precision scale) (Some number)
      end
  | Attr_date _, NullValues.Value_date payload =>
      match payload with
      | None => true
      | Some date => date_value_valid_bool date
      end
  | Attr_time _, NullValues.Value_time payload =>
      match payload with
      | None => true
      | Some time => time_in_range_bool time
      end
  | Attr_timestamp _ precision, NullValues.Value_timestamp payload
  | Attr_timestamptz _ precision, NullValues.Value_timestamptz payload =>
      match payload with
      | None => true
      | Some timestamp => timestamp_fits_precision_bool timestamp precision
      end
  | Attr_numeric _, NullValues.Value_numeric payload =>
      match payload with
      | None => true
      | Some number => numeric_runtime_fits_bool number
      end
  | Attr_Z _, NullValues.Value_Z _
  | Attr_int32 _, NullValues.Value_int32 _
  | Attr_int64 _, NullValues.Value_int64 _
  | Attr_bool _, NullValues.Value_bool _
  | Attr_float _, NullValues.Value_float _
  | Attr_double _, NullValues.Value_double _ => true
  | _, _ => false
  end.

Lemma option_numeric_eqb_true :
  forall first second,
    option_numeric_eqb first second = true -> first = second.
Proof.
intros [first|] [second|] Hequal; cbn in Hequal; try discriminate;
  try reflexivity.
apply Oset.eq_bool_true_iff in Hequal; now subst.
Qed.

Lemma value_conforms_attributeb_sound :
  forall attribute value,
    value_conforms_attributeb attribute value = true ->
    value_conforms_attribute attribute value.
Proof.
intros attribute value.
destruct attribute;
  destruct value as
    [string | integer | integer32 | integer64 | boolean | float | double
    | number | date | time | timestamp | timestamptz];
  cbn; try discriminate; try trivial.
- destruct string as [actual [text|]].
  + rewrite andb_true_iff; intros [Htypmod Htext].
    apply Oset.eq_bool_true_iff in Htypmod; subst actual.
    rewrite andb_true_iff in Htext.
    destruct Htext as [Hfits Hcanonical].
    apply String.eqb_eq in Hcanonical; now split.
  + intros Htypmod.
    apply andb_true_iff in Htypmod as [Htypmod _].
    apply Oset.eq_bool_true_iff in Htypmod; now subst actual.
- destruct number as [number|]; cbn.
  + intro Hnumber; exact Hnumber.
  + intros; exact I.
- destruct number as [number|]; cbn; try trivial.
  intro Hnumber.
  now apply option_numeric_eqb_true in Hnumber.
- destruct date; trivial.
- destruct time; trivial.
- destruct timestamp; trivial.
- destruct timestamptz; trivial.
Qed.

Definition tuple_conforms_sortb
    (sort : Fset.set (A TNull)) (row : tuple TNull) : bool :=
  Fset.equal (A TNull) (labels TNull row) sort &&
  Fset.for_all (A TNull)
    (fun attribute =>
      value_conforms_attributeb attribute (dot TNull row attribute)) sort.

Lemma tuple_conforms_sortb_sound :
  forall sort row,
    tuple_conforms_sortb sort row = true ->
    tuple_conforms_sort sort row.
Proof.
intros sort row Hconforms.
apply andb_true_iff in Hconforms as [Hlabels Hvalues].
split; [exact Hlabels|].
intros attribute Hattribute.
apply value_conforms_attributeb_sound.
rewrite Fset.for_all_spec_alt in Hvalues.
apply Hvalues; exact Hattribute.
Qed.

(** Check the exact canonical row list exposed by [witness_database]. *)
Fixpoint witness_values_conformb
    (expected : db_state) (tables : list witness_table) : bool :=
  match tables with
  | nil => true
  | table :: rest =>
      forallb
        (tuple_conforms_sortb
          (@_basesort TNull expected (witness_table_relation table)))
        (witness_instance_rows tables (witness_table_relation table)) &&
      witness_values_conformb expected rest
  end.

Definition value_is_nullb (value : value TNull) : bool :=
  NullValues.is_null_value value.

Definition row_attributes_not_nullb
    (attributes : list (attribute TNull)) (row : tuple TNull) : bool :=
  forallb
    (fun attribute => negb (value_is_nullb (dot TNull row attribute)))
    attributes.

Definition rows_attributes_not_nullb
    (attributes : list (attribute TNull))
    (rows : list (tuple TNull)) : bool :=
  forallb (row_attributes_not_nullb attributes) rows.

Lemma row_attributes_not_nullb_sound :
  forall attributes row,
    row_attributes_not_nullb attributes row = true ->
    row_attributes_not_null attributes row.
Proof.
intros attributes row Hnotnull attribute Hattribute.
unfold row_attributes_not_nullb in Hnotnull.
rewrite forallb_forall in Hnotnull.
specialize (Hnotnull attribute Hattribute).
apply negb_true_iff in Hnotnull; exact Hnotnull.
Qed.

Lemma rows_attributes_not_nullb_sound :
  forall attributes rows,
    rows_attributes_not_nullb attributes rows = true ->
    rows_attributes_not_null attributes rows.
Proof.
intros attributes rows Hnotnull row Hrow.
unfold rows_attributes_not_nullb in Hnotnull.
rewrite forallb_forall in Hnotnull.
now apply row_attributes_not_nullb_sound, Hnotnull.
Qed.

Definition sql_value_equal_trueb
    (first second : value TNull) : bool :=
  match NullValues.interp_predicate PredicateEq [first; second] with
  | true3 => true
  | false3 | unknown3 => false
  end.

Fixpoint sql_key_equal_trueb
    (first second : list (value TNull)) : bool :=
  match first, second with
  | nil, nil => true
  | left_value :: left_rest, right_value :: right_rest =>
      sql_value_equal_trueb left_value right_value &&
      sql_key_equal_trueb left_rest right_rest
  | _, _ => false
  end.

Lemma sql_value_equal_trueb_sound :
  forall first second,
    sql_value_equal_trueb first second = true ->
    sql_value_equal_true first second.
Proof.
intros first second.
unfold sql_value_equal_trueb, sql_value_equal_true.
now destruct (NullValues.interp_predicate PredicateEq [first; second]).
Qed.

Lemma sql_value_equal_trueb_iff :
  forall first second,
    sql_value_equal_trueb first second = true <->
    sql_value_equal_true first second.
Proof.
intros first second.
unfold sql_value_equal_trueb, sql_value_equal_true.
now destruct (NullValues.interp_predicate PredicateEq [first; second]).
Qed.

Lemma sql_key_equal_trueb_sound :
  forall first second,
    sql_key_equal_trueb first second = true ->
    sql_key_equal_true first second.
Proof.
induction first as [|first_head first_rest IH];
  intros [|second_head second_rest] Hequal;
  cbn in *; try discriminate; try trivial.
apply andb_true_iff in Hequal as [Hhead Hrest].
split; [now apply sql_value_equal_trueb_sound|now apply IH].
Qed.

Lemma sql_key_equal_trueb_iff :
  forall first second,
    sql_key_equal_trueb first second = true <->
    sql_key_equal_true first second.
Proof.
induction first as [|first_head first_rest IH];
  intros [|second_head second_rest];
  cbn; try (split; [discriminate|contradiction]); try tauto.
rewrite andb_true_iff, sql_value_equal_trueb_iff, IH.
tauto.
Qed.

Fixpoint no_relatedb {A : Type}
    (related : A -> A -> bool) (values : list A) : bool :=
  match values with
  | nil => true
  | first :: rest =>
      forallb (fun next => negb (related first next)) rest &&
      no_relatedb related rest
  end.

Lemma no_relatedb_sound :
  forall (A : Type) (relatedb : A -> A -> bool)
      (related : A -> A -> Prop) values,
    (forall first second,
      relatedb first second = true <-> related first second) ->
    no_relatedb relatedb values = true ->
    NoDupA related values.
Proof.
intros A relatedb related values Hsound.
induction values as [|first rest IH]; intro Hnodup; cbn in Hnodup.
- constructor.
- apply andb_true_iff in Hnodup as [Hfirst Hrest].
  constructor.
  + intro Hin.
    apply InA_alt in Hin as [next [Hrelated Hnext]].
    rewrite forallb_forall in Hfirst.
    specialize (Hfirst next Hnext).
    apply negb_true_iff in Hfirst.
    pose proof (proj2 (Hsound first next) Hrelated) as Htrue.
    rewrite Htrue in Hfirst; discriminate.
  + now apply IH.
Qed.

Definition list_nonemptyb {A : Type} (values : list A) : bool :=
  match values with nil => false | _ :: _ => true end.

Lemma list_nonemptyb_sound :
  forall (A : Type) (values : list A),
    list_nonemptyb values = true -> values <> nil.
Proof.
intros A [|first rest]; cbn; discriminate.
Qed.

Definition unique_key_rows_conformb
    (key : list (attribute TNull)) (rows : list (tuple TNull)) : bool :=
  no_relatedb sql_key_equal_trueb (map (project_row key) rows).

Lemma unique_key_rows_conformb_sound :
  forall key rows,
    unique_key_rows_conformb key rows = true ->
    unique_key_rows_conform key rows.
Proof.
intros key rows Hunique.
unfold unique_key_rows_conformb, unique_key_rows_conform.
eapply no_relatedb_sound; [exact sql_key_equal_trueb_iff|exact Hunique].
Qed.

Definition unique_key_conformsb
    (key : list (attribute TNull)) (rows : list (tuple TNull)) : bool :=
  list_nonemptyb key && unique_key_rows_conformb key rows.

Lemma unique_key_conformsb_sound :
  forall key rows,
    unique_key_conformsb key rows = true ->
    unique_key_conforms key rows.
Proof.
intros key rows Hunique.
apply andb_true_iff in Hunique as [Hnonempty Hrows].
split.
- now apply list_nonemptyb_sound.
- now apply unique_key_rows_conformb_sound.
Qed.

Definition primary_key_conformsb
    (key : list (attribute TNull)) (rows : list (tuple TNull)) : bool :=
  list_nonemptyb key &&
  (rows_attributes_not_nullb key rows &&
   unique_key_rows_conformb key rows).

Lemma primary_key_conformsb_sound :
  forall key rows,
    primary_key_conformsb key rows = true ->
    primary_key_conforms key rows.
Proof.
intros key rows Hprimary.
apply andb_true_iff in Hprimary as [Hnonempty Hrest].
apply andb_true_iff in Hrest as [Hnotnull Hunique].
split; [now apply list_nonemptyb_sound|].
split; [now apply rows_attributes_not_nullb_sound|].
now apply unique_key_rows_conformb_sound.
Qed.

Definition foreign_key_attribute_compatibleb
    (source referenced : attribute TNull) : bool :=
  match source, referenced with
  | Attr_string _ source_typmod, Attr_string _ referenced_typmod =>
      Oset.eq_bool OStringTypmod source_typmod referenced_typmod
  | Attr_Z _, Attr_Z _
  | Attr_int32 _, Attr_int32 _
  | Attr_int64 _, Attr_int64 _
  | Attr_int32 _, Attr_int64 _
  | Attr_int64 _, Attr_int32 _
  | Attr_bool _, Attr_bool _
  | Attr_float _, Attr_float _
  | Attr_double _, Attr_double _
  | Attr_numeric _, Attr_numeric _
  | Attr_date _, Attr_date _
  | Attr_time _, Attr_time _ => true
  | Attr_decimal _ source_precision source_scale,
      Attr_decimal _ referenced_precision referenced_scale =>
      Z.eqb source_precision referenced_precision &&
      Z.eqb source_scale referenced_scale
  | Attr_timestamp _ source_precision,
      Attr_timestamp _ referenced_precision
  | Attr_timestamptz _ source_precision,
      Attr_timestamptz _ referenced_precision =>
      Z.eqb source_precision referenced_precision
  | _, _ => false
  end.

Lemma foreign_key_attribute_compatibleb_sound :
  forall source referenced,
    foreign_key_attribute_compatibleb source referenced = true ->
    foreign_key_attribute_compatible source referenced.
Proof.
intros source referenced.
destruct source; destruct referenced; cbn; try discriminate; try trivial.
- intro Htypmod; now apply Oset.eq_bool_true_iff in Htypmod.
- rewrite andb_true_iff; intros [Hprecision Hscale].
  now apply Z.eqb_eq in Hprecision; apply Z.eqb_eq in Hscale.
- intro Hprecision; now apply Z.eqb_eq in Hprecision.
- intro Hprecision; now apply Z.eqb_eq in Hprecision.
Qed.

Definition foreign_key_value_equal_trueb
    (source_attribute referenced_attribute : attribute TNull)
    (source_value referenced_value : value TNull) : bool :=
  foreign_key_attribute_compatibleb source_attribute referenced_attribute &&
  (value_conforms_attributeb source_attribute source_value &&
   (value_conforms_attributeb referenced_attribute referenced_value &&
    sql_value_equal_trueb source_value referenced_value)).

Lemma foreign_key_value_equal_trueb_sound :
  forall source_attribute referenced_attribute source_value referenced_value,
    foreign_key_value_equal_trueb
      source_attribute referenced_attribute source_value referenced_value = true ->
    foreign_key_value_equal_true
      source_attribute referenced_attribute source_value referenced_value.
Proof.
intros source_attribute referenced_attribute source_value referenced_value H.
apply andb_true_iff in H as [Hcompatible Hrest].
apply andb_true_iff in Hrest as [Hsource Hrest].
apply andb_true_iff in Hrest as [Hreferenced Hequal].
repeat split.
- now apply foreign_key_attribute_compatibleb_sound.
- now apply value_conforms_attributeb_sound.
- now apply value_conforms_attributeb_sound.
- now apply sql_value_equal_trueb_sound.
Qed.

Fixpoint foreign_key_key_equal_trueb
    (source_attributes referenced_attributes : list (attribute TNull))
    (source_row referenced_row : tuple TNull) : bool :=
  match source_attributes, referenced_attributes with
  | nil, nil => true
  | source_attribute :: source_rest,
      referenced_attribute :: referenced_rest =>
      foreign_key_value_equal_trueb source_attribute referenced_attribute
        (dot TNull source_row source_attribute)
        (dot TNull referenced_row referenced_attribute) &&
      foreign_key_key_equal_trueb source_rest referenced_rest
        source_row referenced_row
  | _, _ => false
  end.

Lemma foreign_key_key_equal_trueb_sound :
  forall source_attributes referenced_attributes source_row referenced_row,
    foreign_key_key_equal_trueb source_attributes referenced_attributes
      source_row referenced_row = true ->
    foreign_key_key_equal_true source_attributes referenced_attributes
      source_row referenced_row.
Proof.
induction source_attributes as [|source source_rest IH];
  intros [|referenced referenced_rest] source_row referenced_row Hequal;
  cbn in *; try discriminate; try trivial.
apply andb_true_iff in Hequal as [Hhead Hrest].
split; [now apply foreign_key_value_equal_trueb_sound|now apply IH].
Qed.

Definition foreign_key_row_conforms_againstb
    (foreign_key : foreign_key_constraint)
    (referencing_row : tuple TNull)
    (referenced_rows : list (tuple TNull)) : bool :=
  existsb
    (fun attribute => value_is_nullb (dot TNull referencing_row attribute))
    (foreign_key_columns foreign_key) ||
  existsb
    (fun referenced_row =>
      foreign_key_key_equal_trueb
        (foreign_key_columns foreign_key)
        (foreign_key_referenced_columns foreign_key)
        referencing_row referenced_row)
    referenced_rows.

Lemma foreign_key_row_conforms_againstb_sound :
  forall foreign_key referencing_row referenced_rows,
    foreign_key_row_conforms_againstb
      foreign_key referencing_row referenced_rows = true ->
    foreign_key_row_conforms_against
      foreign_key referencing_row referenced_rows.
Proof.
intros foreign_key referencing_row referenced_rows Hconforms.
apply orb_true_iff in Hconforms as [Hnull|Hmatch].
- left.
  rewrite existsb_exists in Hnull.
  destruct Hnull as [attribute [Hattribute Hnull]].
  now exists attribute.
- right.
  rewrite existsb_exists in Hmatch.
  destruct Hmatch as [referenced_row [Hrow Hequal]].
  exists referenced_row; split; [exact Hrow|].
  now apply foreign_key_key_equal_trueb_sound.
Qed.

Definition foreign_key_conformsb
    (tables : list witness_table) (rows : list (tuple TNull))
    (foreign_key : foreign_key_constraint) : bool :=
  list_nonemptyb (foreign_key_columns foreign_key) &&
  (Nat.eqb
     (length (foreign_key_columns foreign_key))
     (length (foreign_key_referenced_columns foreign_key)) &&
   forallb
     (fun row =>
       foreign_key_row_conforms_againstb foreign_key row
         (witness_instance_rows tables
           (foreign_key_referenced_relation foreign_key)))
     rows).

Lemma foreign_key_conformsb_sound :
  forall expected tables rows foreign_key,
    foreign_key_conformsb tables rows foreign_key = true ->
    foreign_key_conforms
      (witness_database expected tables) rows foreign_key.
Proof.
intros expected tables rows foreign_key Hconforms.
apply andb_true_iff in Hconforms as [Hnonempty Hrest].
apply andb_true_iff in Hrest as [Hlength Hrows].
split; [now apply list_nonemptyb_sound|].
split; [now apply Nat.eqb_eq|].
intros row Hrow.
rewrite forallb_forall in Hrows.
apply foreign_key_row_conforms_againstb_sound.
specialize (Hrows row Hrow).
now rewrite witness_database_instance_rows.
Qed.

Fixpoint attribute_list_eqb
    (first second : list (attribute TNull)) : bool :=
  match first, second with
  | nil, nil => true
  | first_head :: first_rest, second_head :: second_rest =>
      Oset.eq_bool OAN first_head second_head &&
      attribute_list_eqb first_rest second_rest
  | _, _ => false
  end.

Lemma attribute_list_eqb_true :
  forall first second,
    attribute_list_eqb first second = true -> first = second.
Proof.
induction first as [|first_head first_rest IH];
  intros [|second_head second_rest] Hequal;
  cbn in Hequal; try discriminate; [reflexivity|].
apply andb_true_iff in Hequal as [Hhead Hrest].
apply Oset.eq_bool_true_iff in Hhead; subst second_head.
f_equal; now apply IH.
Qed.

Fixpoint compatible_attribute_listsb
    (source referenced : list (attribute TNull)) : bool :=
  match source, referenced with
  | nil, nil => true
  | source_head :: source_rest, referenced_head :: referenced_rest =>
      foreign_key_attribute_compatibleb source_head referenced_head &&
      compatible_attribute_listsb source_rest referenced_rest
  | _, _ => false
  end.

Lemma compatible_attribute_listsb_sound :
  forall source referenced,
    compatible_attribute_listsb source referenced = true ->
    Forall2 foreign_key_attribute_compatible source referenced.
Proof.
induction source as [|source_head source_rest IH];
  intros [|referenced_head referenced_rest] Hcompatible;
  cbn in Hcompatible; try discriminate; [constructor|].
apply andb_true_iff in Hcompatible as [Hhead Hrest].
constructor.
- now apply foreign_key_attribute_compatibleb_sound.
- now apply IH.
Qed.

Definition table_declares_unique_keyb
    (constraint : table_constraint)
    (key : list (attribute TNull)) : bool :=
  match constraint_primary_key constraint with
  | Some primary => attribute_list_eqb primary key
  | None => false
  end ||
  existsb (fun unique => attribute_list_eqb unique key)
    (constraint_unique_keys constraint).

Lemma table_declares_unique_keyb_sound :
  forall constraint key,
    table_declares_unique_keyb constraint key = true ->
    table_declares_unique_key constraint key.
Proof.
intros constraint key Hdeclares.
apply orb_true_iff in Hdeclares as [Hprimary|Hunique].
- left.
  destruct (constraint_primary_key constraint) as [primary|] eqn:Hkey;
    cbn in Hprimary; try discriminate.
  apply attribute_list_eqb_true in Hprimary; now subst primary.
- right.
  rewrite existsb_exists in Hunique.
  destruct Hunique as [unique [Hin Hequal]].
  apply attribute_list_eqb_true in Hequal; now subst unique.
Qed.

Definition foreign_key_reference_well_formedb
    (constraints : list table_constraint)
    (foreign_key : foreign_key_constraint) : bool :=
  list_nonemptyb (foreign_key_columns foreign_key) &&
  (Nat.eqb
     (length (foreign_key_columns foreign_key))
     (length (foreign_key_referenced_columns foreign_key)) &&
   (compatible_attribute_listsb
      (foreign_key_columns foreign_key)
      (foreign_key_referenced_columns foreign_key) &&
    existsb
      (fun referenced_constraint =>
        Oset.eq_bool ORN
          (constraint_relation referenced_constraint)
          (foreign_key_referenced_relation foreign_key) &&
        table_declares_unique_keyb referenced_constraint
          (foreign_key_referenced_columns foreign_key))
      constraints)).

Lemma foreign_key_reference_well_formedb_sound :
  forall constraints foreign_key,
    foreign_key_reference_well_formedb constraints foreign_key = true ->
    foreign_key_reference_well_formed constraints foreign_key.
Proof.
intros constraints foreign_key Hwellformed.
apply andb_true_iff in Hwellformed as [Hnonempty Hrest].
apply andb_true_iff in Hrest as [Hlength Hrest].
apply andb_true_iff in Hrest as [Hcompatible Hreference].
split; [now apply list_nonemptyb_sound|].
split; [now apply Nat.eqb_eq|].
split; [now apply compatible_attribute_listsb_sound|].
rewrite existsb_exists in Hreference.
destruct Hreference as [constraint [Hin Hconstraint]].
apply andb_true_iff in Hconstraint as [Hrelation Hkey].
apply Oset.eq_bool_true_iff in Hrelation.
exists constraint; repeat split; try assumption.
now apply table_declares_unique_keyb_sound.
Qed.

Definition option_key_nonemptyb
    (key : option (list (attribute TNull))) : bool :=
  match key with None => true | Some key => list_nonemptyb key end.

Definition table_constraint_declarations_well_formedb
    (constraints : list table_constraint)
    (constraint : table_constraint) : bool :=
  option_key_nonemptyb (constraint_primary_key constraint) &&
  (forallb list_nonemptyb (constraint_unique_keys constraint) &&
   (forallb (foreign_key_reference_well_formedb constraints)
      (constraint_foreign_keys constraint) &&
    forallb
      (fun index => list_nonemptyb (unique_index_terms index))
      (constraint_unique_indexes constraint))).

Lemma table_constraint_declarations_well_formedb_sound :
  forall constraints constraint,
    table_constraint_declarations_well_formedb constraints constraint = true ->
    table_constraint_declarations_well_formed constraints constraint.
Proof.
intros constraints constraint Hwellformed.
apply andb_true_iff in Hwellformed as [Hprimary Hrest].
apply andb_true_iff in Hrest as [Hunique Hrest].
apply andb_true_iff in Hrest as [Hforeign Hindexes].
repeat split.
- destruct (constraint_primary_key constraint) as [key|] eqn:Hkey;
    cbn in Hprimary; trivial.
  now apply list_nonemptyb_sound.
- rewrite Forall_forall; intros key Hkey.
  rewrite forallb_forall in Hunique.
  now apply list_nonemptyb_sound, Hunique.
- rewrite Forall_forall; intros foreign_key Hforeign_key.
  rewrite forallb_forall in Hforeign.
  now apply foreign_key_reference_well_formedb_sound, Hforeign.
- rewrite Forall_forall; intros index Hindex.
  rewrite forallb_forall in Hindexes.
  now apply list_nonemptyb_sound, Hindexes.
Qed.

Definition schema_constraints_well_formedb
    (constraints : list table_constraint) : bool :=
  forallb
    (table_constraint_declarations_well_formedb constraints) constraints.

Lemma schema_constraints_well_formedb_sound :
  forall constraints,
    schema_constraints_well_formedb constraints = true ->
    schema_constraints_well_formed constraints.
Proof.
intros constraints Hwellformed.
unfold schema_constraints_well_formed.
rewrite Forall_forall; intros constraint Hconstraint.
unfold schema_constraints_well_formedb in Hwellformed.
rewrite forallb_forall in Hwellformed.
now apply table_constraint_declarations_well_formedb_sound, Hwellformed.
Qed.

Definition option_primary_key_conformsb
    (key : option (list (attribute TNull)))
    (rows : list (tuple TNull)) : bool :=
  match key with
  | None => true
  | Some key => primary_key_conformsb key rows
  end.

(** CHECK constraints and partial/expression unique indexes remain fail-closed
    for nonempty witness tables. On an empty table, CHECK obligations are
    vacuous and a unique index conforms once its declaration has a nonempty
    term list; no predicate or term is evaluated. *)
Definition deferred_row_constraints_conformb
    (rows : list (tuple TNull))
    (checks : list check_constraint)
    (indexes : list unique_index_constraint) : bool :=
  match rows with
  | nil =>
      forallb
        (fun index => list_nonemptyb (unique_index_terms index)) indexes
  | _ :: _ =>
      match checks with nil => true | _ => false end &&
      match indexes with nil => true | _ => false end
  end.

Lemma deferred_row_constraints_conformb_sound :
  forall db rows checks indexes,
    deferred_row_constraints_conformb rows checks indexes = true ->
    Forall (check_constraint_conforms db rows) checks /\
    Forall (unique_index_conforms db rows) indexes.
Proof.
intros db [|row rows] checks indexes Hconforms.
- split.
  + rewrite Forall_forall; intros check _.
    unfold check_constraint_conforms; constructor.
  + rewrite Forall_forall; intros index Hindex.
    unfold deferred_row_constraints_conformb in Hconforms.
    rewrite forallb_forall in Hconforms.
    specialize (Hconforms index Hindex).
    apply list_nonemptyb_sound in Hconforms.
    unfold unique_index_conforms.
    repeat split; try assumption; try (intros value Hvalue; contradiction).
    constructor.
- unfold deferred_row_constraints_conformb in Hconforms.
  destruct checks as [|check checks], indexes as [|index indexes];
    cbn in Hconforms; try discriminate; split; constructor.
Qed.

Definition rows_constraint_conformb
    (expected : db_state) (tables : list witness_table)
    (constraint : table_constraint) : bool :=
  let rows :=
    witness_instance_rows tables (constraint_relation constraint) in
  rows_attributes_not_nullb (constraint_not_null constraint) rows &&
  (option_primary_key_conformsb
     (constraint_primary_key constraint) rows &&
   (forallb (fun key => unique_key_conformsb key rows)
      (constraint_unique_keys constraint) &&
    (forallb (foreign_key_conformsb tables rows)
       (constraint_foreign_keys constraint) &&
     deferred_row_constraints_conformb
       rows
       (constraint_checks constraint)
       (constraint_unique_indexes constraint)))).

Lemma rows_constraint_conformb_sound :
  forall expected tables constraint,
    rows_constraint_conformb expected tables constraint = true ->
    table_constraint_conforms
      (witness_database expected tables) constraint.
Proof.
intros expected tables constraint Hconforms.
unfold rows_constraint_conformb in Hconforms.
apply andb_true_iff in Hconforms as [Hnotnull Hrest].
apply andb_true_iff in Hrest as [Hprimary Hrest].
apply andb_true_iff in Hrest as [Hunique Hrest].
apply andb_true_iff in Hrest as [Hforeign Hrest].
pose proof
  (deferred_row_constraints_conformb_sound
    (witness_database expected tables)
    (witness_instance_rows tables (constraint_relation constraint))
    (constraint_checks constraint)
    (constraint_unique_indexes constraint)
    Hrest) as [Hchecks Hindexes].
unfold table_constraint_conforms, rows_constraint_conform.
rewrite witness_database_instance_rows.
repeat split.
- now apply rows_attributes_not_nullb_sound.
- destruct (constraint_primary_key constraint) as [key|] eqn:Hkey;
    cbn in Hprimary; trivial.
  now apply primary_key_conformsb_sound.
- rewrite Forall_forall; intros key Hkey.
  rewrite forallb_forall in Hunique.
  now apply unique_key_conformsb_sound, Hunique.
- rewrite Forall_forall; intros foreign_key Hforeign_key.
  rewrite forallb_forall in Hforeign.
  now apply (foreign_key_conformsb_sound expected), Hforeign.
- exact Hchecks.
- exact Hindexes.
Qed.

Definition schema_constraints_conformb
    (expected : db_state) (tables : list witness_table)
    (constraints : list table_constraint) : bool :=
  schema_constraints_well_formedb constraints &&
  forallb (rows_constraint_conformb expected tables) constraints.

Lemma schema_constraints_conformb_sound :
  forall expected tables constraints,
    schema_constraints_conformb expected tables constraints = true ->
    schema_constraints_conform
      (witness_database expected tables) constraints.
Proof.
intros expected tables constraints Hconforms.
apply andb_true_iff in Hconforms as [Hwellformed Htables].
split; [now apply schema_constraints_well_formedb_sound|].
rewrite Forall_forall; intros constraint Hconstraint.
rewrite forallb_forall in Htables.
now apply rows_constraint_conformb_sound, Htables.
Qed.

Lemma witness_values_conformb_lookup_sound :
  forall expected tables relation row,
    witness_values_conformb expected tables = true ->
    In row (witness_instance_rows tables relation) ->
    tuple_conforms_sort (@_basesort TNull expected relation) row.
Proof.
intros expected tables.
induction tables as [|table rest IH]; intros relation row Hconforms Hrow.
- unfold witness_instance_rows, witness_rows_for in Hrow.
  rewrite Febag.elements_empty in Hrow; contradiction.
- cbn in Hconforms.
  apply andb_true_iff in Hconforms as [Hhead Htail].
  unfold witness_instance_rows in Hrow |- *.
  cbn [witness_rows_for] in Hrow.
  destruct (Oset.eq_bool ORN relation (witness_table_relation table))
    eqn:Hrelation.
  + apply Oset.eq_bool_true_iff in Hrelation; subst relation.
    rewrite Oset.eq_bool_refl in Hhead.
    rewrite forallb_forall in Hhead.
    apply tuple_conforms_sortb_sound.
    apply Hhead; exact Hrow.
  + eapply IH; [exact Htail|exact Hrow].
Qed.

Lemma witness_values_conformb_sound :
  forall expected tables,
    witness_values_conformb expected tables = true ->
    database_values_conform (witness_database expected tables).
Proof.
intros expected tables Hconforms relation row Hrow.
change (In row (witness_instance_rows tables relation)) in Hrow.
exact
  (witness_values_conformb_lookup_sound
    expected tables relation row Hconforms Hrow).
Qed.

(** [witness_rows_for] gives every omitted relation the empty row list.  A
    generated witness may therefore store only nonempty tables: value and
    constraint checks below still range over the complete expected schema,
    and constraints on omitted tables are checked against the exact empty
    instance.  The host generator separately binds the sparse list to a
    complete typed PostgreSQL snapshot before emitting this certificate. *)
Definition witness_database_conformsb
    (expected : db_state) (constraints : list table_constraint)
    (tables : list witness_table) : bool :=
  witness_values_conformb expected tables &&
  schema_constraints_conformb expected tables constraints.

Theorem witness_database_conformsb_sound :
  forall expected constraints tables,
    witness_database_conformsb expected constraints tables = true ->
    database_conforms_schema expected constraints
      (witness_database expected tables).
Proof.
intros expected constraints tables Hconforms.
apply andb_true_iff in Hconforms as [Hvalues Hconstraints].
unfold database_conforms_schema.
split; [reflexivity|].
split.
- intro relation.
  change
    (@_basesort TNull expected relation =S=
     @_basesort TNull expected relation).
  apply Fset.equal_refl.
- split.
  + now apply witness_values_conformb_sound.
  + now apply schema_constraints_conformb_sound.
Qed.
