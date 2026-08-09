(************************************************************************************)
(** Finite-domain cardinality facts for conforming PostgreSQL INTEGER keys.        *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet ValueInteger SchemaConstraints.
From Stdlib Require Import List String ZArith NArith Lia.

Import ListNotations.
Import Tuple.

(** There are exactly [2^32] PostgreSQL INTEGER values. *)
Definition int32_domain_size : nat := Z.to_nat int32_modulus.

Lemma int32_domain_size_spec :
  Z.of_nat int32_domain_size = int32_modulus.
Proof.
unfold int32_domain_size.
rewrite Z2Nat.id; [reflexivity |].
unfold int32_modulus; lia.
Qed.

(** Keep the large natural symbolic.  Expanding its binary numeral through
    [seq] or arithmetic normalization is unnecessary and needlessly costly. *)
Opaque int32_domain_size.

Lemma int32_domain_size_is_two_power_32 :
  Z.of_nat int32_domain_size = Z.pow 2 32.
Proof.
rewrite int32_domain_size_spec.
reflexivity.
Qed.

(** A convenient row-local form of the database value-conformance premise. *)
Definition rows_attribute_conform
    (attribute : attribute TNull) (rows : list (tuple TNull)) : Prop :=
  forall row,
    In row rows ->
    value_conforms_attribute attribute (dot TNull row attribute).

(** Transport a typed-cell fact from a generated expected schema to an actual
    database.  Attribute membership is checked against the expected basesort;
    [database_conforms_schema_basesort] is the only bridge to the actual one. *)
Lemma database_conforms_schema_typed_cell :
  forall expected constraints actual relation row attribute,
    database_conforms_schema expected constraints actual ->
    In row (instance_rows actual relation) ->
    attribute inS (@_basesort TNull expected relation) ->
    value_conforms_attribute attribute (dot TNull row attribute).
Proof.
intros expected constraints actual relation row attribute
  Hschema Hrow Hattribute.
pose proof
  (database_conforms_schema_values expected constraints actual Hschema)
  as Hvalues.
specialize (Hvalues relation row Hrow) as [_ Htyped].
apply Htyped.
pose proof
  (database_conforms_schema_basesort expected constraints actual Hschema
    relation) as Hbasesort.
rewrite Fset.equal_spec in Hbasesort.
rewrite Hbasesort.
exact Hattribute.
Qed.

Lemma rows_attribute_conform_from_database :
  forall expected constraints actual relation attribute,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    rows_attribute_conform attribute (instance_rows actual relation).
Proof.
intros expected constraints actual relation attribute Hschema Hattribute
  row Hrow.
eapply database_conforms_schema_typed_cell; eassumption.
Qed.

(** INT32 conformance fixes the value constructor.  The additional non-NULL
    fact fixes its option payload to [Some]. *)
Lemma conforming_int32_value :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    exists payload, value = NullValues.Value_int32 payload.
Proof.
intros name value Hconforms.
destruct value; cbn in Hconforms; try contradiction.
eexists; reflexivity.
Qed.

Lemma conforming_nonnull_int32_value :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    NullValues.is_null_value value = false ->
    exists integer, value = NullValues.Value_int32 (Some integer).
Proof.
intros name value Hconforms Hnonnull.
destruct (conforming_int32_value name value Hconforms)
  as [payload ->].
destruct payload as [integer |]; cbn in Hnonnull.
- now eexists.
- discriminate.
Qed.

(** The only bridge from typed PostgreSQL equality to Rocq self-equality used
    by the cardinality development.  It is intentionally restricted to
    conforming, non-NULL INTEGER values. *)
Lemma sql_value_equal_true_int32_refl :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    NullValues.is_null_value value = false ->
    sql_value_equal_true value value.
Proof.
intros name value Htyped Hnonnull.
destruct (conforming_nonnull_int32_value name value Htyped Hnonnull)
  as [integer ->].
unfold sql_value_equal_true.
cbn.
now rewrite Z.compare_refl.
Qed.

(** Shift the signed carrier into its finite zero-based ordinal. *)
Definition int32_index (integer : int32) : nat :=
  Z.to_nat (int32_value integer - int32_min).

Lemma int32_index_lt :
  forall integer, (int32_index integer < int32_domain_size)%nat.
Proof.
intro integer.
destruct (int32_range integer) as [Hminimum Hmaximum].
apply Nat2Z.inj_lt.
rewrite int32_domain_size_spec.
unfold int32_index.
rewrite Z2Nat.id.
- unfold int32_min, int32_max, int32_modulus in *; lia.
- unfold int32_min in *; lia.
Qed.

Lemma int32_index_in_domain :
  forall integer,
    In (int32_index integer) (seq 0 int32_domain_size).
Proof.
intro integer.
rewrite in_seq.
split; [lia |].
pose proof (int32_index_lt integer).
lia.
Qed.

Lemma int32_index_injective :
  forall left right,
    int32_index left = int32_index right ->
    left = right.
Proof.
intros left right Hequal.
apply int32_ext.
unfold int32_index in Hequal.
apply (f_equal Z.of_nat) in Hequal.
assert (Hleft : 0 <= int32_value left - int32_min).
{
  destruct (int32_range left); unfold int32_min in *; lia.
}
assert (Hright : 0 <= int32_value right - int32_min).
{
  destruct (int32_range right); unfold int32_min in *; lia.
}
rewrite (Z2Nat.id _ Hleft), (Z2Nat.id _ Hright) in Hequal.
lia.
Qed.

Definition int32_value_index (value : value TNull) : nat :=
  match value with
  | NullValues.Value_int32 (Some integer) => int32_index integer
  | _ => 0%nat
  end.

Lemma conforming_nonnull_int32_index_lt :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    NullValues.is_null_value value = false ->
    (int32_value_index value < int32_domain_size)%nat.
Proof.
intros name value Htyped Hnonnull.
destruct (conforming_nonnull_int32_value name value Htyped Hnonnull)
  as [integer ->].
cbn [int32_value_index].
apply int32_index_lt.
Qed.

Lemma conforming_nonnull_int32_index_in_domain :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    NullValues.is_null_value value = false ->
    In (int32_value_index value) (seq 0 int32_domain_size).
Proof.
intros name value Htyped Hnonnull.
rewrite in_seq.
split; [lia |].
now apply (conforming_nonnull_int32_index_lt name value).
Qed.

Lemma conforming_nonnull_int32_index_eq_iff :
  forall name left right,
    value_conforms_attribute (Attr_int32 name) left ->
    value_conforms_attribute (Attr_int32 name) right ->
    NullValues.is_null_value left = false ->
    NullValues.is_null_value right = false ->
    (int32_value_index left = int32_value_index right <-> left = right).
Proof.
intros name left right Hleft Hright Hleft_nonnull Hright_nonnull.
destruct (conforming_nonnull_int32_value name left Hleft Hleft_nonnull)
  as [left_integer ->].
destruct (conforming_nonnull_int32_value name right Hright Hright_nonnull)
  as [right_integer ->].
cbn [int32_value_index].
split.
- intro Hequal.
  now rewrite (int32_index_injective left_integer right_integer Hequal).
- now inversion 1.
Qed.

(** A list-local injection is enough to transport [NoDup].  Requiring key
    equality, rather than row equality, is what lets this consume precisely
    the [primary_key_conforms] projection. *)
Lemma NoDup_map_by_key :
  forall (row key code_type : Type)
         (key_of : row -> key) (code : row -> code_type) rows,
    NoDup (map key_of rows) ->
    (forall left right,
      In left rows ->
      In right rows ->
      code left = code right ->
      key_of left = key_of right) ->
    NoDup (map code rows).
Proof.
intros row key code_type key_of code rows Hkeys.
induction rows as [|first rest IH]; intro Hinjective; cbn in *.
- constructor.
- inversion Hkeys as [|first_key rest_keys Hfirst Hrest]; subst.
  constructor.
  + intros Hcode.
    apply in_map_iff in Hcode as [other [Hequal Hother]].
    apply Hfirst.
    apply in_map_iff.
    exists other; split; [|exact Hother].
    symmetry.
    eapply Hinjective.
    * now left.
    * now right.
    * exact (eq_sym Hequal).
  + apply IH; [exact Hrest |].
    intros left right Hleft Hright Hequal.
    eapply Hinjective; [right | right | exact Hequal]; assumption.
Qed.

(** Singleton complete INT32 primary keys. *)
Lemma int32_singleton_primary_key_projection_nodup :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    NoDup (map (project_row [Attr_int32 name]) rows).
Proof.
intros name rows Htyped Hprimary.
apply (primary_key_conforms_nodup _ _ Hprimary).
intros key_values Hkey.
apply in_map_iff in Hkey as [row [<- Hrow]].
rewrite project_row_cons, project_row_nil.
split.
- apply (sql_value_equal_true_int32_refl name).
  + now apply Htyped.
  + eapply primary_key_conforms_not_null; eauto.
    now left.
- exact I.
Qed.

Lemma int32_singleton_primary_key_codes_nodup :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    NoDup
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 name)))
        rows).
Proof.
intros name rows Htyped Hprimary.
pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
pose proof
  (int32_singleton_primary_key_projection_nodup name rows Htyped Hprimary)
  as Hkeys.
eapply NoDup_map_by_key with
  (key_of := project_row [Attr_int32 name]); [exact Hkeys |].
intros left right Hleft Hright Hequal.
rewrite !project_row_cons, !project_row_nil.
destruct
  (conforming_nonnull_int32_index_eq_iff name
    (dot TNull left (Attr_int32 name))
    (dot TNull right (Attr_int32 name))
    (Htyped left Hleft)
    (Htyped right Hright)
    (Hnonnull left Hleft (Attr_int32 name) (or_introl eq_refl))
    (Hnonnull right Hright (Attr_int32 name) (or_introl eq_refl)))
  as [Hforward _].
now rewrite (Hforward Hequal).
Qed.

Theorem int32_singleton_primary_key_length :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    (List.length rows <= int32_domain_size)%nat.
Proof.
intros name rows Htyped Hprimary.
pose proof
  (int32_singleton_primary_key_codes_nodup name rows Htyped Hprimary)
  as Hcodes.
assert
  (Hinside :
    incl
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 name)))
        rows)
      (seq 0 int32_domain_size)).
{
  intros code Hcode.
  apply in_map_iff in Hcode as [row [<- Hrow]].
  pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
  apply (conforming_nonnull_int32_index_in_domain name).
  - now apply Htyped.
  - exact
      (Hnonnull row Hrow (Attr_int32 name) (or_introl eq_refl)).
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
rewrite length_map, length_seq in Hlength.
exact Hlength.
Qed.

Corollary int32_singleton_primary_key_length_2_32 :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    Z.of_nat (List.length rows) <= Z.pow 2 32.
Proof.
intros name rows Htyped Hprimary.
pose proof
  (int32_singleton_primary_key_length name rows Htyped Hprimary)
  as Hlength.
apply Nat2Z.inj_le in Hlength.
now rewrite int32_domain_size_is_two_power_32 in Hlength.
Qed.

(** The Cartesian product of two duplicate-free finite enumerations is also
    duplicate-free.  This generic list fact keeps the two-key bound symbolic. *)
Lemma NoDup_map_fixed_pair :
  forall (left right : Type) (fixed : left) (values : list right),
    NoDup values ->
    NoDup (map (fun value => (fixed, value)) values).
Proof.
intros left right fixed values Hvalues.
induction Hvalues as [|first rest Hfirst Hrest IH]; cbn.
- constructor.
- constructor; [|exact IH].
  intros Hin.
  apply in_map_iff in Hin as [other [Hequal Hother]].
  injection Hequal as Hequal.
  subst other.
  now apply Hfirst.
Qed.

Lemma NoDup_list_prod :
  forall (left right : Type) (lefts : list left) (rights : list right),
    NoDup lefts ->
    NoDup rights ->
    NoDup (list_prod lefts rights).
Proof.
intros left right lefts rights Hlefts Hrights.
induction Hlefts as [|first rest Hfirst Hrest IH]; cbn.
- constructor.
- apply NoDup_app.
  + now apply NoDup_map_fixed_pair.
  + now apply IH.
  + intros [left_value right_value] Hin_head Hin_tail.
    apply in_map_iff in Hin_head as
      [right_source [Hequal Hright_source]].
    inversion Hequal; subst left_value right_value.
    apply in_prod_iff in Hin_tail as [Hfirst_in_rest _].
    now apply Hfirst.
Qed.

(** Complete two-column INT32 keys use the Cartesian product of two symbolic
    finite domains. *)
Definition int32_pair_index (first second : int32) : nat * nat :=
  (int32_index first, int32_index second).

Lemma int32_pair_index_injective :
  forall first_left second_left first_right second_right,
    int32_pair_index first_left second_left =
      int32_pair_index first_right second_right ->
    first_left = first_right /\ second_left = second_right.
Proof.
intros first_left second_left first_right second_right Hequal.
injection Hequal as Hfirst Hsecond.
split; now apply int32_index_injective.
Qed.

Definition int32_value_pair_index
    (first second : value TNull) : nat * nat :=
  match first, second with
  | NullValues.Value_int32 (Some first_integer),
    NullValues.Value_int32 (Some second_integer) =>
      int32_pair_index first_integer second_integer
  | _, _ => (0%nat, 0%nat)
  end.

Lemma conforming_nonnull_int32_pair_index_eq :
  forall first_name second_name
         first_left second_left first_right second_right,
    value_conforms_attribute (Attr_int32 first_name) first_left ->
    value_conforms_attribute (Attr_int32 second_name) second_left ->
    value_conforms_attribute (Attr_int32 first_name) first_right ->
    value_conforms_attribute (Attr_int32 second_name) second_right ->
    NullValues.is_null_value first_left = false ->
    NullValues.is_null_value second_left = false ->
    NullValues.is_null_value first_right = false ->
    NullValues.is_null_value second_right = false ->
    int32_value_pair_index first_left second_left =
      int32_value_pair_index first_right second_right ->
    first_left = first_right /\ second_left = second_right.
Proof.
intros first_name second_name
  first_left second_left first_right second_right
  Hfirst_left Hsecond_left Hfirst_right Hsecond_right
  Hfirst_left_nonnull Hsecond_left_nonnull
  Hfirst_right_nonnull Hsecond_right_nonnull Hequal.
destruct
  (conforming_nonnull_int32_value first_name first_left
    Hfirst_left Hfirst_left_nonnull) as [first_left_integer ->].
destruct
  (conforming_nonnull_int32_value second_name second_left
    Hsecond_left Hsecond_left_nonnull) as [second_left_integer ->].
destruct
  (conforming_nonnull_int32_value first_name first_right
    Hfirst_right Hfirst_right_nonnull) as [first_right_integer ->].
destruct
  (conforming_nonnull_int32_value second_name second_right
    Hsecond_right Hsecond_right_nonnull) as [second_right_integer ->].
cbn [int32_value_pair_index] in Hequal.
destruct
  (int32_pair_index_injective
    first_left_integer second_left_integer
    first_right_integer second_right_integer Hequal).
now subst.
Qed.

Lemma int32_composite_primary_key_projection_nodup :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    NoDup
      (map
        (project_row [Attr_int32 first_name; Attr_int32 second_name])
        rows).
Proof.
intros first_name second_name rows Hfirst_typed Hsecond_typed Hprimary.
pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
apply (primary_key_conforms_nodup _ _ Hprimary).
intros key_values Hkey.
apply in_map_iff in Hkey as [row [<- Hrow]].
rewrite !project_row_cons, project_row_nil.
split.
- apply (sql_value_equal_true_int32_refl first_name).
  + now apply Hfirst_typed.
  + eapply Hnonnull; [exact Hrow|now left].
- split.
  + apply (sql_value_equal_true_int32_refl second_name).
    * now apply Hsecond_typed.
    * eapply Hnonnull; [exact Hrow|now right; left].
  + exact I.
Qed.

Lemma int32_composite_primary_key_codes_nodup :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    NoDup
      (map
        (fun row =>
          int32_value_pair_index
            (dot TNull row (Attr_int32 first_name))
            (dot TNull row (Attr_int32 second_name)))
        rows).
Proof.
intros first_name second_name rows Hfirst_typed Hsecond_typed Hprimary.
pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
pose proof
  (int32_composite_primary_key_projection_nodup
    first_name second_name rows Hfirst_typed Hsecond_typed Hprimary)
  as Hkeys.
eapply NoDup_map_by_key with
  (key_of := project_row
    [Attr_int32 first_name; Attr_int32 second_name]); [exact Hkeys |].
intros left right Hleft Hright Hequal.
rewrite !project_row_cons, !project_row_nil.
destruct
  (conforming_nonnull_int32_pair_index_eq first_name second_name
    (dot TNull left (Attr_int32 first_name))
    (dot TNull left (Attr_int32 second_name))
    (dot TNull right (Attr_int32 first_name))
    (dot TNull right (Attr_int32 second_name))
    (Hfirst_typed left Hleft) (Hsecond_typed left Hleft)
    (Hfirst_typed right Hright) (Hsecond_typed right Hright)
    (Hnonnull left Hleft (Attr_int32 first_name) (or_introl eq_refl))
    (Hnonnull left Hleft (Attr_int32 second_name) (or_intror (or_introl eq_refl)))
    (Hnonnull right Hright (Attr_int32 first_name) (or_introl eq_refl))
    (Hnonnull right Hright (Attr_int32 second_name) (or_intror (or_introl eq_refl)))
    Hequal) as [Hfirst Hsecond].
now rewrite Hfirst, Hsecond.
Qed.

Theorem int32_composite_primary_key_length :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    (List.length rows <= int32_domain_size * int32_domain_size)%nat.
Proof.
intros first_name second_name rows Hfirst_typed Hsecond_typed Hprimary.
pose proof
  (int32_composite_primary_key_codes_nodup
    first_name second_name rows Hfirst_typed Hsecond_typed Hprimary)
  as Hcodes.
assert
  (Hinside :
    incl
      (map
        (fun row =>
          int32_value_pair_index
            (dot TNull row (Attr_int32 first_name))
            (dot TNull row (Attr_int32 second_name)))
        rows)
      (list_prod
        (seq 0 int32_domain_size)
        (seq 0 int32_domain_size))).
{
  intros code Hcode.
  apply in_map_iff in Hcode as [row [<- Hrow]].
  pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
  destruct
    (conforming_nonnull_int32_value first_name
      (dot TNull row (Attr_int32 first_name))
      (Hfirst_typed row Hrow)
      (Hnonnull row Hrow (Attr_int32 first_name) (or_introl eq_refl)))
    as [first_integer ->].
  destruct
    (conforming_nonnull_int32_value second_name
      (dot TNull row (Attr_int32 second_name))
      (Hsecond_typed row Hrow)
      (Hnonnull row Hrow (Attr_int32 second_name)
        (or_intror (or_introl eq_refl))))
    as [second_integer ->].
  apply in_prod; apply int32_index_in_domain.
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
rewrite length_map, length_prod, !length_seq in Hlength.
exact Hlength.
Qed.

Lemma int32_composite_domain_size_is_two_power_64 :
  Z.of_nat (int32_domain_size * int32_domain_size) = Z.pow 2 64.
Proof.
rewrite Nat2Z.inj_mul, !int32_domain_size_is_two_power_32.
reflexivity.
Qed.

Corollary int32_composite_primary_key_length_2_64 :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    Z.of_nat (List.length rows) <= Z.pow 2 64.
Proof.
intros first_name second_name rows Hfirst Hsecond Hprimary.
pose proof
  (int32_composite_primary_key_length
    first_name second_name rows Hfirst Hsecond Hprimary) as Hlength.
apply Nat2Z.inj_le in Hlength.
now rewrite int32_composite_domain_size_is_two_power_64 in Hlength.
Qed.

(** A component of a composite key is not unique in general.  It becomes a
    finite-domain code for a subgroup only when the other component is
    explicitly fixed throughout that subgroup. *)
Theorem int32_composite_primary_key_fixed_first_length :
  forall first_name second_name rows fixed_first,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    Forall
      (fun row => dot TNull row (Attr_int32 first_name) = fixed_first)
      rows ->
    (List.length rows <= int32_domain_size)%nat.
Proof.
intros first_name second_name rows fixed_first
  Hfirst_typed Hsecond_typed Hprimary Hfixed.
pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
pose proof
  (int32_composite_primary_key_projection_nodup
    first_name second_name rows Hfirst_typed Hsecond_typed Hprimary)
  as Hkeys.
assert
  (Hcodes :
    NoDup
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 second_name)))
        rows)).
{
  eapply NoDup_map_by_key with
    (key_of := project_row
      [Attr_int32 first_name; Attr_int32 second_name]); [exact Hkeys |].
  intros left right Hleft Hright Hequal.
  rewrite !project_row_cons, !project_row_nil.
  rewrite Forall_forall in Hfixed.
  rewrite (Hfixed left Hleft), (Hfixed right Hright).
  destruct
    (conforming_nonnull_int32_index_eq_iff second_name
      (dot TNull left (Attr_int32 second_name))
      (dot TNull right (Attr_int32 second_name))
      (Hsecond_typed left Hleft)
      (Hsecond_typed right Hright)
      (Hnonnull left Hleft (Attr_int32 second_name)
        (or_intror (or_introl eq_refl)))
      (Hnonnull right Hright (Attr_int32 second_name)
        (or_intror (or_introl eq_refl))))
    as [Hforward _].
  now rewrite (Hforward Hequal).
}
assert
  (Hinside :
    incl
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 second_name)))
        rows)
      (seq 0 int32_domain_size)).
{
  intros code Hcode.
  apply in_map_iff in Hcode as [row [<- Hrow]].
  destruct
    (conforming_nonnull_int32_value second_name
      (dot TNull row (Attr_int32 second_name))
      (Hsecond_typed row Hrow)
      (Hnonnull row Hrow (Attr_int32 second_name)
        (or_intror (or_introl eq_refl))))
    as [integer ->].
  apply int32_index_in_domain.
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
rewrite length_map, length_seq in Hlength.
exact Hlength.
Qed.

Theorem int32_composite_primary_key_fixed_second_length :
  forall first_name second_name rows fixed_second,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    Forall
      (fun row => dot TNull row (Attr_int32 second_name) = fixed_second)
      rows ->
    (List.length rows <= int32_domain_size)%nat.
Proof.
intros first_name second_name rows fixed_second
  Hfirst_typed Hsecond_typed Hprimary Hfixed.
pose proof (primary_key_conforms_not_null _ _ Hprimary) as Hnonnull.
pose proof
  (int32_composite_primary_key_projection_nodup
    first_name second_name rows Hfirst_typed Hsecond_typed Hprimary)
  as Hkeys.
assert
  (Hcodes :
    NoDup
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 first_name)))
        rows)).
{
  eapply NoDup_map_by_key with
    (key_of := project_row
      [Attr_int32 first_name; Attr_int32 second_name]); [exact Hkeys |].
  intros left right Hleft Hright Hequal.
  rewrite !project_row_cons, !project_row_nil.
  rewrite Forall_forall in Hfixed.
  rewrite (Hfixed left Hleft), (Hfixed right Hright).
  destruct
    (conforming_nonnull_int32_index_eq_iff first_name
      (dot TNull left (Attr_int32 first_name))
      (dot TNull right (Attr_int32 first_name))
      (Hfirst_typed left Hleft)
      (Hfirst_typed right Hright)
      (Hnonnull left Hleft (Attr_int32 first_name) (or_introl eq_refl))
      (Hnonnull right Hright (Attr_int32 first_name) (or_introl eq_refl)))
    as [Hforward _].
  now rewrite (Hforward Hequal).
}
assert
  (Hinside :
    incl
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 first_name)))
        rows)
      (seq 0 int32_domain_size)).
{
  intros code Hcode.
  apply in_map_iff in Hcode as [row [<- Hrow]].
  destruct
    (conforming_nonnull_int32_value first_name
      (dot TNull row (Attr_int32 first_name))
      (Hfirst_typed row Hrow)
      (Hnonnull row Hrow (Attr_int32 first_name) (or_introl eq_refl)))
    as [integer ->].
  apply int32_index_in_domain.
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
rewrite length_map, length_seq in Hlength.
exact Hlength.
Qed.

(** Nullable INT32 group keys use one extra code for SQL NULL. *)
Definition nullable_int32_value_index (value : value TNull) : nat :=
  match value with
  | NullValues.Value_int32 None => 0%nat
  | NullValues.Value_int32 (Some integer) => S (int32_index integer)
  | _ => 0%nat
  end.

Lemma conforming_nullable_int32_index_lt :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    (nullable_int32_value_index value < S int32_domain_size)%nat.
Proof.
intros name value Hconforms.
destruct (conforming_int32_value name value Hconforms) as [payload ->].
destruct payload as [integer |]; cbn [nullable_int32_value_index].
- pose proof (int32_index_lt integer); lia.
- lia.
Qed.

Lemma conforming_nullable_int32_index_eq_iff :
  forall name left right,
    value_conforms_attribute (Attr_int32 name) left ->
    value_conforms_attribute (Attr_int32 name) right ->
    (nullable_int32_value_index left = nullable_int32_value_index right <->
     left = right).
Proof.
intros name left right Hleft Hright.
destruct (conforming_int32_value name left Hleft) as [left_payload ->].
destruct (conforming_int32_value name right Hright) as [right_payload ->].
destruct left_payload as [left_integer |];
  destruct right_payload as [right_integer |];
  cbn [nullable_int32_value_index].
- split.
  + intro Hequal.
    injection Hequal as Hequal.
    now rewrite (int32_index_injective left_integer right_integer Hequal).
  + now inversion 1.
- split; discriminate.
- split; discriminate.
- tauto.
Qed.

Theorem nullable_int32_nodup_length :
  forall name values,
    Forall (value_conforms_attribute (Attr_int32 name)) values ->
    NoDup values ->
    (List.length values <= S int32_domain_size)%nat.
Proof.
intros name values Htyped Hnodup.
assert
  (Hcodes : NoDup (map nullable_int32_value_index values)).
{
  revert Htyped.
  induction Hnodup as [|first rest Hfirst Hrest IH];
    intros Htyped; cbn.
  - constructor.
  - inversion Htyped as [|typed_first typed_rest Htyped_first Htyped_rest];
      subst.
    constructor; [|now apply IH].
    intros Hin.
    apply in_map_iff in Hin as [other [Hequal Hother]].
    apply Hfirst.
    destruct
      (conforming_nullable_int32_index_eq_iff name first other
        Htyped_first
        ((proj1 (Forall_forall _ _)) Htyped_rest other Hother))
      as [Hforward _].
    pose proof (Hforward (eq_sym Hequal)) as Hsame.
    subst other.
    exact Hother.
}
assert
  (Hinside :
    incl
      (map nullable_int32_value_index values)
      (seq 0 (S int32_domain_size))).
{
  intros code Hcode.
  apply in_map_iff in Hcode as [value [<- Hvalue]].
  rewrite in_seq.
  split; [lia |].
  rewrite Forall_forall in Htyped.
  pose proof (conforming_nullable_int32_index_lt name value
    (Htyped value Hvalue)).
  lia.
}
pose proof (NoDup_incl_length Hcodes Hinside) as Hlength.
rewrite length_map, length_seq in Hlength.
exact Hlength.
Qed.

Lemma nullable_int32_domain_size_is_two_power_32_plus_1 :
  Z.of_nat (S int32_domain_size) = Z.pow 2 32 + 1.
Proof.
rewrite Nat2Z.inj_succ, int32_domain_size_is_two_power_32.
lia.
Qed.

Corollary nullable_int32_nodup_length_2_32_plus_1 :
  forall name values,
    Forall (value_conforms_attribute (Attr_int32 name)) values ->
    NoDup values ->
    Z.of_nat (List.length values) <= Z.pow 2 32 + 1.
Proof.
intros name values Htyped Hnodup.
pose proof (nullable_int32_nodup_length name values Htyped Hnodup)
  as Hlength.
apply Nat2Z.inj_le in Hlength.
now rewrite nullable_int32_domain_size_is_two_power_32_plus_1 in Hlength.
Qed.
