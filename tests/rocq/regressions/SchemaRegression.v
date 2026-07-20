From Stdlib Require Import Lia List String ZArith.
From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet ValueInteger.
From Logos.FormalSQL Require Import SchemaConstraints SchemaCardinality.

Import ListNotations.
Import Tuple.
Open Scope string_scope.
Open Scope Z_scope.

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

Example duplicate_primary_key_is_rejected :
  ~ primary_key_conforms
      [regression_key]
      [regression_row 1 10; regression_row 1 20].
Proof.
intros [_ [_ Hnodup]].
inversion Hnodup as [| projected remaining Hnotin _].
apply Hnotin; left; reflexivity.
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
