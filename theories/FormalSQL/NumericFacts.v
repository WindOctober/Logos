From SQLFS Require Import OrderedSet SqlSyntax GenericInstance Values ValueNumeric ValueNumericTypmod.
From Logos.FormalSQL Require Import TNullSyntax.
From Stdlib Require Import ZArith Qcanon.

Open Scope Z_scope.

(** Core facts for canonical unconstrained NUMERIC and DECIMAL(p,s) typmods. *)

Lemma numeric_compare_refl :
  forall value,
    numeric_compare value value = Eq.
Proof.
intro value.
exact (Oset.compare_eq_refl Onumeric value).
Qed.

Lemma numeric_eqb_refl :
  forall value,
    numeric_eqb value value = true.
Proof.
intro value.
unfold numeric_eqb.
rewrite numeric_compare_refl.
reflexivity.
Qed.

Example numeric_scaled_representations_are_canonical :
  numeric_of_scaled 1 0 = numeric_of_scaled 10 1.
Proof.
apply Qc_decomp.
vm_compute.
reflexivity.
Qed.

Lemma numeric_cast_typmod_result :
  forall value precision scale result,
    numeric_cast_typmod value precision scale = Some result ->
    result = numeric_round_to_scale value scale.
Proof.
intros value precision scale result Hcast.
unfold numeric_cast_typmod in Hcast.
destruct (numeric_fits_typmod_bool value precision scale); try discriminate.
now inversion Hcast.
Qed.

Lemma numeric_div_by_zero :
  forall value,
    numeric_div_at_scales value 0 numeric_zero 0 = None.
Proof.
intro value.
unfold numeric_div_at_scales.
rewrite numeric_eqb_refl.
reflexivity.
Qed.

Example numeric_division_preserves_postgres_input_dscale :
  numeric_div_at_scales
    (numeric_of_scaled 10 0) 20
    (numeric_of_scaled 3 0) 0 =
  Some (numeric_of_scaled 333333333333333333333 20).
Proof.
vm_compute.
reflexivity.
Qed.
