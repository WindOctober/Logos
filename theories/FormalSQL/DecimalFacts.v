From SQLFS Require Import SqlSyntax GenericInstance Values.
From Logos.FormalSQL Require Import TNullSyntax.
From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(*
  Basic facts for the typmod-refined DECIMAL model.

  A decimal value is [Decimal precision scale coeff], denoting
  coeff / 10^scale under SQL typmod DECIMAL(precision, scale).  Values should
  enter this domain through [decimal_checked], which enforces the typmod
  refinement predicate.
*)

Lemma decimal_precision_decimal :
  forall precision scale coeff,
    decimal_precision (Decimal precision scale coeff) = precision.
Proof.
intros; reflexivity.
Qed.

Lemma decimal_scale_decimal :
  forall precision scale coeff,
    decimal_scale (Decimal precision scale coeff) = scale.
Proof.
intros; reflexivity.
Qed.

Lemma decimal_coeff_decimal :
  forall precision scale coeff,
    decimal_coeff (Decimal precision scale coeff) = coeff.
Proof.
intros; reflexivity.
Qed.

Lemma decimal_has_scale_decimal :
  forall precision scale coeff,
    decimal_has_scale (Decimal precision scale coeff) scale.
Proof.
intros; reflexivity.
Qed.

Lemma decimal_compare_refl :
  forall d,
    decimal_compare d d = Eq.
Proof.
intros [precision scale coeff].
unfold decimal_compare; simpl.
rewrite Z.compare_refl.
reflexivity.
Qed.

Lemma decimal_eqb_compare_eq :
  forall d1 d2,
    decimal_eqb d1 d2 = true <-> decimal_compare d1 d2 = Eq.
Proof.
intros d1 d2.
unfold decimal_eqb.
destruct (decimal_compare d1 d2); split; intro H; try reflexivity; discriminate H.
Qed.

Lemma decimal_eqb_refl :
  forall d,
    decimal_eqb d d = true.
Proof.
intro d.
rewrite decimal_eqb_compare_eq.
apply decimal_compare_refl.
Qed.

Lemma decimal_checked_precision :
  forall precision scale coeff result,
    decimal_checked precision scale coeff = Some result ->
    decimal_precision result = precision.
Proof.
intros precision scale coeff [rprecision rscale rcoeff] H.
unfold decimal_checked in H.
case_eq (decimal_fits_typmod_bool precision scale coeff); intro Hfits; rewrite Hfits in H;
  try discriminate H.
inversion H.
reflexivity.
Qed.

Lemma decimal_checked_scale :
  forall precision scale coeff result,
    decimal_checked precision scale coeff = Some result ->
    decimal_scale result = scale.
Proof.
intros precision scale coeff [rprecision rscale rcoeff] H.
unfold decimal_checked in H.
case_eq (decimal_fits_typmod_bool precision scale coeff); intro Hfits; rewrite Hfits in H;
  try discriminate H.
inversion H.
reflexivity.
Qed.

Lemma decimal_checked_coeff :
  forall precision scale coeff result,
    decimal_checked precision scale coeff = Some result ->
    decimal_coeff result = coeff.
Proof.
intros precision scale coeff [rprecision rscale rcoeff] H.
unfold decimal_checked in H.
case_eq (decimal_fits_typmod_bool precision scale coeff); intro Hfits; rewrite Hfits in H;
  try discriminate H.
inversion H.
reflexivity.
Qed.

Lemma decimal_mul_coeff :
  forall d1 d2 result,
    decimal_mul d1 d2 = Some result ->
    decimal_coeff result =
    decimal_coeff d1 * decimal_coeff d2.
Proof.
intros d1 d2 result H.
unfold decimal_mul in H.
eapply decimal_checked_coeff; eassumption.
Qed.

Lemma decimal_mul_scale :
  forall d1 d2 result,
    decimal_mul d1 d2 = Some result ->
    decimal_scale result =
    decimal_scale d1 + decimal_scale d2.
Proof.
intros d1 d2 result H.
unfold decimal_mul in H.
eapply decimal_checked_scale; eassumption.
Qed.

Lemma decimal_div_with_typmod_by_zero :
  forall d precision scale,
    decimal_div_with_typmod d decimal_zero precision scale = None.
Proof.
intros [precision dscale coeff] result_precision scale.
reflexivity.
Qed.

Lemma decimal_div_with_typmod_scale :
  forall d1 d2 result result_precision result_scale,
    decimal_div_with_typmod d1 d2 result_precision result_scale = Some result ->
    decimal_scale result = result_scale.
Proof.
intros d1 d2 result result_precision result_scale H.
unfold decimal_div_with_typmod in H.
destruct (decimal_div d1 d2) as [intermediate |] eqn:Hdiv; try discriminate H.
unfold decimal_cast_typmod in H.
eapply decimal_checked_scale; eassumption.
Qed.

Lemma decimal_div_scale :
  forall d1 d2 result,
    decimal_div d1 d2 = Some result ->
    decimal_scale result = decimal_pg_div_scale d1 d2.
Proof.
intros d1 d2 result H.
unfold decimal_div in H.
destruct (decimal_coeff d2 =? 0) eqn:Hzero; try discriminate H.
eapply decimal_checked_scale; eassumption.
Qed.

Lemma decimal_round_quot_exact :
  forall numerator denominator,
    denominator <> 0 ->
    Z.rem numerator denominator = 0 ->
    decimal_round_quot numerator denominator = Z.quot numerator denominator.
Proof.
intros numerator denominator Hden Hrem.
unfold decimal_round_quot.
rewrite Hrem.
rewrite Z.abs_0.
replace (2 * 0) with 0 by ring.
assert (Habs_pos : 0 < Z.abs denominator).
{
  apply Z.abs_pos.
  assumption.
}
destruct (Z.geb 0 (Z.abs denominator)) eqn:Hround.
- apply Z.geb_ge in Hround.
  exfalso.
  lia.
- reflexivity.
Qed.

Lemma decimal_opp_coeff :
  forall d result,
    decimal_opp d = Some result ->
    decimal_coeff result = - decimal_coeff d.
Proof.
intros d result H.
unfold decimal_opp in H.
eapply decimal_checked_coeff; eassumption.
Qed.

Lemma decimal_opp_scale :
  forall d result,
    decimal_opp d = Some result ->
    decimal_scale result = decimal_scale d.
Proof.
intros d result H.
unfold decimal_opp in H.
eapply decimal_checked_scale; eassumption.
Qed.
