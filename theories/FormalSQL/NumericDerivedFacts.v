From SQLFS Require Import GenericInstance SqlOutcome Values ValueNumeric
  ValueNumericTypmod.
From Logos.FormalSQL Require Import NumericFacts ScalarPredicateFacts.
From Stdlib Require Import Bool Lia List QArith Qcanon ZArith.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.

(** Checked integer constructors expose their mathematical range contract. *)

Lemma int32_checked_result_value : forall integer result,
  int32_checked integer = Some result ->
  int32_value result = integer.
Proof.
  intros integer result Hchecked.
  unfold int32_checked in Hchecked.
  destruct (Z.leb_spec0 int32_min integer); [|discriminate].
  destruct (Z.leb_spec0 integer int32_max); [|discriminate].
  inversion Hchecked; reflexivity.
Qed.

Lemma int64_checked_result_value : forall integer result,
  int64_checked integer = Some result ->
  int64_value result = integer.
Proof.
  intros integer result Hchecked.
  unfold int64_checked in Hchecked.
  destruct (Z.leb_spec0 int64_min integer); [|discriminate].
  destruct (Z.leb_spec0 integer int64_max); [|discriminate].
  inversion Hchecked; reflexivity.
Qed.

(** A non-NULL INTEGER cannot equal two unequal INTEGER constants.  Keeping
    this fact at the typed integer layer prevents proofs from unfolding the
    complete heterogeneous-value comparison dispatcher. *)
Lemma interp_int32_neq_disjunction_true_of_unequal_constants :
  forall value first second,
    int32_value first <> int32_value second ->
    Bool3.orb3
      (NullValues.interp_predicate PredicateNeq
        [Value_int32 (Some value); Value_int32 (Some first)])
      (NullValues.interp_predicate PredicateNeq
        [Value_int32 (Some value); Value_int32 (Some second)]) =
    Bool3.true3.
Proof.
intros value first second Hdistinct.
rewrite (interp_predicate_neq_of_order_compare
  (Value_int32 (Some value)) (Value_int32 (Some first))
  (Z.compare (int32_value value) (int32_value first)) eq_refl).
rewrite (interp_predicate_neq_of_order_compare
  (Value_int32 (Some value)) (Value_int32 (Some second))
  (Z.compare (int32_value value) (int32_value second)) eq_refl).
destruct (Z.compare_spec (int32_value value) (int32_value first));
  destruct (Z.compare_spec (int32_value value) (int32_value second));
  cbn; try reflexivity; congruence.
Qed.

Lemma int32_checked_defined_iff : forall integer,
  (exists result, int32_checked integer = Some result) <->
  int32_min <= integer <= int32_max.
Proof.
  intro integer; split.
  - intros [result Hchecked].
    rewrite <- (int32_checked_result_value integer result Hchecked).
    apply int32_range.
  - intros [Hlower Hupper].
    unfold int32_checked.
    destruct (Z.leb_spec0 int32_min integer); [|lia].
    destruct (Z.leb_spec0 integer int32_max); [|lia].
    eexists; reflexivity.
Qed.

Lemma int64_checked_defined_iff : forall integer,
  (exists result, int64_checked integer = Some result) <->
  int64_min <= integer <= int64_max.
Proof.
  intro integer; split.
  - intros [result Hchecked].
    rewrite <- (int64_checked_result_value integer result Hchecked).
    apply int64_range.
  - intros [Hlower Hupper].
    unfold int64_checked.
    destruct (Z.leb_spec0 int64_min integer); [|lia].
    destruct (Z.leb_spec0 integer int64_max); [|lia].
    eexists; reflexivity.
Qed.

Lemma int32_checked_none_iff : forall integer,
  int32_checked integer = None <->
  integer < int32_min \/ int32_max < integer.
Proof.
  intro integer; split.
  - intro Hnone.
    assert (~ (int32_min <= integer <= int32_max)) as Houtside.
    {
      intro Hrange.
      apply int32_checked_defined_iff in Hrange.
      destruct Hrange as [result Hresult].
      rewrite Hnone in Hresult; discriminate.
    }
    lia.
  - apply int32_checked_outside_range.
Qed.

Lemma int64_checked_none_iff : forall integer,
  int64_checked integer = None <->
  integer < int64_min \/ int64_max < integer.
Proof.
  intro integer; split.
  - intro Hnone.
    assert (~ (int64_min <= integer <= int64_max)) as Houtside.
    {
      intro Hrange.
      apply int64_checked_defined_iff in Hrange.
      destruct Hrange as [result Hresult].
      rewrite Hnone in Hresult; discriminate.
    }
    lia.
  - apply int64_checked_outside_range.
Qed.

Lemma int32_checked_value : forall value,
  int32_checked (int32_value value) = Some value.
Proof.
  intro value.
  pose proof (int32_range value) as Hrange.
  apply int32_checked_defined_iff in Hrange.
  destruct Hrange as [result Hresult].
  rewrite Hresult.
  f_equal; apply int32_ext.
  now apply int32_checked_result_value in Hresult.
Qed.

Lemma int32_to_int64_injective : forall left right,
  int32_to_int64 left = int32_to_int64 right -> left = right.
Proof.
  intros left right Hequal; apply int32_ext.
  apply (f_equal int64_value) in Hequal.
  exact Hequal.
Qed.

Lemma int32_to_int64_value : forall value,
  int64_value (int32_to_int64 value) = int32_value value.
Proof. reflexivity. Qed.

(** Range premises are sufficient to make fixed-width arithmetic total. *)

Lemma int32_add_total_of_range : forall left right,
  int32_min <= int32_value left + int32_value right <= int32_max ->
  exists result,
    int32_add left right = Some result /\
    int32_value result = int32_value left + int32_value right.
Proof.
  intros left right Hrange.
  apply int32_checked_defined_iff in Hrange.
  destruct Hrange as [result Hresult].
  exists result; split; [exact Hresult|].
  now apply int32_checked_result_value in Hresult.
Qed.

Lemma int32_sub_total_of_range : forall left right,
  int32_min <= int32_value left - int32_value right <= int32_max ->
  exists result,
    int32_sub left right = Some result /\
    int32_value result = int32_value left - int32_value right.
Proof.
  intros left right Hrange.
  apply int32_checked_defined_iff in Hrange.
  destruct Hrange as [result Hresult].
  exists result; split; [exact Hresult|].
  now apply int32_checked_result_value in Hresult.
Qed.

Lemma int32_mul_total_of_range : forall left right,
  int32_min <= int32_value left * int32_value right <= int32_max ->
  exists result,
    int32_mul left right = Some result /\
    int32_value result = int32_value left * int32_value right.
Proof.
  intros left right Hrange.
  apply int32_checked_defined_iff in Hrange.
  destruct Hrange as [result Hresult].
  exists result; split; [exact Hresult|].
  now apply int32_checked_result_value in Hresult.
Qed.

Lemma int32_div_total_of_nonzero_range : forall left right,
  int32_value right <> 0 ->
  int32_min <= Z.quot (int32_value left) (int32_value right) <= int32_max ->
  exists result,
    int32_div left right = Some result /\
    int32_value result = Z.quot (int32_value left) (int32_value right).
Proof.
  intros left right Hnonzero Hrange.
  apply int32_checked_defined_iff in Hrange.
  destruct Hrange as [result Hresult].
  exists result; split.
  - unfold int32_div.
    assert (Z.eqb (int32_value right) 0 = false) as Hzero.
    { now apply Z.eqb_neq. }
    rewrite Hzero.
    exact Hresult.
  - now apply int32_checked_result_value in Hresult.
Qed.

(** Exact checked-operation inversion avoids exposing the checked constructor
    implementation in scalar arithmetic proofs. *)

Lemma int32_add_some_iff : forall left right result,
  int32_add left right = Some result <->
  int32_value result = int32_value left + int32_value right.
Proof.
  intros left right result; split; intro Hresult.
  - now apply int32_checked_result_value in Hresult.
  - unfold int32_add.
    rewrite <- Hresult.
    apply int32_checked_value.
Qed.

Lemma int32_sub_some_iff : forall left right result,
  int32_sub left right = Some result <->
  int32_value result = int32_value left - int32_value right.
Proof.
  intros left right result; split; intro Hresult.
  - now apply int32_checked_result_value in Hresult.
  - unfold int32_sub.
    rewrite <- Hresult.
    apply int32_checked_value.
Qed.

Lemma int32_mul_some_iff : forall left right result,
  int32_mul left right = Some result <->
  int32_value result = int32_value left * int32_value right.
Proof.
  intros left right result; split; intro Hresult.
  - now apply int32_checked_result_value in Hresult.
  - unfold int32_mul.
    rewrite <- Hresult.
    apply int32_checked_value.
Qed.

Lemma int32_div_some_iff : forall left right result,
  int32_div left right = Some result <->
  int32_value right <> 0 /\
  int32_value result = Z.quot (int32_value left) (int32_value right).
Proof.
  intros left right result; split; intro Hresult.
  - unfold int32_div in Hresult.
    destruct (Z.eqb (int32_value right) 0) eqn:Hzero; [discriminate |].
    split.
    + now apply Z.eqb_neq in Hzero.
    + now apply int32_checked_result_value in Hresult.
  - destruct Hresult as [Hnonzero Hvalue].
    unfold int32_div.
    assert (Z.eqb (int32_value right) 0 = false) as Hzero.
    { now apply Z.eqb_neq. }
    rewrite Hzero, <- Hvalue.
    apply int32_checked_value.
Qed.

Lemma int32_opp_some_iff : forall input result,
  int32_opp input = Some result <->
  int32_value result = - int32_value input.
Proof.
  intros input result; split; intro Hresult.
  - now apply int32_checked_result_value in Hresult.
  - unfold int32_opp.
    rewrite <- Hresult.
    apply int32_checked_value.
Qed.

Lemma int32_add_none_iff : forall left right,
  int32_add left right = None <->
  int32_value left + int32_value right < int32_min \/
  int32_max < int32_value left + int32_value right.
Proof.
  intros left right; unfold int32_add.
  apply int32_checked_none_iff.
Qed.

Lemma int32_sub_none_iff : forall left right,
  int32_sub left right = None <->
  int32_value left - int32_value right < int32_min \/
  int32_max < int32_value left - int32_value right.
Proof.
  intros left right; unfold int32_sub.
  apply int32_checked_none_iff.
Qed.

Lemma int32_mul_none_iff : forall left right,
  int32_mul left right = None <->
  int32_value left * int32_value right < int32_min \/
  int32_max < int32_value left * int32_value right.
Proof.
  intros left right; unfold int32_mul.
  apply int32_checked_none_iff.
Qed.

Lemma int32_div_none_iff : forall left right,
  int32_div left right = None <->
  int32_value right = 0 \/
  Z.quot (int32_value left) (int32_value right) < int32_min \/
  int32_max < Z.quot (int32_value left) (int32_value right).
Proof.
  intros left right; unfold int32_div.
  destruct (Z.eqb (int32_value right) 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; split; [now left | reflexivity].
  - apply Z.eqb_neq in Hzero.
    rewrite int32_checked_none_iff.
    split.
    + now right.
    + intros [Hcontradiction | Houtside]; [contradiction | exact Houtside].
Qed.

Lemma int32_opp_none_iff : forall input,
  int32_opp input = None <->
  - int32_value input < int32_min \/
  int32_max < - int32_value input.
Proof.
  intro input; unfold int32_opp.
  apply int32_checked_none_iff.
Qed.

(** Runtime classifiers expose exactly the checked-operation failure; malformed
    or NULL shapes remain outside these non-NULL lemmas. *)

Lemma int32_binary_runtime_error_none_iff : forall operation left right,
  int32_binary_runtime_error operation
    [Value_int32 (Some left); Value_int32 (Some right)] = None <->
  exists result, operation left right = Some result.
Proof.
  intros operation left right.
  cbn [int32_binary_runtime_error].
  destruct (operation left right) as [result |] eqn:Hresult.
  - split; [intro; now exists result | intro; reflexivity].
  - split; [discriminate | intros [result H]; discriminate].
Qed.

Lemma int32_binary_runtime_error_out_of_range_iff :
  forall operation left right,
    int32_binary_runtime_error operation
      [Value_int32 (Some left); Value_int32 (Some right)] =
      Some (DataException NumericValueOutOfRange) <->
    operation left right = None.
Proof.
  intros operation left right.
  cbn [int32_binary_runtime_error numeric_value_out_of_range].
  destruct (operation left right); split; intro H; try discriminate;
    reflexivity.
Qed.

Lemma int32_div_runtime_error_none_iff : forall left right,
  int32_div_runtime_error
    [Value_int32 (Some left); Value_int32 (Some right)] = None <->
  int32_value right <> 0 /\
  exists result, int32_div left right = Some result.
Proof.
  intros left right.
  cbn [int32_div_runtime_error].
  destruct (Z.eqb (int32_value right) 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; split; [discriminate |].
    intros [Hnonzero _]; contradiction.
  - apply Z.eqb_neq in Hzero.
    destruct (int32_div left right) as [result |] eqn:Hdivision.
    + split; [intro; split; [exact Hzero | now exists result] | intro; reflexivity].
    + split; [discriminate | intros [_ [result H]]; discriminate].
Qed.

Lemma int32_div_runtime_error_division_by_zero_iff : forall left right,
  int32_div_runtime_error
    [Value_int32 (Some left); Value_int32 (Some right)] =
    Some (DataException DivisionByZero) <->
  int32_value right = 0.
Proof.
  intros left right.
  cbn [int32_div_runtime_error division_by_zero
    numeric_value_out_of_range].
  destruct (Z.eqb (int32_value right) 0) eqn:Hzero.
  - now apply Z.eqb_eq in Hzero.
  - apply Z.eqb_neq in Hzero.
    destruct (int32_div left right); split; intro H; try discriminate;
      contradiction.
Qed.

Lemma int32_div_runtime_error_out_of_range_iff : forall left right,
  int32_div_runtime_error
    [Value_int32 (Some left); Value_int32 (Some right)] =
    Some (DataException NumericValueOutOfRange) <->
  int32_value right <> 0 /\ int32_div left right = None.
Proof.
  intros left right.
  cbn [int32_div_runtime_error division_by_zero
    numeric_value_out_of_range].
  destruct (Z.eqb (int32_value right) 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; split; [discriminate |].
    intros [Hnonzero _]; contradiction.
  - apply Z.eqb_neq in Hzero.
    destruct (int32_div left right) as [result |] eqn:Hdivision.
    + split; [discriminate | intros [_ H]; discriminate].
    + split.
      * intro; now split.
      * intro; reflexivity.
Qed.

Lemma int32_opp_runtime_error_none_iff : forall input,
  int32_opp_runtime_error [Value_int32 (Some input)] = None <->
  exists result, int32_opp input = Some result.
Proof.
  intro input; cbn [int32_opp_runtime_error].
  destruct (int32_opp input) as [result |] eqn:Hresult.
  - split; [intro; now exists result | intro; reflexivity].
  - split; [discriminate | intros [result H]; discriminate].
Qed.

Lemma int64_binary_runtime_error_none_iff :
  forall operation left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_binary_runtime_error operation [left; right] = None <->
    exists result,
      int64_checked (operation left_integer right_integer) = Some result.
Proof.
  intros operation left right left_integer right_integer Hleft Hright.
  cbn [int64_binary_runtime_error].
  rewrite Hleft, Hright.
  destruct (int64_checked (operation left_integer right_integer))
    as [result |] eqn:Hresult.
  - split; [intro; now exists result | intro; reflexivity].
  - split; [discriminate | intros [result H]; discriminate].
Qed.

Lemma int64_binary_runtime_error_out_of_range_iff :
  forall operation left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_binary_runtime_error operation [left; right] =
      Some (DataException NumericValueOutOfRange) <->
    int64_checked (operation left_integer right_integer) = None.
Proof.
  intros operation left right left_integer right_integer Hleft Hright.
  cbn [int64_binary_runtime_error numeric_value_out_of_range].
  rewrite Hleft, Hright.
  destruct (int64_checked (operation left_integer right_integer));
    split; intro H; try discriminate; reflexivity.
Qed.

Lemma int64_div_runtime_error_none_iff :
  forall left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_div_runtime_error [left; right] = None <->
    right_integer <> 0 /\
    exists result,
      int64_checked (Z.quot left_integer right_integer) = Some result.
Proof.
  intros left right left_integer right_integer Hleft Hright.
  cbn [int64_div_runtime_error].
  rewrite Hleft, Hright.
  destruct (Z.eqb right_integer 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; split; [discriminate |].
    intros [Hnonzero _]; contradiction.
  - apply Z.eqb_neq in Hzero.
    destruct (int64_checked (Z.quot left_integer right_integer))
      as [result |] eqn:Hresult.
    + split; [intro; split; [exact Hzero | now exists result] | intro; reflexivity].
    + split; [discriminate | intros [_ [result H]]; discriminate].
Qed.

Lemma int64_div_runtime_error_division_by_zero_iff :
  forall left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_div_runtime_error [left; right] =
      Some (DataException DivisionByZero) <->
    right_integer = 0.
Proof.
  intros left right left_integer right_integer Hleft Hright.
  cbn [int64_div_runtime_error division_by_zero
    numeric_value_out_of_range].
  rewrite Hleft, Hright.
  destruct (Z.eqb right_integer 0) eqn:Hzero.
  - now apply Z.eqb_eq in Hzero.
  - apply Z.eqb_neq in Hzero.
    destruct (int64_checked (Z.quot left_integer right_integer));
      split; intro H; try discriminate; contradiction.
Qed.

Lemma int64_div_runtime_error_out_of_range_iff :
  forall left right left_integer right_integer,
    integral_value_as_z left = Some left_integer ->
    integral_value_as_z right = Some right_integer ->
    int64_div_runtime_error [left; right] =
      Some (DataException NumericValueOutOfRange) <->
    right_integer <> 0 /\
    int64_checked (Z.quot left_integer right_integer) = None.
Proof.
  intros left right left_integer right_integer Hleft Hright.
  cbn [int64_div_runtime_error division_by_zero
    numeric_value_out_of_range].
  rewrite Hleft, Hright.
  destruct (Z.eqb right_integer 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; split; [discriminate |].
    intros [Hnonzero _]; contradiction.
  - apply Z.eqb_neq in Hzero.
    destruct (int64_checked (Z.quot left_integer right_integer))
      as [result |] eqn:Hresult.
    + split; [discriminate | intros [_ H]; discriminate].
    + split.
      * intro; now split.
      * intro; reflexivity.
Qed.

(** Scalar cast bridges keep successful value conversion, SQL NULL, and the
    paired runtime classifier synchronized. *)

Lemma interp_cast_int32_to_double_nonnull : forall value,
  interp_cast_int32_to_double [Value_int32 (Some value)] =
  Value_double (Some (float64_of_Z (int32_value value))).
Proof. reflexivity. Qed.

Lemma interp_cast_int32_to_int64_nonnull : forall value,
  interp_cast_int32_to_int64 [Value_int32 (Some value)] =
  Value_int64 (Some (int32_to_int64 value)).
Proof. reflexivity. Qed.

Lemma interp_cast_int64_to_int32_nonnull : forall value,
  interp_cast_int64_to_int32 [Value_int64 (Some value)] =
  Value_int32 (int32_checked (int64_value value)).
Proof. reflexivity. Qed.

Lemma interp_int32_int64_cast_roundtrip : forall value,
  interp_cast_int64_to_int32
    [Value_int64 (Some (int32_to_int64 value))] =
  Value_int32 (Some value).
Proof.
  intro value; cbn [interp_cast_int64_to_int32].
  rewrite int32_to_int64_value.
  apply f_equal.
  apply int32_checked_value.
Qed.

Lemma numeric_integer_casts_preserve_null :
  interp_cast_int32_to_double [Value_int32 None] = Value_double None /\
  interp_cast_int32_to_int64 [Value_int32 None] = Value_int64 None /\
  interp_cast_int64_to_int32 [Value_int64 None] = Value_int32 None /\
  interp_cast_numeric_to_int32 [Value_numeric None] = Value_int32 None.
Proof. repeat split; reflexivity. Qed.

Lemma scalar_widening_casts_runtime_safe : forall values,
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt32ToDouble) values = None /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt32ToInt64) values = None.
Proof. intro values; split; reflexivity. Qed.

Lemma scalar_cast_int64_to_int32_runtime_error_none_iff : forall value,
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt64ToInt32)
    [Value_int64 (Some value)] = None <->
  exists result, int32_checked (int64_value value) = Some result.
Proof.
  intro value; cbn [scalar_operator_local_runtime_error].
  destruct (int32_checked (int64_value value)) as [result |] eqn:Hcast.
  - split; [intro; now exists result | intro; reflexivity].
  - split; [discriminate | intros [result H]; discriminate].
Qed.

Lemma scalar_cast_int64_to_int32_out_of_range_iff : forall value,
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastInt64ToInt32)
    [Value_int64 (Some value)] =
      Some (DataException NumericValueOutOfRange) <->
  int32_checked (int64_value value) = None.
Proof.
  intro value.
  cbn [scalar_operator_local_runtime_error numeric_value_out_of_range].
  destruct (int32_checked (int64_value value));
    split; intro H; try discriminate; reflexivity.
Qed.

Lemma numeric_to_int32_checked_some_iff : forall value result,
  numeric_to_int32_checked value = Some result <->
  exists finite,
    value = NumericFinite finite /\
    int32_checked (numeric_finite_rounded_coeff finite 0) = Some result.
Proof.
  intros value result; destruct value as [|finite| |];
    cbn [numeric_to_int32_checked numeric_rounded_coeff].
  - split; [discriminate | intros [candidate [H _]]; discriminate].
  - split.
    + intro H; exists finite; now split.
    + intros [candidate [Hequal Hchecked]].
      inversion Hequal; exact Hchecked.
  - split; [discriminate | intros [candidate [H _]]; discriminate].
  - split; [discriminate | intros [candidate [H _]]; discriminate].
Qed.

Lemma numeric_to_int32_checked_result_value : forall value result,
  numeric_to_int32_checked value = Some result ->
  exists finite,
    value = NumericFinite finite /\
    int32_value result = numeric_finite_rounded_coeff finite 0.
Proof.
  intros value result Hcast.
  apply numeric_to_int32_checked_some_iff in Hcast.
  destruct Hcast as [finite [Hvalue Hchecked]].
  exists finite; split; [exact Hvalue |].
  now apply int32_checked_result_value in Hchecked.
Qed.

Lemma scalar_cast_numeric_to_int32_finite_runtime_error_none_iff :
  forall finite,
    scalar_operator_local_runtime_error
      (ScalarCast ScalarCastNumericToInt32)
      [Value_numeric (Some (NumericFinite finite))] = None <->
    exists result,
      numeric_to_int32_checked (NumericFinite finite) = Some result.
Proof.
  intro finite; cbn [scalar_operator_local_runtime_error].
  destruct (numeric_to_int32_checked (NumericFinite finite))
    as [result |] eqn:Hcast.
  - split; [intro; now exists result | intro; reflexivity].
  - split; [discriminate | intros [result H]; discriminate].
Qed.

Lemma scalar_cast_numeric_to_int32_special_unsupported : forall value,
  (value = NumericNegInfinity \/
   value = NumericPosInfinity \/
   value = NumericNaN) ->
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastNumericToInt32)
    [Value_numeric (Some value)] = Some FeatureNotSupported.
Proof.
  intros value [-> | [-> | ->]]; reflexivity.
Qed.

(** IEEE float arithmetic remains abstract at this layer; these iff lemmas
    expose exactly the PostgreSQL overflow, underflow, and zero-divisor guards
    used by the runtime classifier without asserting opaque bit-level laws. *)

Lemma float32_add_runtime_error_none_iff : forall operation left right,
  float32_add_runtime_error operation
    [Value_float (Some left); Value_float (Some right)] = None <->
  andb (float32_is_infinite (operation left right))
    (andb (negb (float32_is_infinite left))
      (negb (float32_is_infinite right))) = false.
Proof.
  intros operation left right.
  cbn [float32_add_runtime_error numeric_value_out_of_range].
  destruct
    (andb (float32_is_infinite (operation left right))
      (andb (negb (float32_is_infinite left))
        (negb (float32_is_infinite right))));
    split; intro H; try discriminate; reflexivity.
Qed.

Lemma float64_add_runtime_error_none_iff : forall operation left right,
  float64_add_runtime_error operation
    [Value_double (Some left); Value_double (Some right)] = None <->
  andb (float64_is_infinite (operation left right))
    (andb (negb (float64_is_infinite left))
      (negb (float64_is_infinite right))) = false.
Proof.
  intros operation left right.
  cbn [float64_add_runtime_error numeric_value_out_of_range].
  destruct
    (andb (float64_is_infinite (operation left right))
      (andb (negb (float64_is_infinite left))
        (negb (float64_is_infinite right))));
    split; intro H; try discriminate; reflexivity.
Qed.

Lemma float32_mul_runtime_error_none_iff : forall left right,
  float32_mul_runtime_error
    [Value_float (Some left); Value_float (Some right)] = None <->
  andb (float32_is_infinite (float32_mul left right))
    (andb (negb (float32_is_infinite left))
      (negb (float32_is_infinite right))) = false /\
  andb (float32_is_zero (float32_mul left right))
    (andb (negb (float32_is_zero left))
      (negb (float32_is_zero right))) = false.
Proof.
  intros left right.
  set (overflow :=
    andb (float32_is_infinite (float32_mul left right))
      (andb (negb (float32_is_infinite left))
        (negb (float32_is_infinite right)))).
  set (underflow :=
    andb (float32_is_zero (float32_mul left right))
      (andb (negb (float32_is_zero left))
        (negb (float32_is_zero right)))).
  change
    ((if overflow then numeric_value_out_of_range
      else if underflow then numeric_value_out_of_range else None) = None <->
     overflow = false /\ underflow = false).
  unfold numeric_value_out_of_range.
  destruct overflow.
  - split; [discriminate | intros [H _]; discriminate].
  - destruct underflow.
    + split; [discriminate | intros [_ H]; discriminate].
    + split; [intro; now split | intro; reflexivity].
Qed.

Lemma float64_mul_runtime_error_none_iff : forall left right,
  float64_mul_runtime_error
    [Value_double (Some left); Value_double (Some right)] = None <->
  andb (float64_is_infinite (float64_mul left right))
    (andb (negb (float64_is_infinite left))
      (negb (float64_is_infinite right))) = false /\
  andb (float64_is_zero (float64_mul left right))
    (andb (negb (float64_is_zero left))
      (negb (float64_is_zero right))) = false.
Proof.
  intros left right.
  set (overflow :=
    andb (float64_is_infinite (float64_mul left right))
      (andb (negb (float64_is_infinite left))
        (negb (float64_is_infinite right)))).
  set (underflow :=
    andb (float64_is_zero (float64_mul left right))
      (andb (negb (float64_is_zero left))
        (negb (float64_is_zero right)))).
  change
    ((if overflow then numeric_value_out_of_range
      else if underflow then numeric_value_out_of_range else None) = None <->
     overflow = false /\ underflow = false).
  unfold numeric_value_out_of_range.
  destruct overflow.
  - split; [discriminate | intros [H _]; discriminate].
  - destruct underflow.
    + split; [discriminate | intros [_ H]; discriminate].
    + split; [intro; now split | intro; reflexivity].
Qed.

Lemma float32_div_runtime_error_division_by_zero_iff : forall left right,
  float32_div_runtime_error
    [Value_float (Some left); Value_float (Some right)] =
      Some (DataException DivisionByZero) <->
  andb (float32_is_zero right) (negb (float32_is_nan left)) = true.
Proof.
  intros left right.
  set (zero_divisor :=
    andb (float32_is_zero right) (negb (float32_is_nan left))).
  set (overflow :=
    andb (float32_is_infinite (float32_div left right))
      (negb (float32_is_infinite left))).
  set (underflow :=
    andb (float32_is_zero (float32_div left right))
      (andb (negb (float32_is_zero left))
        (negb (float32_is_infinite right)))).
  change
    ((if zero_divisor then division_by_zero
      else if overflow then numeric_value_out_of_range
      else if underflow then numeric_value_out_of_range else None) =
        Some (DataException DivisionByZero) <->
     zero_divisor = true).
  unfold division_by_zero, numeric_value_out_of_range.
  destruct zero_divisor.
  - split; intro; reflexivity.
  - destruct overflow, underflow; split; intro H; discriminate.
Qed.

Lemma float64_div_runtime_error_division_by_zero_iff : forall left right,
  float64_div_runtime_error
    [Value_double (Some left); Value_double (Some right)] =
      Some (DataException DivisionByZero) <->
  andb (float64_is_zero right) (negb (float64_is_nan left)) = true.
Proof.
  intros left right.
  set (zero_divisor :=
    andb (float64_is_zero right) (negb (float64_is_nan left))).
  set (overflow :=
    andb (float64_is_infinite (float64_div left right))
      (negb (float64_is_infinite left))).
  set (underflow :=
    andb (float64_is_zero (float64_div left right))
      (andb (negb (float64_is_zero left))
        (negb (float64_is_infinite right)))).
  change
    ((if zero_divisor then division_by_zero
      else if overflow then numeric_value_out_of_range
      else if underflow then numeric_value_out_of_range else None) =
        Some (DataException DivisionByZero) <->
     zero_divisor = true).
  unfold division_by_zero, numeric_value_out_of_range.
  destruct zero_divisor.
  - split; intro; reflexivity.
  - destruct overflow, underflow; split; intro H; discriminate.
Qed.

Lemma float32_div_runtime_error_none_iff : forall left right,
  float32_div_runtime_error
    [Value_float (Some left); Value_float (Some right)] = None <->
  andb (float32_is_zero right) (negb (float32_is_nan left)) = false /\
  andb (float32_is_infinite (float32_div left right))
    (negb (float32_is_infinite left)) = false /\
  andb (float32_is_zero (float32_div left right))
    (andb (negb (float32_is_zero left))
      (negb (float32_is_infinite right))) = false.
Proof.
  intros left right.
  set (zero_divisor :=
    andb (float32_is_zero right) (negb (float32_is_nan left))).
  set (overflow :=
    andb (float32_is_infinite (float32_div left right))
      (negb (float32_is_infinite left))).
  set (underflow :=
    andb (float32_is_zero (float32_div left right))
      (andb (negb (float32_is_zero left))
        (negb (float32_is_infinite right)))).
  change
    ((if zero_divisor then division_by_zero
      else if overflow then numeric_value_out_of_range
      else if underflow then numeric_value_out_of_range else None) = None <->
     zero_divisor = false /\ overflow = false /\ underflow = false).
  unfold division_by_zero, numeric_value_out_of_range.
  destruct zero_divisor.
  - split; [discriminate | intros [H _]; discriminate].
  - destruct overflow.
    + split; [discriminate | intros [_ [H _]]; discriminate].
    + destruct underflow.
      * split; [discriminate | intros [_ [_ H]]; discriminate].
      * split; [intro; repeat split; reflexivity | intro; reflexivity].
Qed.

Lemma float64_div_runtime_error_none_iff : forall left right,
  float64_div_runtime_error
    [Value_double (Some left); Value_double (Some right)] = None <->
  andb (float64_is_zero right) (negb (float64_is_nan left)) = false /\
  andb (float64_is_infinite (float64_div left right))
    (negb (float64_is_infinite left)) = false /\
  andb (float64_is_zero (float64_div left right))
    (andb (negb (float64_is_zero left))
      (negb (float64_is_infinite right))) = false.
Proof.
  intros left right.
  set (zero_divisor :=
    andb (float64_is_zero right) (negb (float64_is_nan left))).
  set (overflow :=
    andb (float64_is_infinite (float64_div left right))
      (negb (float64_is_infinite left))).
  set (underflow :=
    andb (float64_is_zero (float64_div left right))
      (andb (negb (float64_is_zero left))
        (negb (float64_is_infinite right)))).
  change
    ((if zero_divisor then division_by_zero
      else if overflow then numeric_value_out_of_range
      else if underflow then numeric_value_out_of_range else None) = None <->
     zero_divisor = false /\ overflow = false /\ underflow = false).
  unfold division_by_zero, numeric_value_out_of_range.
  destruct zero_divisor.
  - split; [discriminate | intros [H _]; discriminate].
  - destruct overflow.
    + split; [discriminate | intros [_ [H _]]; discriminate].
    + destruct underflow.
      * split; [discriminate | intros [_ [_ H]]; discriminate].
      * split; [intro; repeat split; reflexivity | intro; reflexivity].
Qed.

(** Algebraic laws for the full finite/special NUMERIC carrier. *)

Lemma numeric_add_commutative : forall left right,
  numeric_add left right = numeric_add right left.
Proof.
  intros left right.
  destruct left as [|left| |]; destruct right as [|right| |];
    cbn [numeric_add]; try reflexivity.
  f_equal; apply Qcplus_comm.
Qed.

Lemma numeric_mul_commutative : forall left right,
  numeric_mul left right = numeric_mul right left.
Proof.
  intros left right.
  destruct left as [|left| |]; destruct right as [|right| |];
    cbn [numeric_mul numeric_mul_infinity numeric_sign]; try reflexivity.
  f_equal; apply Qcmult_comm.
Qed.

Lemma numeric_opp_involutive : forall value,
  numeric_opp (numeric_opp value) = value.
Proof.
  intro value; destruct value; cbn [numeric_opp]; try reflexivity.
  f_equal; apply Qcopp_involutive.
Qed.

Lemma numeric_add_zero_left : forall value,
  numeric_add numeric_zero value = value.
Proof.
  intro value; destruct value; cbn [numeric_add numeric_zero];
    try reflexivity.
  f_equal; apply Qcplus_0_l.
Qed.

Lemma numeric_sub_self_finite : forall value,
  numeric_sub (NumericFinite value) (NumericFinite value) = numeric_zero.
Proof.
  intro value.
  unfold numeric_sub, numeric_add, numeric_opp, numeric_zero.
  f_equal; apply Qcplus_opp_r.
Qed.

Lemma numeric_min_idempotent : forall value,
  numeric_min value value = value.
Proof.
  intro value; unfold numeric_min.
  now rewrite numeric_compare_refl.
Qed.

Lemma numeric_max_idempotent : forall value,
  numeric_max value value = value.
Proof.
  intro value; unfold numeric_max.
  now rewrite numeric_compare_refl.
Qed.

(** Finite values and special values remain distinguishable through the
    rounding and representation interfaces. *)

Lemma numeric_is_nan_true_iff : forall value,
  numeric_is_nan value = true <-> value = NumericNaN.
Proof.
  intro value; destruct value; cbn; split; intro H;
    try discriminate; reflexivity.
Qed.

Lemma numeric_rounded_coeff_some_iff : forall value scale coefficient,
  numeric_rounded_coeff value scale = Some coefficient <->
  exists finite,
    value = NumericFinite finite /\
    coefficient = numeric_finite_rounded_coeff finite scale.
Proof.
  intros value scale coefficient; destruct value as [|finite| |]; cbn.
  - split; [discriminate|intros [value [H _]]; discriminate].
  - split.
    + intro H; inversion H; subst.
      exists finite; split; reflexivity.
    + intros [value [Hequal Hcoefficient]].
      inversion Hequal; subst; reflexivity.
  - split; [discriminate|intros [value [H _]]; discriminate].
  - split; [discriminate|intros [value [H _]]; discriminate].
Qed.

Lemma numeric_decimal_parts_some_is_finite : forall value parts,
  numeric_decimal_parts value = Some parts ->
  exists finite, value = NumericFinite finite.
Proof.
  intros value parts Hparts.
  destruct value as [|finite| |]; try discriminate.
  now exists finite.
Qed.

Lemma numeric_round_special_identity : forall value scale,
  (value = NumericNegInfinity \/
   value = NumericPosInfinity \/
   value = NumericNaN) ->
  numeric_round_to_scale value scale = value.
Proof.
  intros value scale [-> | [-> | ->]]; reflexivity.
Qed.

Lemma numeric_runtime_fits_special : forall value,
  (value = NumericNegInfinity \/
   value = NumericPosInfinity \/
   value = NumericNaN) ->
  numeric_runtime_fits_bool value = true.
Proof.
  intros value [-> | [-> | ->]]; reflexivity.
Qed.

(** Typmod casts expose both their guard and their exact rounded result. *)

Lemma numeric_typmod_valid_true_iff : forall precision scale,
  numeric_typmod_valid_bool precision scale = true <->
  1 <= precision /\ precision <= numeric_max_precision /\
  numeric_min_scale <= scale /\ scale <= numeric_max_scale.
Proof.
  intros precision scale.
  unfold numeric_typmod_valid_bool.
  rewrite !Bool.andb_true_iff, !Z.leb_le.
  tauto.
Qed.

Lemma numeric_fits_typmod_true_implies_valid : forall value precision scale,
  numeric_fits_typmod_bool value precision scale = true ->
  numeric_typmod_valid_bool precision scale = true.
Proof.
  intros value precision scale Hfits.
  unfold numeric_fits_typmod_bool in Hfits.
  now apply Bool.andb_true_iff in Hfits.
Qed.

Lemma numeric_cast_typmod_some_iff : forall value precision scale result,
  numeric_cast_typmod value precision scale = Some result <->
  numeric_fits_typmod_bool value precision scale = true /\
  result = numeric_round_to_scale value scale.
Proof.
  intros value precision scale result.
  unfold numeric_cast_typmod.
  destruct (numeric_fits_typmod_bool value precision scale) eqn:Hfits.
  - split.
    + intro H; inversion H; now split.
    + intros [_ ->]; reflexivity.
  - split.
    + discriminate.
    + intros [H _]; discriminate.
Qed.

Lemma numeric_cast_typmod_none_iff : forall value precision scale,
  numeric_cast_typmod value precision scale = None <->
  numeric_fits_typmod_bool value precision scale = false.
Proof.
  intros value precision scale.
  unfold numeric_cast_typmod.
  destruct (numeric_fits_typmod_bool value precision scale) eqn:Hfits.
  - split; [discriminate|intro H; discriminate].
  - split; intro; reflexivity.
Qed.

Lemma numeric_cast_typmod_nan_iff : forall precision scale,
  numeric_cast_typmod NumericNaN precision scale = Some NumericNaN <->
  numeric_typmod_valid_bool precision scale = true.
Proof.
  intros precision scale.
  unfold numeric_cast_typmod, numeric_fits_typmod_bool.
  cbn [numeric_round_to_scale].
  destruct (numeric_typmod_valid_bool precision scale) eqn:Hvalid;
    cbn; split; intro H; try discriminate; reflexivity.
Qed.

Lemma numeric_cast_typmod_infinity_rejected : forall value precision scale,
  (value = NumericNegInfinity \/ value = NumericPosInfinity) ->
  numeric_cast_typmod value precision scale = None.
Proof.
  intros value precision scale [-> | ->];
    unfold numeric_cast_typmod, numeric_fits_typmod_bool;
    destruct (numeric_typmod_valid_bool precision scale); reflexivity.
Qed.

Lemma numeric_of_scaled_with_typmod_some_iff :
  forall precision scale coefficient result,
    numeric_of_scaled_with_typmod precision scale coefficient = Some result <->
    numeric_fits_typmod_bool
      (numeric_of_scaled coefficient scale) precision scale = true /\
    result = numeric_round_to_scale
      (numeric_of_scaled coefficient scale) scale.
Proof.
  intros precision scale coefficient result.
  unfold numeric_of_scaled_with_typmod.
  apply numeric_cast_typmod_some_iff.
Qed.

Lemma numeric_div_with_typmod_some_iff :
  forall left left_scale right right_scale precision scale result,
    numeric_div_with_typmod
      left left_scale right right_scale precision scale = Some result <->
    exists quotient,
      numeric_div_at_scales left left_scale right right_scale = Some quotient /\
      numeric_cast_typmod quotient precision scale = Some result.
Proof.
  intros left left_scale right right_scale precision scale result.
  unfold numeric_div_with_typmod.
  destruct (numeric_div_at_scales left left_scale right right_scale)
    as [quotient|] eqn:Hdivision.
  - split.
    + intro Hcast; exists quotient; now split.
    + intros [candidate [Hcandidate Hcast]].
      inversion Hcandidate; exact Hcast.
  - split.
    + discriminate.
    + intros [quotient [Hquotient _]].
      discriminate.
Qed.

(** Runtime classifiers are total under explicit representability premises. *)

Lemma numeric_result_runtime_error_none_iff : forall result,
  numeric_result_runtime_error result = None <->
  numeric_runtime_fits_bool result = true.
Proof.
  intro result; unfold numeric_result_runtime_error.
  destruct (numeric_runtime_fits_bool result) eqn:Hfits.
  - split; intro; reflexivity.
  - split; [discriminate|intro H; discriminate].
Qed.

Lemma numeric_binary_runtime_error_total : forall operation left right,
  numeric_runtime_fits_bool (operation left right) = true ->
  numeric_binary_runtime_error operation
    [Value_numeric (Some left); Value_numeric (Some right)] = None.
Proof.
  intros operation left right Hfits.
  cbn [numeric_binary_runtime_error].
  now apply numeric_result_runtime_error_none_iff.
Qed.

Lemma numeric_unary_runtime_error_total : forall operation input,
  numeric_runtime_fits_bool (operation input) = true ->
  numeric_unary_runtime_error operation [Value_numeric (Some input)] = None.
Proof.
  intros operation input Hfits.
  cbn [numeric_unary_runtime_error].
  now apply numeric_result_runtime_error_none_iff.
Qed.

Lemma numeric_typmod_runtime_error_success_iff :
  forall value precision scale,
    numeric_typmod_runtime_error
      [Value_numeric (Some value); Value_Z (Some precision);
       Value_Z (Some scale)] = None <->
    exists result,
      numeric_cast_typmod value precision scale = Some result.
Proof.
  intros value precision scale.
  cbn [numeric_typmod_runtime_error].
  destruct (numeric_cast_typmod value precision scale) as [result|] eqn:Hcast.
  - split; [intro; now exists result|intro; reflexivity].
  - split.
    + discriminate.
    + intros [result Hresult]; discriminate.
Qed.

Lemma numeric_typmod_runtime_error_failure_iff :
  forall value precision scale,
    numeric_typmod_runtime_error
      [Value_numeric (Some value); Value_Z (Some precision);
       Value_Z (Some scale)] =
      Some (DataException NumericValueOutOfRange) <->
    numeric_cast_typmod value precision scale = None.
Proof.
  intros value precision scale.
  cbn [numeric_typmod_runtime_error numeric_value_out_of_range].
  destruct (numeric_cast_typmod value precision scale);
    split; intro H; try discriminate; reflexivity.
Qed.

(** NUMERIC division keeps NaN, infinity, zero-divisor, and typmod behavior
    explicit rather than collapsing failures to NULL. *)

Lemma numeric_div_nan_left : forall right left_scale right_scale,
  numeric_div_at_scales NumericNaN left_scale right right_scale =
  Some NumericNaN.
Proof. intros right left_scale right_scale; destruct right; reflexivity. Qed.

Lemma numeric_div_nan_right : forall left left_scale right_scale,
  numeric_div_at_scales left left_scale NumericNaN right_scale =
  Some NumericNaN.
Proof. intros left left_scale right_scale; destruct left; reflexivity. Qed.

Lemma numeric_div_finite_by_infinity : forall finite divisor left_scale right_scale,
  (divisor = NumericNegInfinity \/ divisor = NumericPosInfinity) ->
  numeric_div_at_scales
    (NumericFinite finite) left_scale divisor right_scale = Some numeric_zero.
Proof.
  intros finite divisor left_scale right_scale [-> | ->]; reflexivity.
Qed.

Lemma numeric_div_runtime_error_zero_divisor : forall left left_scale right_scale,
  numeric_div_runtime_error
    [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
     Value_numeric (Some numeric_zero); Value_Z (Some right_scale)] =
  Some (DataException DivisionByZero).
Proof.
  intros left left_scale right_scale.
  cbn [numeric_div_runtime_error numeric_is_nan].
  rewrite numeric_eqb_refl; reflexivity.
Qed.

Lemma numeric_div_runtime_error_nan :
  forall left left_scale right right_scale,
    (numeric_is_nan left = true \/ numeric_is_nan right = true) ->
    numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] = None.
Proof.
  intros left left_scale right right_scale Hnan.
  cbn [numeric_div_runtime_error].
  apply Bool.orb_true_iff in Hnan.
  now rewrite Hnan.
Qed.

Lemma numeric_div_runtime_error_division_by_zero :
  forall left left_scale right right_scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = true ->
    numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] =
      Some (DataException DivisionByZero).
Proof.
  intros left left_scale right right_scale Hleft Hright Hzero.
  cbn [numeric_div_runtime_error division_by_zero].
  now rewrite Hleft, Hright, Hzero.
Qed.

Lemma numeric_div_runtime_error_success_iff :
  forall left left_scale right right_scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    (numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] = None <->
     exists result,
       numeric_div_at_scales left left_scale right right_scale = Some result /\
       numeric_runtime_fits_bool result = true).
Proof.
  intros left left_scale right right_scale
    Hleft Hright Hnonzero Hleft_scale Hright_scale.
  cbn [numeric_div_runtime_error].
  rewrite Hleft, Hright, Hnonzero, Hleft_scale, Hright_scale.
  cbn.
  destruct (numeric_div_at_scales left left_scale right right_scale)
    as [result |] eqn:Hdivision.
  - unfold numeric_result_runtime_error.
    destruct (numeric_runtime_fits_bool result) eqn:Hfits.
    + split.
      * intro; exists result; now split.
      * intro; reflexivity.
    + split; [discriminate |].
      intros [candidate [Hcandidate Hcandidate_fits]].
      inversion Hcandidate; subst; rewrite Hfits in Hcandidate_fits;
        discriminate.
  - split; [discriminate | intros [result [Hresult _]]; discriminate].
Qed.

Lemma numeric_div_runtime_error_invalid_scale :
  forall left left_scale right right_scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    (numeric_display_scale_valid_bool left_scale = false \/
     numeric_display_scale_valid_bool right_scale = false) ->
    numeric_div_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale)] =
      Some (DataException NumericValueOutOfRange).
Proof.
  intros left left_scale right right_scale
    Hleft Hright Hnonzero Hscale.
  cbn [numeric_div_runtime_error numeric_value_out_of_range].
  rewrite Hleft, Hright, Hnonzero.
  apply Bool.andb_false_iff in Hscale.
  now rewrite Hscale.
Qed.

Lemma numeric_div_typmod_runtime_error_success_iff :
  forall left left_scale right right_scale precision scale,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    (numeric_div_typmod_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale);
       Value_Z (Some precision); Value_Z (Some scale)] = None <->
     exists result,
       numeric_div_with_typmod
         left left_scale right right_scale precision scale = Some result).
Proof.
  intros left left_scale right right_scale precision scale
    Hleft Hright Hnonzero Hleft_scale Hright_scale.
  cbn [numeric_div_typmod_runtime_error].
  rewrite Hleft, Hright, Hnonzero, Hleft_scale, Hright_scale.
  destruct (numeric_div_with_typmod
    left left_scale right right_scale precision scale)
    as [result |] eqn:Hdivision.
  - split; [intro; now exists result | intro; reflexivity].
  - split; [discriminate | intros [result Hresult]; discriminate].
Qed.

Lemma numeric_div_typmod_runtime_error_total :
  forall left left_scale right right_scale precision scale result,
    numeric_is_nan left = false ->
    numeric_is_nan right = false ->
    numeric_eqb right numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_with_typmod
      left left_scale right right_scale precision scale = Some result ->
    numeric_div_typmod_runtime_error
      [Value_numeric (Some left); Value_Z (Some left_scale);
       Value_numeric (Some right); Value_Z (Some right_scale);
       Value_Z (Some precision); Value_Z (Some scale)] = None.
Proof.
  intros left left_scale right right_scale precision scale result
    Hleft_nan Hright_nan Hnonzero Hleft_scale Hright_scale Hdivision.
  cbn [numeric_div_typmod_runtime_error].
  rewrite Hleft_nan, Hright_nan, Hnonzero, Hleft_scale, Hright_scale,
    Hdivision.
  reflexivity.
Qed.

(** Aggregate finalizers separate empty state, special-value priority, and
    finite materialization. *)

Lemma numeric_sum_from_state_empty : forall state,
  numeric_sum_total_count state = 0 ->
  numeric_sum_from_state state = None.
Proof.
  intros state Hcount; unfold numeric_sum_from_state.
  now rewrite Hcount, Z.eqb_refl.
Qed.

Lemma numeric_sum_from_state_special : forall state special,
  numeric_sum_total_count state <> 0 ->
  numeric_agg_special_result
    (numeric_sum_nan_count state)
    (numeric_sum_pos_inf_count state)
    (numeric_sum_neg_inf_count state) = Some special ->
  numeric_sum_from_state state = Some special.
Proof.
  intros state special Hcount Hspecial.
  unfold numeric_sum_from_state.
  assert ((numeric_sum_total_count state =? 0) = false) as Hcountb.
  { now apply Z.eqb_neq. }
  rewrite Hcountb.
  now rewrite Hspecial.
Qed.

Lemma numeric_sum_from_state_finite : forall state,
  numeric_sum_total_count state <> 0 ->
  numeric_agg_special_result
    (numeric_sum_nan_count state)
    (numeric_sum_pos_inf_count state)
    (numeric_sum_neg_inf_count state) = None ->
  numeric_sum_from_state state =
    Some (NumericFinite (numeric_sum_finite_accumulator state)).
Proof.
  intros state Hcount Hspecial.
  unfold numeric_sum_from_state.
  assert ((numeric_sum_total_count state =? 0) = false) as Hcountb.
  { now apply Z.eqb_neq. }
  rewrite Hcountb.
  now rewrite Hspecial.
Qed.

Lemma numeric_avg_from_scale_state_empty : forall input_scale state,
  numeric_avg_scale_total_count state = 0 ->
  numeric_avg_from_scale_state input_scale state = None.
Proof.
  intros input_scale state Hcount; unfold numeric_avg_from_scale_state.
  now rewrite Hcount, Z.eqb_refl.
Qed.

Lemma numeric_avg_from_scale_state_finite :
  forall input_scale state result,
    numeric_avg_scale_total_count state <> 0 ->
    numeric_agg_special_result
      (numeric_avg_nan_count state)
      (numeric_avg_pos_inf_count state)
      (numeric_avg_neg_inf_count state) = None ->
    numeric_div_at_scales
      (numeric_of_scaled (numeric_avg_sum_coeff state) input_scale)
      input_scale
      (numeric_of_Z (numeric_avg_finite_count state)) 0 = Some result ->
    numeric_avg_from_scale_state input_scale state = Some result.
Proof.
  intros input_scale state result Hcount Hspecial Hdivision.
  unfold numeric_avg_from_scale_state.
  assert ((numeric_avg_scale_total_count state =? 0) = false) as Hcountb.
  { now apply Z.eqb_neq. }
  rewrite Hcountb.
  now rewrite Hspecial, Hdivision.
Qed.

Lemma numeric_agg_special_result_nan : forall nan_count pos_count neg_count,
  0 < nan_count ->
  numeric_agg_special_result nan_count pos_count neg_count = Some NumericNaN.
Proof.
  intros nan_count pos_count neg_count Hnan.
  unfold numeric_agg_special_result.
  assert ((0 <? nan_count) = true) as Hnanb.
  { now apply Z.ltb_lt. }
  now rewrite Hnanb.
Qed.

Lemma numeric_agg_special_result_mixed_infinities :
  forall nan_count pos_count neg_count,
    nan_count <= 0 -> 0 < pos_count -> 0 < neg_count ->
    numeric_agg_special_result nan_count pos_count neg_count = Some NumericNaN.
Proof.
  intros nan_count pos_count neg_count Hnan Hpos Hneg.
  unfold numeric_agg_special_result.
  assert ((0 <? nan_count) = false) as Hnanb.
  { now apply Z.ltb_ge. }
  assert ((0 <? pos_count) = true) as Hposb.
  { now apply Z.ltb_lt. }
  assert ((0 <? neg_count) = true) as Hnegb.
  { now apply Z.ltb_lt. }
  now rewrite Hnanb, Hposb, Hnegb.
Qed.

Lemma numeric_agg_special_result_positive_infinity :
  forall nan_count pos_count neg_count,
    nan_count <= 0 -> 0 < pos_count -> neg_count <= 0 ->
    numeric_agg_special_result nan_count pos_count neg_count =
      Some NumericPosInfinity.
Proof.
  intros nan_count pos_count neg_count Hnan Hpos Hneg.
  unfold numeric_agg_special_result.
  assert ((0 <? nan_count) = false) as Hnanb.
  { now apply Z.ltb_ge. }
  assert ((0 <? pos_count) = true) as Hposb.
  { now apply Z.ltb_lt. }
  assert ((0 <? neg_count) = false) as Hnegb.
  { now apply Z.ltb_ge. }
  now rewrite Hnanb, Hposb, Hnegb.
Qed.

Lemma numeric_agg_special_result_negative_infinity :
  forall nan_count pos_count neg_count,
    nan_count <= 0 -> pos_count <= 0 -> 0 < neg_count ->
    numeric_agg_special_result nan_count pos_count neg_count =
      Some NumericNegInfinity.
Proof.
  intros nan_count pos_count neg_count Hnan Hpos Hneg.
  unfold numeric_agg_special_result.
  assert ((0 <? nan_count) = false) as Hnanb.
  { now apply Z.ltb_ge. }
  assert ((0 <? pos_count) = false) as Hposb.
  { now apply Z.ltb_ge. }
  assert ((0 <? neg_count) = true) as Hnegb.
  { now apply Z.ltb_lt. }
  now rewrite Hnanb, Hposb, Hnegb.
Qed.

Lemma numeric_agg_special_result_none : forall nan_count pos_count neg_count,
  nan_count <= 0 -> pos_count <= 0 -> neg_count <= 0 ->
  numeric_agg_special_result nan_count pos_count neg_count = None.
Proof.
  intros nan_count pos_count neg_count Hnan Hpos Hneg.
  unfold numeric_agg_special_result.
  assert ((0 <? nan_count) = false) as Hnanb.
  { now apply Z.ltb_ge. }
  assert ((0 <? pos_count) = false) as Hposb.
  { now apply Z.ltb_ge. }
  assert ((0 <? neg_count) = false) as Hnegb.
  { now apply Z.ltb_ge. }
  now rewrite Hnanb, Hposb, Hnegb.
Qed.
