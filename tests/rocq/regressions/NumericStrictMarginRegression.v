From SQLFS Require Import ValueNumeric Values.
From Logos.FormalSQL Require Import NumericFacts.
From Stdlib Require Import Lia List QArith Qcanon ZArith.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.

(** The reusable coefficient interface exposes the exact half-unit error,
    independently of any particular aggregate or comparison threshold. *)
Theorem nonnegative_rounding_error_is_bounded :
  forall numerator denominator,
    0 <= numerator ->
    0 < denominator ->
    2 * numerator - denominator <=
      2 * numeric_round_quot numerator denominator * denominator <=
    2 * numerator + denominator.
Proof.
apply numeric_round_quot_nonnegative_half_ulp.
Qed.

Theorem scaled_cross_product_implies_numeric_order :
  forall left_coeff left_scale right_coeff right_scale,
    0 <= left_scale ->
    0 <= right_scale ->
    left_coeff * Z.pow 10 right_scale <
      right_coeff * Z.pow 10 left_scale ->
    numeric_compare
      (numeric_of_scaled left_coeff left_scale)
      (numeric_of_scaled right_coeff right_scale) = Lt.
Proof.
apply numeric_of_scaled_compare_lt.
Qed.


(** These small values select both rounding layers without fixing a schema,
    typmod, aggregate cardinality, or application threshold. *)
Example square_root_decimal_rounding_uses_half_unit_rule :
  numeric_sqrt_at_scale (numeric_of_Z 2) 1 =
    Some (numeric_of_scaled 14 1).
Proof. vm_compute; reflexivity. Qed.

Example square_root_decimal_rounding_can_round_up :
  numeric_sqrt_at_scale (numeric_of_Z 3) 0 =
    Some (numeric_of_scaled 2 0).
Proof. vm_compute; reflexivity. Qed.

Example square_root_decimal_halfway_tie_rounds_up :
  numeric_sqrt_at_scale (numeric_of_scaled 225 2) 0 =
    Some (numeric_of_scaled 2 0).
Proof. vm_compute; reflexivity. Qed.

Example finite_division_has_no_runtime_error_when_result_fits :
  numeric_div_runtime_error
    [Value_numeric (Some (numeric_of_Z 1)); Value_Z (Some 0);
     Value_numeric (Some (numeric_of_Z 8)); Value_Z (Some 0)] = None.
Proof. vm_compute; reflexivity. Qed.

(** A concrete finite instance discharges the exact final half-unit margin;
    this applies the theorem rather than merely computing the conclusion. *)
Local Transparent Qred.
Example finite_half_ratio_strict_margin_is_discharged :
  let left := Q2Qc (inject_Z 1) in
  let right := Q2Qc (inject_Z 2) in
  let quotient := Qcdiv left right in
  let scaled := this (Qcmult quotient (numeric_scale_factor 20)) in
  let result_coeff :=
    numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)) in
  numeric_div_at_scales
    (NumericFinite left) 0 (NumericFinite right) 0 =
      Some (numeric_of_scaled result_coeff 20) /\
  numeric_compare
    (numeric_of_scaled result_coeff 20) (numeric_of_scaled 1 0) = Lt /\
  numeric_div_runtime_error
    [Value_numeric (Some (NumericFinite left)); Value_Z (Some 0);
     Value_numeric (Some (NumericFinite right)); Value_Z (Some 0)] = None.
Proof.
apply
  (finite_numeric_division_strict_margin
    (Q2Qc (inject_Z 1)) (Q2Qc (inject_Z 2)) 0 0 20 1 0).
all: vm_compute; try reflexivity; try lia; try discriminate.
Qed.

Example finite_zero_divisor_error_is_reachable :
  numeric_div_runtime_error
    [Value_numeric (Some (numeric_of_Z 1)); Value_Z (Some 0);
     Value_numeric (Some numeric_zero); Value_Z (Some 0)] =
  Some (SqlOutcome.DataException SqlOutcome.DivisionByZero).
Proof. vm_compute; reflexivity. Qed.

Example finite_invalid_scale_error_is_reachable :
  numeric_div_runtime_error
    [Value_numeric (Some (numeric_of_Z 1)); Value_Z (Some (-1));
     Value_numeric (Some (numeric_of_Z 2)); Value_Z (Some 0)] =
  Some (SqlOutcome.DataException SqlOutcome.NumericValueOutOfRange).
Proof. vm_compute; reflexivity. Qed.

Example finite_nondecimal_scale_selection_error_is_reachable :
  numeric_div_runtime_error
    [Value_numeric (Some (NumericFinite (Q2Qc (1 # 3)%Q)));
     Value_Z (Some 0);
     Value_numeric (Some (numeric_of_Z 2)); Value_Z (Some 0)] =
  Some (SqlOutcome.DataException SqlOutcome.NumericValueOutOfRange).
Proof. vm_compute; reflexivity. Qed.

Theorem finite_out_of_range_result_error_is_preserved :
  forall left right left_scale right_scale result,
    numeric_eqb (NumericFinite right) numeric_zero = false ->
    numeric_display_scale_valid_bool left_scale = true ->
    numeric_display_scale_valid_bool right_scale = true ->
    numeric_div_at_scales
      (NumericFinite left) left_scale
      (NumericFinite right) right_scale = Some result ->
    numeric_runtime_fits_bool result = false ->
    numeric_div_runtime_error
      [Value_numeric (Some (NumericFinite left)); Value_Z (Some left_scale);
       Value_numeric (Some (NumericFinite right)); Value_Z (Some right_scale)] =
      Some (SqlOutcome.DataException SqlOutcome.NumericValueOutOfRange).
Proof.
apply finite_numeric_division_runtime_error_result_out_of_range.
Qed.

Check numeric_pg_div_scale_display_valid.
Check numeric_round_to_scale_nonnegative_half_ulp.
Check finite_numeric_division_result_rounding.
Check finite_numeric_division_strict_margin.
Check finite_numeric_division_runtime_error_zero_divisor.
Check finite_numeric_division_runtime_error_invalid_scale.
Check finite_numeric_division_runtime_error_missing_result.
Check finite_numeric_division_runtime_error_result_out_of_range.
Check numeric_sqrt_at_scale_half_ulp_shape.
Check numeric_integer_stddev_samp_positive_success_iff.
Check int32_avg_numeric_with_scale_success_iff.
Check numeric_of_scaled_compare_not_gt.
Check positive_numeric_of_scaled_nonzero.
Check numeric_runtime_fits_from_decimal_parts.

Print Assumptions numeric_round_quot_nonnegative_half_ulp.
Print Assumptions numeric_pg_div_scale_display_valid.
Print Assumptions numeric_of_scaled_compare_lt.
Print Assumptions numeric_round_to_scale_nonnegative_half_ulp.
Print Assumptions finite_numeric_division_result_rounding.
Print Assumptions finite_numeric_division_strict_margin.
Print Assumptions finite_numeric_division_runtime_error_zero_divisor.
Print Assumptions finite_numeric_division_runtime_error_invalid_scale.
Print Assumptions finite_numeric_division_runtime_error_missing_result.
Print Assumptions finite_numeric_division_runtime_error_result_out_of_range.
Print Assumptions numeric_sqrt_at_scale_half_ulp_shape.
Print Assumptions numeric_integer_stddev_samp_positive_success_iff.
Print Assumptions int32_avg_numeric_with_scale_success_iff.
Print Assumptions numeric_of_scaled_compare_not_gt.
Print Assumptions positive_numeric_of_scaled_nonzero.
Print Assumptions numeric_runtime_fits_from_decimal_parts.
