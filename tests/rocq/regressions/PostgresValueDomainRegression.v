(******************************************************************************)
(** PostgreSQL-realizable value-domain regressions for quantified databases. **)
(******************************************************************************)

From SQLFS Require Import
  GenericInstance SqlOutcome SqlSyntax ValueNumeric ValueString ValueTemporal
  ValueTextInteger Values.
From Stdlib Require Import Ascii List QArith Qcanon String ZArith.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.
Open Scope string_scope.

Example text_int32_accepts_postgres_integer_syntax :
  parse_text_integer_magnitude int32_min int32_max "  +1_024  " =
    TextIntegerValue 1024.
Proof. vm_compute; reflexivity. Qed.

Example text_int32_accepts_alternate_base :
  parse_text_integer_magnitude int32_min int32_max "-0x80000000" =
    TextIntegerValue int32_min.
Proof. vm_compute; reflexivity. Qed.

Example text_int32_matches_postgres_prefix_underscore_syntax :
  parse_text_integer_magnitude int32_min int32_max "0x_10" =
    TextIntegerValue 16 /\
  parse_text_integer_magnitude int32_min int32_max "_10" =
    TextIntegerInvalid.
Proof. vm_compute; split; reflexivity. Qed.

Example text_int64_accepts_extreme_values :
  parse_text_integer_magnitude int64_min int64_max "9223372036854775807" =
    TextIntegerValue int64_max.
Proof. vm_compute; reflexivity. Qed.

Example text_int32_reports_invalid_syntax :
  parse_text_int32 "ARCHIVED" = TextIntegerInvalid.
Proof. vm_compute; reflexivity. Qed.

Example text_int32_reports_range_overflow :
  parse_text_int32 "2147483648" = TextIntegerOutOfRange.
Proof. vm_compute; reflexivity. Qed.

Example text_int32_preserves_postgres_error_precedence :
  parse_text_int32 "99999999999x" = TextIntegerOutOfRange /\
  parse_text_int32 "2147483648x" = TextIntegerInvalid.
Proof. vm_compute; split; reflexivity. Qed.

Example character_padding_is_removed_before_integer_input :
  parse_text_integer_magnitude int32_min int32_max
    (string_cast_source_value (StringChar 8) "12      ") =
      TextIntegerValue 12.
Proof. vm_compute; reflexivity. Qed.

Example string_integer_cast_errors_are_observable :
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt32)
    [Value_string (StringValue StringText (Some "SECURITY"))] =
      Some (DataException InvalidTextRepresentation) /\
  scalar_operator_local_runtime_error
    (ScalarCast ScalarCastStringToInt64)
    [Value_string (StringValue StringText (Some "9223372036854775808"))] =
      Some (DataException NumericValueOutOfRange).
Proof. vm_compute; split; reflexivity. Qed.

(** Unconstrained NUMERIC is arbitrary precision, but still a finite decimal
    representation rather than an arbitrary rational. *)
Example repeating_rational_does_not_conform_to_numeric :
  ~ value_conforms_attribute
      (Attr_numeric "n")
      (NullValues.Value_numeric
        (Some (NumericFinite (Q2Qc (1 # 3)%Q)))).
Proof. vm_compute; discriminate. Qed.

(** TIMESTAMP(p) rounds values to a multiple of [10^(6-p)] microseconds when
    they enter the column. *)
Example half_second_does_not_conform_to_timestamp_zero :
  ~ value_conforms_attribute
      (Attr_timestamp "ts" 0)
      (NullValues.Value_timestamp (Some 500000)).
Proof. vm_compute; discriminate. Qed.

Example whole_second_conforms_to_timestamp_zero :
  value_conforms_attribute
    (Attr_timestamp "ts" 0)
    (NullValues.Value_timestamp (Some 1000000)).
Proof. vm_compute; reflexivity. Qed.

Example timestamp_infinity_ignores_precision :
  value_conforms_attribute
    (Attr_timestamp "ts" 0)
    (NullValues.Value_timestamp (Some postgres_timestamp_pos_infinity)).
Proof. vm_compute; reflexivity. Qed.

(** PostgreSQL text/varchar/character values cannot contain U+0000. *)
Example zero_byte_does_not_conform_to_text :
  ~ value_conforms_attribute
      (Attr_string "s" StringText)
      (NullValues.Value_string
        (StringText, Some (String (Ascii.ascii_of_nat 0) EmptyString))).
Proof.
vm_compute.
intros [_ [Hinvalid _]].
discriminate Hinvalid.
Qed.
