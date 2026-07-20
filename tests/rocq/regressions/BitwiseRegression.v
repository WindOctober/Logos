From Stdlib Require Import Lia List Sorting.Permutation String ZArith
  ZArith.ZModOffset ZArith.Zbitwise ZArith.Znat Zmod.Bits.
From SQLFS Require Import GenericInstance SqlOutcome SqlSyntax Values.
From Logos.FormalSQL Require Import BitwiseFacts.

Import ListNotations.
Import NullValues.
Open Scope Z_scope.

(** Signed endpoints catch accidental reintroduction of wraparound arithmetic
    in the Logos bitwise aggregate bridge. *)
Example bitwise_signed_boundaries :
  interp_bit_and_int32
    [Value_int32 (Some (int32_from_twos_complement int32_min));
     Value_int32 (Some (int32_from_twos_complement int32_max))] =
    Value_int32 (Some (int32_from_twos_complement 0)) /\
  interp_bit_or_int64
    [Value_int64 (Some (int64_from_twos_complement int64_min));
     Value_int64 (Some (int64_from_twos_complement int64_max))] =
    Value_int64 (Some (int64_from_twos_complement (-1))).
Proof.
vm_compute; split; f_equal; f_equal.
- apply int32_ext; reflexivity.
- apply int64_ext; reflexivity.
Qed.

Example distinct_bitwise_aggregate_eliminates_duplicates :
  interp_aggregate (DistinctAggregate AggregateBitOrInt32)
    [Value_int32 (Some (int32_from_twos_complement 4));
     Value_int32 (Some (int32_from_twos_complement 4));
     Value_int32 (Some (int32_from_twos_complement 1))] =
  Value_int32 (Some (int32_from_twos_complement 5)).
Proof.
vm_compute; f_equal; f_equal; apply int32_ext; reflexivity.
Qed.

Example bitwise_aggregate_propagates_child_error :
  interp_aggregate_runtime_error (Aggregate AggregateBitAndInt32)
    [(Some (DataException DivisionByZero), Value_int32 None)] =
  Some (DataException DivisionByZero).
Proof. reflexivity. Qed.
