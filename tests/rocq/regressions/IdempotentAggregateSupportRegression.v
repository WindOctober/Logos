From SQLFS Require Import GenericInstance SqlErrorSemantics SqlOutcome Values.
From Logos.FormalSQL Require Import AggregateRuntimeFacts.
From Stdlib Require Import List ZArith.

Import ListNotations.
Import NullValues.

Open Scope Z_scope.

(** The generic interface exposes support invariance only after the caller
    supplies associativity, commutativity, and idempotence. *)
Lemma z_max_fold_support_interface : forall left right,
  (forall value, In value left <-> In value right) ->
  fold_nonempty Z.max left = fold_nonempty Z.max right.
Proof.
  intros left right Hsupport.
  apply fold_nonempty_support_equiv.
  - apply Z.max_comm.
  - intros; symmetry; apply Z.max_assoc.
  - apply Z.max_id.
  - exact Hsupport.
Qed.

(** Both ALL and DISTINCT use the same exact-extrema support boundary. *)
Lemma max_int32_aggregate_support_interface : forall quantifier left right,
  (forall value, In value left <-> In value right) ->
  interp_aggregate (AggregateCall AggregateMaxInt32 quantifier) left =
  interp_aggregate (AggregateCall AggregateMaxInt32 quantifier) right.
Proof.
  intros quantifier left right Hsupport.
  apply exact_extrema_aggregate_support_equiv.
  - tauto.
  - exact Hsupport.
Qed.

Lemma max_int32_aggregate_duplicate_block_interface :
  forall quantifier prefix block suffix,
    interp_aggregate (AggregateCall AggregateMaxInt32 quantifier)
      (prefix ++ block ++ block ++ suffix) =
    interp_aggregate (AggregateCall AggregateMaxInt32 quantifier)
      (prefix ++ block ++ suffix).
Proof.
  intros quantifier prefix block suffix.
  apply exact_extrema_aggregate_duplicate_block.
  tauto.
Qed.

(** Runtime preservation is separate from value support: this interface uses
    an identical reached observation block, so left-biased child-error choice
    is unchanged. *)
Lemma max_int32_runtime_duplicate_block_interface :
  forall quantifier prefix block suffix,
    interp_aggregate_runtime_error
      (AggregateCall AggregateMaxInt32 quantifier)
      (prefix ++ block ++ block ++ suffix) =
    interp_aggregate_runtime_error
      (AggregateCall AggregateMaxInt32 quantifier)
      (prefix ++ block ++ suffix).
Proof.
  intros quantifier prefix block suffix.
  apply exact_extrema_aggregate_runtime_error_duplicate_block.
  tauto.
Qed.

(** Repeating NULL and an invalidly typed value preserves full value support.
    The checked MAX interpreter therefore takes the same typed-NULL branch on
    both sides instead of silently assuming well-typed, non-NULL input. *)
Example max_z_null_invalid_support_interface :
  interp_aggregate (AggregateCall AggregateMaxZ AggregateAll)
    [Value_Z None; Value_bool (Some true); Value_Z None] =
  interp_aggregate (AggregateCall AggregateMaxZ AggregateAll)
    [Value_bool (Some true); Value_Z None].
Proof.
  apply exact_extrema_aggregate_support_equiv.
  - tauto.
  - intro current; cbn; tauto.
Qed.

(** DISTINCT, NULL, and the exact NUMERIC extremum share the same duplicate
    boundary; no fixed precision or scale enters this interface. *)
Example min_numeric_distinct_null_duplicate_interface :
  interp_aggregate (AggregateCall AggregateMinNumeric AggregateDistinct)
    ([Value_numeric None] ++
     [Value_numeric (Some numeric_zero)] ++
     [Value_numeric (Some numeric_zero)] ++ []) =
  interp_aggregate (AggregateCall AggregateMinNumeric AggregateDistinct)
    ([Value_numeric None] ++
     [Value_numeric (Some numeric_zero)] ++ []).
Proof.
  apply exact_extrema_aggregate_duplicate_block.
  tauto.
Qed.

(** C-collated TEXT MAX is included because [text_c_max] is proved ACI, not
    merely because it is syntactically another MAX constructor. *)
Lemma max_string_aggregate_support_interface : forall quantifier left right,
  (forall value, In value left <-> In value right) ->
  interp_aggregate (AggregateCall AggregateMaxString quantifier) left =
  interp_aggregate (AggregateCall AggregateMaxString quantifier) right.
Proof.
  intros quantifier left right Hsupport.
  apply exact_extrema_aggregate_support_equiv.
  - tauto.
  - exact Hsupport.
Qed.

(** The first error inside the repeated block remains authoritative; the later
    category is neither promoted nor erased by the duplicate. *)
Example duplicate_block_preserves_child_error_precedence :
  interp_aggregate_runtime_error
    (AggregateCall AggregateMaxZ AggregateAll)
    ([(None, Value_Z None)] ++
     [(Some CardinalityViolation, Value_Z None);
      (Some (DataException NumericValueOutOfRange), Value_Z None)] ++
     [(Some CardinalityViolation, Value_Z None);
      (Some (DataException NumericValueOutOfRange), Value_Z None)] ++
     [(Some (DataException DivisionByZero), Value_Z None)]) =
  interp_aggregate_runtime_error
    (AggregateCall AggregateMaxZ AggregateAll)
    ([(None, Value_Z None)] ++
     [(Some CardinalityViolation, Value_Z None);
      (Some (DataException NumericValueOutOfRange), Value_Z None)] ++
     [(Some (DataException DivisionByZero), Value_Z None)]).
Proof.
  apply exact_extrema_aggregate_runtime_error_duplicate_block.
  tauto.
Qed.

(** FLOAT/DOUBLE SUM and AVG intentionally have no corresponding
    support/duplicate theorem; their order-sensitive counterexamples remain
    exercised by [FloatAggregateOrderRegression]. *)

Print Assumptions fold_nonempty_support_equiv.
Print Assumptions exact_extrema_aggregate_permutation.
Print Assumptions exact_extrema_aggregate_support_equiv.
Print Assumptions exact_extrema_aggregate_duplicate_block.
Print Assumptions first_runtime_error_duplicate_block.
Print Assumptions first_observation_error_duplicate_block.
Print Assumptions exact_extrema_aggregate_runtime_error_duplicate_block.
