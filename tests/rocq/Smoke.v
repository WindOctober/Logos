From Stdlib Require Import List String ZArith.
From SQLFS Require Import SqlAlgebra SqlOutcome SqlSyntax GenericInstance Values.
From Logos.FormalSQL Require Import
  TNullSyntax QueryTNullSyntax ErrorFacts.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** Keep this module deliberately small.  It checks the pinned SQLFS load path,
    the concrete TNull adapter, and one Logos query-level theorem. *)
Check SqlAlgebra.Q_Table.
Check NullValues.interp_scalar_operator.
Check NullValues.interp_aggregate.

Example logos_query_error_fact_is_available :
  ~ query_equiv init_db division_by_zero_query division_by_zero_query.
Proof.
exact division_by_zero_query_not_equivalent_to_itself.
Qed.

Example numeric_exp_display_scale_boundary_is_checked :
  NumericExpSuccessValid numeric_zero postgres_numeric_max_display_scale = true /\
  NumericExpSuccessValid numeric_zero
    (postgres_numeric_max_display_scale + 1) = false.
Proof.
vm_compute; split; reflexivity.
Qed.

Example tnull_scalar_adapter_preserves_sql_null :
  NullValues.interp_scalar_operator
    (ScalarCast ScalarCastInt32ToDouble)
    [NullValues.Value_int32 None] =
  NullValues.Value_double None.
Proof. reflexivity. Qed.
