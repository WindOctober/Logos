From Stdlib Require Import List String ZArith.
From SQLFS Require Import SqlOutcome SqlSyntax GenericInstance Values
  SqlQuerySyntax.
From Logos.FormalSQL Require Import
  TNullSyntax QueryTNullSyntax.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** Keep this module deliberately small.  It checks the pinned SQLFS load path,
    the concrete TNull adapter, and one generic Logos query-level theorem. *)
Check QExpr_Table.
Check NullValues.interp_scalar_operator.
Check NullValues.interp_aggregate.

Example tnull_scalar_adapter_preserves_sql_null :
  NullValues.interp_scalar_operator
    (ScalarCast ScalarCastInt32ToDouble)
    [NullValues.Value_int32 None] =
  NullValues.Value_double None.
Proof. reflexivity. Qed.
