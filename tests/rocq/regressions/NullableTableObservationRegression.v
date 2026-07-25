(******************************************************************************)
(** Nullable-safe schema-to-table observation regressions.                   **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  SchemaConstraints SqlErrorSemantics SqlOutcome SqlQuerySemantics
  SqlQuerySyntax Values.
From Logos.FormalSQL Require Import QueryCardinality.

Import Tuple.

Section NullableTableObservationRegression.

Theorem nullable_schema_bag_observation_regression :
  forall expected constraints actual relation attribute rows,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_present_conforms attribute) rows.
Proof.
intros expected constraints actual relation attribute rows
  Hschema Hattribute Hrows.
eapply query_same_rows_as_conforming_table_present_attribute;
  eassumption.
Qed.

Theorem nullable_table_success_observation_regression :
  forall expected constraints actual relation attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_present_conforms attribute) rows.
Proof.
intros expected constraints actual relation attribute outputs env rows
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  Hschema Hattribute Hsort Hrows.
eapply query_expr_table_success_rows_present_conform_attribute;
  eassumption.
Qed.

End NullableTableObservationRegression.

Print Assumptions query_same_rows_as_conforming_table_present_attribute.
Print Assumptions query_expr_table_success_rows_present_conform_attribute.
