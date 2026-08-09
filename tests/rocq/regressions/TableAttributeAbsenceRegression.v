(******************************************************************************)
(** Nullable-safe table attribute-absence observation regressions.           **)
(******************************************************************************)

From Stdlib Require Import List.
From SQLFS Require Import
  Bool3 Env FiniteBag FiniteCollection FiniteSet FTuples GenericInstance
  SchemaConstraints SqlErrorSemantics SqlOutcome SqlQuerySemantics
  SqlQuerySyntax SqlSyntax Values.
From Logos.FormalSQL Require Import QueryCardinality.

Import Tuple.

Section TableAttributeAbsenceRegression.

Theorem table_bag_absence_regression :
  forall actual relation attribute rows,
    database_values_conform actual ->
    (attribute inS? @_basesort TNull actual relation) = false ->
    @query_same_rows_as_bag TNull rows
      (@_instance TNull actual relation) ->
    Forall (row_attribute_absent attribute) rows.
Proof.
intros actual relation attribute rows Hvalues Habsent Hrows.
eapply query_same_rows_as_table_absent_attribute; eassumption.
Qed.

Theorem conforming_table_success_absence_regression :
  forall expected constraints actual relation attribute outputs env rows
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    (attribute inS? @_basesort TNull expected relation) = false ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_absent attribute) rows.
Proof.
intros expected constraints actual relation attribute outputs env rows
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Habsent Hsort Hrows.
eapply query_expr_table_success_rows_absent_attribute; eassumption.
Qed.

End TableAttributeAbsenceRegression.

Print Assumptions row_attribute_absent_proper.
Print Assumptions query_same_rows_as_table_absent_attribute.
Print Assumptions query_same_rows_as_conforming_table_absent_attribute.
Print Assumptions query_expr_table_success_rows_absent_attribute.
