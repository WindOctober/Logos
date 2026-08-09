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
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @query_outputs_sort TNull outputs =S=
      @_basesort TNull actual relation ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    Forall (row_attribute_present_conforms attribute) rows.
Proof.
intros expected constraints actual relation attribute outputs env rows
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hattribute Hsort Hrows.
eapply query_expr_table_success_rows_present_conform_attribute;
eassumption.
Qed.

Theorem nullable_generated_sort_row_observation_regression :
  forall expected constraints actual relation attribute outputs env rows row
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    @_basesort TNull expected relation =S=
      @query_outputs_sort TNull outputs ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs relation)
      (SqlSuccess rows) ->
    In row rows ->
    row_attribute_present_conforms attribute row.
Proof.
intros expected constraints actual relation attribute outputs env rows row
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hattribute Hsort Hrows Hrow.
eapply query_expr_table_success_row_present_conform_attribute_generated_sort;
  eassumption.
Qed.

Theorem nonnull_generated_sort_row_observation_regression :
  forall expected constraints actual constraint attribute outputs env rows row
      unknown symbol_runtime_error aggregate_runtime_error value_is_null
      boolean_schedule,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    attribute inS
      (@_basesort TNull expected (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    @_basesort TNull expected (constraint_relation constraint) =S=
      @query_outputs_sort TNull outputs ->
    @eval_query_expr_outcome TNull relname
      (@_basesort TNull actual) (@_instance TNull actual)
      unknown symbol_runtime_error aggregate_runtime_error
      value_is_null boolean_schedule env
      (@QExpr_Table TNull relname outputs
        (constraint_relation constraint))
      (SqlSuccess rows) ->
    In row rows ->
    row_attribute_present_nonnull_conforms attribute row.
Proof.
intros expected constraints actual constraint attribute outputs env rows row
  unknown symbol_runtime_error aggregate_runtime_error value_is_null
  boolean_schedule
  Hschema Hconstraint Hattribute Hnot_null Hsort Hrows Hrow.
eapply query_expr_table_success_row_conform_attribute_generated_sort;
  eassumption.
Qed.

End NullableTableObservationRegression.

Print Assumptions query_same_rows_as_conforming_table_present_attribute.
Print Assumptions query_expr_table_success_rows_present_conform_attribute.
Print Assumptions
  query_expr_table_success_row_present_conform_attribute_generated_sort.
Print Assumptions
  query_expr_table_success_row_conform_attribute_generated_sort.
