# Schema conformance and integrity constraints

Route here for: typing/schema conformance, NOT NULL, PK/UNIQUE/FK/CHECK, unique indexes.

This focused catalog contains 62 declarations routed at declaration granularity from `IntegrityFacts.v`, `SchemaCardinality.v`. Source declarations are authoritative; every statement below is verbatim and has no proof body.

## `project_row_length`

Source: [`theories/FormalSQL/IntegrityFacts.v:15`](../IntegrityFacts.v#L15)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `projection` (rank 52), `cardinality` (rank 44), `schema` (rank 36)

Search aliases: `schema and integrity semantics`, `projection`, `SELECT list`, `cardinality`

```rocq
Lemma project_row_length :
  forall attributes row,
    List.length (project_row attributes row) = List.length attributes.
```

## `sql_key_equal_true_length`

Source: [`theories/FormalSQL/IntegrityFacts.v:25`](../IntegrityFacts.v#L25)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `cardinality` (rank 44), `schema` (rank 36)

Search aliases: `schema and integrity semantics`, `cardinality`

```rocq
Lemma sql_key_equal_true_length :
  forall left right,
    sql_key_equal_true left right ->
    List.length left = List.length right.
```

## `sql_key_equal_true_iff_Forall2`

Source: [`theories/FormalSQL/IntegrityFacts.v:42`](../IntegrityFacts.v#L42)

Purpose/direction: Gives necessary and sufficient conditions for schema and integrity reasoning.

Applicability: Use in either direction to invert or construct a goal about schema and integrity reasoning.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`

```rocq
Lemma sql_key_equal_true_iff_Forall2 :
  forall left right,
    sql_key_equal_true left right <->
    Forall2 sql_value_equal_true left right.
```

## `row_attributes_not_null_project`

Source: [`theories/FormalSQL/IntegrityFacts.v:72`](../IntegrityFacts.v#L72)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `row_attributes_not_null_project` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `projection` (rank 52), `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `projection`, `SELECT list`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma row_attributes_not_null_project :
  forall attributes row,
    row_attributes_not_null attributes row ->
    Forall
      (fun value => NullValues.is_null_value value = false)
      (project_row attributes row).
```

## `rows_attributes_not_null_weaken`

Source: [`theories/FormalSQL/IntegrityFacts.v:91`](../IntegrityFacts.v#L91)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `rows_attributes_not_null_weaken` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma rows_attributes_not_null_weaken :
  forall required declared rows,
    incl required declared ->
    rows_attributes_not_null declared rows ->
    rows_attributes_not_null required rows.
```

## `rows_attributes_not_null_filter`

Source: [`theories/FormalSQL/IntegrityFacts.v:104`](../IntegrityFacts.v#L104)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `rows_attributes_not_null_filter` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `filter` (rank 44), `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `filter`, `WHERE`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma rows_attributes_not_null_filter :
  forall attributes rows keep,
    rows_attributes_not_null attributes rows ->
    rows_attributes_not_null attributes (filter keep rows).
```

## `primary_key_component_not_null`

Source: [`theories/FormalSQL/IntegrityFacts.v:115`](../IntegrityFacts.v#L115)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `primary_key_component_not_null` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 22), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `integrity constraint`, `key`

```rocq
Lemma primary_key_component_not_null :
  forall primary_key rows row attribute,
    primary_key_conforms primary_key rows ->
    In row rows ->
    In attribute primary_key ->
    NullValues.is_null_value (dot TNull row attribute) = false.
```

## `primary_key_projection_not_null`

Source: [`theories/FormalSQL/IntegrityFacts.v:128`](../IntegrityFacts.v#L128)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `primary_key_projection_not_null` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit.

Cross-index: `projection` (rank 51), `schema` (rank 21), `scalar` (rank 51)

Search aliases: `schema and integrity semantics`, `projection`, `SELECT list`, `NULL`, `UNKNOWN`, `three-valued logic`, `integrity constraint`, `key`

```rocq
Corollary primary_key_projection_not_null :
  forall primary_key rows row,
    primary_key_conforms primary_key rows ->
    In row rows ->
    Forall
      (fun value => NullValues.is_null_value value = false)
      (project_row primary_key row).
```

## `unique_key_conforms_filter`

Source: [`theories/FormalSQL/IntegrityFacts.v:143`](../IntegrityFacts.v#L143)

Purpose/direction: States the unique key conforms filter law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `unique_key_conforms_filter` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 44), `schema` (rank 24)

Search aliases: `schema and integrity semantics`, `filter`, `WHERE`, `integrity constraint`, `key`

```rocq
Lemma unique_key_conforms_filter :
  forall key rows keep,
    unique_key_conforms key rows ->
    unique_key_conforms key (filter keep rows).
```

## `unique_key_pairwise_lookup_length_le_one`

Source: [`theories/FormalSQL/IntegrityFacts.v:157`](../IntegrityFacts.v#L157)

Purpose/direction: Provides the stated reusable upper bound for schema and integrity reasoning.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 38), `schema` (rank 22)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`, `cardinality`

```rocq
Theorem unique_key_pairwise_lookup_length_le_one :
  forall key rows keep,
    unique_key_conforms key rows ->
    (forall left right,
      In left rows ->
      In right rows ->
      keep left = true ->
      keep right = true ->
      sql_key_equal_true
        (project_row key left) (project_row key right)) ->
    (List.length (filter keep rows) <= 1)%nat.
```

## `foreign_key_conforms_shape`

Source: [`theories/FormalSQL/IntegrityFacts.v:182`](../IntegrityFacts.v#L182)

Purpose/direction: States the foreign key conforms shape law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `foreign_key_conforms_shape` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 26)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma foreign_key_conforms_shape :
  forall db rows foreign_key,
    foreign_key_conforms db rows foreign_key ->
    foreign_key_columns foreign_key <> nil /\
    List.length (foreign_key_columns foreign_key) =
      List.length (foreign_key_referenced_columns foreign_key).
```

## `foreign_key_conforms_nonnull_row_referenced`

Source: [`theories/FormalSQL/IntegrityFacts.v:195`](../IntegrityFacts.v#L195)

Purpose/direction: States the foreign key conforms nonnull row referenced law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `foreign_key_conforms_nonnull_row_referenced` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 26)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma foreign_key_conforms_nonnull_row_referenced :
  forall db rows foreign_key row,
    foreign_key_conforms db rows foreign_key ->
    In row rows ->
    row_attributes_not_null (foreign_key_columns foreign_key) row ->
    exists referenced_row,
      In referenced_row
        (instance_rows db
          (foreign_key_referenced_relation foreign_key)) /\
      foreign_key_key_equal_true
        (foreign_key_columns foreign_key)
        (foreign_key_referenced_columns foreign_key)
        row referenced_row.
```

## `foreign_key_conforms_filter`

Source: [`theories/FormalSQL/IntegrityFacts.v:221`](../IntegrityFacts.v#L221)

Purpose/direction: States the foreign key conforms filter law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `foreign_key_conforms_filter` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 44), `schema` (rank 26)

Search aliases: `schema and integrity semantics`, `filter`, `WHERE`, `integrity constraint`, `key`

```rocq
Lemma foreign_key_conforms_filter :
  forall db rows foreign_key keep,
    foreign_key_conforms db rows foreign_key ->
    foreign_key_conforms db (filter keep rows) foreign_key.
```

## `check_constraint_conforms_row`

Source: [`theories/FormalSQL/IntegrityFacts.v:237`](../IntegrityFacts.v#L237)

Purpose/direction: States the check constraint conforms row law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `check_constraint_conforms_row` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma check_constraint_conforms_row :
  forall db rows check row,
    check_constraint_conforms db rows check ->
    In row rows ->
    check_row_conforms db check row.
```

## `check_constraint_conforms_filter`

Source: [`theories/FormalSQL/IntegrityFacts.v:251`](../IntegrityFacts.v#L251)

Purpose/direction: States the check constraint conforms filter law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `check_constraint_conforms_filter` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 44), `schema` (rank 36)

Search aliases: `schema and integrity semantics`, `filter`, `WHERE`, `integrity constraint`, `key`

```rocq
Lemma check_constraint_conforms_filter :
  forall db rows check keep,
    check_constraint_conforms db rows check ->
    check_constraint_conforms db (filter keep rows) check.
```

## `check_constraint_conforms_app_iff`

Source: [`theories/FormalSQL/IntegrityFacts.v:265`](../IntegrityFacts.v#L265)

Purpose/direction: Gives necessary and sufficient conditions for schema and integrity reasoning.

Applicability: Use in either direction to invert or construct a goal about schema and integrity reasoning.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma check_constraint_conforms_app_iff :
  forall db left right check,
    check_constraint_conforms db (left ++ right) check <->
    check_constraint_conforms db left check /\
    check_constraint_conforms db right check.
```

## `unique_index_row_participates_iff`

Source: [`theories/FormalSQL/IntegrityFacts.v:278`](../IntegrityFacts.v#L278)

Purpose/direction: Gives necessary and sufficient conditions for schema and integrity reasoning.

Applicability: Use in either direction to invert or construct a goal about schema and integrity reasoning.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 24)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma unique_index_row_participates_iff :
  forall db index row,
    unique_index_row_participates db index row = true <->
    unique_index_predicate_error db row index = None /\
    unique_index_predicate_truth db row index = true3.
```

## `unique_index_without_predicate_participates`

Source: [`theories/FormalSQL/IntegrityFacts.v:309`](../IntegrityFacts.v#L309)

Purpose/direction: States the unique index without predicate participates law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `unique_index_without_predicate_participates` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 24), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `predicate`, `Bool3`, `integrity constraint`, `key`

```rocq
Lemma unique_index_without_predicate_participates :
  forall db index row,
    unique_index_predicate index = None ->
    unique_index_row_participates db index row = true.
```

## `unique_index_key_length`

Source: [`theories/FormalSQL/IntegrityFacts.v:323`](../IntegrityFacts.v#L323)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 44), `schema` (rank 24)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`, `cardinality`

```rocq
Lemma unique_index_key_length :
  forall terms row,
    List.length (unique_index_key terms row) = List.length terms.
```

## `unique_index_conforms_filter`

Source: [`theories/FormalSQL/IntegrityFacts.v:334`](../IntegrityFacts.v#L334)

Purpose/direction: States the unique index conforms filter law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `unique_index_conforms_filter` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 44), `schema` (rank 24)

Search aliases: `schema and integrity semantics`, `filter`, `WHERE`, `integrity constraint`, `key`

```rocq
Lemma unique_index_conforms_filter :
  forall db rows index keep,
    unique_index_conforms db rows index ->
    unique_index_conforms db (filter keep rows) index.
```

## `unique_index_pairwise_lookup_length_le_one`

Source: [`theories/FormalSQL/IntegrityFacts.v:362`](../IntegrityFacts.v#L362)

Purpose/direction: Provides the stated reusable upper bound for schema and integrity reasoning.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 38), `schema` (rank 22)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`, `cardinality`

```rocq
Theorem unique_index_pairwise_lookup_length_le_one :
  forall db rows index keep,
    unique_index_conforms db rows index ->
    (forall left right,
      In left rows ->
      In right rows ->
      unique_index_row_participates db index left = true ->
      unique_index_row_participates db index right = true ->
      keep left = true ->
      keep right = true ->
      sql_key_equal_true
        (unique_index_key (unique_index_terms index) left)
        (unique_index_key (unique_index_terms index) right)) ->
    (List.length
      (filter keep
        (filter (unique_index_row_participates db index) rows)) <= 1)%nat.
```

## `rows_constraint_conform_filter`

Source: [`theories/FormalSQL/IntegrityFacts.v:396`](../IntegrityFacts.v#L396)

Purpose/direction: States the rows constraint conform filter law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rows_constraint_conform_filter` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `filter` (rank 42), `schema` (rank 34)

Search aliases: `schema and integrity semantics`, `filter`, `WHERE`, `schema conformance`, `typing`

```rocq
Theorem rows_constraint_conform_filter :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows keep,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes (filter keep rows).
```

## `table_constraint_conforms_not_null`

Source: [`theories/FormalSQL/IntegrityFacts.v:440`](../IntegrityFacts.v#L440)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `table_constraint_conforms_not_null` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `NULL`, `UNKNOWN`, `three-valued logic`

```rocq
Lemma table_constraint_conforms_not_null :
  forall db constraint,
    table_constraint_conforms db constraint ->
    rows_attributes_not_null
      (constraint_not_null constraint)
      (instance_rows db (constraint_relation constraint)).
```

## `table_constraint_conforms_primary_key`

Source: [`theories/FormalSQL/IntegrityFacts.v:453`](../IntegrityFacts.v#L453)

Purpose/direction: States the table constraint conforms primary key law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `table_constraint_conforms_primary_key` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 22)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma table_constraint_conforms_primary_key :
  forall db constraint key,
    table_constraint_conforms db constraint ->
    constraint_primary_key constraint = Some key ->
    primary_key_conforms key
      (instance_rows db (constraint_relation constraint)).
```

## `table_constraint_conforms_unique_key`

Source: [`theories/FormalSQL/IntegrityFacts.v:467`](../IntegrityFacts.v#L467)

Purpose/direction: States the table constraint conforms unique key law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `table_constraint_conforms_unique_key` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 24)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma table_constraint_conforms_unique_key :
  forall db constraint key,
    table_constraint_conforms db constraint ->
    In key (constraint_unique_keys constraint) ->
    unique_key_conforms key
      (instance_rows db (constraint_relation constraint)).
```

## `table_constraint_conforms_foreign_key`

Source: [`theories/FormalSQL/IntegrityFacts.v:480`](../IntegrityFacts.v#L480)

Purpose/direction: States the table constraint conforms foreign key law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `table_constraint_conforms_foreign_key` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 26)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma table_constraint_conforms_foreign_key :
  forall db constraint foreign_key,
    table_constraint_conforms db constraint ->
    In foreign_key (constraint_foreign_keys constraint) ->
    foreign_key_conforms db
      (instance_rows db (constraint_relation constraint)) foreign_key.
```

## `table_constraint_conforms_check`

Source: [`theories/FormalSQL/IntegrityFacts.v:493`](../IntegrityFacts.v#L493)

Purpose/direction: States the table constraint conforms check law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `table_constraint_conforms_check` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`

```rocq
Lemma table_constraint_conforms_check :
  forall db constraint check,
    table_constraint_conforms db constraint ->
    In check (constraint_checks constraint) ->
    check_constraint_conforms db
      (instance_rows db (constraint_relation constraint)) check.
```

## `table_constraint_conforms_unique_index`

Source: [`theories/FormalSQL/IntegrityFacts.v:506`](../IntegrityFacts.v#L506)

Purpose/direction: States the table constraint conforms unique index law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `table_constraint_conforms_unique_index` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 24)

Search aliases: `schema and integrity semantics`, `integrity constraint`, `key`

```rocq
Lemma table_constraint_conforms_unique_index :
  forall db constraint index,
    table_constraint_conforms db constraint ->
    In index (constraint_unique_indexes constraint) ->
    unique_index_conforms db
      (instance_rows db (constraint_relation constraint)) index.
```

## `database_conforms_schema_table_constraint`

Source: [`theories/FormalSQL/IntegrityFacts.v:519`](../IntegrityFacts.v#L519)

Purpose/direction: States the database conforms schema table constraint law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `database_conforms_schema_table_constraint` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 28)

Search aliases: `schema and integrity semantics`, `schema conformance`, `typing`

```rocq
Lemma database_conforms_schema_table_constraint :
  forall expected constraints actual constraint,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    table_constraint_conforms actual constraint.
```

## `database_conforms_schema_not_null_member`

Source: [`theories/FormalSQL/IntegrityFacts.v:534`](../IntegrityFacts.v#L534)

Purpose/direction: Makes the SQL NULL/UNKNOWN branch explicit for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `database_conforms_schema_not_null_member` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; preserve the stated SQL NULL/Bool3 hypotheses; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 27), `scalar` (rank 51)

Search aliases: `schema and integrity semantics`, `NULL`, `UNKNOWN`, `three-valued logic`, `schema conformance`, `typing`

```rocq
Corollary database_conforms_schema_not_null_member :
  forall expected constraints actual constraint row attribute,
    database_conforms_schema expected constraints actual ->
    In constraint constraints ->
    In row (instance_rows actual (constraint_relation constraint)) ->
    In attribute (constraint_not_null constraint) ->
    NullValues.is_null_value (dot TNull row attribute) = false.
```

## `int32_domain_size_spec`

Source: [`theories/FormalSQL/SchemaCardinality.v:16`](../SchemaCardinality.v#L16)

Purpose/direction: States the int32 domain size spec law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_domain_size_spec` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_domain_size_spec :
  Z.of_nat int32_domain_size = int32_modulus.
```

## `int32_domain_size_is_two_power_32`

Source: [`theories/FormalSQL/SchemaCardinality.v:28`](../SchemaCardinality.v#L28)

Purpose/direction: States the int32 domain size is two power 32 law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_domain_size_is_two_power_32` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_domain_size_is_two_power_32 :
  Z.of_nat int32_domain_size = Z.pow 2 32.
```

## `database_conforms_schema_typed_cell`

Source: [`theories/FormalSQL/SchemaCardinality.v:45`](../SchemaCardinality.v#L45)

Purpose/direction: States the database conforms schema typed cell law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `database_conforms_schema_typed_cell` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 28)

Search aliases: `schema and integrity semantics`, `schema conformance`, `typing`

```rocq
Lemma database_conforms_schema_typed_cell :
  forall expected constraints actual relation row attribute,
    database_conforms_schema expected constraints actual ->
    In row (instance_rows actual relation) ->
    attribute inS (@_basesort TNull expected relation) ->
    value_conforms_attribute attribute (dot TNull row attribute).
```

## `rows_attribute_conform_from_database`

Source: [`theories/FormalSQL/SchemaCardinality.v:67`](../SchemaCardinality.v#L67)

Purpose/direction: States the rows attribute conform from database law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `rows_attribute_conform_from_database` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`, `schema conformance`, `typing`

```rocq
Lemma rows_attribute_conform_from_database :
  forall expected constraints actual relation attribute,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    rows_attribute_conform attribute (instance_rows actual relation).
```

## `conforming_int32_value`

Source: [`theories/FormalSQL/SchemaCardinality.v:80`](../SchemaCardinality.v#L80)

Purpose/direction: States the conforming int32 value law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `conforming_int32_value` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma conforming_int32_value :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    exists payload, value = NullValues.Value_int32 payload.
```

## `conforming_nonnull_int32_value`

Source: [`theories/FormalSQL/SchemaCardinality.v:90`](../SchemaCardinality.v#L90)

Purpose/direction: States the conforming nonnull int32 value law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `conforming_nonnull_int32_value` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma conforming_nonnull_int32_value :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    NullValues.is_null_value value = false ->
    exists integer, value = NullValues.Value_int32 (Some integer).
```

## `sql_value_equal_true_int32_refl`

Source: [`theories/FormalSQL/SchemaCardinality.v:107`](../SchemaCardinality.v#L107)

Purpose/direction: Establishes reflexivity for schema and integrity reasoning.

Applicability: Use to orient, transport, or compose a semantic relation about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; supply the declared equivalence/properness relation.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `equivalence`, `congruence`

```rocq
Lemma sql_value_equal_true_int32_refl :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    NullValues.is_null_value value = false ->
    sql_value_equal_true value value.
```

## `int32_index_lt`

Source: [`theories/FormalSQL/SchemaCardinality.v:125`](../SchemaCardinality.v#L125)

Purpose/direction: States the int32 index strict-bound law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_index_lt` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_index_lt :
  forall integer, (int32_index integer < int32_domain_size)%nat.
```

## `int32_index_in_domain`

Source: [`theories/FormalSQL/SchemaCardinality.v:138`](../SchemaCardinality.v#L138)

Purpose/direction: States the int32 index in domain law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_index_in_domain` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_index_in_domain :
  forall integer,
    In (int32_index integer) (seq 0 int32_domain_size).
```

## `int32_index_injective`

Source: [`theories/FormalSQL/SchemaCardinality.v:149`](../SchemaCardinality.v#L149)

Purpose/direction: Recovers source equality from the declared schema and integrity reasoning representation.

Applicability: Use when the goal or a hypothesis matches the `int32_index_injective` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_index_injective :
  forall left right,
    int32_index left = int32_index right ->
    left = right.
```

## `conforming_nonnull_int32_index_eq_iff`

Source: [`theories/FormalSQL/SchemaCardinality.v:176`](../SchemaCardinality.v#L176)

Purpose/direction: Gives necessary and sufficient conditions for schema and integrity reasoning.

Applicability: Use in either direction to invert or construct a goal about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 44)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma conforming_nonnull_int32_index_eq_iff :
  forall name left right,
    value_conforms_attribute (Attr_int32 name) left ->
    value_conforms_attribute (Attr_int32 name) right ->
    NullValues.is_null_value left = false ->
    NullValues.is_null_value right = false ->
    (int32_value_index left = int32_value_index right <-> left = right).
```

## `NoDup_map_by_key`

Source: [`theories/FormalSQL/SchemaCardinality.v:199`](../SchemaCardinality.v#L199)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `NoDup_map_by_key` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`

```rocq
Lemma NoDup_map_by_key :
  forall (row key code_type : Type)
         (key_of : row -> key) (code : row -> code_type) rows,
    NoDup (map key_of rows) ->
    (forall left right,
      In left rows ->
      In right rows ->
      code left = code right ->
      key_of left = key_of right) ->
    NoDup (map code rows).
```

## `int32_singleton_primary_key_projection_nodup`

Source: [`theories/FormalSQL/SchemaCardinality.v:231`](../SchemaCardinality.v#L231)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; keep schema/integrity conformance premises explicit.

Cross-index: `projection` (rank 52), `bag` (rank 52), `schema` (rank 22), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `projection`, `SELECT list`, `INTEGER`, `int32`, `integrity constraint`, `key`, `multiplicity`

```rocq
Lemma int32_singleton_primary_key_projection_nodup :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    NoDup (map (project_row [Attr_int32 name]) rows).
```

## `int32_singleton_primary_key_codes_nodup`

Source: [`theories/FormalSQL/SchemaCardinality.v:250`](../SchemaCardinality.v#L250)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; keep schema/integrity conformance premises explicit.

Cross-index: `bag` (rank 52), `schema` (rank 22), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `multiplicity`

```rocq
Lemma int32_singleton_primary_key_codes_nodup :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    NoDup
      (map
        (fun row => int32_value_index (dot TNull row (Attr_int32 name)))
        rows).
```

## `int32_singleton_primary_key_length`

Source: [`theories/FormalSQL/SchemaCardinality.v:280`](../SchemaCardinality.v#L280)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 36), `schema` (rank 20), `scalar` (rank 50)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Theorem int32_singleton_primary_key_length :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    (List.length rows <= int32_domain_size)%nat.
```

## `int32_singleton_primary_key_length_2_32`

Source: [`theories/FormalSQL/SchemaCardinality.v:314`](../SchemaCardinality.v#L314)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 37), `schema` (rank 21), `scalar` (rank 51)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Corollary int32_singleton_primary_key_length_2_32 :
  forall name rows,
    rows_attribute_conform (Attr_int32 name) rows ->
    primary_key_conforms [Attr_int32 name] rows ->
    Z.of_nat (List.length rows) <= Z.pow 2 32.
```

## `NoDup_map_fixed_pair`

Source: [`theories/FormalSQL/SchemaCardinality.v:330`](../SchemaCardinality.v#L330)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `NoDup_map_fixed_pair` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`

```rocq
Lemma NoDup_map_fixed_pair :
  forall (left right : Type) (fixed : left) (values : list right),
    NoDup values ->
    NoDup (map (fun value => (fixed, value)) values).
```

## `NoDup_list_prod`

Source: [`theories/FormalSQL/SchemaCardinality.v:346`](../SchemaCardinality.v#L346)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when the goal or a hypothesis matches the `NoDup_list_prod` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36)

Search aliases: `schema and integrity semantics`

```rocq
Lemma NoDup_list_prod :
  forall (left right : Type) (lefts : list left) (rights : list right),
    NoDup lefts ->
    NoDup rights ->
    NoDup (list_prod lefts rights).
```

## `int32_pair_index_injective`

Source: [`theories/FormalSQL/SchemaCardinality.v:371`](../SchemaCardinality.v#L371)

Purpose/direction: Recovers source equality from the declared schema and integrity reasoning representation.

Applicability: Use when the goal or a hypothesis matches the `int32_pair_index_injective` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_pair_index_injective :
  forall first_left second_left first_right second_right,
    int32_pair_index first_left second_left =
      int32_pair_index first_right second_right ->
    first_left = first_right /\ second_left = second_right.
```

## `conforming_nonnull_int32_pair_index_eq`

Source: [`theories/FormalSQL/SchemaCardinality.v:391`](../SchemaCardinality.v#L391)

Purpose/direction: States the conforming nonnull int32 pair index equality law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `conforming_nonnull_int32_pair_index_eq` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma conforming_nonnull_int32_pair_index_eq :
  forall first_name second_name
         first_left second_left first_right second_right,
    value_conforms_attribute (Attr_int32 first_name) first_left ->
    value_conforms_attribute (Attr_int32 second_name) second_left ->
    value_conforms_attribute (Attr_int32 first_name) first_right ->
    value_conforms_attribute (Attr_int32 second_name) second_right ->
    NullValues.is_null_value first_left = false ->
    NullValues.is_null_value second_left = false ->
    NullValues.is_null_value first_right = false ->
    NullValues.is_null_value second_right = false ->
    int32_value_pair_index first_left second_left =
      int32_value_pair_index first_right second_right ->
    first_left = first_right /\ second_left = second_right.
```

## `int32_composite_primary_key_projection_nodup`

Source: [`theories/FormalSQL/SchemaCardinality.v:431`](../SchemaCardinality.v#L431)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; keep schema/integrity conformance premises explicit.

Cross-index: `projection` (rank 52), `bag` (rank 52), `schema` (rank 22), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `projection`, `SELECT list`, `INTEGER`, `int32`, `integrity constraint`, `key`, `multiplicity`

```rocq
Lemma int32_composite_primary_key_projection_nodup :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    NoDup
      (map
        (project_row [Attr_int32 first_name; Attr_int32 second_name])
        rows).
```

## `int32_composite_primary_key_codes_nodup`

Source: [`theories/FormalSQL/SchemaCardinality.v:459`](../SchemaCardinality.v#L459)

Purpose/direction: Establishes the displayed duplicate-freedom property for schema and integrity reasoning.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary; keep schema/integrity conformance premises explicit.

Cross-index: `bag` (rank 52), `schema` (rank 22), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `multiplicity`

```rocq
Lemma int32_composite_primary_key_codes_nodup :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    NoDup
      (map
        (fun row =>
          int32_value_pair_index
            (dot TNull row (Attr_int32 first_name))
            (dot TNull row (Attr_int32 second_name)))
        rows).
```

## `int32_composite_primary_key_length`

Source: [`theories/FormalSQL/SchemaCardinality.v:500`](../SchemaCardinality.v#L500)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 36), `schema` (rank 20), `scalar` (rank 50)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Theorem int32_composite_primary_key_length :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    (List.length rows <= int32_domain_size * int32_domain_size)%nat.
```

## `int32_composite_domain_size_is_two_power_64`

Source: [`theories/FormalSQL/SchemaCardinality.v:549`](../SchemaCardinality.v#L549)

Purpose/direction: States the int32 composite domain size is two power 64 law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `int32_composite_domain_size_is_two_power_64` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma int32_composite_domain_size_is_two_power_64 :
  Z.of_nat (int32_domain_size * int32_domain_size) = Z.pow 2 64.
```

## `int32_composite_primary_key_length_2_64`

Source: [`theories/FormalSQL/SchemaCardinality.v:556`](../SchemaCardinality.v#L556)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 37), `schema` (rank 21), `scalar` (rank 51)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Corollary int32_composite_primary_key_length_2_64 :
  forall first_name second_name rows,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    Z.of_nat (List.length rows) <= Z.pow 2 64.
```

## `int32_composite_primary_key_fixed_first_length`

Source: [`theories/FormalSQL/SchemaCardinality.v:575`](../SchemaCardinality.v#L575)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 36), `schema` (rank 20), `scalar` (rank 50)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Theorem int32_composite_primary_key_fixed_first_length :
  forall first_name second_name rows fixed_first,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    Forall
      (fun row => dot TNull row (Attr_int32 first_name) = fixed_first)
      rows ->
    (List.length rows <= int32_domain_size)%nat.
```

## `int32_composite_primary_key_fixed_second_length`

Source: [`theories/FormalSQL/SchemaCardinality.v:644`](../SchemaCardinality.v#L644)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; keep schema/integrity conformance premises explicit.

Cross-index: `cardinality` (rank 36), `schema` (rank 20), `scalar` (rank 50)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `integrity constraint`, `key`, `cardinality`

```rocq
Theorem int32_composite_primary_key_fixed_second_length :
  forall first_name second_name rows fixed_second,
    rows_attribute_conform (Attr_int32 first_name) rows ->
    rows_attribute_conform (Attr_int32 second_name) rows ->
    primary_key_conforms
      [Attr_int32 first_name; Attr_int32 second_name] rows ->
    Forall
      (fun row => dot TNull row (Attr_int32 second_name) = fixed_second)
      rows ->
    (List.length rows <= int32_domain_size)%nat.
```

## `conforming_nullable_int32_index_lt`

Source: [`theories/FormalSQL/SchemaCardinality.v:718`](../SchemaCardinality.v#L718)

Purpose/direction: States the conforming nullable int32 index strict-bound law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `conforming_nullable_int32_index_lt` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma conforming_nullable_int32_index_lt :
  forall name value,
    value_conforms_attribute (Attr_int32 name) value ->
    (nullable_int32_value_index value < S int32_domain_size)%nat.
```

## `conforming_nullable_int32_index_eq_iff`

Source: [`theories/FormalSQL/SchemaCardinality.v:730`](../SchemaCardinality.v#L730)

Purpose/direction: Gives necessary and sufficient conditions for schema and integrity reasoning.

Applicability: Use in either direction to invert or construct a goal about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required.

Cross-index: `schema` (rank 36), `scalar` (rank 44)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma conforming_nullable_int32_index_eq_iff :
  forall name left right,
    value_conforms_attribute (Attr_int32 name) left ->
    value_conforms_attribute (Attr_int32 name) right ->
    (nullable_int32_value_index left = nullable_int32_value_index right <->
     left = right).
```

## `nullable_int32_nodup_length`

Source: [`theories/FormalSQL/SchemaCardinality.v:753`](../SchemaCardinality.v#L753)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 50), `cardinality` (rank 36), `schema` (rank 34), `scalar` (rank 50)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `cardinality`, `multiplicity`

```rocq
Theorem nullable_int32_nodup_length :
  forall name values,
    Forall (value_conforms_attribute (Attr_int32 name)) values ->
    NoDup values ->
    (List.length values <= S int32_domain_size)%nat.
```

## `nullable_int32_domain_size_is_two_power_32_plus_1`

Source: [`theories/FormalSQL/SchemaCardinality.v:802`](../SchemaCardinality.v#L802)

Purpose/direction: States the nullable int32 domain size is two power 32 plus 1 law for schema and integrity reasoning, in the exact direction displayed by the declaration.

Applicability: Use when the goal or a hypothesis matches the `nullable_int32_domain_size_is_two_power_32_plus_1` direction for schema and integrity reasoning; do not reverse or strengthen the displayed conclusion.

Important premises: No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration.

Cross-index: `schema` (rank 36), `scalar` (rank 52)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`

```rocq
Lemma nullable_int32_domain_size_is_two_power_32_plus_1 :
  Z.of_nat (S int32_domain_size) = Z.pow 2 32 + 1.
```

## `nullable_int32_nodup_length_2_32_plus_1`

Source: [`theories/FormalSQL/SchemaCardinality.v:809`](../SchemaCardinality.v#L809)

Purpose/direction: Relates schema and integrity reasoning to the exact list length or bag cardinality shown below.

Applicability: Use when moving from the modeled operator result to a bound, length, or occurrence fact about schema and integrity reasoning.

Important premises: every explicit antecedent (`->`) in the declaration is required; respect the exact list-versus-bag and multiplicity boundary.

Cross-index: `bag` (rank 51), `cardinality` (rank 37), `schema` (rank 35), `scalar` (rank 51)

Search aliases: `schema and integrity semantics`, `INTEGER`, `int32`, `cardinality`, `multiplicity`

```rocq
Corollary nullable_int32_nodup_length_2_32_plus_1 :
  forall name values,
    Forall (value_conforms_attribute (Attr_int32 name)) values ->
    NoDup values ->
    Z.of_nat (List.length values) <= Z.pow 2 32 + 1.
```
