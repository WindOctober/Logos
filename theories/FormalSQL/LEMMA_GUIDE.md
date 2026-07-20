# Logos FormalSQL Lemma Guide

This guide lists Logos-local lemmas available to proof agents.  These files are
read-only proof context; generated proof attempts should edit only the generated
problem workspace.

## Generated Schema Constraints

`Schema.generated_schema_conforms db` is the complete trusted premise for a
generated database. It includes the exact relation names and base sorts,
`database_values_conform`, every declared `NOT NULL`, and every declared
primary key. Generated proofs must use this predicate directly rather than
reconstructing a weaker schema premise.

Base rows are exposed by `instance_rows` as `Febag.elements` of the stored
bag. The list retains bag multiplicity; it is never a set of rows. A primary
key requires a nonempty ordered attribute list, non-NULL projected components,
and `NoDup` of the projected key list.

Useful projection lemmas from
[`theories/FormalSQL/SchemaConstraints.v`] include:

- `instance_rows_nb_occ` for the bag/list multiplicity bridge;
- `primary_key_conforms_nonempty`, `primary_key_conforms_not_null`, and
  `primary_key_conforms_nodup`;
- `schema_constraints_conform_member` for selecting a generated table
  constraint;
- `database_conforms_schema_relnames`,
  `database_conforms_schema_basesort`,
  `database_conforms_schema_values`, and
  `database_conforms_schema_constraints`.

Carrier-list equality is exact for conforming `INT32` primary keys. When a
PostgreSQL operator class identifies more representations, structural `NoDup`
admits additional invalid database states and is therefore a conservative
over-approximation rather than a weakening of a proof obligation. Do not use a
string, float, numeric, partial, or otherwise non-`INT32` key to derive
PostgreSQL cardinality until a corresponding SQL-equality bridge is available.

## PostgreSQL INTEGER Cardinality

[`theories/FormalSQL/SchemaCardinality.v`] keeps the PostgreSQL `INTEGER`
domain size symbolic as `int32_domain_size`; its proved integer value is
`2^32`. Never unfold that constant beneath `seq`, `list_prod`, or natural-number
normalization. Use the exported bounds instead:

- `database_conforms_schema_typed_cell` and
  `rows_attribute_conform_from_database` transport generated schema typing to
  stored rows;
- `int32_singleton_primary_key_length_2_32` bounds a complete one-column
  `INT32` primary key by `2^32` rows;
- `int32_composite_primary_key_length_2_64` bounds a complete two-column
  `INT32` primary key by `2^64` rows;
- `int32_composite_primary_key_fixed_first_length` and
  `int32_composite_primary_key_fixed_second_length` give a `2^32` subgroup
  bound only when the other complete key component is explicitly fixed; and
- `nullable_int32_nodup_length_2_32_plus_1` bounds duplicate-free nullable
  `INT32` keys by `2^32 + 1` values, including SQL NULL.

A composite primary key does not make either component unique by itself.
The compact interface and primary-key regressions are in
[`tests/rocq/regressions/SchemaRegression.v`].

## Relational Occurrence Cardinality

[`theories/FormalSQL/QueryCardinality.v`] bounds successful relational
evaluation without changing ordered query semantics or quotienting duplicate
rows. Its list lemmas count occurrences, while the bag bridges use
`query_same_rows_as_bag` only after requiring the filter predicate to respect
`OTuple` equality through `tuple_predicate_proper`.

Useful results include:

- `theta_join_list_functional_length_le`,
  `two_way_filtered_cartesian_length_le`, and
  `three_way_filtered_cartesian_length_le`: a theta join, or a finite
  composition of such joins, does not increase the left occurrence count when
  every left occurrence has at most one accepted right occurrence;
- `raw_cross_filter_count_for_any_representative` and its nested-cross form:
  exact filtered counts transport from any valid cross-join representative to
  the concrete Cartesian list, provided the predicate is proper;
- `int32_primary_key_true_matches_at_most_one` and
  `null_int32_primary_key_matches_none`: PostgreSQL three-valued `INTEGER`
  equality turns a complete one-column primary key into an at-most-one match,
  while a NULL fact-side key matches no row;
- `int32_composite_primary_key_true_matches_at_most_one`: both equality
  conjuncts against a complete two-column `INTEGER` primary key give at most
  one match. One conjunct alone is never enough;
- `functional_theta_join_chain_length_le`: any finite left-deep chain of
  explicitly functional theta stages preserves the driver occurrence bound;
- `functional_chain_fixed_first_composite_int32_group_length_2_32` and
  `functional_chain_composite_int32_group_length_2_64`: parameterized bounds
  for an arbitrary finite functional chain whose driver has a complete
  two-column `INTEGER` primary key. The former requires one key component to
  be fixed; neither theorem fixes a query topology or stage count;
- `filter_rows_success_exact_count`: a successful FormalSQL filter has the
  exact occurrence count of a supplied Boolean predicate when every successful
  row evaluation is related explicitly; `filter_rows_error_observable` keeps
  runtime-error outcomes observable rather than treating them as empty rows;
- `query_make_groups_member_length_le` and
  `eval_groups_success_length_le`: grouping cannot make an individual group or
  a successful ordinary grouped output longer than its input occurrence list;
  and
- `functional_three_way_composite_int32_group_length_2_64_direct`: the
  parameterized noncanonical three-way handoff. It retains every functionality,
  predicate-properness, occurrence-count, and group-membership premise; it does
  not infer foreign keys or trust planner estimates.

These handoff lemmas deliberately expose predicate properness, exact
filter-count correspondence, and per-left-row dimension functionality as
premises. A concrete proof may instantiate those premises from its schema and
query, but no benchmark identifier or fixed query shape belongs in this public
module.

## PostgreSQL NUMERIC Facts

[`theories/FormalSQL/NumericFacts.v`] exposes NUMERIC properties in terms of
explicit precision, scale, operand, range, and representability premises. It
does not provide certificates specialized to a particular schema typmod or
benchmark.

- `numeric_cast_typmod_result` characterizes a successful constrained cast for
  arbitrary `precision` and `scale`;
- `numeric_avg_scale_transition_commutes` and
  `numeric_avg_scale_fold_permutation` provide order-independent AVG state
  transitions for an arbitrary attested scale;
- `numeric_avg_fixed_attested_finite_exact` recovers an arbitrary finite value
  from a successful `NUMERIC(precision, scale)` cast, while
  `numeric_avg_attested_scale_finite_exact` states the scale-only form;
- `finite_decimal_numeric_division_total` separates mathematical division
  totality from the concrete finite-decimal representation premises consumed
  by PostgreSQL's result-scale selection;
- `finite_numeric_division_runtime_error_none` separately requires valid input
  display scales, a successful division result, and the existing PostgreSQL
  runtime-fit check; and
- `numeric_positive_from_integer_lower_bound` turns any positive integral lower
  bound into the nonzero fact required by division.

Aggregate child errors, overflow limits, divisor guards, and cardinality bounds
remain explicit obligations. A proof may instantiate these generic lemmas with
the schema's actual typmod, but that instantiation belongs in the generated
problem proof rather than in the trusted Logos lemma library.


## Evaluation Outcomes

SQL runtime errors are outer evaluation outcomes, not SQL values.  They must
not be replaced with NULL, an empty relation, or a default value.  Frontend
parse failures and unsupported Logos lowering are not `sql_runtime_error`
constructors because no FormalSQL query exists in those cases.

```coq
Inductive sql_outcome (A : Type) : Type :=
  | SqlSuccess : A -> sql_outcome A
  | SqlError : sql_runtime_error -> sql_outcome A.
```

### `successful_outcome_equiv` [`vendor/FormalSQL/src/data/sql/SqlOutcome.v`]

Deterministic evaluations are equivalent only when both are successful and
their returned values satisfy the supplied relation.  Errors are never
equivalent, including two instances of the same error.

```coq
Definition successful_outcome_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A) : Prop :=
  match left, right with
  | SqlSuccess left_value, SqlSuccess right_value =>
      value_equiv left_value right_value
  | _, _ => False
  end.
```

### `successful_relation_equiv` [`vendor/FormalSQL/src/data/sql/SqlOutcome.v`]

For nondeterministic relational evaluators, equivalence requires a successful
output, excludes all error outcomes on both sides, and matches successful
outputs in both directions through the supplied observable-value relation.

```coq
Definition successful_relation_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) : Prop :=
  (exists value, left (SqlSuccess value)) /\
  (forall error, ~ left (SqlError error)) /\
  (forall error, ~ right (SqlError error)) /\
  (forall left_value,
    left (SqlSuccess left_value) ->
    exists right_value,
      right (SqlSuccess right_value) /\ value_equiv left_value right_value) /\
  (forall right_value,
    right (SqlSuccess right_value) ->
    exists left_value,
      left (SqlSuccess left_value) /\ value_equiv left_value right_value).
```

### `outcome_equiv` and `outcome_relation_equiv` [`vendor/FormalSQL/src/data/sql/SqlOutcome.v`]

Error-preserving mode compares every observable outcome. Deterministic errors
must carry the same `sql_runtime_error`; relational evaluators must match every
successful observation in both directions and expose exactly the same set of
error categories. Both outcome relations must be inhabited, so two incomplete
evaluators cannot be vacuously equivalent. Use `outcome_relation_equiv_refl`
for an inhabited identical outcome relation and `outcome_relation_equiv_intro`
for the two inhabitance and three matching obligations.

```coq
Definition outcome_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A) : Prop :=
  match left, right with
  | SqlSuccess left_value, SqlSuccess right_value =>
      value_equiv left_value right_value
  | SqlError left_error, SqlError right_error =>
      left_error = right_error
  | _, _ => False
  end.
```

`query_expr_outcome_equiv` and `query_program_outcome_equiv` in
`SqlQuerySemantics.v` add exact ordered output-schema equality and lift this
relation pointwise over a read-only query program. Both safe and
error-preserving query equivalence compare ordered result lists with
`ordered_rows_equiv`: order and multiplicity are exact, while corresponding
rows use `OTuple`'s extensional SQL-row equality rather than Coq representation
equality.

### `query_expr_equiv_implies_outcome_equiv` and `query_program_equiv_implies_outcome_equiv` [`vendor/FormalSQL/src/data/sql/SqlQuerySemantics.v`]

A safe equivalence proof is a stronger certificate than error-preserving
equivalence. In `OUTCOME-UNCONDITIONAL` mode, prove safety in Rocq and apply one
of these lemmas when that route is simpler. The host does not classify a query
as safe.

### Structured conditional verification [`theories/FormalSQL/VerificationConditions.v`]

Conditional mode permits only the closed `verification_condition` language:
typed column bounds/nonzero/non-NULL/string-length facts, relation cardinality,
conjunction, and `ConditionTrue`. `precondition_source_obligation` requires a
well-formed condition and then distinguishes two certificate strengths:

- `PreconditionDerived`: every database satisfying the generated schema
  contract already satisfies the condition;
- `PreconditionExternal`: at least one database jointly satisfies the original
  contract and the additional condition.

Generated conditional proofs must define `generated_precondition` and a direct,
fully qualified `generated_precondition_source` using
`Logos.FormalSQL.VerificationConditions.PreconditionDerived` or
`Logos.FormalSQL.VerificationConditions.PreconditionExternal`, prove
`generated_precondition_valid`, and then prove outcome equivalence under the
condition. Do not encode query evaluation or the desired equivalence inside a
precondition; the closed syntax intentionally has no such constructor.

### `query_equiv_iff_success_and_bag_equality` [`theories/FormalSQL/TNullSyntax.v`]

Query equivalence consists of three obligations: both evaluations are free of
runtime errors, and their successful bag results are equal.

```coq
Lemma query_equiv_iff_success_and_bag_equality :
  forall db q1 q2,
    query_equiv db q1 q2 <->
    query_succeeds db q1 /\
    query_succeeds db q2 /\
    eval_query_in_state db q1 =BE= eval_query_in_state db q2.
```

### `query_runtime_error_not_equiv_left` [`theories/FormalSQL/ErrorFacts.v`]

A query that raises a runtime error cannot be equivalent to any query.

```coq
Lemma query_runtime_error_not_equiv_left :
  forall db q1 q2 error,
    query_runtime_error_in_state db q1 = Some error ->
    ~ query_equiv db q1 q2.
```

### `query_runtime_error_not_equiv_right` [`theories/FormalSQL/ErrorFacts.v`]

The corresponding rule when the right query raises a runtime error.

```coq
Lemma query_runtime_error_not_equiv_right :
  forall db q1 q2 error,
    query_runtime_error_in_state db q2 = Some error ->
    ~ query_equiv db q1 q2.
```

## Numeric Semantics

FormalSQL uses one canonical runtime domain, `numeric`, for finite values,
PostgreSQL infinities, and `NaN`. Canonical rational equality ensures that
values such as `1`, `1.0`, and `1.00` are identical in predicates, bags, set
operations, grouping, and `DISTINCT`. Special values use PostgreSQL's total
order `-Infinity < finite < Infinity < NaN`; `NaN` equals itself. Precision and
declared scale remain explicit parameters validated by
`numeric_typmod_valid_bool` and are applied by casts, typed writes, and
generated schema-conformance preconditions. PostgreSQL
display scale is not part of numeric equality, so scale-sensitive operations
receive it explicitly. The lowering rejects such an operation when the scale
cannot be derived from a column typmod, literal, explicit cast, or a modeled
arithmetic expression. Unconstrained table-backed `NUMERIC` remains rejected
because per-value display scale is not represented; constrained `DECIMAL(p,s)`
cannot store infinities and is fully modeled with finite values plus `NaN`.
PostgreSQL numeric operators expose typmodless
`numeric` results unless an explicit typmod cast surrounds the expression;
FormalSQL therefore keeps inferred operand display scale separate from the
typed output signature.

```coq
Inductive numeric : Set :=
  | NumericNegInfinity : numeric
  | NumericFinite : Qc -> numeric
  | NumericPosInfinity : numeric
  | NumericNaN : numeric.

Definition numeric_typmod_valid_bool (precision scale : Z) : bool :=
  (1 <=? precision)
  && (precision <=? numeric_max_precision)
  && (numeric_min_scale <=? scale)
  && (scale <=? numeric_max_scale).
```

### `numeric_compare_refl` [`theories/FormalSQL/NumericFacts.v`]

Canonical numeric comparison is reflexive.

```coq
Lemma numeric_compare_refl :
  forall value,
    numeric_compare value value = Eq.
```

### `numeric_eqb_refl` [`theories/FormalSQL/NumericFacts.v`]

Numeric boolean equality identifies every canonical value with itself.

```coq
Lemma numeric_eqb_refl :
  forall value,
    numeric_eqb value value = true.
```

### `numeric_cast_typmod_result` [`theories/FormalSQL/NumericFacts.v`]

A successful cast to `DECIMAL(p,s)` is the numeric value rounded to the
declared scale; the cast succeeds only when the rounded coefficient fits the
declared precision.

```coq
Lemma numeric_cast_typmod_result :
  forall value precision scale result,
    numeric_cast_typmod value precision scale = Some result ->
    result = numeric_round_to_scale value scale.
```

### `int32_checked_outside_range` [`vendor/FormalSQL/src/data/proof_of_concept/ValueInteger.v`]

The checked PostgreSQL `INTEGER` constructor returns no value outside the
signed int4 range. Runtime-aware casts use this fact to turn the failed value
construction into `NumericValueOutOfRange` rather than SQL NULL.

```coq
Lemma int32_checked_outside_range : forall z,
  z < int32_min \/ int32_max < z -> int32_checked z = None.
```

### `int32_value_in_int64_range` [`vendor/FormalSQL/src/data/proof_of_concept/ValueInteger.v`]

Every PostgreSQL `INTEGER` value lies in the signed `BIGINT` range. The
resulting `int32_to_int64` conversion is an exact total representation change,
so its interpreter preserves NULL and has no local runtime error.

```coq
Lemma int32_value_in_int64_range : forall value,
  int64_min <= int32_value value <= int64_max.
```

### `numeric_to_int32_checked_result_in_range` [`theories/FormalSQL/NumericFacts.v`]

A successful `NUMERIC`/`DECIMAL` to `INTEGER` conversion has already rounded
ties away from zero and passed the signed int4 bounds. Special numeric values
are classified separately as PostgreSQL `FeatureNotSupported` runtime errors.

```coq
Lemma numeric_to_int32_checked_result_in_range :
  forall value result,
    numeric_to_int32_checked value = Some result ->
    int32_min <= int32_value result <= int32_max.
```

### `finite_numeric_div_by_zero` [`theories/FormalSQL/NumericFacts.v`]

Finite numeric division reports failure on a zero divisor. The error-aware
evaluator maps this failure to `SqlError (DataException DivisionByZero)` rather
than SQL NULL. PostgreSQL checks numeric special values first, so `NaN / 0` and
`0 / NaN` instead return `NaN`; the runtime-error interpreter follows the same
precedence.

```coq
Lemma finite_numeric_div_by_zero :
  forall value,
    numeric_div_at_scales (NumericFinite value) 0 numeric_zero 0 = None.
```

## Character Typmod Semantics

FormalSQL represents `TEXT`, unbounded `VARCHAR`, `VARCHAR(n)`, `CHAR(n)`, and
typmodless PostgreSQL `BPCHAR` with one string value domain and an explicit
`string_typmod`.  The typmod is
retained by NULL values and output attributes.  `VARCHAR(n)` constrains length
without padding; `CHAR(n)` has canonical trailing-blank-insensitive values and
can reconstruct physical padding when an operation observes it. Typmod length
and truncation validate UTF-8 and count Unicode code points. Generated schema
preconditions require every tuple value to match its attribute typmod and use a
canonical payload. Under the explicitly selected PostgreSQL UTF-8/libc-C
environment (default collation `C`, character classification `C`, locale
provider `libc`, and server encoding `UTF8`), FormalSQL's string order is the
lexicographic order of UTF-8 bytes, `UPPER`/`LOWER` map ASCII letters only, and
`MAX(TEXT)` uses that same byte order. Omitting any one environment dimension
does not select these rules. Explicit `COLLATE` clauses and other locale
environments remain outside the supported correspondence boundary. At the
trusted Rust boundary, one ordering-free PostgreSQL normalization is accepted
under the deterministic-default-collation contract: for a direct `TEXT`
reference and the same untyped literal, `(x < c OR x > c)` is rewritten to
`x <> c`. Trichotomy proves the non-NULL case and strictness preserves UNKNOWN
for NULL; other ordering shapes remain rejected unless the complete explicit
UTF-8/libc-C environment is present.

```coq
Inductive string_typmod : Set :=
  | StringText
  | StringVarchar
  | StringVarcharN (limit : nat)
  | StringChar (width : nat)
  | StringBpchar.
```

`StringBpchar` is produced when PostgreSQL operator or common-type resolution
discards a fixed `CHAR(n)` width. It retains blank-padded comparison semantics
but has no length at which casts may truncate or pad a value.

These string operations are part of the SQLFS semantic contract. Logos does not
maintain a parallel concrete-example suite for them; Rust integration tests and
generated-query checks cover the adapter boundary.

## Occurrence Semantics

### `query_occ` [`theories/FormalSQL/OccFacts.v`]

multiplicity of tuple `t` in the result of query `q`
on database state `db`.

```coq
Definition query_occ (db : db_state) (q : Query) (t : tuple TNull) :=
  Febag.nb_occ _ t (eval_query_in_state db q).
```

### `query_nonempty` [`theories/FormalSQL/OccFacts.v`]

query `q` has at least one output tuple on `db`.

```coq
Definition query_nonempty (db : db_state) (q : Query) : Prop :=
  exists t, t inBE eval_query_in_state db q.
```

### `query_equiv_iff_occ` [`theories/FormalSQL/OccFacts.v`]

Query equivalence is exactly runtime success on both sides plus pointwise
equality of tuple multiplicities.

```coq
Lemma query_equiv_iff_occ :
  forall db q1 q2,
    query_equiv db q1 q2 <->
    query_succeeds db q1 /\
    query_succeeds db q2 /\
    forall t, query_occ db q1 t = query_occ db q2 t.
```

### `pi_congr` [`theories/FormalSQL/OccFacts.v`]

If two input queries are equivalent and both projected queries are runtime
safe, applying the same projection preserves equivalence.

```coq
Lemma pi_congr :
  forall db s q1 q2,
    query_equiv db q1 q2 ->
    query_succeeds db (Pi s q1) ->
    query_succeeds db (Pi s q2) ->
    query_equiv db (Pi s q1) (Pi s q2).
```

### `sigma_congr` [`theories/FormalSQL/OccFacts.v`]

If two input queries are equivalent and both filtered queries are runtime safe,
filtering both by the same predicate preserves equivalence.

```coq
Lemma sigma_congr :
  forall db f q1 q2,
    query_equiv db q1 q2 ->
    query_succeeds db (Sigma f q1) ->
    query_succeeds db (Sigma f q2) ->
    query_equiv db (Sigma f q1) (Sigma f q2).
```

### `query_satisfies_of_equiv` [`theories/FormalSQL/OccFacts.v`]

an invariant that holds for all output tuples of a
query also holds for any bag-equivalent query.

```coq
Lemma query_satisfies_of_equiv :
  forall db q1 q2 f,
    query_equiv db q1 q2 ->
    query_satisfies db q1 f ->
    query_satisfies db q2 f.
```

## Projection Facts

### `well_sorted_database` [`theories/FormalSQL/PiFacts.v`]

every tuple stored in each base table has labels equal
to the table schema sort.

```coq
Definition well_sorted_database (db : db_state) : Prop :=
  forall tbl t,
    t inBE (@_instance TNull db tbl) ->
    labels TNull t =S= @_basesort TNull db tbl.
```

### `select_list_sort` [`vendor/FormalSQL/src/data/flat/Projection.v`]

The output label set derived from the authoritative ordered select-list
outputs.

```coq
Definition select_list_sort (las : _select_list) : Fset.set (A T) :=
  Fset.mk_set (A T) (select_list_outputs las).
```

### `pi_sort` [`theories/FormalSQL/PiFacts.v`]

the FormalSQL sort of `Pi s q` is exactly the output
sort of `s`.

```coq
Lemma pi_sort :
  forall db s q,
    @sort TNull relname (@_basesort TNull db) (Pi s q) =S= select_list_sort s.
```

### `pi_output_tuple_has_select_list_sort` [`theories/FormalSQL/PiFacts.v`]

every tuple output by a projection has labels equal to
the select-list output sort.

```coq
Lemma pi_output_tuple_has_select_list_sort :
  forall db s q t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s q) ->
    labels TNull t =S= select_list_sort s.
```

### `common_pi_output_tuple_implies_same_select_list_sort` [`theories/FormalSQL/PiFacts.v`]

if the same tuple appears in two projected outputs,
then the two select lists have the same output sort.

```coq
Lemma common_pi_output_tuple_implies_same_select_list_sort :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    t inBE eval_query_in_state db (Pi s2 q2) ->
    select_list_sort s1 =S= select_list_sort s2.
```

### `pi_sort_mismatch_not_equiv_with_witness` [`theories/FormalSQL/PiFacts.v`]

if one projected result is nonempty and the two
select-list output sorts differ, then the projected queries are not equivalent.

```coq
Lemma pi_sort_mismatch_not_equiv_with_witness :
  forall db s1 q1 s2 q2 t,
    well_sorted_database db ->
    t inBE eval_query_in_state db (Pi s1 q1) ->
    (select_list_sort s1 =S= select_list_sort s2 -> False) ->
    ~ query_equiv db (Pi s1 q1) (Pi s2 q2).
```

### `nonempty_pi_equiv_iff_sort_and_occ` [`theories/FormalSQL/PiFacts.v`]

for nonempty projected outputs over a well-sorted
database, query equivalence is equivalent to equal output sorts plus pointwise
equality of tuple multiplicities.

```coq
Lemma nonempty_pi_equiv_iff_sort_and_occ :
  forall db s1 q1 s2 q2,
    well_sorted_database db ->
    query_nonempty db (Pi s1 q1) ->
    query_equiv db (Pi s1 q1) (Pi s2 q2) <->
      query_succeeds db (Pi s1 q1) /\
      query_succeeds db (Pi s2 q2) /\
      select_list_sort s1 =S= select_list_sort s2 /\
      forall t, query_occ db (Pi s1 q1) t = query_occ db (Pi s2 q2) t.
```

## Selection Rewrite Facts

### `query_entails` [`theories/FormalSQL/RewriteSpec.v`]

on every tuple output by query `q`, truth of
`premise` implies truth of `conclusion`.  Use this as the generic hook for
case-specific arithmetic or predicate reasoning.

```coq
Definition query_entails
    (db : db_state) (q : Query) (premise conclusion : Formula) : Prop :=
  forall t,
    t inBE eval_query_in_state db q ->
    eval_formula_in_state db t premise = true ->
    eval_formula_in_state db t conclusion = true.
```

### `eval_formula_in_env_eq_tuple` [`theories/FormalSQL/RewriteSpec.v`]

formula evaluation is compatible with tuple setoid equality.

```coq
Lemma eval_formula_in_env_eq_tuple :
  forall db env f t1 t2,
    t1 =t= t2 ->
    eval_formula_in_env db env t1 f = eval_formula_in_env db env t2 f.
```

### `sigma_outputs_satisfy_predicate` [`theories/FormalSQL/RewriteSpec.v`]

every tuple output by `Sigma f q` satisfies `f`.

```coq
Lemma sigma_outputs_satisfy_predicate :
  forall db q f,
    query_satisfies db (Sigma f q) f.
```

### `sigma_outputs_satisfy_entailed` [`theories/FormalSQL/RewriteSpec.v`]

if `premise` implies `conclusion` on the base query
output, then every tuple output by `Sigma premise q` satisfies `conclusion`.

```coq
Lemma sigma_outputs_satisfy_entailed :
  forall db q premise conclusion,
    query_entails db q premise conclusion ->
    query_satisfies db (Sigma premise q) conclusion.
```

### `eval_and` [`theories/FormalSQL/RewriteSpec.v`]

evaluating `p AND h` is the Boolean conjunction of
evaluating `p` and evaluating `h`.

```coq
Lemma eval_and :
  forall db env t p h,
    eval_formula_in_env db env t (And p h) =
    (eval_formula_in_env db env t p && eval_formula_in_env db env t h)%bool.
```

### `query_satisfies_conj_l` [`theories/FormalSQL/RewriteSpec.v`]

if every output tuple satisfies `p AND h`, then every output tuple satisfies
`p`.

```coq
Lemma query_satisfies_conj_l :
  forall db q p h,
    query_satisfies db q (And p h) ->
    query_satisfies db q p.
```

### `query_satisfies_conj_r` [`theories/FormalSQL/RewriteSpec.v`]

if every output tuple satisfies `p AND h`, then every output tuple satisfies
`h`.

```coq
Lemma query_satisfies_conj_r :
  forall db q p h,
    query_satisfies db q (And p h) ->
    query_satisfies db q h.
```

### `sigma_id_of_query_satisfies` [`theories/FormalSQL/RewriteSpec.v`]

if every output tuple of `q` already satisfies `f`, then filtering `q` by `f`
does not change the query result.

```coq
Lemma sigma_id_of_query_satisfies :
  forall db q f,
    query_satisfies db q f ->
    query_succeeds db (Sigma f q) ->
    query_succeeds db q ->
    query_equiv db (Sigma f q) q.
```

### `sigma_drop_redundant_conjunct` [`theories/FormalSQL/RewriteSpec.v`]

if predicate `h` is true on every output tuple of
`q`, then adding `h` as an extra conjunct under a selection does not change the
query result.

```coq
Lemma sigma_drop_redundant_conjunct :
  forall db q p h,
    query_satisfies db q h ->
    query_succeeds db (Sigma (And p h) q) ->
    query_succeeds db (Sigma p q) ->
    query_equiv db (Sigma (And p h) q) (Sigma p q).
```

### `sigma_sigma_merge` [`theories/FormalSQL/RewriteSpec.v`]

two nested selections can be merged into one selection
with a conjunctive predicate.

```coq
Lemma sigma_sigma_merge :
  forall db q outer inner,
    query_succeeds db (Sigma outer (Sigma inner q)) ->
    query_succeeds db (Sigma (And outer inner) q) ->
    query_equiv db (Sigma outer (Sigma inner q)) (Sigma (And outer inner) q).
```

### `andb3_indicator_mul_factor` [`theories/FormalSQL/RewriteSpec.v`]

low-level arithmetic helper for factoring the `true3` indicator of `andb3`.
Most generated proofs should prefer higher-level `Sigma` lemmas.

```coq
Lemma andb3_indicator_mul_factor :
  forall n outer_value inner_value,
    (n *
      (if match andb3 outer_value inner_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0))%N =
    (n *
      (if match inner_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0) *
      (if match outer_value with
          | true3 => true
          | _ => false
          end
       then 1
       else 0))%N.
```

## Projection Preservation

### `select_list_directly_selects_attr` [`theories/FormalSQL/RewriteSpec.v`]

`s` contains a direct projection of attribute `a` to the same output attribute.
This is a syntactic premise for simple attribute-preservation proofs.

```coq
Definition select_list_directly_selects_attr
    (s : SelectListT) (a : attribute TNull) : Prop :=
  match s with
  | @_Select_List _ l => In (@Select_As TNull (@A_Expr TNull (@F_Dot TNull a)) a) l
  end.
```

### `select_list_has_unique_outputs` [`theories/FormalSQL/RewriteSpec.v`]

the select list has no duplicate output attributes.

```coq
Definition select_list_has_unique_outputs (s : SelectListT) : Prop :=
  match s with
  | @_Select_List _ l => all_diff (map fst (map (@pair_of_select TNull) l))
  end.
```

### `projection_preserves_attr` [`theories/FormalSQL/RewriteSpec.v`]

projecting with `s` preserves the value of attribute `a` for tuples that
contain `a`.

```coq
Definition projection_preserves_attr
    (env : Env.env TNull) (s : SelectListT) (a : attribute TNull) : Prop :=
  forall t, a inS labels TNull t -> @dot TNull (projected_tuple env s t) a = @dot TNull t a.
```

### `select_list_preserves_formula_eval` [`theories/FormalSQL/RewriteSpec.v`]

projecting with select list `s` preserves the truth
value of formula `f` on every tuple.  This is the generic predicate-level
projection-preservation premise.

```coq
Definition select_list_preserves_formula_eval
    (db : db_state) (s : SelectListT) (f : Formula) : Prop :=
  forall t,
    eval_formula_in_state db (projected_tuple nil s t) f =
    eval_formula_in_state db t f.
```

### `direct_projection_preserves_attr` [`theories/FormalSQL/RewriteSpec.v`]

if a select list directly preserves an attribute under
the same output name and has distinct output attributes, then projection
preserves that attribute's value.

```coq
Lemma direct_projection_preserves_attr :
  forall env s a,
    select_list_directly_selects_attr s a ->
    select_list_has_unique_outputs s ->
    projection_preserves_attr env s a.
```

### `pi_sigma_outputs_satisfy_preserved` [`theories/FormalSQL/RewriteSpec.v`]

if a projection preserves predicate `f`, then
`Pi s (Sigma f q)` still satisfies `f` after the projection.

```coq
Lemma pi_sigma_outputs_satisfy_preserved :
  forall db q s f,
    select_list_preserves_formula_eval db s f ->
    query_satisfies db (Pi s (Sigma f q)) f.
```

### `pi_sigma_outputs_satisfy_entailed` [`theories/FormalSQL/RewriteSpec.v`]

if `premise` implies `conclusion` on `q`, and the
projection preserves `conclusion`, then `Pi s (Sigma premise q)` satisfies
`conclusion`.

```coq
Lemma pi_sigma_outputs_satisfy_entailed :
  forall db q s premise conclusion,
    select_list_preserves_formula_eval db s conclusion ->
    query_entails db q premise conclusion ->
    query_satisfies db (Pi s (Sigma premise q)) conclusion.
```

## Exact Ordered-Query Observation Proofs

Generated problems import `SqlQuerySyntax`, `SqlQuerySemantics`,
`SqlBagAbstraction`, `SqlQueryFacts`, `SqlQueryContexts`, and
`SqlQueryWellFormed`. `QueryExpr` and `FormulaExpr` are their `TNull`
specializations. The outcome relation over ordered row lists is the single
exact query semantics. `alpha` maps its successful observations to a relation
of possible bags; `gamma` forgets order by permutation closure and is an
over-approximation in general. `BagClosed` is exactly the condition under which
that abstraction is complete for equivalence. Bag lemmas are therefore a proof
abstraction for order-insensitive regions, not a peer query semantics. The
semantic completeness claim concerns the defined normalized core, not proof
search or the unverified Rust/Calcite frontend.

### `query_expr_equiv_of_ordered_observations` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

Use this to prove a general typed ordered-observation goal. Its premises, in
order, are ordered-output equality, one successful source observation, source
safety, target safety, and bidirectional successful-list witnesses related by
`ordered_rows_equiv`. Thus list position, length, and multiplicity remain exact,
while hidden tuple representations are compared through `OTuple`.

```coq
apply query_expr_equiv_of_ordered_observations.
```

`query_expr_equiv_of_observations` remains a convenience specialization when
both sides expose the exact same Rocq list representatives.

### `bag_query_expr_equiv_iff_bag_query_equiv` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

For two `QExpr_Bag` nodes, provide their exact ordered output lists and prove
those lists equal. Typed query-expression equivalence is then iff the original
deterministic `bag_query_equiv`. A set-sort equality is deliberately
insufficient here: it cannot recover column order. This is the direct route
back to existing bag-algebra lemmas.

```coq
apply bag_query_expr_equiv_iff_bag_query_equiv.
(* remaining schema premise: left_outputs = right_outputs *)
```

### `bag_query_equiv_intro` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

Construct deterministic bag-query equivalence from two runtime-safety proofs
and one bag equality proof. `QExpr_Bag` connects to this contract directly;
there is no intermediate list-query syntax or evaluator.

```coq
Lemma bag_query_equiv_intro :
  forall env q1 q2,
    bag_query_runtime_error env q1 = None ->
    bag_query_runtime_error env q2 = None ->
    eval_query basesort instance unknown contains_nulls env q1 =BE=
    eval_query basesort instance unknown contains_nulls env q2 ->
    bag_query_equiv env q1 q2.
```

### `query_expr_effect_sound` and `bag_closed_rel_equiv_iff_alpha_rel_equiv` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`, `vendor/FormalSQL/src/data/sql/SqlBagAbstraction.v`]

`query_expr_effect q = BagEffect` soundly implies `OutcomeBagClosed` for its
denotation. For bag-closed successful observation relations,
`bag_closed_rel_equiv_iff_alpha_rel_equiv` gives both directions between exact
list-relation equivalence and equality of their possible-bag abstractions. The
abstraction remains a relation of bags: never select one bag when tied top-k
evaluation admits several. Use `outcome_alpha_bag_query_expr_singleton` only
when a `QExpr_Bag` result supplies the proved deterministic singleton case.

For error-preserving goals, use
`query_bag_effect_typed_outcome_equiv_iff_possible_bag_equiv`. It preserves the
set of runtime-error categories exactly while abstracting only successful row
lists to possible bags.


### `query_expr_context_equiv_safe` [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v`]

Use this for mechanically checked substitution through an arbitrary typed
query-expression context. It lifts global typed raw-outcome equivalence of
replacements; the instantiated outer queries still require explicit safety
and source-success premises before obtaining success-only `query_expr_equiv`.

### `query_success_bags_of_success_rel_equiv` and `query_bag_effect_equiv_of_success_bags_safe` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`, `vendor/FormalSQL/src/data/sql/SqlQueryContexts.v`]

These are the two directions of the local reset workflow. The first maps
bidirectionally matched ordered row lists through `alpha` to equality of
`query_success_bags`. After an enclosing operator has been handled
with lifted bag relations, `query_bag_effect_equiv_of_success_bags_safe`
returns to exact typed equivalence. It requires both result effects to be
`BagEffect`, equal possible bags, explicit safety of both outer queries, and a
successful source observation. Thus bag reasoning cannot conceal an error or
manufacture success.

### `query_distinct_equiv_of_local_success_rel_equiv` and `query_distinct_local_list_equiv_congr` [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v`]

Use these for an actual `QExpr_Distinct` parent, not merely an abstract bag
context. `query_distinct_equiv_of_local_success_rel_equiv` exposes the outer
safety and success premises explicitly. It maps the local exact-list iff
through `alpha`, applies `query_distinct_actual_success_bags_congr`, and uses
`BagClosed` completeness to recover exact equivalence. If the children already
satisfy the standard fixed-environment `query_expr_equiv` contract,
`query_distinct_local_list_equiv_congr` packages those obligations directly.

### `order_by_rows_has_observation` and `eval_query_expr_order_by_has_success` [`vendor/FormalSQL/src/data/sql/SqlListFacts.v`, `vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

Every finite child list has at least one legal sorted permutation. These
lemmas provide a concrete success witness without making ORDER BY
deterministic: other permutations of tied rows remain legal outcomes.
Each `SqlOrder.sort_key` carries the concrete SQL value comparator together
with its checked opposite-direction law; these lemmas use that invariant and
do not infer SQL order from the structural `Tuple.OVal` carrier.  The active
`TNullSyntax` constructors install `NullValues.sql_order_value_compare`, which
in particular preserves PostgreSQL's `false < true` Boolean order for
`ORDER BY`, `RANK`, and cumulative window keys.

### `query_expr_equiv_possible_bag_context_congr` [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v`]

Use this at an order-insensitive boundary. A typed exact list-equivalence proof
for two local subqueries induces equality, with result-sort compatibility,
after any context built from lifted unary and binary possible-bag relations.
Continue the outer proof with bag reasoning; this theorem does not assume the
possible-bag relation is a singleton.

### `possible_bag_context_well_formed` and `plug_possible_bag_context_extensional` [`vendor/FormalSQL/src/data/sql/SqlQueryContexts.v`]

Generated possible-bag contexts should prove
`possible_bag_context_well_formed`: every lifted unary/binary operation and
fixed bag relation must respect FormalSQL bag equality. Plugging an
extensional replacement then remains extensional by
`plug_possible_bag_context_extensional`.
`successful_possible_bags_extensional` discharges the replacement condition
for an `alpha` abstraction, and
`possible_bag_context_successful_plug_extensional` packages the common case.

### `eval_group_bag_outcome_input_equiv`, `query_group_success_bags`, and `query_group_success_bags_congr` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

Grouping existentially consumes a list representative of each possible input
bag. `eval_group_bag_outcome_input_equiv` transports every success or error
outcome across bag-equal inputs, while `query_group_success_bags` identifies
the actual grouped possible bags with the lifted relational operation.
`query_group_success_bags_congr` is the substitution rule for the actual
`QExpr_Group` result. `query_group_bag_relation_extensional` supplies the
quotient-respecting operation fact. The checked examples also compute that
`query_make_groups nil nil nil = [nil]`, so a global aggregate has one group
on empty input, and transport grouping outcomes across a swapped two-row bag
representative.

### `query_tuple_equal` [`vendor/FormalSQL/src/data/sql/SqlQuerySemantics.v`]

`FExpr_In` compares aligned scalar or row-valued subquery results with
componentwise SQL three-valued equality. A definite field mismatch makes the
row comparison FALSE even when another field is NULL; otherwise any NULL
field makes it UNKNOWN. `FExpr_Not` therefore gives the correct
NULL-contaminated `NOT IN` result. Rust routes multi-column membership through
this exact formula and uses compact `Sql_In` only for the proved one-column
case. The checked examples
`row_in_definite_mismatch_dominates_null` and
`row_in_single_candidate_is_false_despite_null_component` exercise the rule.

### `query_join_success_bags` and `query_join_success_bags_congr` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

`QExpr_Join` is the native shared-child semantics for inner, left, right,
full, semi, and anti joins. One possible bag is chosen for each child and one
predicate-condition matrix is shared by matched and unmatched-row decisions;
the semantics does not duplicate a nondeterministic child by desugaring an
outer join into several query occurrences. `query_join_success_bags`
characterizes the result by the lifted binary `query_join_bag_relation`,
`query_join_bag_relation_extensional` proves quotient invariance, and
`query_join_success_bags_congr` supports replacement of either child's
possible-bag relation.

### `query_natural_join_compatible_eq` and `query_natural_join_bag_congr` [`vendor/FormalSQL/src/data/sql/SqlQueryFacts.v`]

Exact `QExpr_NaturalJoin` requires every common attribute to be non-NULL on
both sides and value-equal, so two common NULLs never match.
`query_natural_join_compatible_eq` proves that test respects tuple equality;
`query_natural_join_bag_congr` and
`query_natural_join_bag_relation_extensional` lift it soundly to possible
bags. The former deterministic bag-only natural join was removed because its
NULL matching disagreed with SQL and it had no admitted normalized caller.

The ordered schema is derived from the child ordinal witnesses rather than
from a canonically sorted union. `query_natural_join_outputs` uses the same
ordered-attribute identity as the common-label compatibility test and follows
PostgreSQL order exactly: common columns in left order, then left-only columns,
then right-only columns. `QExpr_CrossJoin` preserves all positions by appending
the right witness to the left witness; admissibility requires its child sorts
to be disjoint, so `join_tuple` cannot collapse a pair of positions.

### `query_expr_admissible` [`vendor/FormalSQL/src/data/sql/SqlQueryWellFormed.v`]

The exact `query_expr` syntax is also the formal frontend boundary; no second
isomorphic query AST is introduced. `QExpr_Error`, `QExpr_Values`,
`QExpr_Bag`, and `QExpr_RowMap` each carry an explicit
`list (attribute T)` output witness. `query_expr_outputs q` returns those lists
directly (and is independent of `basesort`), while `query_expr_sort q` is only
`Fset.mk_set ... (query_expr_outputs q)`. No `Fset.elements` result is an
ordinal witness. `query_expr_admissible` recursively checks ordered schemas,
compact bag leaves, nested formulas, grouping-set ordered output
compatibility, window-key scope and output freshness, ordering-key scope, and
native join projection compatibility. Every active projection witness must
have unique output attributes. The four explicit leaf/adapter witnesses use
the same generic `query_output_attributes_unique` predicate. Values rows must
agree with the derived set, a compact bag witness must agree with the compact
query sort, and every successful row-map output must agree with the derived
set; error witnesses must also be unique. Grouping-set branches have the same
ordered outputs and unique aliases; native joins impose uniqueness on
precisely the matched/unmatched projections evaluated by their join kind.
Exact and compact cross joins require disjoint child sorts, and compact
`Project`/`Aggregate` apply the same projection-uniqueness rule. These
obligations prevent tuple label sets and `join_tuple` from silently collapsing
SQL output positions.
This judgment does not mechanically verify the Rust/Calcite frontend. The
formal core's outer error evaluation remains strict and compositional by
definition, while physical executor scheduling is outside the declarative
semantics.

IN admission is positional rather than set-only. `query_expr_outputs` tracks
syntax-directed output order through projection, grouping, set-left, and
transparent unary operators. `query_in_positionally_aligned` requires a
nonempty row, unique aliases, equal arity, and exact left/right alias order.
`formula_expr_admissible_in_positionally_aligned` and
`bag_formula_admissible_in_positionally_aligned` extract this certificate
from exact and compact admissibility.

For native joins, `query_join_projection_sorts_compatible` requires every
projection list that a join kind can emit to agree with its declared result
sort: matched/left for left join, matched/right for right join, and all three
for full join. `query_expr_admissible_join_projection_sorts` extracts this
certificate from an admissible `QExpr_Join`;
`query_expr_admissible_join_projection_uniqueness` extracts the corresponding
alias-uniqueness certificate, and
`query_expr_admissible_cross_join_disjoint` exposes the cross-join premise.

## Declarative Fixed-Scale NUMERIC Aggregates

The aggregate layer uses one aggregate-owned state for fixed-scale NUMERIC
AVG. It does not rewrite AVG into SUM, checked COUNT, and scalar division.
`numeric_avg_scale_state` retains exact finite, NaN, and infinity counts and
the exact finite coefficient sum; only aggregate finalization materializes the
PostgreSQL NUMERIC result and any associated error. The
`AggregateAverageNumericFixed p s` applies this state to
schema-authoritative `DECIMAL(p,s)` inputs, and
`AggregateAverageNumericAtScale s` applies it when the lowering layer can
prove the expression's display scale. Precision is enforced by schema
conformance where a fixed typmod is available and does not alter PostgreSQL's
transition or finalization semantics.

### `fixed_numeric_aggregate_permutation` [`theories/FormalSQL/NumericFacts.v`]

```coq
Lemma fixed_numeric_aggregate_permutation :
  forall precision scale function left right,
    In function
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    interp_aggregate function left = interp_aggregate function right.
```

### `fixed_numeric_aggregate_runtime_error_permutation` [`theories/FormalSQL/NumericFacts.v`]

```coq
Lemma fixed_numeric_aggregate_runtime_error_permutation :
  forall precision scale function left right,
    In function
      [Aggregate (AggregateStddevSampleNumericFixed precision scale);
       DistinctAggregate (AggregateStddevSampleNumericFixed precision scale);
       Aggregate (AggregateAverageNumericFixed precision scale);
       DistinctAggregate (AggregateAverageNumericFixed precision scale)] ->
    Permutation left right ->
    aggregate_local_runtime_error function left =
    aggregate_local_runtime_error function right.
```

## Declarative NUMERIC EXP Row Mapping

`QExpr_RowMap output_attributes row_map input` is an order-preserving logical row
transformation. It first observes its complete logical child; a child error is
propagated, while a successful list is mapped from left to right and the first
row-map error becomes the query outcome. The operator is `ListEffect`; its
pointwise permutation lemma does not collapse exact list observations to one
chosen bag. `RowMapExpr` passes its received ordered list through unchanged;
`NumericExpRowMapExpr_admissible` therefore requires an explicit uniqueness
proof for its constructed output list in addition to child admissibility.

For `EXP(AVG(integer))`, `AggregateAverageInt32Numeric` and the structured
`AggregateNumericDisplayScale NumericAverageInt32` observation read the same
NULL-skipping group input. `NumericExpRowAdapter` bypasses the model for NULL
AVG and otherwise calls one deterministic `NumericExpModel` with the exact
average value and display scale. A successful model result is accepted only
when it is finite, fits PostgreSQL NUMERIC, has a valid display scale, and is
already rounded at that scale; every invalid success and
`NumericExpValueOutOfRange` becomes SQLSTATE 22003. Generated equivalence
goals universally quantify one shared model for source and target. This is a
conservative parametric proof interface: a proof must work for every admitted
deterministic EXP behavior, so it cannot assume a convenient value or erase
an overflow that PostgreSQL can observe.

## Integral BIT_AND/BIT_OR Algebra

[`theories/FormalSQL/BitwiseFacts.v`] is pre-imported into every generated
proof problem. Proof agents must use that trusted import and must not add a
`Require` command. The theory models PostgreSQL `BIT_AND` and `BIT_OR` over
signed `INTEGER` and `BIGINT` by applying `Z.land`/`Z.lor` directly to their
range-refined mathematical values. The `int32_{land,lor}_in_range` and
`int64_{land,lor}_in_range` lemmas prove that these operations remain in the
same signed width, so no modulo normalization occurs on an SQL value. The
`*_bit_{and,or}_as_word` lemmas separately establish agreement with fixed-width
two's-complement words. The aggregate fold keeps `None` for an empty or
all-NULL transition state instead of inventing an identity value.

`int32_from_twos_complement` and `int64_from_twos_complement` are explicit
raw-bit decoding boundaries, not arithmetic or aggregate operators. SQL
literals and arithmetic use checked constructors and must not use those
decoders.

The operator laws are available for both widths and both operations:

- `int32_bit_and_associative`, `int32_bit_or_associative`,
  `int64_bit_and_associative`, and `int64_bit_or_associative` reassociate
  transition values;
- `int32_bit_and_commutative`, `int32_bit_or_commutative`,
  `int64_bit_and_commutative`, and `int64_bit_or_commutative` swap operands;
  and
- `int32_bit_and_idempotent`, `int32_bit_or_idempotent`,
  `int64_bit_and_idempotent`, and `int64_bit_or_idempotent` collapse a
  duplicate value.

For optional aggregate states, use `combine_nullable_state_associative` and
`combine_nullable_state_commutative`. The generic
`fold_nullable_state_partition` lemma splits a concatenated input. Its
specializations are `int32_bit_and_fold_partition`,
`int32_bit_or_fold_partition`, `int64_bit_and_fold_partition`, and
`int64_bit_or_fold_partition`; they require no extra algebra premises.

Order-insensitive aggregate reasoning should use
`int32_bit_and_fold_permutation`, `int32_bit_or_fold_permutation`,
`int64_bit_and_fold_permutation`, or `int64_bit_or_fold_permutation`.
DISTINCT reasoning uses `int32_bit_and_fold_distinct_invariant`,
`int32_bit_or_fold_distinct_invariant`,
`int64_bit_and_fold_distinct_invariant`, or
`int64_bit_or_fold_distinct_invariant`; each removes one adjacent duplicate
from any prefix/suffix context. For a non-adjacent duplicate, first use the
corresponding permutation lemma to place equal values together; do not treat
the input list as a set or discard NULL-state behavior.

## PostgreSQL DATE-to-TIMESTAMP Comparisons

The concrete `predicate` carrier is a closed inductive containing exactly the
predicates implemented by `NullPredicates.interp_predicate`. Rust lowering uses
the corresponding closed `FormalPredicate` enum and emits those constructors
directly. There is no arbitrary-string predicate fallback: unsupported SQL
operators are rejected by lowering instead of silently evaluating to UNKNOWN.

`date_cmp_timestamp_internal` in
`vendor/FormalSQL/src/data/proof_of_concept/ValueTemporal.v` models
PostgreSQL's cross-type DATE/TIMESTAMP comparator rather than a checked cast.
A finite DATE in TIMESTAMP range compares at midnight. A finite positive
overflow orders above every finite TIMESTAMP but below TIMESTAMP `infinity`;
the total negative branch analogously orders below finite values but above
`-infinity`. DATE and TIMESTAMP special infinities compare as the matching
special values. `date_lt_timestamp_bool`, `date_lte_timestamp_bool`,
`date_gt_timestamp_bool`, and `date_gte_timestamp_bool` expose respectively
the exact `= Lt`, `<> Gt`, `= Gt`, and `<> Lt` decisions; their corresponding
spec lemmas reduce each Boolean result to the shared internal comparison.

`NullPredicates.interp_predicate` recognizes
`PredicateDateLtTimestamp`, `PredicateDateLteTimestamp`,
`PredicateDateGtTimestamp`, and `PredicateDateGteTimestamp`. Each
returns SQL UNKNOWN for NULL or ill-typed inputs and otherwise uses that
comparator. The emitted TNull interfaces are `PgDateLtTimestamp`,
`PgDateLteTimestamp`, `PgDateGtTimestamp`, and `PgDateGteTimestamp`. Predicate
error semantics inspect only the two ordered child expressions, formalized by
the corresponding `pg_date_{lt,lte,gt,gte}_timestamp_runtime_error_is_children`
lemmas; none of the comparisons introduces a cast error. This does not change
DATE-plus-or-minus-INTERVAL: its timestamp-valued child continues to use
checked `cast_date_to_timestamp`, including SQLSTATE 22008 for an out-of-range
DATE midnight, and the exact predicates preserve that child error.

## Standard Rocq Tools Available

Proof scripts may import standard libraries as needed:

```coq
From Stdlib Require Import String ZArith Lia NArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
```

Use `lia` for linear integer arithmetic and `nia` for nonlinear integer
arithmetic.  Arithmetic facts should be proved in the generated problem or a
separate generated helper file, not added as axioms to the read-only lemma
context.
