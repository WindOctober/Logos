# Shared FormalSQL semantic primer

This is a compact mental model shared by equivalence and counterexample search,
not a specification or a certificate. The exact SQL and schema are the input;
the typed lowering, imported FormalSQL definitions, and Rocq kernel are
authoritative when a formal workspace is present. PostgreSQL is used for
static output analysis and for type-checking and freezing candidate database
state, never for accepting a data-dependent EQ/NEQ result. On conflict, follow
the authoritative sources and report drift.

## One query syntax, two observation levels

`QueryExpr` in `vendor/FormalSQL/src/data/sql/SqlQuerySyntax.v` is the only
query language. Table and VALUES leaves, set operations, joins, projection,
row maps, filtering, grouping, DISTINCT, ORDER BY, OFFSET, FETCH, rank, and
windows all compose in that AST and share one error-aware outcome relation.
There is no embedded deterministic bag-query syntax and no second evaluator.

`alpha` maps evaluated successful lists to possible bags. `BagReset` classifies
only the root constructor. `BagClosed` is the semantic composition property:
every possible result bag can realize any requested row order through an
actually evaluated list that is `ordered_rows_equiv` to the request. It does
not require the evaluator to reproduce hidden Rocq tuple representations.
Set operations, joins, grouping, grouping sets, DISTINCT, rank, and windows are
bag resets. Projection, row mapping, and filtering preserve a reset-derived
closure certificate when their required properness contracts hold, so
`Filter (CrossJoin left right)` is directly `BagClosed`. ORDER BY establishes
order; OFFSET and FETCH consume it. Ties remain relational rather than
following a physical order.

## Outcomes and equivalence

`eval_query_expr_outcome env query outcome` is a relation, not a function. An
outcome is either `SqlSuccess rows` or `SqlError category`. A query can have
multiple legal successful row lists, particularly around bag resets and ORDER
BY ties.

For exact successful observations, `ordered_rows_equiv` preserves row order and
multiplicity and quotients only the hidden Rocq representation of corresponding
tuples. It is stronger than bag equality and weaker than Leibniz equality of
tuple records.

Error-preserving `query_expr_outcome_equiv` requires:

- identical ordered output signatures;
- an inhabited outcome relation on each side;
- successful observations matched in both directions by
  `ordered_rows_equiv`; and
- exactly the same exposed SQL runtime-error categories.

At the query-pair boundary, Logos canonicalizes final output labels by ordinal.
Consequently, final SELECT alias spelling alone is not observable; positional
arity, types, and typmods still are. Names inside a query remain relevant where
they bind expressions and for the separate admissibility checks below.

Program equivalence is pointwise and preserves statement count and statement
order. Success-only query equivalence additionally proves that neither side can
error. It may be lifted to error-preserving equivalence only after Rocq proves
that safety; the selected verification mode is not a safety oracle.

The core definitions are in
`vendor/FormalSQL/src/data/sql/SqlOutcome.v`,
`SqlBagAbstraction.v`, and `SqlQuerySemantics.v`.

## Observation certificates and countermodels

A PostgreSQL execution chooses one physical result from a relational
semantics, so the counterexample path never executes the source and target to
decide equivalence. Host-computed observation certificates remain useful for
proof navigation and for selecting the right bag or ordered lemmas, but they
do not authorize an executor-based NEQ result.

`BagClosed` is permutation completeness for each possible bag. It does not say
that there is only one possible bag. Likewise, ORDER BY does not make an exact
list unique when sort keys tie. OFFSET/FETCH can expose which tied row is chosen,
and DISTINCT ON can expose which row represents a peer group. One physical
PostgreSQL choice at such a boundary must not be reported as NEQ merely because
another execution or another query chose a different legal representative.

A sound data-dependent non-equivalence result always requires a FormalSQL
countermodel: a concrete conforming database and a legal outcome on one side
that cannot be matched by any legal outcome on the other side (or the symmetric
direction), including SQL error categories where relevant. The host may use
PostgreSQL to materialize that database into the exact typed witness carrier,
but only the trusted Rocq selector may accept the separation claim. Failure to
construct that certificate is uncertainty, not NEQ. Output arity, type, typmod,
or analysis-outcome mismatches are handled separately by static preflight.

## NULL, predicates, and errors

TNull models SQL three-valued logic. WHERE and HAVING retain only TRUE; FALSE
and UNKNOWN both reject a row or group, but they are not generally
interchangeable in other contexts. Strict comparisons with NULL normally
produce UNKNOWN. Never turn NULL into FALSE or erase NULL premises.

Runtime errors are separate observations from the value computed by the total
value interpreter. This separation is needed for evaluation order and
non-strict constructs such as CASE. A rewrite that removes evaluation of an
expression must either preserve its possible errors or prove that expression
safe on every removed row or group. Preserve exact error categories, including
cardinality, cast, numeric/typmod, and analysis errors.

Grouping has additional ordering of checks: group-key errors, aggregate
finalization errors, HAVING outcomes, and SELECT evaluation are modeled
explicitly. A filter pushed below grouping needs a proof that its truth depends
only on the grouping key, respects TRUE versus non-TRUE acceptance, and does
not suppress an error on a removed group. Empty global aggregation also has a
special group and must not be treated as ordinary nonempty partitioning.

## Schemas and admissibility

`database_conforms_schema` preserves declared relations and base sorts, value
typing, and the generated integrity constraints. Use only constraints present
in `Schema.generated_schema_constraints`. In particular, MATCH SIMPLE foreign
keys do not promise a referenced row when a referencing component is NULL, and
uniqueness does not silently imply a non-NULL fact outside the modeled
constraint.

Table values must also be PostgreSQL-realizable: text-like values contain no
zero byte, unconstrained NUMERIC values still satisfy PostgreSQL's finite-
decimal/storage bounds, and finite TIMESTAMP/TIMESTAMPTZ values obey their
declared precision (infinities remain valid). These are part of
`value_conforms_attribute`; a FormalSQL countermodel may not exploit a larger
mathematical carrier than PostgreSQL can store.

`query_expr_admissible` is a separate static obligation covering output-label
uniqueness, predicate arity, sort compatibility, positional IN alignment,
grouping-set shape, and key scope. Admissibility is not semantic equivalence,
runtime safety, or outcome totality. Its definition is in
`vendor/FormalSQL/src/data/sql/SqlQueryWellFormed.v`; the schema contract is in
`vendor/FormalSQL/src/data/proof_of_concept/SchemaConstraints.v`.

Rows crossing a bag boundary are equal extensionally. When reading a cell from
such a row, retain both attribute presence and value-typing/non-NULL premises.
Projection need not be injective: several source occurrences can map to the
same output occurrence, so preserve multiplicities through a proved map or bag
congruence law.
