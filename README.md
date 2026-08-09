# Logos

Logos is a Rocq-based theorem-proving workspace for LLM-assisted verification of SQL schema rewrite equivalence. The intended trust boundary is explicit: LLMs may propose rewrites, lemmas, proof plans, and proof scripts, but equivalence claims must be checked by Rocq.

## Formal SQL Semantics

Logos builds on the existing SQLCoq/SQLFormalSemantics development instead of discarding its mature bag theory:

- `vendor/FormalSQL`: a Rocq-modernized fork of SQLCoq/SQLFormalSemantics. Logos uses one compositional normalized query syntax with a scheduled exact ordered-outcome relation and a public possible-outcome relation that existentially ranges over every legal Boolean schedule, together with reusable bag operators and a proved possible-bag abstraction.

Generated proofs target typed equality of exact ordered observations:

```coq
forall db,
  generated_schema_conforms db ->
  query_expr_equiv_in_state db source_query_expr target_query_expr.
```

The error-preserving mode analogously targets
`query_expr_outcome_equiv_in_state`; both stable TNull aliases now unfold to
the corresponding `query_expr_possible_*` relation. A theorem about one fixed
Boolean schedule is only an internal pointwise lemma, never a final SQL
rewrite certificate.

The scheduled evaluator remains an outcome relation over ordered row lists at every nesting depth, while the public evaluator is the union of those relations over Boolean schedules. Boolean evaluation schedules do not weaken row order: `ORDER BY`, `OFFSET`, `FETCH`, rank, windows, and nested top-k continue to observe exact lists. For a `BagClosed` region, every possible bag can recover any requested row order through an actually evaluated, `ordered_rows_equiv` result, so `alpha` is complete without requiring a particular hidden Rocq tuple representation. Proofs may then use lifted bag operations. Reset-derived permutation closure composes through projection, row mapping, and filtering; in particular, the relational expansion `Filter (CrossJoin left right)` directly has the permutation-closed SQL observation expected of an inner join.

`PossibleOutcomeFacts.v` is the public rewrite layer. Besides relational and
ordered contexts, it provides kind-indexed scalar congruence for calls, CASE,
flattened AND/OR, `IN`, quantified predicates, `EXISTS`, and scalar subqueries,
with public lifts through the single typed `QExpr_Project`, `QExpr_Filter`, and
`QExpr_Group` interface. `EXISTS` keeps its target-eliding demand observation;
scalar subqueries use exact typed row outcomes; Group clause replacement keeps
aggregate-finalization errors as explicit premises.

The formal architecture is split by responsibility: `SqlQuerySyntax.v` defines the compositional exact query syntax, `SqlQuerySemantics.v` its ordered-outcome relation, `SqlQueryWellFormed.v` the conservative structural admission boundary, `SqlBagAbstraction.v` the possible-bag abstraction and lifted operations, `SqlQueryFacts.v` order-behavior soundness and observable bag-reuse bridges, and `SqlQueryContexts.v` typed substitution/congruence. These modules describe one exact query semantics plus a proof abstraction; they do not denote competing bag and list semantics.

Logos does not vendor SQLToNRACert, DBCert, or the Q*Cert NRAEnv-to-JavaScript compilation path. Those components target certified SQL-to-JavaScript compilation, while Logos focuses on SQL rewrite equivalence.

## Counterexample Semantics

PostgreSQL assists Logos at two bounded interfaces: static output analysis and typed candidate-database materialization. It does not execute the source and target to decide a data-dependent equivalence result. Every such `EQ` or `NEQ` claim is accepted through the same trusted FormalSQL/Rocq selector.

In principle, query equivalence should be stated against a precise SQL semantics. In practice, there is no widely used, executable, full standard-SQL reference interpreter that covers the benchmark dialects we use. Existing tools and benchmark sources each expose their own accepted SQL subset or dialect. Logos therefore normalizes inputs toward PostgreSQL-compatible SQL and models PostgreSQL behavior in FormalSQL, while keeping PostgreSQL execution outside the final query-equivalence decision.

The checker treats the ordered output type shape as part of query equivalence, but column labels are not observable. Source and target query programs must be nonempty, contain the same number of statements, and return the same number of columns with compatible PostgreSQL output types in each aligned ordinal position. Both the PostgreSQL base type/OID and its type modifier are compared, so `char(n)` and typmodless `bpchar`, or `varchar(n)` and unconstrained `varchar`, remain distinct. For every verification run, including one with counterexample synthesis disabled, PostgreSQL describes every statement on both sides under one stable transaction snapshot before either agent is invoked. A modeled parse-analysis failure (`42702`, `42703`, `42883`, or `22P02`) is retained as an observable FormalSQL error category rather than misreported as infrastructure failure; a statically visible output or analysis-outcome mismatch is terminal. Infrastructure, schema-setup, unmodeled SQLSTATE, or metadata failures still fail closed. `--transform-only` remains a pure lowering mode and deliberately does not execute this PostgreSQL preflight. FormalSQL applies the same output-shape boundary by relabeling only the final source and target observations to shared ordinal names; internal SQL names and bindings are unchanged.

Normal verification starts in one proof-agent workflow. That agent may prove equivalence directly or request counterexample synthesis. A counterexample agent returns only DML for a candidate database; PostgreSQL executes the schema and DML, enforces the benchmark integrity contract, and exports every table into a complete typed snapshot without running either query. The host then regenerates a read-only `Witness.v`, and the trusted Rocq selector must prove either the requested equivalence theorem or complete outcome separation on that exact database. If synthesis returns no candidate, the original proof session resumes. Thus unordered bags, ORDER BY ties, nested top-k, `DISTINCT ON`, runtime errors, and other possible-observation behavior are judged by the formal semantics rather than by one physical plan.

The PostgreSQL materialization URL is an execution boundary and must identify a dedicated disposable server or an equivalently isolated database role. Logos rolls ordinary schema and witness database changes back and prevents submitted SQL from terminating or replacing its transaction, but PostgreSQL sequences, external functions, triggers, foreign data wrappers, and operating-system effects are not made transactional by `ROLLBACK`. The transaction is therefore a cleanup mechanism, not a sandbox for an untrusted shared production database.

Temporal SQL follows the configured session time zone. Logos defaults to `UTC`; pass `--sql-time-zone <zone>` or set `LOGOS_SQL_TIME_ZONE` to change the PostgreSQL `SET TIME ZONE` value used during static analysis and witness materialization. This matters when `timestamp without time zone` and `timestamp with time zone` values are mixed: PostgreSQL interprets the naive timestamp in the session time zone before comparing it to an instant. FormalSQL lowering keeps `timestamp with time zone` as a distinct UTC-instant value rather than collapsing it into an ordinary local `timestamp`; the configured SQL time zone is used only to interpret timezone-less `timestamp with time zone` literals. Rocq lowering supports `UTC`/`Z`, bare fixed-offset zones such as `+08:00`, and IANA time zone names such as `America/New_York`; ambiguous or nonexistent local timestamp literals around daylight-saving transitions are rejected conservatively. POSIX-style prefixed offsets such as `UTC+8` or `GMT+8` are intentionally rejected so Rust lowering and PostgreSQL materialization cannot disagree about offset signs. Generated `database_values_conform` hypotheses admit exactly the finite PostgreSQL `DATE`, `TIME`, `TIMESTAMP`, and `TIMESTAMPTZ` ranges plus the two PostgreSQL temporal infinities where the type supports them. DATE and timestamp infinities use ordered sentinels outside the finite range, survive supported arithmetic and casts, and `EXTRACT(YEAR FROM date)` returns numeric infinity while `EXTRACT(MONTH FROM date)` returns SQL NULL.

Locale-observable text behavior requires an explicit database environment. Pass `--sql-default-collation C --sql-character-classification C --sql-locale-provider libc --sql-server-encoding UTF8` (or the corresponding `LOGOS_SQL_DEFAULT_COLLATION`, `LOGOS_SQL_CHARACTER_CLASSIFICATION`, `LOGOS_SQL_LOCALE_PROVIDER`, and `LOGOS_SQL_SERVER_ENCODING` variables) to enable the exact PostgreSQL UTF-8/libc-C model. The selected environment is carried through Calcite/Logos IR, the lowering cache key, proof reports, and generated `Schema.v`; PostgreSQL-backed validation requires `pg_database.datcollate = 'C'`, `datctype = 'C'`, the libc `datlocprovider`, and UTF8 encoding. In this environment, text ordering and `MAX(text)` compare UTF-8 bytes lexicographically, while `UPPER`/`LOWER` use libc's C character classification and therefore map ASCII letters only. Non-ASCII UTF-8 bytes remain unchanged. Omitting any dimension is deliberately not interpreted as “use the database default.” Explicit schema or query `COLLATE` clauses remain unsupported unless separately modeled exactly.

The final acceptance path is shared: equivalence and data-dependent non-equivalence both select a generated claim in `Problem.v`, and immutable `Goal.v` plus the trusted Rocq checker validates that selector. Static PostgreSQL output or analysis-outcome mismatches are the only pre-proof `NEQ` boundary.

Reusable Logos-local results and the curated FormalSQL-owned context/renaming
interfaces remain documented in `theories/FormalSQL/catalog/INDEX.md`.
Search its `possible` route first for final SQL theorems; the `scheduled` route
is an explicitly foundational implementation layer. `manifest.json` records
every indexed `Lemma`, `Theorem`, and `Corollary` with its exact ownership
source, line, interface layer, replacement, and declaration.
Run `python3 scripts/generate-formal-sql-catalog.py --check` to reject
catalog/source drift. At proof time Logos does not classify the query or route
lemmas. The agent searches the authoritative read-only `.v` sources directly
from its proof sketch and residual goals.

Hard-case lemma mining is trace-driven rather than a static query-feature
audit. A pre-run classification is provisional. After every representative
run, the latest terminal `Problem.v`, proof plan, checked scratch declarations,
and checker events of every timeout and slow solved case must be inventoried.
For each substantial local helper, record its normalized statement, first
FormalSQL evaluator or representation boundary, proof cost and downstream
uses, the closest public contract, and whether that contract is exact,
short-derivable, or missing. In particular, evaluator-to-logical bridges,
list/bag transport, cross-environment stability, and first-error scheduler
lifts may not be dismissed as generic "proof plumbing" without this contract
comparison. The audit evaluates what the agent could find in the authoritative
source tree; it does not replay a host-generated shortlist.

Genericity is decided from the parameterized statement, not from the concrete
case in which the helper was discovered. A schema-independent single-operator
or semantic-boundary law may be intrinsic core semantics even when first seen
in one case; repeated use across independent branches is also reuse evidence.
Conversely, fixed tables, columns, constants, generated trees, branch counts,
or a complete source-to-target rewrite remain case-specific. A successful
certificate does not waive this post-run harvest, and `intrinsic composition`
is terminal only after its reusable sublemmas have been separated. Independent
fairness and soundness reviews cover accepted lemmas; a separate recall review
must inspect omitted local helpers and bind its evidence to a run no older than
the resulting library audit.

FormalSQL represents modeled SQL runtime failures as outer `SqlError` outcomes, not as SQL `NULL` values. Logos exposes three proof modes through `--verification-mode`, with error-preserving `outcome-unconditional` as the default. `safe-unconditional` is the strongest certificate: both programs must be runtime-error free on every conforming database and their exact successful ordered-list observations must agree. `outcome-unconditional` instead compares the complete observable outcome relation: each side must expose at least one legal outcome, successful observations must agree, and both sides must expose exactly the same modeled SQL runtime-error categories. `conditional` proves that same error-preserving equivalence under a structured input condition. A conditional certificate separately proves that the condition is well formed and either follows from the original schema contract (`CONDITIONAL-DERIVED`) or is jointly satisfiable with it (`CONDITIONAL-EXTERNAL`). The condition language contains typed range, nonzero, non-NULL, string-length, and relation-cardinality constraints; it cannot contain an arbitrary Rocq proposition, the query evaluator, a false constructor, or the equivalence goal itself. The proof-agent run log records both the source classification and the exact audited `generated_precondition` definition.

Aggregate semantics are declarative and plan-independent. `SUM(INTEGER)` denotes the mathematical sum followed by PostgreSQL's `BIGINT` result-range check; integral `AVG` and variance/stddev use mathematical count, sum, and sum-of-squares states followed by PostgreSQL's numeric finalization rules. NUMERIC aggregate counters are exact mathematical counts. These meanings do not depend on serial versus parallel aggregation, HashAggregate versus SortAggregate, spill behavior, `work_mem`, or worker scheduling. No PostgreSQL executor profile defines the theorem.

General SQL `EXP` and `POWER` are not currently part of the modeled scalar-operator surface. Lowering rejects those expressions until reusable, parameterized PostgreSQL semantics are available. One deliberately narrow Calcite materialization shape is modeled end to end: `CAST(POWER(bigint_expression, 0.5::numeric) AS integer)` preserves PostgreSQL's NUMERIC square-root scale, explicit-cast rounding, invalid-power error, and int4 overflow behavior. FormalSQL's generic `QExpr_RowMap` remains available for caller-supplied row functions with explicit output schemas and ordinary `SqlOutcome` behavior.

Row-dependent `NUMERIC`/`DECIMAL` division and `DECIMAL(p,s)` casts are emitted with built-in division-by-zero and numeric-overflow error interpretations. Explicit `NUMERIC`/`DECIMAL` to `INTEGER` casts round finite values to the nearest integer with ties away from zero before checking the signed int4 range; NULL stays NULL, range overflow is a data exception, and NaN or infinity produces PostgreSQL's feature-not-supported runtime outcome. `INTEGER` to `BIGINT` is represented by a distinct total cast symbol whose Rocq interpreter preserves the exact mathematical value and NULL, rather than conflating the int32 and int64 carriers. These possible failures and representation changes therefore remain visible to the generated source/target runtime-safety obligations instead of being erased by static metadata. Fixed `DECIMAL(p,s)` table values include PostgreSQL `NaN`: it equals itself, sorts above finite values, propagates through arithmetic and `SUM`/`AVG`, and is accepted by every valid numeric typmod. Generated schema preconditions require each finite fixed-decimal value to be a canonical value of its declared typmod. `AVG` over a fixed `DECIMAL(_,2)` uses one aggregate-owned logical PostgreSQL numeric state, including exact counters, fixed-scale accumulation, special values, and finalization; it is never decomposed into independently evaluated `SUM` and `COUNT`. Other fixed scales and unconstrained `NUMERIC` AVG inputs remain conservatively rejected. Numeric `+`, `-`, `*`, `/`, and unary minus results are observably typmodless PostgreSQL `numeric` unless an explicit source-level typmod cast is present; operand display-scale inference is retained only for scale-sensitive evaluation and never trusted as an output typmod. Planner-time constant folding does not define the logical expression semantics. Every present `OFFSET` and `LIMIT`/`FETCH` count is validated before a `FETCH 0` empty-result simplification, so the simplification cannot hide a language-level invalid count.

Nullable Boolean equality and ordering follow PostgreSQL's native Boolean comparison domain: `false` sorts before `true`, equal non-NULL values compare equal, and any ordinary comparison with SQL `NULL` yields `UNKNOWN`. This interpretation is shared by ordinary predicates, grouped HAVING predicates, and quantified singleton scalar-subquery comparisons.

PostgreSQL does not implicitly coerce an integer to Boolean while resolving `boolean = integer`: the statement terminates during parse analysis with `undefined_function` (SQLSTATE 42883). Calcite instead changes a bare source `0`/`1` into a well-typed Boolean `false`/`true`. Logos accepts that erased error only through a root-WHERE marker produced while the Java wrapper still has the independently parsed source tree and the generated Rex tree. The marker binds the exact equality path, operand order, source and generated values, input index, and base-table field; the Rust importer revalidates every redundant field before attaching typed provenance. Lowering then requires the marker count, the independently rediscovered Boolean-Rex/numeric-source mismatch count, and the exact consumed-marker count to agree before emitting `QExpr_Error UndefinedFunction`. Missing, duplicate, stale, cross-scope, qualifier-drifted, explicitly cast, string, or ordinary integer comparisons cannot fall through to Calcite's Boolean approximation.

Calcite can also discard an unsliced `ORDER BY` inside an `IN` subquery. Logos does not treat that erasure as generally sound: PostgreSQL can still expose evaluation errors, volatile calls, or set-returning behavior while producing the subquery rows. Recovery requires an exact source-AST attestation that binds parser scopes, one direct projected base-table column, one direct base-table order key, complete unsliced/non-distinct/non-grouped source shape, authoritative schema ordinals and types, and the corresponding erased Rex-subquery tree. Rust revalidates the bound table, field positions, generated arities, projection type, direction, and NULL placement before reconstructing the missing inner `Sort`. An absent, stale, duplicated, decorated, or mutated attestation is rejected; neither a descendant Sort nor an unverified root collation is accepted as evidence.

HAVING and derived-table WHERE retain their declarative clause ownership. A source HAVING is installed as the logical Group Boolean expression and its SELECT target remains a logical projection above that group. Aggregate expressions registered by the group are finalized, and their language-level errors observed, before scalar HAVING decides whether to retain the group; post-HAVING scalar target operations are evaluated only for retained groups. An outer WHERE over a grouped derived table remains an outer Filter; lowering never moves it below grouping merely because PostgreSQL's optimizer could. Source provenance still binds parser query blocks, aliases, aggregate slots, and base-column lineage so Calcite cannot mislabel the clause, but that evidence authorizes no predicate pushdown or executor schedule. Forged or cross-block provenance remains fail-closed.

The normalized formal outcome relation follows the logical query tree. A filter denotes selection over its logical input; joins combine their logical inputs; grouping denotes mathematical partitioning and aggregate finalization; `ORDER BY`, `OFFSET`, and `FETCH` use the exact ordered-list relation. Physical predicate order, projection pruning, plan-time constant folding, aggregate strategy, and executor scheduling do not define that relation. Native `AND`/`OR` exposes PostgreSQL's unspecified executor evaluation schedule relationally: either operand may be evaluated first, either decisive operand may stop evaluation, and an evaluated failing operand contributes its `SqlError` outcome. Runtime-total operands still have the unique SQL three-valued result. Planner-time constant evaluation is not conflated with this schedule; lowering fails closed when a closed immutable Boolean subexpression can make planner folding alter error visibility. Native one-column scalar subqueries retain PostgreSQL's zero-row typed NULL, one-row value, and multirow cardinality-error contract. Declarative `EXISTS` uses an explicit capped-cardinality semantics: ordinary target-only projections, row maps, bare duplicate elimination, and bare ordering delegate without evaluating dead target computations; `FETCH 0` and filters short-circuit at the semantic boundary. A union stops once either arm establishes nonemptiness. Native inner/semi/anti joins scan one pair ordering only until the first row whose match status determines output, while outer joins derive existence from the same single pair of chosen child observations without constructing an unused complete ON-condition matrix. OFFSET and window operators demand their ordinary child computation, while grouping demand still finalizes SELECT and HAVING aggregates before deciding cardinality but leaves post-HAVING scalar targets dead. Calcite represents both `SELECT DISTINCT` and grouping-only queries as call-free `LogicalAggregate` nodes; the wrapper therefore emits a byte-exact `sourceDistinct` attestation, Rust validates its original query-block span and complete all-output key/type shape, and only then emits native `QExpr_Distinct`. These are trusted source-level rules rather than an appeal to a particular optimizer plan. Searched `CASE` retains lazy selected-branch semantics, and aggregate `FILTER` remains logically prior to its argument. Authoritative child types and source provenance repair information lost by Calcite, but never attest a physical evaluation schedule.

The formal query target is the normalized relational core emitted by the frontend, not all of SQL. Its single exact evaluator is a compositional outcome relation over ordered row lists, covering `Project`, `Filter`, joins, set operations, grouping, duplicate elimination, `ORDER BY`, `OFFSET`, and `FETCH` at arbitrary nesting depth. Ordering constrains legal permutations but does not choose an order between ties; slicing is applied to every legal input list, so a nested tied top-k may denote several possible result bags. Native outer, semi, and anti joins choose one outcome from each child and reuse one coherent condition matrix, so a nondeterministic ordered child cannot be chosen independently by different desugared branches. Ordering-insensitive operators then close each result bag under permutation. The abstraction `alpha` maps evaluated ordered lists to their possible bags, while `gamma` forgets order by taking every permutation of each possible bag and is therefore a permutation-closure over-approximation in general. `BagClosed` characterizes exactly the regions where every abstract bag can be recovered as an `ordered_rows_equiv` SQL observation. In those regions Logos can use lifted bag operations, and it reuses deterministic FormalSQL bag proofs when the possible-bag relation is proved to be a singleton. Bag theory is a proof abstraction, not a second or peer query semantics. “Semantically complete” refers to equivalence in this defined normalized core; it does not claim that the Rust/Calcite frontend is mechanically verified or that proof search finds every true equivalence.

Multiply referenced, nonrecursive statement-root CTEs are reconstructed as query-local bindings around this existing core, rather than as another FormalSQL algebra operator. The definition is lowered once, each reference becomes a fresh internal table leaf backed by the same successful bag, and dependency order, output types, statement ownership, and source/target isolation are checked before emission. Queries without such bindings retain the original generated interface. Recursive or nested `WITH` scopes and unsupported materialization modifiers remain fail-closed. PostgreSQL may avoid evaluating a CTE that is not demanded, whereas the current composition relation materializes its definitions eagerly; consequently, trusted bound-query outcome equivalence and Rocq countermodels require materialization safety exactly for statements with local bindings. Binding-free statements directly reuse the canonical evaluator and retain exact successful and error outcomes. This conservative boundary prevents an eagerly exposed common binding error from certifying either `EQ` or `NEQ` until demand-aware shared evaluation is modeled directly.

Native `QExpr_GroupingSets` evaluates one child outcome, converts that successful result to a bag, evaluates every grouping set against the same bag, propagates branch errors, and combines successful branches with bag `UNION ALL`. Absent full-grouping-key positions become typed `NULL`, and duplicate grouping sets remain duplicate branches. The operator is a permutation-closing reset, so its exact ordered semantics and possible-bag proof abstraction remain coherent without allowing independent child choices.

FormalSQL directly represents the cumulative window fragment needed by TPC-DS 51: structured `ROW_NUMBER()`, `SUM(expr)`, and `MAX(expr)` over one shared partition/order specification with `ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW`. It chooses every ordering permitted between peers, evaluates every window item against the same chosen partition prefixes, preserves PostgreSQL NULL partitioning and explicit/default NULL ordering, and reports BIGINT/aggregate language-level errors. Ordinary expressions and order keys are staged once only when moving them is total. Calcite's nullable-NUMERIC window-SUM CASE/COUNT rewrite is removed only after the independently parsed source window, complete generated tree, input lineage, identifiers, result type, and both window specifications agree. Other frames, nested window expressions, DISTINCT/ordered aggregate modifiers, and mixed window specifications remain conservatively unsupported.

`SqlQueryWellFormed.v` checks the post-desugaring Rocq core directly, without introducing a second isomorphic query AST or a second query traversal for typed operands. Every generated and independently trusted certificate goal requires both ordered query programs to satisfy the canonical `TNullQueryExprAdmissible` judgment under each conforming database. It combines the parameterized structural/type recursion `query_expr_admissible`—including scalar result kinds and types, unique projection outputs, disjoint cross-join schemas, ordered set compatibility, grouping metadata, window attributes, and positional subqueries—with statement-root analysis-error placement and statement-wide unique, nonempty Boolean schedule sites. Each immutable generated `Queries.v` compiles that one typed admissibility-with-outputs certificate; an externally attested `QExpr_Error` is legal only at the root and therefore cannot be hidden by target elimination or `FETCH 0`. Calcite and Rust remain trusted for translation into that core. The Rust validator runs after lowering and again at emission, where it additionally checks exact PostgreSQL NUMERIC versus `DECIMAL(p,s)` result shapes instead of treating their typmods as interchangeable; Rocq then checks the generated certificate. Together these boundaries prevent a malformed emitted term from bypassing validation.

The proof path derives every output shape from one ordered typed signature carried by the successfully lowered FormalSQL syntax. Table leaves retain their authoritative column order, and exact error, VALUES, table, and row-adapter terms carry or preserve that witness; set-valued schema observations are derived from those lists. Internal query labels remain unchanged for binding, while the final paired source and target observations are projected to shared ordinal labels so SQL result-column names are not treated as observable. `Queries.v` records those canonical final signatures, and every generated or independently trusted goal first requires each recorded list to equal `map query_expr_outputs` of its semantic query program before requiring source/target signature equality and query equivalence. Arity and positional base-type or typmod differences are rejected by the static PostgreSQL preflight before proof search and remain explicit FormalSQL signature obligations. At every schema-bound table scan, Logos resolves the relation in the authoritative generated schema and requires the reported arity, column names, base types, and PostgreSQL typmods to agree before any typed attribute reference can be emitted; later scope analysis enriches that signature only with numeric display-scale provenance rather than deriving another schema. Set-operation children are projected to their common internal labels by ordinal position. An otherwise unresolved top-level `NULL` follows PostgreSQL's output coercion to `text`.

Set-operation typing is derived from the successfully lowered child scopes, never by relabeling a child with the parent Calcite row type. Each existing binary `UNION`, `INTERSECT`, or `EXCEPT` node is resolved left to right using PostgreSQL's common-type rules. Equal types retain an identical typmod; differing numeric typmods become unconstrained `numeric`; and the mutually implicitly coercible `text`, `varchar`, and `bpchar` bases retain the first non-unknown base while differing or cross-base typmods become unconstrained. Only the resulting modeled implicit coercion is emitted. A root bare source `NULL` or string literal is treated as PostgreSQL `unknown` only when its independently parsed source node attests that exact literal; explicit casts remain known inputs, and missing, ambiguous, or source-less propagated provenance is rejected rather than inferred from Calcite's contextual child type. Unknown inputs are ignored for base-type selection but force typmodless output, while an all-unknown binary pair resolves to `text`. Unknown-string conversion to a selected non-string category remains conservatively rejected because the target input conversion and its parse-time error are not yet modeled. This preserves TPC-DS concatenation as `text` and `SUM`/numeric arithmetic as unconstrained `numeric` through nested bag and distinct unions without trusting stale `CHAR(28)` or `DECIMAL(19,2)` metadata.

PostgreSQL numeric display scale is tracked separately from the equality carrier while lowering scale-sensitive division. Fixed-scale columns, literals, explicit casts, `+`, `-`, `*`, and supported aggregates propagate internal provenance across projections and renames; Calcite's derived result typmods are never used as that provenance. The provenance may also record a representative scale whose only variation is for a zero value: nonzero values have the recorded scale, while zero values have no greater scale. This property is preserved by same-scale `CASE` alternatives and `SUM` and is sufficient for division because a zero numerator remains zero and a zero divisor raises independently of display scale. Alternatives with incompatible possible nonzero scales remain conservatively blocked.

Character values share one FormalSQL string carrier while retaining the observable PostgreSQL typmod: `text`, unconstrained `varchar`, `varchar(n)`, `char(n)`, or typmodless `bpchar`. The last form is PostgreSQL's internal blank-padded base type produced when operator/common-type resolution discards a fixed width; it has no width at which values are truncated. Its logical carrier canonicalizes trailing spaces because the currently accepted observations use PostgreSQL `bpchar` equality, grouping, and set semantics. Serialized physical output and byte-counting observations such as `octet_length` remain unsupported. Literal `LIKE` patterns are exact under the deterministic-default-collation contract for text, varchar, and fixed-width `char(n)` operands when their only metacharacter is an unescaped `%`: matching covers the complete string, `%` consumes zero or more UTF-8 code points, SQL NULL remains UNKNOWN, and fixed-width padding is reconstructed before matching. Typmodless `bpchar` LIKE remains blocked because its physical trailing spaces are observable but its lost width cannot be reconstructed; `_`, escape syntax, and nonliteral patterns are also conservatively blocked. Three-argument `substring` is accepted only for authoritative bounded `char(n)`/`varchar(n)` inputs with a typed literal start of at least one and a typed nonnegative literal count; it applies PostgreSQL's CHARACTER-to-text trailing-space conversion and then slices Unicode code points, while dynamic or negative bounds remain unsupported. Explicit casts to constrained character types truncate; assignment coercion reports right truncation unless the discarded suffix consists only of spaces. Fixed-width `char(n)` values use canonical logical payloads with reconstructible blank padding, including PostgreSQL's mixed `char`/`varchar`/`text` equality rules. Rocq strings are validated as UTF-8 and typmod lengths count Unicode code points rather than bytes. General locale-sensitive behavior stays outside the value carrier; exact ordering, ASCII case conversion, and `MAX(text)` are enabled only by the explicit UTF-8/libc-C environment above. One ordering-free normalization is exact under the deterministic-default-collation contract: for a direct `text` reference and one identical untyped string literal, `(x < c OR x > c)` becomes `x <> c`; both forms remain UNKNOWN for NULL, and mismatched/computed/other-typmod shapes stay blocked. Default PostgreSQL equality and the accepted literal `LIKE` fragment are modeled under the same deterministic-collation contract.

PostgreSQL identifier identity is preserved at ingestion: unquoted names fold to lower case, double-quoted names retain their exact spelling and compare case-sensitively, and backtick quoting is rejected. Text concatenation is emitted only when literals and declared `CHAR(n)`/`VARCHAR(n)` bounds prove that every intermediate result, including its varlena header, stays within PostgreSQL `MaxAllocSize`; unconstrained text concatenation remains conservatively unsupported rather than losing `program_limit_exceeded` behavior.

Lowering also blocks SQL behavior whose PostgreSQL semantics is not yet represented faithfully. Typed scalar value subqueries support one resolved output column in the modeled value domains and preserve the zero/one/many-row contract; surrounding representation-sensitive operators without an exact signature, correlated HAVING environments, and scalar HAVING over multi-branch grouping sets remain fail-closed. Other unsupported behavior includes `NULLIF` after Calcite has rewritten away PostgreSQL's first-argument result typing, literal/expression `IN` lists, window shapes outside the cumulative fragment above, aggregate-local ordering or other modifiers, nonliteral/negative/NULL or signed-`bigint`-out-of-range LIMIT/OFFSET counts, string ordering without the explicit modeled UTF-8/libc-C environment and Calcite's clustered collation direction, unconstrained table-backed `numeric` values while per-value display scale is unavailable, and precision-changing `time` casts. Aggregate `FILTER` is supported for the modeled NULL-ignoring built-ins by materializing `CASE WHEN filter THEN argument ELSE NULL END` in a lazy projection before aggregation; `COUNT(*) FILTER` uses a non-NULL marker only in the selected branch, and `DISTINCT` remains on the aggregate. Scalar and row-valued subquery `IN` are aligned positionally to the subquery result and use componentwise SQL three-valued equality: a definite field mismatch makes the row comparison false even when another field is NULL. `NOT IN` is the three-valued negation of that typed membership expression, so NULL contamination remains UNKNOWN instead of being desugared unsoundly to `NOT EXISTS`. The remaining items are unsupported proof obligations rather than approximated successful queries.

The CLI reflects this distinction in its result display. A trusted proof is reported as `SAFE-UNCONDITIONAL`, `OUTCOME-UNCONDITIONAL`, `CONDITIONAL-DERIVED`, or `CONDITIONAL-EXTERNAL`; these categories remain separate in JSON rather than being merged into one solved count. `NOT EQUIVALENT` is shown as a red terminal result only for a static output/analysis mismatch or a trusted FormalSQL countermodel. Before spending proof-agent tokens, Logos compiles and independently kernel-checks the generated schema, query, and witness modules against the host-built FormalSQL/Logos theorem closure. The batch runner resolves that immutable closure through a content-addressed cache and binds its exact source/object, Rocq, standard-library, runtime, and checker bytes in the trusted-stack manifest. Generated Schema/Queries/Witness prefixes are likewise cached by source and authority digests; cache hits are still independently kernel-checked. Missing or mutually inconsistent `.vo` files, a missing checker dependency, or another baseline-loading failure is a non-repairable trusted-environment error; it terminates the solver instead of resuming an agent that can edit only `Problem.v`. Proof search gives the first invocation the complete deadline remaining after the trusted-check reserve; repair continuations resume the same private Codex session and only restart it after 16 unsuccessful invocations. Each later generation starts in a distinct private `CODEX_HOME`; prior session/history trees are never mounted into it. A strict Unix-socket broker provides sequential synchronous compiler diagnostics with no completed-check or request-count quota. A request may select any positive timeout; the host clips it to the current proof invocation's remaining deadline. The proof prompt asks the agent to keep a top-level `Problem.v` route and use local helpers for concrete residuals, but the broker does not enforce a search order or helper count. Only the host executes the checker and records its telemetry. This preserves authoritative `turn.completed` usage accounting and prevents agent-written telemetry from entering experiment metrics. A proof agent may write a strict `counterexample-handoff.json`; Logos treats it only as guidance for a fresh counterexample-agent round. Successful DML materialization creates a new typed `Witness.v` proof generation, while `no_candidate` resumes the existing proof session. Neither response is a verdict. A proof-agent command or diagnostic that exits successfully is not itself a proof: the overall solver result remains `equivalence_verification_incomplete` unless the immutable `Goal.v`, source audit, and separate complete trusted Rocq check all accept the selected certificate. The default CLI prints a pretty terminal summary and writes the machine-readable JSON report to `<log_dir>/report.json`; batch runners can pass `--quiet` to suppress the pretty stdout while keeping the JSON report file.

## Submodules

The SQLCoq dependency is pinned as a Git submodule:

```bash
git submodule update --init --recursive
```

Current configuration:

```text
vendor/FormalSQL  git@github.com:WindOctober/FormalSQL.git  branch master
```

## Build

Machine-local paths are not encoded in tracked scripts. Start from the example
configuration and enable the repository-local direnv environment:

```bash
cp .env.example .env
direnv allow
```

`.envrc` loads `.env` through direnv; Python entry points consume the resulting
process environment and do not parse `.env` themselves. Run them with an
active direnv shell or `direnv exec . <command>`. A complete proof run needs:

- `LOGOS_JAVA_HOME` pointing to JDK 17;
- `CODEX_HOME` containing the authenticated Codex configuration;
- `LOGOS_ROCQ_OPAM_SWITCH` pointing to the repository Rocq switch;
- `LOGOS_POSTGRES_URL` pointing to PostgreSQL 17 with UTF8 encoding, the libc
  locale provider, `LC_COLLATE=C`, and `LC_CTYPE=C`;
- Docker and Linux `bubblewrap` access.

Check these before starting an expensive batch:

```bash
direnv exec . bash -euo pipefail -c '
  test -x "$LOGOS_JAVA_HOME/bin/java"
  test -x "$LOGOS_ROCQ_OPAM_SWITCH/_opam/bin/rocq"
  test -f "$CODEX_HOME/config.toml"
  grep -Fxq '"'"'model = "gpt-5.6-sol"'"'"' "$CODEX_HOME/config.toml"
  grep -Fxq '"'"'model_reasoning_effort = "medium"'"'"' "$CODEX_HOME/config.toml"
  test -n "$LOGOS_POSTGRES_URL"
  docker image inspect \
    sha256:bba804128f28ee6948ed601afac7bd158bab3617d784e2479ef588d03a97459b \
    >/dev/null
  psql "$LOGOS_POSTGRES_URL" -Atqc \
    "select current_setting('"'"'server_version_num'"'"'), datcollate, datctype,
            datlocprovider, pg_encoding_to_char(encoding)
       from pg_database where datname = current_database();"
'
```

The database query must report PostgreSQL 17, `C|C|c|UTF8`. External
publication and baseline-tool locations use
`LOGOS_FINAL_EXPERIMENT_DIR`, `LOGOS_QED_PARSER`, and
`LOGOS_SQLSOLVER_JAR`. Benchmark membership, the proof gate, and materializer
byte baselines are repository-owned under `benchmarks/core/authority/`; neither
published results nor `var/` state define a benchmark campaign.

Logos uses the Rocq-compatible SQLCoq fork in `vendor/FormalSQL`. Rocq build targets require `LOGOS_ROCQ_OPAM_SWITCH`, `ROCQ_OPAM_SWITCH`, or `OPAM_SWITCH`; the default repository-local switch is `.opam-rocq`.

Trusted proof checking also requires `bubblewrap` (`bwrap`) on Linux. The checker compiles agent-controlled `Problem.v` from an empty-root sandbox containing only a read-only mount of the manifest-bound non-example FormalSQL/Logos source-object authority closure, the Rocq runtime and standard library, the exact required OS runtime files, and a disposable writable problem directory. The host repository, catalogs, examples, and retained histories are absent. It then compiles the trusted `Goal.v` from a fresh directory. The batch runner binds the exact `rocq`, `rocqchk`, `rocqworker`, `rocqnative`, and `bwrap` executables, their ELF interpreter/dependency closure, and the effective findlib/runtime metadata in its trusted proof-stack manifest. It also binds a reviewed exhaustive checker-tool list (including the pinned host `bash` and `timeout`, staging utilities, digest tools, and one of the reviewed Ubuntu 22.04/23.04 `ldd` scripts plus its Bash interpreter), every literal `ldd` runtime-loader candidate including required absence state, the system loader cache/preload state, and the fixed NSS identity inputs `/etc/nsswitch.conf` and `/etc/passwd`. Manifest inspection starts from an empty, fixed environment. The runner likewise starts the solver and SQL-frontend preparation from recorded clear-then-fixed environments; the frontend manifest binds its absolute Bash invocation, script tools, Maven shell/tools, JDK, classes, and runtime jars, while the provider manifest binds the Codex wrapper, `/usr/bin/env`/Node interpreter chain, fixed PATH, and command-child policy. The Rust solver independently clears inherited state before the SQL frontend, counterexample provider, trusted checker, and proof-agent launcher, restoring only each boundary's recorded fixed values and explicit contract variables. Thus `BASH_ENV`, exported shell functions, ambient loader/OCaml/Java/Maven paths, proxy/provider overrides, and caller-selected temporary paths cannot replace manifest-bound tools or alter semantic lowering, proof-context staging, or certification. Every manifest and policy digest is recomputed before a run can become terminal-complete. This attestation begins inside the already-running Python runner: the Python interpreter, operating-system kernel, and filesystem implementation remain part of the ambient experiment-host trust boundary rather than recursively self-attested inputs. The solver Docker image installs `bwrap`.

The host executes an embedded proof-agent launcher outside the container's writable problem directory. The launcher directly mounts a digest-manifested immutable closure containing only source-backed non-example FormalSQL `.v`/`.vo` pairs; source-less build residue, examples, catalogs, guides, retained runs, the host Rocq switch, and the trusted checker are not mounted. The only agent-visible checker is a strict client for a nonce- and digest-bound host Unix-socket broker. Diagnostics are sequential and share the invocation deadline, without a separate request-count or fixed per-check ceiling; the agent cannot select the compiler or request final certification. Before every diagnostic process, the host snapshots and deterministically audits the exact candidate with the same command/import policy used for final source auditing. Rejected candidates produce host telemetry and feedback without starting Rocq. Every broker request and reserved timeout is reconciled in the report. An accepted request binds its clean source-audit artifact to one contiguous checker sequence; a source-audit rejection instead binds its candidate, request, rejecting audit, and explicit no-checker feedback, and contributes neither a checker invocation nor checker elapsed time. Preflight resolves a source- and authority-digest-bound, host-only Schema/Queries/Witness cache for accepted diagnostics; the cache is never mounted into the agent. Fixed-witness generations reuse unchanged Schema/Queries objects and replace only Witness. Successful problem diagnostics retain an exact prefix-bound `Problem.vo`. Final certification verifies those source/object bindings, reuses that checked Problem object when available, compiles the immutable `Goal.v` separately, and explicitly kernel-checks `Schema`, `Queries`, `Witness`, `Problem`, and `Goal`; only the manifest-bound host theorem closure is admitted as the already-built dependency. Successful problem-only checks advance a host-owned compile-clean checkpoint restored at bounded session resets. The container root is read-only, and all mutable agent state shares one configurable kernel-enforced tmpfs quota (2 GiB by default); no generated Rocq file has a smaller framework cap. After the container exits, Logos validates the mounted-closure manifest against the host files, snapshots the generated sources, verifies that `Schema.v`, `Queries.v`, and `Goal.v` are unchanged, audits the exact checked `Problem.v`, and invokes a different embedded checker from a host-only directory. Diagnostic and final telemetry are therefore not writable by the proof agent, and only the final isolated kernel/axiom check can determine `ProofComplete`.

```bash
make submodules
make logos-formal-sql-lemmas
```

`logos-formal-sql-lemmas` builds the vendored FormalSQL semantics and only the trusted Logos definitions and lemmas required by generated proof checking. It deliberately excludes example modules from the production build.

Run the complete regression suite explicitly when changing the formal semantics:

```bash
make logos-formal-sql-checks
```

This target compiles a small set of Logos-owned regressions under `tests/rocq/regressions` plus `tests/rocq/Smoke.v`. General SQL value and query semantics remain the responsibility of FormalSQL; Logos keeps only adapter, proof-fact, and benchmark regressions that cross the repository boundary. For a quick integration check, `make smoke` compiles only `tests/rocq/Smoke.v` after FormalSQL.

If a compatible Rocq environment is already available and you only want to inspect the submodule state, run:

```bash
make submodules
make status
```

## Calcite Frontend

Logos uses an Apache Calcite CLI wrapper to turn SQL schemas and queries into the structured relational and scalar IR consumed by the Rust lowering pipeline. The wrapper is a Maven-managed Java project; its `pom.xml` declares the Calcite dependency, Java version, and CLI entry point.

The wrapper lives in:

```text
frontend/calcite-wrapper
```

Run the bundled example with:

```bash
make calcite-ir
```

The Makefile target runs the default ingestion pipeline, which normalizes SQL through the SQLGlot dialect adapter and then invokes Calcite. To bypass dialect normalization and invoke the Calcite wrapper directly:

```bash
scripts/calcite-ir \
  --schema frontend/calcite-wrapper/examples/schema.sql \
  --sql frontend/calcite-wrapper/examples/query.sql
```

The benchmark runner does not execute Maven for every query. It prepares and
hashes the compiled classes and runtime dependency classpath once, then selects
the fail-closed `LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE` path in
`scripts/calcite-ir` and runs the bound JDK directly. Ordinary development
invocations leave that variable unset and retain the Maven-backed behavior.

Run the complete frontend regression layer, including Maven unit tests, the
wrapper-backed Rust integration suite, and SQLGlot adapter tests, with:

```bash
make frontend-tests
```

Each query contains one authoritative `rel` tree. It carries Calcite's validated
relational nodes, structured Rex operands, and exact source attestations needed
by the Rust importer. Obsolete parallel `sqlAst` and display-text plan views are
rejected instead of being silently ignored or hydrated.

The current DDL reader only covers simple `CREATE TABLE (...)` declarations. It exists to bootstrap Calcite validation and is not part of the trusted semantics. Logos should treat Calcite output as frontend IR, then generate explicit FormalSQL/Rocq definitions, theorems, and obligations for kernel checking.

## SQLGlot Dialect Adapter

Logos also includes an optional SQLGlot adapter for translating vendor SQL dialects into Calcite-friendly SQL before invoking the Calcite wrapper. The normalized SQL is the statement that the verifier actually models, so PostgreSQL-mode patches are restricted to unambiguous syntax normalization; later proof checking cannot repair a meaning-changing preprocessing rewrite.

The adapter lives in:

```text
frontend/sqlglot-adapter
```

Normalize a SQL file explicitly:

```bash
benchmarks/scripts/sqlglot-normalize \
  --input input.sql \
  --output normalized.sql \
  --report normalized.report.json \
  --read tsql \
  --write postgres \
  --identify
```

Or run the full SQLGlot-to-Calcite pipeline:

```bash
scripts/calcite-ir-sqlglot \
  --schema path/to/schema.sql \
  --sql path/to/query.sql \
  --read tsql \
  --write postgres \
  --normalized-output normalized.sql \
  --report normalized.report.json
```

The adapter currently performs three kinds of work:

- SQLGlot transpilation, for example translating T-SQL-style `SELECT TOP n` into Calcite-accepted `LIMIT n`.
- Identifier quoting via `--identify`, which avoids parser conflicts with aliases such as `year` or `returns`.
- Narrow Calcite-compatibility rendering for structured PostgreSQL
  timestamp-with-time-zone type nodes and unambiguous interval literals.

See `frontend/sqlglot-adapter/README.md` for the current patch list. These patches are frontend compatibility rewrites, not trusted proof rules.

The optional generated report records adapter-side normalizations for audit and
debugging. The normalized SQL itself is the authoritative statement passed to
the Calcite/Logos pipeline; the report is not a parallel semantic input.

## Benchmarks

The initial core rewrite benchmark seed lives in:

```text
benchmarks/core
```

It contains selected VeriEQL, R-Bot, and WeTune cases for frontend and equivalence-pipeline development without vendoring the full upstream repositories. See `benchmarks/core/README.md` for source commits, file layout, and size notes.

## SQLCoq Maintenance Status

The upstream SQLCoq repository is not currently maintained as a modern Rocq stack:

- The upstream `sqlformalsemantics` project targets Coq 8.11.2.
- `vendor/FormalSQL` tracks `WindOctober/FormalSQL` on branch `master`, forked from `formaldata/sqlformalsemantics`, with the goal of supporting Rocq 9.2 while preserving the original formal SQL semantics.

Accordingly, Logos currently depends only on FormalSQL's SQL semantics and SQLAlgebra definitions.
