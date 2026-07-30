.PHONY: submodules check-rocq-env formal-sql formal-sql-catalog smoke logos-formal-sql-lemmas logos-formal-sql-checks trusted-rocq-sandbox-test calcite-ir calcite-wrapper-tests sqlglot-adapter-tests materializer-tests frontend-tests status

OPAM ?= opam
ROCQ_OPAM_SWITCH ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH),$(CURDIR)/.opam-rocq)
OPAM_SWITCH := $(ROCQ_OPAM_SWITCH)
ROCQLIB ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH)/_opam/lib/coq,)
COQLIB ?= $(ROCQLIB)
OCAMLFIND_CONF ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH)/_opam/lib/findlib.conf,)
MAVEN ?= $(if $(wildcard $(CURDIR)/.cache/apache-maven-3.9.11/bin/mvn),$(CURDIR)/.cache/apache-maven-3.9.11/bin/mvn,mvn)
SQLGLOT_PYTHON ?= $(if $(wildcard $(CURDIR)/.cache/sqlglot-venv/bin/python),$(CURDIR)/.cache/sqlglot-venv/bin/python,python3)
FORMALSQL_DIR := vendor/FormalSQL
FORMALSQL_SRC := $(FORMALSQL_DIR)/src
ROCQ_ENV := ROCQLIB=$(ROCQLIB) COQLIB=$(COQLIB) OCAMLFIND_CONF=$(OCAMLFIND_CONF)
LOGOS_ROCQ_COMPILE = $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories Logos
LOGOS_ROCQ_TEST_COMPILE = $(LOGOS_ROCQ_COMPILE) -Q tests/rocq LogosTests

formal-sql-catalog: submodules
	python3 scripts/generate-formal-sql-catalog.py --check

submodules:
	git submodule update --init --recursive

check-rocq-env:
	@test -n "$(OPAM_SWITCH)" || { echo "Set ROCQ_OPAM_SWITCH or OPAM_SWITCH before building Rocq targets."; exit 2; }

formal-sql: check-rocq-env formal-sql-catalog
	cd $(FORMALSQL_SRC) && $(RM) Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	cd $(FORMALSQL_SRC) && $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq makefile -f _CoqProject -o Makefile.rocq
	cd $(FORMALSQL_SRC) && $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- make -f Makefile.rocq -j1

smoke: logos-formal-sql-lemmas
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/Smoke.v

# The ordered theory commands are exhaustively checked against the structured
# Rust trusted-theory registry by the proof-stage unit tests.
logos-formal-sql-lemmas: formal-sql
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/TNullSyntax.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/NumericFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/VerificationConditions.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/SchemaCardinality.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/QueryCardinality.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/QueryTNullSyntax.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/BitwiseFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/CardinalityCombinators.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/IntegrityFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/ScalarPredicateFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/StringTemporalFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/NumericDerivedFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/GroupingRewriteFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/AggregateRuntimeFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/RelationalAlgebraFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/OuterJoinFilterFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/GroupedFilterOutcomeFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/SemijoinCompositionFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/NumericRegroupFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/OrderedQueryFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/OrderedObservationTransportFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/RenameTransportFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/ProofAgentFacade.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/SubqueryFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/MembershipCompositionFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/WitnessFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/CountermodelFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/AggregateOutcomeBridgeFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/CorrelatedMembershipFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/MembershipJoinCompositionFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/FilterFkEliminationFacts.v

logos-formal-sql-checks: logos-formal-sql-lemmas
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/BitwiseRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/AcceptanceGroupInterfacesRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/ScalarPredicateAcceptanceRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/GroupedFilterOutcomeRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/FilterExtensionalOutcomeRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/GroupingGenericInterfacesRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/AggregatePartitionSupportRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/IdempotentAggregateSupportRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/AggregateOutcomeBridgeRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/FloatAggregateOrderRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/LeftJoinFunctionalProjectionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/FullJoinSourceSupportRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/RelationalSupportFilterRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OuterJoinFilterRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/BagHomomorphismInterfacesRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OutcomeResetCongruenceRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OrderedGroupChildOutcomeRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OrderedGroupingSetsFunctionalityRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OrderedWindowStructureRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OrderedObservationTransportRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/NumericRegroupRuntimeRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/NumericGroupObservationRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/NumericStrictMarginRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/ProjectionEnvironmentExtensionalityRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/ProjectionSelectListExtensionalityRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/ProjectionUnionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/OperatorOutcomeInterfacesRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/SuccessForallCompositionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/NullableTableObservationRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/PostgresValueDomainRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/TableAttributeAbsenceRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/SchemaRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/SubqueryEnvironmentCongruenceRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/SubqueryTruthAcceptanceRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/NativeScalarExpressionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/MembershipCompositionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/InSemijoinAcceptanceRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/SemijoinCompositionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/RenamingTransportRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/ProofAgentFacadeRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/ProofSelectorAuthorityRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/CountermodelFactsRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/CountermodelCardinalityRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/CorrelatedMembershipRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/MembershipJoinCompositionRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/FilterFkEliminationRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/Smoke.v

trusted-rocq-sandbox-test: logos-formal-sql-lemmas
	LOGOS_ROCQ_OPAM_SWITCH=$(OPAM_SWITCH) bash crates/logos-solver/scripts/test-trusted-rocq-check-sandbox.sh

calcite-ir:
	scripts/calcite-ir-sqlglot --schema frontend/calcite-wrapper/examples/schema.sql --sql frontend/calcite-wrapper/examples/query.sql --read postgres

calcite-wrapper-tests:
	cd frontend/calcite-wrapper && $(MAVEN) -q test
	RUST_MIN_STACK=67108864 CARGO_BUILD_JOBS=4 cargo test -p logos-ir --test calcite_wrapper -- --ignored --test-threads=1

sqlglot-adapter-tests:
	$(SQLGLOT_PYTHON) -m unittest discover -s frontend/sqlglot-adapter -p 'test_*.py'

materializer-tests:
	python3 -m unittest discover -s benchmarks/adapters/materializers -p 'test_*.py'

frontend-tests: calcite-wrapper-tests sqlglot-adapter-tests materializer-tests

status:
	git submodule status
	@git -C $(FORMALSQL_DIR) status --short --branch
