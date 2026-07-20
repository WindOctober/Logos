.PHONY: submodules check-rocq-env formal-sql smoke logos-formal-sql-lemmas logos-formal-sql-checks calcite-ir status

OPAM ?= opam
ROCQ_OPAM_SWITCH ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH),$(CURDIR)/.opam-rocq)
OPAM_SWITCH := $(ROCQ_OPAM_SWITCH)
ROCQLIB ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH)/_opam/lib/coq,)
COQLIB ?= $(ROCQLIB)
OCAMLFIND_CONF ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH)/_opam/lib/findlib.conf,)
FORMALSQL_DIR := vendor/FormalSQL
FORMALSQL_SRC := $(FORMALSQL_DIR)/src
ROCQ_ENV := ROCQLIB=$(ROCQLIB) COQLIB=$(COQLIB) OCAMLFIND_CONF=$(OCAMLFIND_CONF)
LOGOS_ROCQ_COMPILE = $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories Logos
LOGOS_ROCQ_TEST_COMPILE = $(LOGOS_ROCQ_COMPILE) -Q tests/rocq LogosTests

submodules:
	git submodule update --init --recursive

check-rocq-env:
	@test -n "$(OPAM_SWITCH)" || { echo "Set ROCQ_OPAM_SWITCH or OPAM_SWITCH before building Rocq targets."; exit 2; }

formal-sql: check-rocq-env submodules
	cd $(FORMALSQL_SRC) && $(RM) Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	cd $(FORMALSQL_SRC) && $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq makefile -f _CoqProject -o Makefile.rocq
	cd $(FORMALSQL_SRC) && $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- make -f Makefile.rocq -j1

smoke: logos-formal-sql-lemmas
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/Smoke.v

logos-formal-sql-lemmas: formal-sql
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/TNullSyntax.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/NumericFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/RewriteSpec.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/SchemaConstraints.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/VerificationConditions.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/SchemaCardinality.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/QueryCardinality.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/QueryTNullSyntax.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/ErrorFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/BitwiseFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/OccFacts.v
	$(LOGOS_ROCQ_COMPILE) theories/FormalSQL/PiFacts.v

logos-formal-sql-checks: logos-formal-sql-lemmas
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/BitwiseRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/regressions/SchemaRegression.v
	$(LOGOS_ROCQ_TEST_COMPILE) tests/rocq/Smoke.v

calcite-ir:
	scripts/calcite-ir-sqlglot --schema frontend/calcite-wrapper/examples/schema.sql --sql frontend/calcite-wrapper/examples/query.sql --read postgres

status:
	git submodule status
	@git -C $(FORMALSQL_DIR) status --short --branch
