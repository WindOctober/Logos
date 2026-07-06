.PHONY: submodules check-rocq-env formal-sql smoke logos-formal-sql-lemmas calcite-ir status

OPAM ?= opam
ROCQ_OPAM_SWITCH ?= $(OPAM_SWITCH)
OPAM_SWITCH := $(ROCQ_OPAM_SWITCH)
ROCQLIB ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH)/_opam/lib/coq,)
COQLIB ?= $(ROCQLIB)
OCAMLFIND_CONF ?= $(if $(OPAM_SWITCH),$(OPAM_SWITCH)/_opam/lib/findlib.conf,)
FORMALSQL_DIR := vendor/FormalSQL
FORMALSQL_SRC := $(FORMALSQL_DIR)/src
ROCQ_ENV := ROCQLIB=$(ROCQLIB) COQLIB=$(COQLIB) OCAMLFIND_CONF=$(OCAMLFIND_CONF)

submodules:
	git submodule update --init --recursive

check-rocq-env:
	@test -n "$(OPAM_SWITCH)" || { echo "Set ROCQ_OPAM_SWITCH or OPAM_SWITCH before building Rocq targets."; exit 2; }

formal-sql: check-rocq-env submodules
	cd $(FORMALSQL_SRC) && $(RM) Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	cd $(FORMALSQL_SRC) && $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq makefile -f _CoqProject -o Makefile.rocq
	cd $(FORMALSQL_SRC) && $(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- make -f Makefile.rocq -j1

smoke: formal-sql
	$(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories LogosSmoke theories/Smoke.v

logos-formal-sql-lemmas: formal-sql
	$(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories Logos theories/FormalSQL/TNullSyntax.v
	$(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories Logos theories/FormalSQL/RewriteSpec.v
	$(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories Logos theories/FormalSQL/OccFacts.v
	$(ROCQ_ENV) $(OPAM) exec --switch=$(OPAM_SWITCH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories Logos theories/FormalSQL/PiFacts.v

calcite-ir:
	scripts/calcite-ir-sqlglot --schema frontend/calcite-wrapper/examples/schema.sql --sql frontend/calcite-wrapper/examples/query.sql --read postgres

status:
	git submodule status
	@git -C $(FORMALSQL_DIR) status --short --branch
