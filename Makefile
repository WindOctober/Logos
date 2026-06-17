.PHONY: submodules formal-sql smoke calcite-ir status

OPAM ?= opam
OPAM_SWITCH ?= ../FormalSQL/.opam-rocq
OPAM_SWITCH_PATH := $(abspath $(OPAM_SWITCH))
FORMALSQL_DIR := vendor/FormalSQL
FORMALSQL_SRC := $(FORMALSQL_DIR)/src

submodules:
	git submodule update --init --recursive

formal-sql: submodules
	cd $(FORMALSQL_SRC) && $(OPAM) exec --switch=$(OPAM_SWITCH_PATH) -- rocq makefile -f _CoqProject -o Makefile.rocq
	cd $(FORMALSQL_SRC) && $(OPAM) exec --switch=$(OPAM_SWITCH_PATH) -- make -f Makefile.rocq -j1

smoke: formal-sql
	$(OPAM) exec --switch=$(OPAM_SWITCH_PATH) -- rocq compile -Q $(FORMALSQL_SRC) SQLFS -Q theories LogosSmoke theories/Smoke.v

calcite-ir:
	scripts/calcite-ir-sqlglot --schema frontend/calcite-wrapper/examples/schema.sql --sql frontend/calcite-wrapper/examples/query.sql --read postgres

status:
	git submodule status
	@git -C $(FORMALSQL_DIR) status --short --branch
