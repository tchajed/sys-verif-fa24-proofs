SRC_DIRS := 'src' 'perennial'
ALL_VFILES := $(shell find $(SRC_DIRS) \
							-not -path "perennial/external/coqutil/etc/coq-scripts/*" \
						    -not -path "perennial/new*/*" \
							-name "*.v")
PROJ_VFILES := $(shell find 'src/sys_verif' -name "*.v")
SF_VFILES := $(shell find 'src/software_foundations' -name "*.v")

# extract any global arguments for Coq from _CoqProject
COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _CoqProject)

# user configurable
Q:=@
COQ_ARGS := -noglob
COQC := coqc

default: vo

sf: $(SF_VFILES:.v=.vo)

# PROJ_VFILES includes src/sys_verif/software_foundations.v which builds a subset of SF
vo: $(PROJ_VFILES:.v=.vo)
vos: $(PROJ_VFILES:.v=.vos)
vok: $(PROJ_VFILES:.v=.vok)

all: vo sf

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject | .coqdeps.d
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vok $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vok $(COQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	$(Q)rm -f .timing.sqlite3
	$(Q)find src/software_foundations \( -not -name "impdriver.ml" \
		-name "*.ml" -o -name "*.mli" \) -delete
	rm -f .coqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
