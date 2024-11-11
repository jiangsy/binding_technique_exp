COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile
OTT_FLAGS := -coq_lngen true -signal_parse_errors true

ifeq ($(OS), Windows_NT)
	UNAME_S := Windows
else
	UNAME_S := $(shell uname -s)
endif

ifeq ($(UNAME_S), Darwin)
	SED_FLAG := -i ""
else
	SED_FLAG := -i
endif

SYSTEMS := systemf
IGNORE_DIRS := "test"

OTT_OUTS   := $(addsuffix /lngen/def.v,${SYSTEMS})
LNGEN_OUTS := $(addsuffix /lngen/prop_ln.v,${SYSTEMS})
AUTOSUBST2_OUTS := $(addsuffix /autosubst2/def.v,${SYSTEMS})

ott: $(OTT_OUTS)
lngen: ${LNGEN_OUTS}
autosubst2: ${AUTOSUBST2_OUTS}

%/autosubst2/def.v: %/autosubst2/language.sig
	autosubst $*/autosubst2/language.sig -o $@ -s ucoq
	# rename files and modify imports
	mv $*/autosubst2/core.v $*/autosubst2/prop_as_core.v
	mv $*/autosubst2/unscoped.v $*/autosubst2/prop_as_unscoped.v
	sed -e "s/Require Import core./Require Import $*.autosubst2.prop_as_core./g" ${SED_FLAG}  $*/autosubst2/prop_as_unscoped.v
	sed -e "s/Require Import core unscoped./Require Import $*.autosubst2.prop_as_core binder.autosubst2.prop_as_unscoped./g" ${SED_FLAG} $*/autosubst2/def.v
	# fix warning about % in Arguments in Coq 8.19
	sed -e "/Arguments/ s/%/%_/g" ${SED_FLAG} $*/autosubst2/prop_as_unscoped.v
	# modify constructor names
	sed -e "s/var_ftyp/ftyp_var/g" ${SED_FLAG} $*/autosubst2/def.v 
	sed -e "s/var_fexp/fexp_var/g" ${SED_FLAG} $*/autosubst2/def.v 

%/lngen/def.v: %/lngen/language.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" ${SED_FLAG} $@

%/lngen/prop_ln.v: %/lngen/def.v
	lngen-new --coq $@ --coq-ott .ott $*/lngen/language.ott
	sed -e "s/Require Export .ott./Require Export $*.lngen.def./g" ${SED_FLAG} $@ 

# a hack to force makefile to detect source file changes
.FILE_LIST : ${LNGEN_OUTS} FORCE
	tree . -if -I ${IGNORE_DIRS} | grep -E "v$$" | sort -s > .FILE_LIST.tmp
	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT}  .FILE_LIST
	tree . -if  -I ${IGNORE_DIRS} | grep -E "v$$" | xargs coq_makefile -o $@ -f ${COQ_PROJECT}

coq-only: $(COQ_MAKEFILE)
	${MAKE} -f ${COQ_MAKEFILE}

coq: $(COQ_MAKEFILE) lngen autosubst2
	${MAKE} -f ${COQ_MAKEFILE}

clean-coq-only: 
	${MAKE} -f ${COQ_MAKEFILE} clean

.phony: coq coq_only ott lngen