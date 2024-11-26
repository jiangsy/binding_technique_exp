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

SYSTEMS := systemf stlc fsub
IGNORE_DIRS := test

# https://stackoverflow.com/questions/3774568/makefile-issue-smart-way-to-scan-directory-tree-for-c-files
rwildcard=$(wildcard $(addsuffix $2, $1))$(foreach d,$(wildcard $(addsuffix *, $1)),$(call rwildcard,$d/,$2))
ALL_SIGS:= $(call rwildcard,${SYSTEMS},*.sig)
ALL_OTTS:= $(call rwildcard,${SYSTEMS},*.ott)

ALL_SIG_DIRS:= $(foreach file,$(ALL_SIGS),$(dir $(file)))
ALL_OTT_DIRS:= $(foreach file,$(ALL_OTTS),$(dir $(file)))

OTT_OUTS   := $(addsuffix def_ott.v,${ALL_OTT_DIRS})
LNGEN_OUTS := $(addsuffix prop_ln.v,${ALL_OTT_DIRS})
# AUTOSUBST2_OUTS := $(addsuffix def_as2.v,${ALL_SIG_DIRS}) $(addsuffix prop_as_unscoped.v,${ALL_SIG_DIRS}) $(addsuffix prop_as_core.v,${ALL_SIG_DIRS})
AUTOSUBST2_OUTS := $(addsuffix def_as2.v,${ALL_SIG_DIRS})

ott: $(OTT_OUTS)
lngen: ${LNGEN_OUTS}
autosubst2: ${AUTOSUBST2_OUTS}

# %/def_as2.v %/prop_as_core.v %/prop_as_unscoped.v: %/language.sig
# 	autosubst $*/language.sig -o $@ -s ucoq
# 	# rename files and modify imports
# 	mv $*/core.v $*/prop_as_core.v
# 	mv $*/unscoped.v $*/prop_as_unscoped.v
# 	sed -e "s/Require Import core./Require Import $(subst /,.,$*).prop_as_core./g" ${SED_FLAG}  $*/prop_as_unscoped.v
#   sed -e "s/Require Import core unscoped./Require Import $(subst /,.,$*).prop_as_core $(subst /,.,$*).prop_as_unscoped./g" ${SED_FLAG} $*/def_as2.v
# 	# fix warning about % in Arguments in Coq 8.19
# 	sed -e "/Arguments/ s/%/%_/g" ${SED_FLAG} $*/prop_as_unscoped.v
# 	# modify constructor names, subst "var_*" intro "*_var" except "var_zero"
# 	perl -i -pe 's/\bvar_((?!zero\b)[a-zA-Z0-9]+)/\1_var/g' $*/def_as2.v

%/def_as2.v: %/language.sig
	autosubst $*/language.sig -o $@ -s ucoq
	rm $*/core.v $*/unscoped.v
	sed -e "s/Require Import core unscoped./Require Import common.prop_as_core common.prop_as_unscoped./g" ${SED_FLAG} $*/def_as2.v
	# modify constructor names, subst "var_*" intro "*_var" except "var_zero"
	perl -i -pe 's/\bvar_((?!zero\b)[a-zA-Z0-9]+)/\1_var/g' $*/def_as2.v

%/def_ott.v: %/language.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" ${SED_FLAG} $@

%/prop_ln.v: %/def_ott.v
	lngen-new --coq $@ --coq-ott $(subst /,.,$*).def_ott $*/language.ott

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

coq: lngen autosubst2 $(COQ_MAKEFILE)
	${MAKE} -f ${COQ_MAKEFILE}

clean-coq-only: 
	${MAKE} -f ${COQ_MAKEFILE} clean

clean: clean-coq-only
	rm ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf
	rm ${OTT_OUTS} ${LNGEN_OUTS} ${AUTOSUBST2_OUTS}

.phony: coq coq_only ott lngen autosubst2