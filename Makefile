COQMAKEFILE := CoqMakefile
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)
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

coq_only: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) coq

coq: $(COQMAKEFILE) autosubst2/def.v lngen/prop_ln.v
	+$(MAKE) -f $(COQMAKEFILE) all

autosubst2/def.v:
	autosubst autosubst2/systemf.sig -o $@ -s ucoq
	# rename files and modify imports
	mv autosubst2/core.v autosubst2/prop_as_core.v
	mv autosubst2/unscoped.v autosubst2/prop_as_unscoped.v
	sed -e "s/Require Import core./Require Import binder.autosubst2.prop_as_core./g" ${SED_FLAG}  autosubst2/prop_as_unscoped.v
	sed -e "s/Require Import core unscoped./Require Import binder.autosubst2.prop_as_core binder.autosubst2.prop_as_unscoped./g" ${SED_FLAG} autosubst2/def.v
	# fix warning about % in Arguments in Coq 8.19
	sed -e "/Arguments/ s/%/%_/g" ${SED_FLAG} autosubst2/prop_as_unscoped.v
	# modify constructor names
	sed -e "s/var_ftyp/ftyp_var/g" ${SED_FLAG} autosubst2/def.v 
	sed -e "s/var_fexp/fexp_var/g" ${SED_FLAG} autosubst2/def.v 

lngen/def.v: lngen/systemf.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" ${SED_FLAG} $@

lngen/prop_ln.v: lngen/def.v
	lngen-new --coq $@ --coq-ott $*.ott lngen/systemf.ott
	sed -e "s/Require Export .ott./Require Export binder.lngen.def./g" ${SED_FLAG} $@ 

$(COQMAKEFILE):
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

.phony: coq coq_only