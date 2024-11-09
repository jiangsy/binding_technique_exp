COQMAKEFILE := CoqMakefile
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

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

autosubst2/def.v:
	autosubst autosubst2/systemf.sig -o autosubst2/def.v -s ucoq
	mv autosubst2/core.v autosubst2/prop_as_core.v
	mv autosubst2/unscoped.v autosubst2/prop_as_unscoped.v
	sed -e "s/Require Import core./Require Import binder.autosubst2.prop_as_core./g" ${SED_FLAG} autosubst2/prop_as_unscoped.v
	sed -e "s/Require Import core unscoped./Require Import binder.autosubst2.prop_as_core binder.autosubst2.prop_as_unscoped./g" ${SED_FLAG} autosubst2/def.v 
	sed -e "s/var_ftyp/ftyp_var/g" ${SED_FLAG} autosubst2/def.v 
	sed -e "s/var_fexp/fexp_var/g" ${SED_FLAG} autosubst2/def.v 

$(COQMAKEFILE):
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

coq: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

.phony: coq autosubst2/def.v