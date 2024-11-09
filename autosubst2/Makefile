COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

VS := $(wildcard *.v)

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): Makefile $(VS)
	coq_makefile -R . autosubst2 $(VS) -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

.PHONY: all clean