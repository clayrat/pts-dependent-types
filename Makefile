COQMAKEFILE ?= coq_makefile

.PHONY: all rocq vendor clean
all: rocq

vendor/strictness-pcf/theories/Ty.v:
	@echo "vendor/strictness-pcf is missing; run: git submodule update --init" >&2
	@exit 1

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $@

rocq: vendor/strictness-pcf/theories/Ty.v Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	@if test -f Makefile.coq; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
