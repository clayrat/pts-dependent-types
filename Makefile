COQMAKEFILE ?= coq_makefile

.PHONY: all rocq extract demo test check clean
all: rocq

vendor/strictness-pcf/theories/Ty.v:
	@echo "vendor/strictness-pcf is missing; run: git submodule update --init" >&2
	@exit 1

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $@

rocq: vendor/strictness-pcf/theories/Ty.v Makefile.coq
	$(MAKE) -f Makefile.coq

# The extracted checker: OCaml demonstrations and regression tests.
extract:
	$(MAKE) -C extraction extract

demo:
	$(MAKE) -C extraction run

test:
	$(MAKE) -C extraction test
	$(MAKE) -C reference test

check: rocq test

clean:
	@if test -f Makefile.coq; then $(MAKE) -f Makefile.coq clean; fi
	$(MAKE) -C extraction clean
	$(MAKE) -C reference clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
