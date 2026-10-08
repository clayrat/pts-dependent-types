COQC ?= coqc
DUNE ?= dune

.PHONY: all core extract run test clean
all: run

core:
	$(MAKE) -C .. rocq

extract: core
	mkdir -p generated
	$(COQC) -Q ../theories DepTypes Extract.v

run: extract
	$(DUNE) exec ./main.exe

test: extract
	$(DUNE) test

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
