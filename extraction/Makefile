COQC ?= coqc
DUNE ?= dune

.PHONY: all core extract run test slow clean
all: run

core:
	$(MAKE) -C .. rocq

extract: core
	mkdir -p generated
	$(COQC) -Q ../vendor/strictness-pcf/theories PCF -Q ../theories DepTypes Extract.v

run: extract
	$(DUNE) exec ./main.exe

test: extract
	$(DUNE) test

# fact 4 = 24 through the PCF translation: about a minute.
slow: extract
	$(DUNE) exec ./slow.exe

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
