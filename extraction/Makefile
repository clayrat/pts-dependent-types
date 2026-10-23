COQC ?= coqc
DUNE ?= dune

.PHONY: all core extract run test lecture6 slow clean
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
	$(MAKE) lecture6

# The demos print exactly what they printed at the tag lecture-6, whose
# traces and counts the notes of lecture 6 cite.  lecture6.expected is
# that output, recorded at the tag; it changes only with a new tag.
lecture6: extract
	$(DUNE) exec ./main.exe > generated/lecture6.out
	diff -u lecture6.expected generated/lecture6.out
	@echo "lecture6: the demos print the output of the tag lecture-6"

# fact 4 = 24 through the PCF translation: about a minute.
slow: extract
	$(DUNE) exec ./slow.exe

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
