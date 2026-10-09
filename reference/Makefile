OCAML ?= ocaml
OCAMLC ?= ocamlc

.PHONY: all run test clean
all: test

run:
	$(OCAML) pts_native.ml

# The native implementation is separate from the extract.  Only this test
# compiles them together, to compare their answers and complete traces.
test:
	$(MAKE) -C ../extraction extract
	mkdir -p _build
	cp ../extraction/generated/deptypes.ml ../extraction/generated/deptypes.mli pts_native.mli pts_native.ml looping.ml encodings.ml translate.ml choose.ml eliminators.ml diff.ml _build/
	cd _build && $(OCAMLC) deptypes.mli deptypes.ml pts_native.mli pts_native.ml looping.ml encodings.ml translate.ml choose.ml eliminators.ml diff.ml -o diff
	_build/diff

clean:
	rm -rf _build
