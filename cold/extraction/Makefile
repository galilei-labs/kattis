# The marray extraction of cold, built here from ../cold.spec,
# ../cold_implem.v. Unlike the kattis repo's extraction/Makefile, this one
# keeps the .mli Rocq generates: `make` writes
#
#   cold_extracted_marray.ml    the extracted code
#   cold_extracted_marray.mli   its interface, shown on the page
#
# ../.generated/Prelude.v is generated from the .spec as in the kattis repo's
# spec/Makefile. rocq-speck and StdGalilei come from the active opam switch;
# SPECK= can override the executable.
# `make check` compiles the .ml against the .mli.
PROBLEM := cold
LOGICAL := Cold
SPECK   ?= rocq-speck
ROOT    := $(abspath $(CURDIR)/..)
COQC    := rocq compile -Q $(ROOT)/.generated Speck -Q $(ROOT) $(LOGICAL)
OCAMLPKG ?= $(shell ocamlfind query rocq-runtime.kernel >/dev/null 2>&1 && echo rocq-runtime.kernel || echo coq-core.kernel)

all: marray

marray: $(ROOT)/$(PROBLEM)_proofs.vo
	$(COQC) extract_marray.v

$(ROOT)/$(PROBLEM)_proofs.vo: $(ROOT)/$(PROBLEM)_proofs.v $(ROOT)/$(PROBLEM)_implem.vo
	$(COQC) $<

$(ROOT)/$(PROBLEM)_implem.vo: $(ROOT)/$(PROBLEM)_implem.v $(ROOT)/.generated/Prelude.vo
	$(COQC) $<

$(ROOT)/.generated/Prelude.vo: $(ROOT)/.generated/Prelude.v
	$(COQC) $<

$(ROOT)/.generated/Prelude.v: $(ROOT)/$(PROBLEM).spec
	mkdir -p $(ROOT)/.generated
	$(SPECK) dump-spec --prelude $< > $@

check: marray
	rm -rf .check && mkdir .check
	cp marray.ml $(PROBLEM)_extracted_marray.ml $(PROBLEM)_extracted_marray.mli .check/
	cd .check && ocamlfind ocamlc -w -a -package $(OCAMLPKG) -c marray.ml $(PROBLEM)_extracted_marray.mli $(PROBLEM)_extracted_marray.ml
	rm -rf .check
	@echo "$(PROBLEM)_extracted_marray.ml matches its .mli"

# The .ml and .mli are kept: the page reads them.
clean:
	rm -rf .check $(ROOT)/.generated
	rm -f *.vo *.vos *.vok *.glob .*.aux
	rm -f $(ROOT)/*.vo $(ROOT)/*.vos $(ROOT)/*.vok $(ROOT)/*.glob $(ROOT)/.*.aux $(ROOT)/$(PROBLEM)_spec.v

.PHONY: all marray check clean
