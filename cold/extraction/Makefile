# Compatibility interface: Dune builds proofs, extraction and OCaml artifacts
# under the repository's _build/. The snapshot in ocaml/ is kept.
ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../..)
DUNE ?= dune
SPECK ?= rocq-speck
export SPECK

all: marray

marray:
	$(DUNE) build --root "$(ROOT)" --display short cold/extraction/cold_extracted_marray.ml cold/extraction/cold_extracted_marray.mli

check:
	$(DUNE) build --root "$(ROOT)" --display short cold/extraction
	@echo "cold_extracted_marray.ml matches its .mli"

# Dune's build directory is shared by the whole repository.
clean:
	$(DUNE) clean --root "$(ROOT)"

.PHONY: all marray check clean
