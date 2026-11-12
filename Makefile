.DEFAULT_GOAL := help
.DELETE_ON_ERROR:
DUNEFLAGS ?= --display short

help:
	@echo "make build                   Build all Dune-enabled problems"
	@echo "make cold                    Build Cold only"
	@echo "make extract                 Generate both OCaml and Rust extractions"
	@echo "make check-snapshot          Check both backends' reference snapshots"
	@echo "make check-submissions       Check both backends' standalone bundle freshness"
	@echo "Use -ocaml or -rust on extract/check-snapshot/check-submissions for one backend"
	@echo "make clean                   Remove the shared Dune build directory"
	@echo "make builddep                Install the project's opam dependencies"
	@echo "make builddep-opamfiles      Generate the virtual builddep package"
.PHONY: help

build:
	dune build $(DUNEFLAGS) @all

cold:
	dune build $(DUNEFLAGS) cold

extract:
	dune build $(DUNEFLAGS) @extract @extract-rust

extract-ocaml:
	dune build $(DUNEFLAGS) @extract

extract-rust:
	dune build $(DUNEFLAGS) @extract-rust

check-snapshot:
	dune build $(DUNEFLAGS) @check-snapshot @check-rust-snapshot

check-snapshot-ocaml:
	dune build $(DUNEFLAGS) @check-snapshot

check-snapshot-rust:
	dune build $(DUNEFLAGS) @check-rust-snapshot

check-submissions:
	dune build $(DUNEFLAGS) @check-submission @check-rust-submission

check-submissions-ocaml:
	dune build $(DUNEFLAGS) @check-submission

check-submissions-rust:
	dune build $(DUNEFLAGS) @check-rust-submission

.PHONY: extract extract-ocaml extract-rust check-snapshot check-snapshot-ocaml check-snapshot-rust
.PHONY: check-submissions check-submissions-ocaml check-submissions-rust

clean:
	dune clean

.PHONY: build cold clean

### Builddep handling
# Keep dependencies installed without pinning or building the project itself.
define BUILDDEP_OPAM_BODY
opam-version: "2.0"
name: "kattis-builddep"
maintainer: "Galilei Labs"
authors: "Galilei Labs"
homepage: "https://github.com/galilei-labs/kattis"
bug-reports: "https://github.com/galilei-labs/kattis/issues"
synopsis: "Dependencies for the Kattis examples"
description: "A virtual package tracking the dependencies of kattis.opam."
endef
export BUILDDEP_OPAM_BODY

builddep/kattis-builddep.opam: kattis.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@echo "$$BUILDDEP_OPAM_BODY" > $@
	@echo 'depends: [' >> $@
	@opam show -f depends: ./kattis.opam >> $@
	@echo ']' >> $@
	@pins="$$(opam show -f pin-depends: ./kattis.opam)" && \
		if test -n "$$pins"; then \
			printf 'pin-depends: [\n%s\n]\n' "$$pins" >> $@; \
		fi

builddep: builddep/kattis-builddep.opam
	@opam install $(OPAMFLAGS) $<
.PHONY: builddep

builddep-opamfiles: builddep/kattis-builddep.opam
.PHONY: builddep-opamfiles
