.DEFAULT_GOAL := help
.DELETE_ON_ERROR:

help:
	@echo "make builddep                Install the project's opam dependencies"
	@echo "make builddep-opamfiles      Generate the virtual builddep package"
.PHONY: help

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
