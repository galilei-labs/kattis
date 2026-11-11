# Kattis examples

## Setup

Create and select an opam switch (OCaml 4.14 or later):

```sh
opam switch create kattis ocaml-base-compiler.4.14.2
opam switch link kattis .
eval "$(opam env)"
```

Add the required repositories and install the dependencies:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add galilei-dev git@github.com:galilei-labs/opam.git
make builddep
```

The Galilei repository and its packages require GitHub SSH access.
`kattis.opam` tracks the dependencies, including Rocq 9.2.0 and
`std-galilei`. `make builddep` installs a virtual package retaining those
dependencies without building this project.
Use `OPAMFLAGS=-y` for non-interactive installation.

## Structure

Each of the 100 problems contains:

- `<problem>.spec`: the formal specification and Focus documentation.
- `<problem>_implem.v`: executable definitions, termination lemmas, and correctness proofs.
- `galilei.toml`: presentation and download metadata.
- `extraction/`: the selected extraction driver and checked-in OCaml `.ml`,
  `.mli`, and separate runtime files under `ocaml/`.

Problem content is generated from the authoritative private repository; see
[Upstream](#upstream) before editing it.

## Build

The root Dune project builds all 100 problems, including their Rocq proofs and
fresh OCaml extractions compiled against their generated interfaces.

```sh
opam exec -- make build       # Build all Dune-enabled problems
opam exec -- make cold        # Build Cold only
opam exec -- make clean       # Remove the shared _build/ directory
```

Equivalently, use `dune build`, or `dune build <problem>` for one problem.
Generated and compiled artifacts stay under `_build/`; builds do not overwrite
checked-in files.

**These builds do not run `rocq-speck check`.** Compilation checks the supplied
proofs, but does not establish that every specification obligation is implemented
or enforce the specification's allowed-axiom policy.

## OCaml extraction

Generate all selected OCaml programs, interfaces, and separate runtimes:

```sh
opam exec -- dune build @extract
```

Check that freshly extracted `.ml` and `.mli` files match the checked-in snapshots:

```sh
opam exec -- dune build @check-snapshot
# Or check one problem:
opam exec -- dune build @cold/extraction/check-snapshot
```

These checks report differences without updating source files. Fix stale
snapshots in the private repository and re-export them, rather than promoting
changes here.

The mutable-array and bigint extraction mappings are trusted, not a verified
extraction backend. Mutable arrays rely on linear use.

## Preview

Preview from the sibling Galilei tooling checkout:

```sh
cd ../focus
PORT=3001 uv run python scripts/serve.py ../kattis/cold
```

The local preview and page path is `/kattis/cold/`.

## Upstream

Problem directories are exported from `100_problems/` in
[`galilei-labs/kattis-private`](https://github.com/galilei-labs/kattis-private).
Make specification, implementation, metadata, and snapshot changes there, then
run its public exporter. `public-export.json` records the exported files and
their hashes; the public build harness is maintained separately.

This repository was previously named `tristan-kattis2`.
