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

Install `rustc` (stable) to build the Rust programs. Both repositories use the
published extractor snapshot specified in `kattis.opam`.

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
- `extraction/ocaml/` and `extraction/rust/`: backend-specific extraction drivers
  and build rules, generated references under `snapshots/`, I/O harnesses
  (`ocaml/submit/main.ml` and `rust/harness.rs`), and standalone programs under
  `submit/`. OCaml runtime references also live under `ocaml/snapshots/`.

Problem content is generated from the authoritative private repository; see
[Upstream](#upstream) before editing it.

## Build

The root Dune project builds all 100 problems, including their Rocq proofs and
fresh OCaml extractions compiled against their generated interfaces, standalone
OCaml programs, and Rust
programs compiled in debug and optimized modes.

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
opam exec -- dune build @cold/extraction/ocaml/check-snapshot
```

These checks report differences without updating source files. Fix stale
snapshots in the private repository and re-export them, rather than promoting
changes here.

The I/O harness is `extraction/ocaml/submit/main.ml`; the assembled standalone
program is `extraction/ocaml/submit/<problem>.ml`. Check its freshness with
`opam exec -- make check-submissions-ocaml`. For example, compile Cold directly:

```sh
cp cold/extraction/ocaml/submit/cold.ml _build/cold.ml
ocamlopt -I +unix -I +str unix.cmxa str.cmxa _build/cold.ml -o _build/cold-ocaml
```

The mutable-array and bigint extraction mappings are trusted, not a verified
extraction backend. Mutable arrays rely on linear use.

## Rust extraction

```sh
opam exec -- make extract-rust
opam exec -- make check-snapshot-rust
opam exec -- make check-submissions-rust
rustc --edition=2021 -O cold/extraction/rust/submit/cold.rs -o _build/cold-rust
```

`make extract`, `make check-snapshot` and `make check-submissions` cover both languages; append `-ocaml`
or `-rust` to select one. Snapshot and standalone-bundle checks never promote
changes here: regenerate privately and re-export. The public CI builds both
Rust profiles, checks reference and bundle freshness, and tests the assembler.
Private samples, validators, submission tools and judge credentials are not
exported, so public CI does not run the private sample or judge campaigns.

The standalone Rust files contain their selected runtimes and BSD notices and
need no Cargo dependencies or extractor installation to compile. Re-extraction
uses the installed extractor's runtime files. Each route explicitly pairs its
array import and copy-on-write option with the corresponding runtime; ordinary
and strong CoW are not interchangeable. Strong CoW revokes older array versions
and is not a general persistent-array refinement. These runtime mappings and
I/O adapters are trusted; the complete compiler is not proved correct.

The combined extraction download described by `galilei.toml` includes both
OCaml and Rust sources. Both language interfaces point to their standalone programs.

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
